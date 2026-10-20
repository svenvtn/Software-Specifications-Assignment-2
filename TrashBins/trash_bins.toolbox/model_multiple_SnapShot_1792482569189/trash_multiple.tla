--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
    \* Bin variables (indexed by b \in Bins)
    outerDoorOpen = [b \in Bins |-> FALSE],
    outerDoorLocked = [b \in Bins |-> TRUE],
    trapDoorOpen = [b \in Bins |-> FALSE],
    ramExtended = [b \in Bins |-> FALSE],
    trashInTop = [b \in Bins |-> 0],
    trashCompressed = [b \in Bins |-> 0],
    trashUncompressed = [b \in Bins |-> 0],
    trashCapacity = [b \in Bins |-> MaxCapacity],
    trapDestroyed = [b \in Bins |-> FALSE],
    binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
    binSensor = [b \in Bins |-> [sensor |-> "idle"]],

    \* User variables (indexed by u \in Users)
    userTrash = [u \in Users |-> 0],
    permissions = [u \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]],

    \* Truck variables (indexed by t \in Trucks)
    truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]],

    \* Central communication and verification
    scans = << >>,
    serverRequests = << >>,
    serverResponses = << >>,
    authorizedUsers = [u \in Users |-> FALSE];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each trash bin, the outer door can only be locked if it is closed.
OuterDoorLocked == FALSE
\* For each trash bin, the vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == FALSE
\* For each trash bin, every time it is full, it is eventually not full anymore.
TrashEmptied == FALSE
\* No unauthorized user can open the outer door of any trash bin.
AuthorizedOpenOnly == FALSE
\* Each user infinitely often has trash and infinitely often has no trash.
UserTrash == FALSE
\* For each user, every time they have trash they can deposit their trash.
UserTrashDeposited == FALSE
\* For each trash bin, every time a truck is requested for it, a truck has eventually emptied it.
TruckEmpties == FALSE

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
process binProcess \in Bins
begin
    BinWaitForCommand:
    while TRUE do
        await binCommand[self].command /= "finished";
        if binCommand[self].command = "change_outer_door" then
            assert ~outerDoorLocked[self];
            outerDoorOpen[self] := binCommand[self].open;
            if ~outerDoorOpen[self] then
                binSensor[self] := [sensor |-> "outer_door_closed"];
            end if
        elsif binCommand[self].command = "change_outer_lock" then
            assert ~outerDoorOpen[self];
            outerDoorLocked[self] := ~(binCommand[self].open);
        elsif binCommand[self].command = "change_trap_door" then
            assert outerDoorLocked[self];
            if ramExtended[self] \/ (trashCompressed[self] + trashUncompressed[self] > trashCapacity[self]) then
                trapDestroyed[self] := TRUE;
            end if;
            trapDoorOpen[self] := binCommand[self].open;
            if trapDoorOpen[self] then
                trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
                trashInTop[self] := 0;
            end if
        elsif binCommand[self].command = "change_ram" then
            assert outerDoorLocked[self];
            ramExtended[self] := binCommand[self].open;
            if ramExtended[self] then
                if ~trapDoorOpen[self] then
                    trapDestroyed[self] := TRUE;
                end if;
                compress(trashCompressed[self], trashUncompressed[self]);
            end if;
        elsif binCommand[self].command = "empty" then
            assert outerDoorLocked[self];
            assert ~trapDoorOpen[self];
            assert ~ramExtended[self];
            assert trashInTop[self] = 0;
            assert trashUncompressed[self] = 0;
            trashCompressed[self] := 0;
        end if;
    BinCommandFinished:
        binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
    with b \in Bins do
        write(scans, [user |-> self, bin |-> b]);
    end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* DUMMY truck process type.
\* Remodel it to react to requests and empty the requested trash bin!
fair process truckProcess \in Trucks
begin
TruckStart:
    while TRUE do
        WaitRequest:
        await truckCommand[self].command = "request";
        
        Arrived:
        truckCommand[self] := [command |-> "arrived", bin |-> truckCommand[self].bin];
        
        EmptyBin:
        binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
        
        WaitEmptyBin:
        await binCommand[truckCommand[self].bin].command = "finished";
        
        Emptied:
        truckCommand[self] := [command |-> "emptied", bin |-> truckCommand[self].bin];
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control all trash bins in the system and handle requests by users!
fair process controlProcess = Control
variables
    req = [user |-> 0, bin |-> 0],
    sRes = [user |-> 0, permission |-> FALSE],
    \* Stores 0 if no truck is assigned, or the truck ID t \in Trucks
    truckRequested = [b \in Bins |-> 0];
begin
ControlStart:
    while TRUE do
        \* 1. Dispatch an available truck to any bin exceeding capacity
        if \E b \in Bins : ~TrashFitsCapacity(b, MaxUserTrash) /\ truckRequested[b] = 0 then
            if \E t \in Trucks : truckCommand[t].command = "emptied" /\ (\A b2 \in Bins : truckRequested[b2] /= t) then
                with b \in {bin \in Bins : ~TrashFitsCapacity(bin, MaxUserTrash) /\ truckRequested[bin] = 0},
                     t \in {tr \in Trucks : truckCommand[tr].command = "emptied" /\ (\A b2 \in Bins : truckRequested[b2] /= tr)} do
                    truckCommand[t] := [command |-> "request", bin |-> b];
                    truckRequested[b] := t;
                end with;
            end if;
        end if;

        \* 2. Non-deterministic event processing
        WaitEvent:
        either
            \* Acknowledge emptied trucks
            await \E b \in Bins : truckRequested[b] /= 0 /\ truckCommand[truckRequested[b]].command = "emptied";
            with b \in {bin \in Bins : truckRequested[bin] /= 0 /\ truckCommand[truckRequested[bin]].command = "emptied"} do
                truckRequested[b] := 0;
            end with;
        or
            \* Handle user scans ONLY IF no finished truck is awaiting acknowledgement
            await ~(\E b \in Bins : truckRequested[b] /= 0 /\ truckCommand[truckRequested[b]].command = "emptied");
            read(scans, req);
            write(serverRequests, [user |-> req.user]);
            
            WaitServer:
            read(serverResponses, sRes);
            
            CheckPermission:
            if sRes.permission /\ TrashFitsCapacity(req.bin, MaxUserTrash) /\ truckRequested[req.bin] = 0 then
                \* Unlock outer door for req.bin
                binCommand[req.bin] := [command |-> "change_outer_lock", open |-> TRUE];
                
                WaitUserUnlock:
                await binCommand[req.bin].command = "finished";
                
                \* Track authorization globally
                authorizedUsers[req.user] := TRUE;
                write(permissions[req.user], [user |-> req.user, bin |-> req.bin, granted |-> TRUE]);
                
                WaitDoorClose:
                await binSensor[req.bin].sensor = "outer_door_closed" /\ binCommand[req.bin].command = "finished";
                binSensor[req.bin] := [sensor |-> "idle"];
                
                \* Revoke authorization
                authorizedUsers[req.user] := FALSE;
                
                LockOuterDoor:
                binCommand[req.bin] := [command |-> "change_outer_lock", open |-> FALSE];
                
                WaitLockOuterDoor:
                await binCommand[req.bin].command = "finished";
                
                OpenTrapDoor:
                binCommand[req.bin] := [command |-> "change_trap_door", open |-> TRUE];
                
                WaitOpenTrap:
                await binCommand[req.bin].command = "finished";
                
                ExtendRam:
                binCommand[req.bin] := [command |-> "change_ram", open |-> TRUE];
                
                WaitExtendRam:
                await binCommand[req.bin].command = "finished";
                
                RetractRam:
                binCommand[req.bin] := [command |-> "change_ram", open |-> FALSE];
                
                WaitRetractRam:
                await binCommand[req.bin].command = "finished";
                
                CloseTrapDoor:
                binCommand[req.bin] := [command |-> "change_trap_door", open |-> FALSE];
                
                WaitCloseTrap:
                await binCommand[req.bin].command = "finished";
            else
                \* Decline permission for req.bin
                write(permissions[req.user], [user |-> req.user, bin |-> req.bin, granted |-> FALSE]);
            end if;
        end either;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "19259d60" /\ chksum(tla) = "b3bcf2d5")
\* Process variable req of process serverProcess at line 253 col 3 changed to req_
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, binCommand, binSensor, userTrash, permissions, 
          truckCommand, scans, serverRequests, serverResponses, 
          authorizedUsers, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}






TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)









OuterDoorLocked == FALSE

RamOuterDoor == FALSE

TrashEmptied == FALSE

AuthorizedOpenOnly == FALSE

UserTrash == FALSE

UserTrashDeposited == FALSE

TruckEmpties == FALSE

VARIABLES perm, selectedBin, req_, req, sRes, truckRequested

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, binCommand, binSensor, userTrash, permissions, 
           truckCommand, scans, serverRequests, serverResponses, 
           authorizedUsers, pc, perm, selectedBin, req_, req, sRes, 
           truckRequested >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ userTrash = [u \in Users |-> 0]
        /\ permissions = [u \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        /\ scans = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ authorizedUsers = [u \in Users |-> FALSE]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req_ = [user |-> 0]
        (* Process controlProcess *)
        /\ req = [user |-> 0, bin |-> 0]
        /\ sRes = [user |-> 0, permission |-> FALSE]
        /\ truckRequested = [b \in Bins |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 165, column 13.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 171, column 13.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 174, column 13.")
                                                            /\ IF ramExtended[self] \/ (trashCompressed[self] + trashUncompressed[self] > trashCapacity[self])
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 184, column 13.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 193, column 13.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 194, column 13.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 195, column 13.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 196, column 13.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 197, column 13.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, binCommand, 
                                           userTrash, permissions, 
                                           truckCommand, scans, serverRequests, 
                                           serverResponses, authorizedUsers, 
                                           perm, selectedBin, req_, req, sRes, 
                                           truckRequested >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, binSensor, 
                                            userTrash, permissions, 
                                            truckCommand, scans, 
                                            serverRequests, serverResponses, 
                                            authorizedUsers, perm, selectedBin, 
                                            req_, req, sRes, truckRequested >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, binCommand, 
                                           binSensor, userTrash, permissions, 
                                           truckCommand, scans, serverRequests, 
                                           serverResponses, authorizedUsers, 
                                           perm, selectedBin, req_, req, sRes, 
                                           truckRequested >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E b \in Bins:
                           scans' = Append(scans, ([user |-> self, bin |-> b]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, userTrash, permissions, 
                                      truckCommand, serverRequests, 
                                      serverResponses, authorizedUsers, perm, 
                                      selectedBin, req_, req, sRes, 
                                      truckRequested >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 228, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 229, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               binCommand, binSensor, 
                                               userTrash, truckCommand, scans, 
                                               serverRequests, serverResponses, 
                                               authorizedUsers, selectedBin, 
                                               req_, req, sRes, truckRequested >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binSensor, 
                                      userTrash, permissions, truckCommand, 
                                      scans, serverRequests, serverResponses, 
                                      authorizedUsers, perm, selectedBin, req_, 
                                      req, sRes, truckRequested >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, binCommand, 
                                           binSensor, userTrash, permissions, 
                                           truckCommand, scans, serverRequests, 
                                           serverResponses, authorizedUsers, 
                                           perm, selectedBin, req_, req, sRes, 
                                           truckRequested >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 236, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, permissions, 
                                          truckCommand, scans, serverRequests, 
                                          serverResponses, authorizedUsers, 
                                          perm, selectedBin, req_, req, sRes, 
                                          truckRequested >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, binSensor, 
                                       userTrash, permissions, truckCommand, 
                                       scans, serverRequests, serverResponses, 
                                       authorizedUsers, perm, selectedBin, 
                                       req_, req, sRes, truckRequested >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, binCommand, 
                                             binSensor, userTrash, permissions, 
                                             truckCommand, scans, 
                                             serverRequests, serverResponses, 
                                             authorizedUsers, perm, 
                                             selectedBin, req_, req, sRes, 
                                             truckRequested >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, permissions, truckCommand, 
                                      scans, serverRequests, serverResponses, 
                                      authorizedUsers, perm, selectedBin, req_, 
                                      req, sRes, truckRequested >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       binCommand, binSensor, userTrash, 
                                       permissions, truckCommand, scans, 
                                       serverRequests, serverResponses, 
                                       authorizedUsers, perm, selectedBin, 
                                       req_, req, sRes, truckRequested >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req_' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req_'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req_'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, userTrash, permissions, 
                                      truckCommand, scans, authorizedUsers, 
                                      perm, selectedBin, req, sRes, 
                                      truckRequested >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "WaitRequest"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, binCommand, 
                                    binSensor, userTrash, permissions, 
                                    truckCommand, scans, serverRequests, 
                                    serverResponses, authorizedUsers, perm, 
                                    selectedBin, req_, req, sRes, 
                                    truckRequested >>

WaitRequest(self) == /\ pc[self] = "WaitRequest"
                     /\ truckCommand[self].command = "request"
                     /\ pc' = [pc EXCEPT ![self] = "Arrived"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, binCommand, 
                                     binSensor, userTrash, permissions, 
                                     truckCommand, scans, serverRequests, 
                                     serverResponses, authorizedUsers, perm, 
                                     selectedBin, req_, req, sRes, 
                                     truckRequested >>

Arrived(self) == /\ pc[self] = "Arrived"
                 /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "arrived", bin |-> truckCommand[self].bin]]
                 /\ pc' = [pc EXCEPT ![self] = "EmptyBin"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binCommand, binSensor, 
                                 userTrash, permissions, scans, serverRequests, 
                                 serverResponses, authorizedUsers, perm, 
                                 selectedBin, req_, req, sRes, truckRequested >>

EmptyBin(self) == /\ pc[self] = "EmptyBin"
                  /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                  /\ pc' = [pc EXCEPT ![self] = "WaitEmptyBin"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, binSensor, userTrash, 
                                  permissions, truckCommand, scans, 
                                  serverRequests, serverResponses, 
                                  authorizedUsers, perm, selectedBin, req_, 
                                  req, sRes, truckRequested >>

WaitEmptyBin(self) == /\ pc[self] = "WaitEmptyBin"
                      /\ binCommand[truckCommand[self].bin].command = "finished"
                      /\ pc' = [pc EXCEPT ![self] = "Emptied"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, userTrash, permissions, 
                                      truckCommand, scans, serverRequests, 
                                      serverResponses, authorizedUsers, perm, 
                                      selectedBin, req_, req, sRes, 
                                      truckRequested >>

Emptied(self) == /\ pc[self] = "Emptied"
                 /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "emptied", bin |-> truckCommand[self].bin]]
                 /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binCommand, binSensor, 
                                 userTrash, permissions, scans, serverRequests, 
                                 serverResponses, authorizedUsers, perm, 
                                 selectedBin, req_, req, sRes, truckRequested >>

truckProcess(self) == TruckStart(self) \/ WaitRequest(self)
                         \/ Arrived(self) \/ EmptyBin(self)
                         \/ WaitEmptyBin(self) \/ Emptied(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ IF \E b \in Bins : ~TrashFitsCapacity(b, MaxUserTrash) /\ truckRequested[b] = 0
                      THEN /\ IF \E t \in Trucks : truckCommand[t].command = "emptied" /\ (\A b2 \in Bins : truckRequested[b2] /= t)
                                 THEN /\ \E b \in {bin \in Bins : ~TrashFitsCapacity(bin, MaxUserTrash) /\ truckRequested[bin] = 0}:
                                           \E t \in {tr \in Trucks : truckCommand[tr].command = "emptied" /\ (\A b2 \in Bins : truckRequested[b2] /= tr)}:
                                             /\ truckCommand' = [truckCommand EXCEPT ![t] = [command |-> "request", bin |-> b]]
                                             /\ truckRequested' = [truckRequested EXCEPT ![b] = t]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << truckCommand, 
                                                      truckRequested >>
                      ELSE /\ TRUE
                           /\ UNCHANGED << truckCommand, truckRequested >>
                /\ pc' = [pc EXCEPT ![Control] = "WaitEvent"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, binCommand, binSensor, 
                                userTrash, permissions, scans, serverRequests, 
                                serverResponses, authorizedUsers, perm, 
                                selectedBin, req_, req, sRes >>

WaitEvent == /\ pc[Control] = "WaitEvent"
             /\ \/ /\ \E b \in Bins : truckRequested[b] /= 0 /\ truckCommand[truckRequested[b]].command = "emptied"
                   /\ \E b \in {bin \in Bins : truckRequested[bin] /= 0 /\ truckCommand[truckRequested[bin]].command = "emptied"}:
                        truckRequested' = [truckRequested EXCEPT ![b] = 0]
                   /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                   /\ UNCHANGED <<scans, serverRequests, req>>
                \/ /\ ~(\E b \in Bins : truckRequested[b] /= 0 /\ truckCommand[truckRequested[b]].command = "emptied")
                   /\ scans /= <<>>
                   /\ req' = Head(scans)
                   /\ scans' = Tail(scans)
                   /\ serverRequests' = Append(serverRequests, ([user |-> req'.user]))
                   /\ pc' = [pc EXCEPT ![Control] = "WaitServer"]
                   /\ UNCHANGED truckRequested
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             binCommand, binSensor, userTrash, permissions, 
                             truckCommand, serverResponses, authorizedUsers, 
                             perm, selectedBin, req_, sRes >>

WaitServer == /\ pc[Control] = "WaitServer"
              /\ serverResponses /= <<>>
              /\ sRes' = Head(serverResponses)
              /\ serverResponses' = Tail(serverResponses)
              /\ pc' = [pc EXCEPT ![Control] = "CheckPermission"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              binCommand, binSensor, userTrash, permissions, 
                              truckCommand, scans, serverRequests, 
                              authorizedUsers, perm, selectedBin, req_, req, 
                              truckRequested >>

CheckPermission == /\ pc[Control] = "CheckPermission"
                   /\ IF sRes.permission /\ TrashFitsCapacity(req.bin, MaxUserTrash) /\ truckRequested[req.bin] = 0
                         THEN /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
                              /\ pc' = [pc EXCEPT ![Control] = "WaitUserUnlock"]
                              /\ UNCHANGED permissions
                         ELSE /\ permissions' = [permissions EXCEPT ![req.user] = Append((permissions[req.user]), ([user |-> req.user, bin |-> req.bin, granted |-> FALSE]))]
                              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                              /\ UNCHANGED binCommand
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, binSensor, 
                                   userTrash, truckCommand, scans, 
                                   serverRequests, serverResponses, 
                                   authorizedUsers, perm, selectedBin, req_, 
                                   req, sRes, truckRequested >>

WaitUserUnlock == /\ pc[Control] = "WaitUserUnlock"
                  /\ binCommand[req.bin].command = "finished"
                  /\ authorizedUsers' = [authorizedUsers EXCEPT ![req.user] = TRUE]
                  /\ permissions' = [permissions EXCEPT ![req.user] = Append((permissions[req.user]), ([user |-> req.user, bin |-> req.bin, granted |-> TRUE]))]
                  /\ pc' = [pc EXCEPT ![Control] = "WaitDoorClose"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, binCommand, binSensor, 
                                  userTrash, truckCommand, scans, 
                                  serverRequests, serverResponses, perm, 
                                  selectedBin, req_, req, sRes, truckRequested >>

WaitDoorClose == /\ pc[Control] = "WaitDoorClose"
                 /\ binSensor[req.bin].sensor = "outer_door_closed" /\ binCommand[req.bin].command = "finished"
                 /\ binSensor' = [binSensor EXCEPT ![req.bin] = [sensor |-> "idle"]]
                 /\ authorizedUsers' = [authorizedUsers EXCEPT ![req.user] = FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "LockOuterDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binCommand, userTrash, 
                                 permissions, truckCommand, scans, 
                                 serverRequests, serverResponses, perm, 
                                 selectedBin, req_, req, sRes, truckRequested >>

LockOuterDoor == /\ pc[Control] = "LockOuterDoor"
                 /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
                 /\ pc' = [pc EXCEPT ![Control] = "WaitLockOuterDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binSensor, userTrash, 
                                 permissions, truckCommand, scans, 
                                 serverRequests, serverResponses, 
                                 authorizedUsers, perm, selectedBin, req_, req, 
                                 sRes, truckRequested >>

WaitLockOuterDoor == /\ pc[Control] = "WaitLockOuterDoor"
                     /\ binCommand[req.bin].command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, binCommand, 
                                     binSensor, userTrash, permissions, 
                                     truckCommand, scans, serverRequests, 
                                     serverResponses, authorizedUsers, perm, 
                                     selectedBin, req_, req, sRes, 
                                     truckRequested >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_trap_door", open |-> TRUE]]
                /\ pc' = [pc EXCEPT ![Control] = "WaitOpenTrap"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, binSensor, userTrash, 
                                permissions, truckCommand, scans, 
                                serverRequests, serverResponses, 
                                authorizedUsers, perm, selectedBin, req_, req, 
                                sRes, truckRequested >>

WaitOpenTrap == /\ pc[Control] = "WaitOpenTrap"
                /\ binCommand[req.bin].command = "finished"
                /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, binCommand, binSensor, 
                                userTrash, permissions, truckCommand, scans, 
                                serverRequests, serverResponses, 
                                authorizedUsers, perm, selectedBin, req_, req, 
                                sRes, truckRequested >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_ram", open |-> TRUE]]
             /\ pc' = [pc EXCEPT ![Control] = "WaitExtendRam"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             binSensor, userTrash, permissions, truckCommand, 
                             scans, serverRequests, serverResponses, 
                             authorizedUsers, perm, selectedBin, req_, req, 
                             sRes, truckRequested >>

WaitExtendRam == /\ pc[Control] = "WaitExtendRam"
                 /\ binCommand[req.bin].command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "RetractRam"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binCommand, binSensor, 
                                 userTrash, permissions, truckCommand, scans, 
                                 serverRequests, serverResponses, 
                                 authorizedUsers, perm, selectedBin, req_, req, 
                                 sRes, truckRequested >>

RetractRam == /\ pc[Control] = "RetractRam"
              /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_ram", open |-> FALSE]]
              /\ pc' = [pc EXCEPT ![Control] = "WaitRetractRam"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              binSensor, userTrash, permissions, truckCommand, 
                              scans, serverRequests, serverResponses, 
                              authorizedUsers, perm, selectedBin, req_, req, 
                              sRes, truckRequested >>

WaitRetractRam == /\ pc[Control] = "WaitRetractRam"
                  /\ binCommand[req.bin].command = "finished"
                  /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, binCommand, binSensor, 
                                  userTrash, permissions, truckCommand, scans, 
                                  serverRequests, serverResponses, 
                                  authorizedUsers, perm, selectedBin, req_, 
                                  req, sRes, truckRequested >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [binCommand EXCEPT ![req.bin] = [command |-> "change_trap_door", open |-> FALSE]]
                 /\ pc' = [pc EXCEPT ![Control] = "WaitCloseTrap"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binSensor, userTrash, 
                                 permissions, truckCommand, scans, 
                                 serverRequests, serverResponses, 
                                 authorizedUsers, perm, selectedBin, req_, req, 
                                 sRes, truckRequested >>

WaitCloseTrap == /\ pc[Control] = "WaitCloseTrap"
                 /\ binCommand[req.bin].command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, binCommand, binSensor, 
                                 userTrash, permissions, truckCommand, scans, 
                                 serverRequests, serverResponses, 
                                 authorizedUsers, perm, selectedBin, req_, req, 
                                 sRes, truckRequested >>

controlProcess == ControlStart \/ WaitEvent \/ WaitServer
                     \/ CheckPermission \/ WaitUserUnlock \/ WaitDoorClose
                     \/ LockOuterDoor \/ WaitLockOuterDoor \/ OpenTrapDoor
                     \/ WaitOpenTrap \/ ExtendRam \/ WaitExtendRam
                     \/ RetractRam \/ WaitRetractRam \/ CloseTrapDoor
                     \/ WaitCloseTrap

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Oct 19 17:19:53 CEST 2026 by 20254351
\* Last modified Mon Oct 19 16:53:55 CEST 2026 by 20254351
