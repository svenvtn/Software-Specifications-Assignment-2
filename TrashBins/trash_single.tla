---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

variables
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  userTrash = 0,

  binCommand = [command |-> "finished", open |-> FALSE],
  binSensor = [sensor |-> "idle"],
  scans = << >>,
  permissions = << >>,
  serverRequests = << >>,
  serverResponses = << >>,
  truckCommand = [command |-> "emptied", bin |-> 1];
  authorizedUsers = [u \in Users |-> FALSE];

define

Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity

TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1

CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded

OuterDoorLocked == outerDoorLocked => ~outerDoorOpen
RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)
TrashEmptied == [](~TrashFitsCapacity(MaxUserTrash) => <>(Trash = 0))
AuthorizedOpenOnly == outerDoorOpen => \E u \in Users : authorizedUsers[u]
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)
UserTrashDeposited == []((userTrash > 0) => <>(userTrash = 0))
TruckEmpties == []((truckCommand.command = "request") => <>(truckCommand.command = "emptied"))

end define;

macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro

fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;

fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
      end if;
    end while;
end process;

fair process serverProcess = Server
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

fair process truckProcess \in Trucks
begin
TruckStart:
    while TRUE do
        WaitRequest:
        await truckCommand.command = "request";
        
        Arrived:
        truckCommand := [command |-> "arrived", bin |-> 1];
        
        EmptyBin:
        binCommand := [command |-> "empty", open |-> FALSE];
        
        WaitEmptyBin:
        await binCommand.command = "finished";
        
        Emptied:
        truckCommand := [command |-> "emptied", bin |-> 1];
    end while;
end process

fair process controlProcess = Control
variables
    req = [user |-> 0, bin |-> 0],
    sRes = [user |-> 0, permission |-> FALSE],
    truckRequested = FALSE;
begin
ControlStart:
    while TRUE do
        if ~TrashFitsCapacity(MaxUserTrash) /\ ~truckRequested then
            truckCommand := [command |-> "request", bin |-> 1];
            truckRequested := TRUE;
        end if;
        
        WaitEvent:
        either
            await truckCommand.command = "emptied" /\ truckRequested;
            truckRequested := FALSE;
        or
            await ~(truckCommand.command = "emptied" /\ truckRequested);
            read(scans, req);
            write(serverRequests, [user |-> req.user]);
            
            WaitServer:
            read(serverResponses, sRes);
            
            CheckPermission:
            if sRes.permission /\ TrashFitsCapacity(MaxUserTrash) /\ ~truckRequested then
                binCommand := [command |-> "change_outer_lock", open |-> TRUE];
                
                WaitUserUnlock:
                await binCommand.command = "finished";
                
                authorizedUsers[req.user] := TRUE;
                write(permissions, [user |-> req.user, bin |-> req.bin, granted |-> TRUE]);
                
                WaitDoorClose:
                await binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished";
                binSensor := [sensor |-> "idle"];
                
                authorizedUsers[req.user] := FALSE;
                
                LockOuterDoor:
                binCommand := [command |-> "change_outer_lock", open |-> FALSE];
                
                WaitLockOuterDoor:
                await binCommand.command = "finished";
                
                OpenTrapDoor:
                binCommand := [command |-> "change_trap_door", open |-> TRUE];
                
                WaitOpenTrap:
                await binCommand.command = "finished";
                
                ExtendRam:
                binCommand := [command |-> "change_ram", open |-> TRUE];
                
                WaitExtendRam:
                await binCommand.command = "finished";
                
                RetractRam:
                binCommand := [command |-> "change_ram", open |-> FALSE];
                
                WaitRetractRam:
                await binCommand.command = "finished";
                
                CloseTrapDoor:
                binCommand := [command |-> "change_trap_door", open |-> FALSE];
                
                WaitCloseTrap:
                await binCommand.command = "finished";
            else
                write(permissions, [user |-> req.user, bin |-> req.bin, granted |-> FALSE]);
            end if;
        end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4e8905c1" /\ chksum(tla) = "8cc8ed4e")
\* Process variable req of process serverProcess at line 188 col 3 changed to req_
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, authorizedUsers, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity

TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1

CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded

OuterDoorLocked == outerDoorLocked => ~outerDoorOpen
RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)
TrashEmptied == [](~TrashFitsCapacity(MaxUserTrash) => <>(Trash = 0))
AuthorizedOpenOnly == outerDoorOpen => \E u \in Users : authorizedUsers[u]
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)
UserTrashDeposited == []((userTrash > 0) => <>(userTrash = 0))
TruckEmpties == []((truckCommand.command = "request") => <>(truckCommand.command = "emptied"))

VARIABLES perm, req_, req, sRes, truckRequested

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           authorizedUsers, pc, perm, req_, req, sRes, truckRequested >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        /\ authorizedUsers = [u \in Users |-> FALSE]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req_ = [user |-> 0]
        (* Process controlProcess *)
        /\ req = [user |-> 0, bin |-> 0]
        /\ sRes = [user |-> 0, permission |-> FALSE]
        /\ truckRequested = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 109, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 115, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 118, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 128, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 137, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 138, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 139, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 140, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 141, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 144, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, authorizedUsers, perm, 
                                           req_, req, sRes, truckRequested >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, authorizedUsers, 
                                            perm, req_, req, sRes, 
                                            truckRequested >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           authorizedUsers, perm, req_, req, 
                                           sRes, truckRequested >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, authorizedUsers, perm, 
                                      req_, req, sRes, truckRequested >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 167, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 168, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, authorizedUsers, 
                                               req_, req, sRes, truckRequested >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, authorizedUsers, perm, 
                                      req_, req, sRes, truckRequested >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           authorizedUsers, perm, req_, req, 
                                           sRes, truckRequested >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 175, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          authorizedUsers, perm, req_, req, 
                                          sRes, truckRequested >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, authorizedUsers, perm, 
                                       req_, req, sRes, truckRequested >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             authorizedUsers, perm, req_, req, 
                                             sRes, truckRequested >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, authorizedUsers, perm, 
                                      req_, req, sRes, truckRequested >>

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
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, 
                                       authorizedUsers, perm, req_, req, sRes, 
                                       truckRequested >>

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
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, 
                                      authorizedUsers, perm, req, sRes, 
                                      truckRequested >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "WaitRequest"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, authorizedUsers, perm, req_, 
                                    req, sRes, truckRequested >>

WaitRequest(self) == /\ pc[self] = "WaitRequest"
                     /\ truckCommand.command = "request"
                     /\ pc' = [pc EXCEPT ![self] = "Arrived"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, authorizedUsers, perm, req_, 
                                     req, sRes, truckRequested >>

Arrived(self) == /\ pc[self] = "Arrived"
                 /\ truckCommand' = [command |-> "arrived", bin |-> 1]
                 /\ pc' = [pc EXCEPT ![self] = "EmptyBin"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, authorizedUsers, perm, req_, 
                                 req, sRes, truckRequested >>

EmptyBin(self) == /\ pc[self] = "EmptyBin"
                  /\ binCommand' = [command |-> "empty", open |-> FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "WaitEmptyBin"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binSensor, scans, 
                                  permissions, serverRequests, serverResponses, 
                                  truckCommand, authorizedUsers, perm, req_, 
                                  req, sRes, truckRequested >>

WaitEmptyBin(self) == /\ pc[self] = "WaitEmptyBin"
                      /\ binCommand.command = "finished"
                      /\ pc' = [pc EXCEPT ![self] = "Emptied"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, 
                                      authorizedUsers, perm, req_, req, sRes, 
                                      truckRequested >>

Emptied(self) == /\ pc[self] = "Emptied"
                 /\ truckCommand' = [command |-> "emptied", bin |-> 1]
                 /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, authorizedUsers, perm, req_, 
                                 req, sRes, truckRequested >>

truckProcess(self) == TruckStart(self) \/ WaitRequest(self)
                         \/ Arrived(self) \/ EmptyBin(self)
                         \/ WaitEmptyBin(self) \/ Emptied(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ IF ~TrashFitsCapacity(MaxUserTrash) /\ ~truckRequested
                      THEN /\ truckCommand' = [command |-> "request", bin |-> 1]
                           /\ truckRequested' = TRUE
                      ELSE /\ TRUE
                           /\ UNCHANGED << truckCommand, truckRequested >>
                /\ pc' = [pc EXCEPT ![Control] = "WaitEvent"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, authorizedUsers, perm, req_, 
                                req, sRes >>

WaitEvent == /\ pc[Control] = "WaitEvent"
             /\ \/ /\ truckCommand.command = "emptied" /\ truckRequested
                   /\ truckRequested' = FALSE
                   /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                   /\ UNCHANGED <<scans, serverRequests, req>>
                \/ /\ ~(truckCommand.command = "emptied" /\ truckRequested)
                   /\ scans /= <<>>
                   /\ req' = Head(scans)
                   /\ scans' = Tail(scans)
                   /\ serverRequests' = Append(serverRequests, ([user |-> req'.user]))
                   /\ pc' = [pc EXCEPT ![Control] = "WaitServer"]
                   /\ UNCHANGED truckRequested
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, permissions, 
                             serverResponses, truckCommand, authorizedUsers, 
                             perm, req_, sRes >>

WaitServer == /\ pc[Control] = "WaitServer"
              /\ serverResponses /= <<>>
              /\ sRes' = Head(serverResponses)
              /\ serverResponses' = Tail(serverResponses)
              /\ pc' = [pc EXCEPT ![Control] = "CheckPermission"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binCommand, binSensor, scans, 
                              permissions, serverRequests, truckCommand, 
                              authorizedUsers, perm, req_, req, truckRequested >>

CheckPermission == /\ pc[Control] = "CheckPermission"
                   /\ IF sRes.permission /\ TrashFitsCapacity(MaxUserTrash) /\ ~truckRequested
                         THEN /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
                              /\ pc' = [pc EXCEPT ![Control] = "WaitUserUnlock"]
                              /\ UNCHANGED permissions
                         ELSE /\ permissions' = Append(permissions, ([user |-> req.user, bin |-> req.bin, granted |-> FALSE]))
                              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                              /\ UNCHANGED binCommand
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binSensor, scans, serverRequests, 
                                   serverResponses, truckCommand, 
                                   authorizedUsers, perm, req_, req, sRes, 
                                   truckRequested >>

WaitUserUnlock == /\ pc[Control] = "WaitUserUnlock"
                  /\ binCommand.command = "finished"
                  /\ authorizedUsers' = [authorizedUsers EXCEPT ![req.user] = TRUE]
                  /\ permissions' = Append(permissions, ([user |-> req.user, bin |-> req.bin, granted |-> TRUE]))
                  /\ pc' = [pc EXCEPT ![Control] = "WaitDoorClose"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, 
                                  binSensor, scans, serverRequests, 
                                  serverResponses, truckCommand, perm, req_, 
                                  req, sRes, truckRequested >>

WaitDoorClose == /\ pc[Control] = "WaitDoorClose"
                 /\ binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished"
                 /\ binSensor' = [sensor |-> "idle"]
                 /\ authorizedUsers' = [authorizedUsers EXCEPT ![req.user] = FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "LockOuterDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, perm, req_, req, sRes, 
                                 truckRequested >>

LockOuterDoor == /\ pc[Control] = "LockOuterDoor"
                 /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "WaitLockOuterDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, authorizedUsers, perm, req_, 
                                 req, sRes, truckRequested >>

WaitLockOuterDoor == /\ pc[Control] = "WaitLockOuterDoor"
                     /\ binCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, authorizedUsers, perm, req_, 
                                     req, sRes, truckRequested >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
                /\ pc' = [pc EXCEPT ![Control] = "WaitOpenTrap"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binSensor, scans, 
                                permissions, serverRequests, serverResponses, 
                                truckCommand, authorizedUsers, perm, req_, req, 
                                sRes, truckRequested >>

WaitOpenTrap == /\ pc[Control] = "WaitOpenTrap"
                /\ binCommand.command = "finished"
                /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, authorizedUsers, 
                                perm, req_, req, sRes, truckRequested >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
             /\ pc' = [pc EXCEPT ![Control] = "WaitExtendRam"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             authorizedUsers, perm, req_, req, sRes, 
                             truckRequested >>

WaitExtendRam == /\ pc[Control] = "WaitExtendRam"
                 /\ binCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "RetractRam"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, 
                                 authorizedUsers, perm, req_, req, sRes, 
                                 truckRequested >>

RetractRam == /\ pc[Control] = "RetractRam"
              /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
              /\ pc' = [pc EXCEPT ![Control] = "WaitRetractRam"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binSensor, scans, permissions, 
                              serverRequests, serverResponses, truckCommand, 
                              authorizedUsers, perm, req_, req, sRes, 
                              truckRequested >>

WaitRetractRam == /\ pc[Control] = "WaitRetractRam"
                  /\ binCommand.command = "finished"
                  /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, 
                                  binSensor, scans, permissions, 
                                  serverRequests, serverResponses, 
                                  truckCommand, authorizedUsers, perm, req_, 
                                  req, sRes, truckRequested >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "WaitCloseTrap"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, authorizedUsers, perm, req_, 
                                 req, sRes, truckRequested >>

WaitCloseTrap == /\ pc[Control] = "WaitCloseTrap"
                 /\ binCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, 
                                 authorizedUsers, perm, req_, req, sRes, 
                                 truckRequested >>

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
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Oct 20 12:11:24 CEST 2026 by 20254351
