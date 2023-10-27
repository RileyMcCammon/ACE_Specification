---- MODULE ace ----
EXTENDS TLC, Naturals

CONSTANTS
    NumCores           \* Number of caches in the system

ASSUME NumCoresAssump == (NumCores \in Nat) /\ (NumCores > 0)
     
VARIABLES
    cores,          \* Represents processors each with their own cache
    data            \* Maintains data in cache line

vars == << cores, data >>

Operations == {"read", "write"}

ProcSet == (0..NumCores-1)

DataSet == ProcSet

Init == /\ cores = [i \in ProcSet |-> [ state |-> "Invalid", data |-> CHOOSE x \in DataSet : TRUE ]]
        /\ data = CHOOSE x \in DataSet : TRUE 

DemotUniqueClean(self, state) == \E i \in ProcSet : /\ cores[i].state = state
                        /\ cores' = [cores EXCEPT ![self].state = "SharedClean", ![self].data = cores[i].data, ![i].state = "SharedClean"]
                        /\ data' = cores[i].data

PushToOwnerState(self) == \E i \in ProcSet : /\ cores[i].state = "UniqueDirty"
                        /\ cores' = [cores EXCEPT ![self].state = "SharedClean", ![self].data = cores[i].data, ![i].state = "SharedDirty"]
                        /\ data' = cores[i].data

GainExclusivity(self) == \A i \in ProcSet : cores[i].state = "Invalid"
                            /\ cores' = [cores EXCEPT ![self].state = "UniqueClean", ![self].data = data]
                            /\ data' = data

GainSharedStatus(self) == \A i \in ProcSet : cores[i].state /= "UniqueClean"
                /\ cores[i].state /= "UniqueDirty"
                /\ \E j \in ProcSet : cores[j].state = "SharedClean"
                /\ cores' = [cores EXCEPT ![self].state = "SharedClean", ![self].data = data]
                /\ data' = data

PerformRead(self) == DemotUniqueClean(self, "UniqueClean") 
                    \/ PushToOwnerState(self) 
                    \/ GainExclusivity(self)
                    \/ GainSharedStatus(self)

PerformWrite(self, invalidateOthers) == LET d == CHOOSE x \in DataSet: TRUE IN
                        /\ cores' = [i \in ProcSet |-> 
                                     IF i = self 
                                     THEN [ state |-> "UniqueDirty", data |-> d ]
                                     ELSE [ state |-> IF invalidateOthers = TRUE THEN "Invalid" ELSE cores[i].state, 
                                            data  |-> cores[i].data]]
                        /\ data' = d

UniqueDirty(self, operation) == /\ cores[self].state = "UniqueDirty"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, FALSE)))

SharedDirty(self, operation) == /\ cores[self].state = "SharedDirty"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, TRUE)))

UniqueClean(self, operation) == /\ cores[self].state = "UniqueClean"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, FALSE)))
                                        
SharedClean(self, operation) == /\ cores[self].state = "SharedClean"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, TRUE)))
    
Invalid(self, operation) ==  /\ cores[self].state = "Invalid"
                            /\ ((operation = "read" /\ PerformRead(self))
                                \/ (operation = "write" /\ PerformWrite(self, TRUE)))

Next == (\E self \in ProcSet: 
                \E operation \in Operations:    \/ UniqueDirty(self, operation)
                                                \/ SharedDirty(self, operation) 
                                                \/ UniqueClean(self, operation) 
                                                \/ SharedClean(self, operation) 
                                                \/ Invalid(self, operation) )

Spec == Init /\ [][Next]_vars

\* INVARIENTS
TypeOK == /\ \A i \in ProcSet: cores[i].state \in {"UniqueDirty", "SharedDirty", "UniqueClean", "SharedClean", "Invalid"}
          /\ \A i \in ProcSet: cores[i].data \in DataSet
          /\ data \in DataSet 
          /\ data \in Nat
    
PermittedStates(state, permitted) == \A i, j \in ProcSet : cores[i].state = state /\ j /= i
            => cores[j].state \in permitted

UniqueDirtyPermits == PermittedStates("UniqueDirty", {"Invalid"})
SharedDirtyPermits == PermittedStates("SharedDirty", {"SharedClean", "Invalid"})
UniqueCleanPermits == PermittedStates("UniqueClean", {"Invalid"})
SharedCleanPermits == PermittedStates("SharedClean", {"SharedDirty", "SharedClean", "Invalid"})
InvalidPermits     == PermittedStates("Invalid", {"UniqueDirty", "SharedDirty", "UniqueClean", "SharedClean", "Invalid"})

SharedImpliesEquivalentData == \A i, j \in ProcSet : 
                                /\ cores[i].state \in {"SharedDirty", "SharedClean"}
                                /\ cores[j].state \in {"SharedDirty", "SharedClean"}
                                => cores[i].data = cores[j].data

====