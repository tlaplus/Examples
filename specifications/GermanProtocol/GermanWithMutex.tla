----------------------------- MODULE GermanWithMutex -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    NODE,
    DATA,
    NoData,
    NoNode

ASSUME NoDataNotInDATA == NoData \notin DATA
ASSUME NoNodeNotInNODE == NoNode \notin NODE

CacheState == {"I", "S", "E"}
MsgCmd     == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

Payload == DATA \cup {NoData}

VARIABLES
    cache,
    chan1,
    chan2,
    chan3,
    invSet,
    shrSet,
    exGntd,
    curCmd,
    curPtr,
    memData,
    auxData

vars == <<cache, chan1, chan2, chan3, invSet, shrSet,
          exGntd, curCmd, curPtr, memData, auxData>>

-------------------------------------------------------------------------------

TypeOK ==
    /\ cache  \in [NODE -> [state : CacheState, data : Payload]]
    /\ chan1  \in [NODE -> [cmd : MsgCmd, data : Payload]]
    /\ chan2  \in [NODE -> [cmd : MsgCmd, data : Payload]]
    /\ chan3  \in [NODE -> [cmd : MsgCmd, data : Payload]]
    /\ invSet \in [NODE -> BOOLEAN]
    /\ shrSet \in [NODE -> BOOLEAN]
    /\ exGntd \in BOOLEAN
    /\ curCmd \in MsgCmd
    /\ curPtr \in NODE \cup {NoNode}
    /\ memData \in DATA
    /\ auxData \in DATA

Init ==
    \E d \in DATA :
        /\ cache  = [i \in NODE |-> [state |-> "I", data |-> NoData]]
        /\ chan1  = [i \in NODE |-> [cmd |-> "Empty", data |-> NoData]]
        /\ chan2  = [i \in NODE |-> [cmd |-> "Empty", data |-> NoData]]
        /\ chan3  = [i \in NODE |-> [cmd |-> "Empty", data |-> NoData]]
        /\ invSet = [i \in NODE |-> FALSE]
        /\ shrSet = [i \in NODE |-> FALSE]
        /\ exGntd = FALSE
        /\ curCmd = "Empty"
        /\ curPtr = NoNode
        /\ memData = d
        /\ auxData = d

-------------------------------------------------------------------------------

Store(i, d) ==
    /\ cache[i].state = "E"
    /\ cache' = [cache EXCEPT ![i].data = d]
    /\ auxData' = d
    /\ UNCHANGED <<chan1, chan2, chan3, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData>>

SendReqS(i) ==
    /\ chan1[i].cmd = "Empty"
    /\ cache[i].state = "I"
    /\ chan1' = [chan1 EXCEPT ![i].cmd = "ReqS"]
    /\ UNCHANGED <<cache, chan2, chan3, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

SendReqE(i) ==
    /\ chan1[i].cmd = "Empty"
    /\ cache[i].state \in {"I", "S"}
    /\ chan1' = [chan1 EXCEPT ![i].cmd = "ReqE"]
    /\ UNCHANGED <<cache, chan2, chan3, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

RecvGntS(i) ==
    /\ chan2[i].cmd = "GntS"
    /\ cache' = [cache EXCEPT ![i].state = "S", ![i].data = chan2[i].data]
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "Empty", ![i].data = NoData]
    /\ UNCHANGED <<chan1, chan3, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

RecvGntE(i) ==
    /\ chan2[i].cmd = "GntE"
    /\ cache' = [cache EXCEPT ![i].state = "E", ![i].data = chan2[i].data]
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "Empty", ![i].data = NoData]
    /\ UNCHANGED <<chan1, chan3, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

SendInvAck(i) ==
    /\ chan2[i].cmd = "Inv"
    /\ chan3[i].cmd = "Empty"
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "Empty", ![i].data = NoData]
    /\ chan3' = [chan3 EXCEPT ![i].cmd = "InvAck",
                              ![i].data = IF cache[i].state = "E"
                                          THEN cache[i].data
                                          ELSE NoData]
    /\ cache' = [cache EXCEPT ![i].state = "I", ![i].data = NoData]
    /\ UNCHANGED <<chan1, invSet, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

-------------------------------------------------------------------------------

RecvReqS(i) ==
    /\ curCmd = "Empty"
    /\ chan1[i].cmd = "ReqS"
    /\ curCmd' = "ReqS"
    /\ curPtr' = i
    /\ chan1' = [chan1 EXCEPT ![i].cmd = "Empty"]
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan2, chan3, shrSet,
                   exGntd, memData, auxData>>

RecvReqE(i) ==
    /\ curCmd = "Empty"
    /\ chan1[i].cmd = "ReqE"
    /\ curCmd' = "ReqE"
    /\ curPtr' = i
    /\ chan1' = [chan1 EXCEPT ![i].cmd = "Empty"]
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan2, chan3, shrSet,
                   exGntd, memData, auxData>>

SendInv(i) ==
    /\ chan2[i].cmd = "Empty"
    /\ invSet[i] = TRUE
    /\ (curCmd = "ReqE" \/ (curCmd = "ReqS" /\ exGntd = TRUE))
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "Inv"]
    /\ invSet' = [invSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<cache, chan1, chan3, shrSet,
                   exGntd, curCmd, curPtr, memData, auxData>>

RecvInvAck(i) ==
    /\ chan3[i].cmd = "InvAck"
    /\ curCmd # "Empty"
    /\ shrSet' = [shrSet EXCEPT ![i] = FALSE]
    /\ IF exGntd = TRUE
         THEN /\ exGntd'  = FALSE
              /\ memData' = chan3[i].data
              /\ chan3'   = [chan3 EXCEPT ![i].cmd = "Empty", ![i].data = NoData]
         ELSE /\ chan3'   = [chan3 EXCEPT ![i].cmd = "Empty"]
              /\ UNCHANGED <<exGntd, memData>>
    /\ UNCHANGED <<cache, chan1, chan2, invSet, curCmd, curPtr, auxData>>

SendGntS(i) ==
    /\ curCmd = "ReqS"
    /\ curPtr = i
    /\ chan2[i].cmd = "Empty"
    /\ exGntd = FALSE
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "GntS", ![i].data = memData]
    /\ shrSet' = [shrSet EXCEPT ![i] = TRUE]
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan3, invSet, exGntd, memData, auxData>>

SendGntE(i) ==
    /\ curCmd = "ReqE"
    /\ curPtr = i
    /\ chan2[i].cmd = "Empty"
    /\ exGntd = FALSE
    /\ \A j \in NODE : shrSet[j] = FALSE
    /\ chan2' = [chan2 EXCEPT ![i].cmd = "GntE", ![i].data = memData]
    /\ shrSet' = [shrSet EXCEPT ![i] = TRUE]
    /\ exGntd' = TRUE
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan3, invSet, memData, auxData>>

-------------------------------------------------------------------------------

Next ==
    \/ \E i \in NODE, d \in DATA : Store(i, d)
    \/ \E i \in NODE :
         \/ SendReqS(i)    \/ SendReqE(i)
         \/ RecvReqS(i)    \/ RecvReqE(i)
         \/ SendInv(i)     \/ SendInvAck(i)   \/ RecvInvAck(i)
         \/ SendGntS(i)    \/ SendGntE(i)
         \/ RecvGntS(i)    \/ RecvGntE(i)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

Abstract == INSTANCE GermanCoherence WITH
    cache <- [i \in NODE |-> cache[i].state],
    chan1 <- [i \in NODE |-> chan1[i].cmd],
    chan2 <- [i \in NODE |-> chan2[i].cmd],
    chan3 <- [i \in NODE |-> chan3[i].cmd]

Refinement == Abstract!Spec

-------------------------------------------------------------------------------

Coherence ==
    \A i, j \in NODE :
        i # j =>
            /\ (cache[i].state = "E" => cache[j].state = "I")
            /\ (cache[i].state = "S" => cache[j].state \in {"I", "S"})

DataProp ==
    /\ (exGntd = FALSE => memData = auxData)
    /\ \A i \in NODE : cache[i].state # "I" => cache[i].data = auxData

-------------------------------------------------------------------------------

ChannelWellFormed ==
    \A i \in NODE :
        /\ chan1[i].cmd \in {"Empty", "ReqS", "ReqE"}
        /\ chan2[i].cmd \in {"Empty", "Inv", "GntS", "GntE"}
        /\ chan3[i].cmd \in {"Empty", "InvAck"}

TransactionConsistency ==
    (curCmd = "Empty") <=> (curPtr = NoNode)

DirectoryAccurate ==
    \A i \in NODE : cache[i].state \in {"S", "E"} => shrSet[i] = TRUE

ExclusiveIsolation ==
    \A i \in NODE :
        cache[i].state = "E" =>
            /\ exGntd = TRUE
            /\ \A j \in NODE :
                 j # i =>
                     /\ cache[j].state = "I"
                     /\ chan2[j].cmd \notin {"GntS", "GntE"}
                     /\ chan3[j].cmd # "InvAck"

WritebackCarriesLatest ==
    \A i \in NODE :
        (chan3[i].cmd = "InvAck" /\ curCmd # "Empty" /\ exGntd = TRUE) =>
            /\ chan3[i].data = auxData
            /\ \A j \in NODE :
                 j # i =>
                     /\ cache[j].state # "E"
                     /\ chan2[j].cmd # "GntE"
                     /\ chan3[j].cmd # "InvAck"

-------------------------------------------------------------------------------

Fairness ==
    \A i \in NODE :
        /\ SF_vars(RecvReqS(i))
        /\ SF_vars(RecvReqE(i))
        /\ WF_vars(SendInv(i))
        /\ WF_vars(SendInvAck(i))
        /\ WF_vars(RecvInvAck(i))
        /\ WF_vars(SendGntS(i))
        /\ WF_vars(SendGntE(i))
        /\ WF_vars(RecvGntS(i))
        /\ WF_vars(RecvGntE(i))

FairSpec == Spec /\ Fairness

RequestEventuallyServed ==
    \A i \in NODE :
        (chan1[i].cmd \in {"ReqS", "ReqE"}) ~> (chan1[i].cmd = "Empty")

SharedRequestEventuallyGranted ==
    \A i \in NODE :
        (chan1[i].cmd = "ReqS") ~> (cache[i].state # "I")

ExclusiveRequestEventuallyGranted ==
    \A i \in NODE :
        (chan1[i].cmd = "ReqE") ~> (cache[i].state = "E")

=============================================================================
