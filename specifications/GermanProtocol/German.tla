-------------------------------- MODULE German --------------------------------
CONSTANTS
    NODE,
    Other,
    NoNode

ASSUME Other \notin NODE
ASSUME NoNode \notin NODE /\ NoNode # Other

CacheState == {"I", "S", "E"}
MsgCmd     == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

VARIABLES
    cache, chan1, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr

vars == <<cache, chan1, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

-------------------------------------------------------------------------------

TypeOK ==
    /\ cache  \in [NODE -> CacheState]
    /\ chan1  \in [NODE -> MsgCmd]
    /\ chan2  \in [NODE -> MsgCmd]
    /\ chan3  \in [NODE -> MsgCmd]
    /\ invSet \in [NODE -> BOOLEAN]
    /\ shrSet \in [NODE -> BOOLEAN]
    /\ exGntd \in BOOLEAN
    /\ curCmd \in MsgCmd
    /\ curPtr \in NODE \cup {Other, NoNode}

Init ==
    /\ cache  = [i \in NODE |-> "I"]
    /\ chan1  = [i \in NODE |-> "Empty"]
    /\ chan2  = [i \in NODE |-> "Empty"]
    /\ chan3  = [i \in NODE |-> "Empty"]
    /\ invSet = [i \in NODE |-> FALSE]
    /\ shrSet = [i \in NODE |-> FALSE]
    /\ exGntd = FALSE
    /\ curCmd = "Empty"
    /\ curPtr = NoNode

-------------------------------------------------------------------------------

SendReqS(i) ==
    /\ chan1[i] = "Empty"
    /\ cache[i] = "I"
    /\ chan1' = [chan1 EXCEPT ![i] = "ReqS"]
    /\ UNCHANGED <<cache, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

SendReqE(i) ==
    /\ chan1[i] = "Empty"
    /\ cache[i] \in {"I", "S"}
    /\ chan1' = [chan1 EXCEPT ![i] = "ReqE"]
    /\ UNCHANGED <<cache, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

RecvReqS(i) ==
    /\ curCmd = "Empty"
    /\ chan1[i] = "ReqS"
    /\ curCmd' = "ReqS"
    /\ curPtr' = i
    /\ chan1' = [chan1 EXCEPT ![i] = "Empty"]
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan2, chan3, shrSet, exGntd>>

RecvReqE(i) ==
    /\ curCmd = "Empty"
    /\ chan1[i] = "ReqE"
    /\ curCmd' = "ReqE"
    /\ curPtr' = i
    /\ chan1' = [chan1 EXCEPT ![i] = "Empty"]
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan2, chan3, shrSet, exGntd>>

SendInv(i) ==
    /\ chan2[i] = "Empty"
    /\ invSet[i] = TRUE
    /\ (curCmd = "ReqE" \/ (curCmd = "ReqS" /\ exGntd = TRUE))
    /\ chan2' = [chan2 EXCEPT ![i] = "Inv"]
    /\ invSet' = [invSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<cache, chan1, chan3, shrSet, exGntd, curCmd, curPtr>>

SendInvAck(i) ==
    /\ chan2[i] = "Inv"
    /\ chan3[i] = "Empty"
    /\ chan2' = [chan2 EXCEPT ![i] = "Empty"]
    /\ chan3' = [chan3 EXCEPT ![i] = "InvAck"]
    /\ cache' = [cache EXCEPT ![i] = "I"]
    /\ UNCHANGED <<chan1, invSet, shrSet, exGntd, curCmd, curPtr>>

RecvInvAck(i) ==
    /\ chan3[i] = "InvAck"
    /\ curCmd # "Empty"
    /\ chan3' = [chan3 EXCEPT ![i] = "Empty"]
    /\ shrSet' = [shrSet EXCEPT ![i] = FALSE]
    /\ exGntd' = IF exGntd = TRUE THEN FALSE ELSE exGntd
    /\ UNCHANGED <<cache, chan1, chan2, invSet, curCmd, curPtr>>

SendGntS(i) ==
    /\ curCmd = "ReqS"
    /\ curPtr = i
    /\ chan2[i] = "Empty"
    /\ exGntd = FALSE
    /\ chan2' = [chan2 EXCEPT ![i] = "GntS"]
    /\ shrSet' = [shrSet EXCEPT ![i] = TRUE]
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan3, invSet, exGntd>>

SendGntE(i) ==
    /\ curCmd = "ReqE"
    /\ curPtr = i
    /\ chan2[i] = "Empty"
    /\ exGntd = FALSE
    /\ \A j \in NODE : shrSet[j] = FALSE
    /\ chan2' = [chan2 EXCEPT ![i] = "GntE"]
    /\ shrSet' = [shrSet EXCEPT ![i] = TRUE]
    /\ exGntd' = TRUE
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan3, invSet>>

RecvGntS(i) ==
    /\ chan2[i] = "GntS"
    /\ cache' = [cache EXCEPT ![i] = "S"]
    /\ chan2' = [chan2 EXCEPT ![i] = "Empty"]
    /\ UNCHANGED <<chan1, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

RecvGntE(i) ==
    /\ chan2[i] = "GntE"
    /\ cache' = [cache EXCEPT ![i] = "E"]
    /\ chan2' = [chan2 EXCEPT ![i] = "Empty"]
    /\ UNCHANGED <<chan1, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

-------------------------------------------------------------------------------

ABS_RecvReqS ==
    /\ curCmd = "Empty"
    /\ curCmd' = "ReqS"
    /\ curPtr' = Other
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan1, chan2, chan3, shrSet, exGntd>>

ABS_RecvReqE ==
    /\ curCmd = "Empty"
    /\ curCmd' = "ReqE"
    /\ curPtr' = Other
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan1, chan2, chan3, shrSet, exGntd>>

ABS_SendGntS ==
    /\ curCmd = "ReqS"
    /\ curPtr = Other
    /\ exGntd = FALSE
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan2, chan3, invSet, shrSet, exGntd>>

ABS_SendGntE ==
    /\ curCmd = "ReqE"
    /\ curPtr = Other
    /\ exGntd = FALSE
    /\ \A j \in NODE : shrSet[j] = FALSE
    /\ exGntd' = TRUE
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan2, chan3, invSet, shrSet>>

\* Other acknowledges relinquishing its exclusive copy.  Guarded (as in
\* german.m) so it only fires when no concrete node is exclusive / mid-grant /
\* mid-ack -- the noninterference condition that keeps the abstraction sound.
ABS_RecvInvAck ==
    /\ curCmd # "Empty"
    /\ exGntd = TRUE
    \* Operational form of the mutual-exclusion noninterference lemma ("Lemma_1"
    \* of Chou, Mannava & Park, FMCAD 2004 = ref [11] of Sethi, Talupur & Malik,
    \* arXiv:1407.7468, whose online models these are).  germanWithMutex.m is the
    \* CMP-strengthened abstraction that conjoins this guard onto absRecvInvAck;
    \* germanNoMutex.m omits it on purpose -- the deadlock-study model that needs
    \* no noninterference lemma -- so it admits the spurious "bogus InvAck from
    \* Other" counterexample to mutual exclusion.  Dropping this one conjunct makes
    \* German.tla bisimilar to germanNoMutex.m.
    /\ \A j \in NODE :
         /\ cache[j] # "E"
         /\ chan2[j] # "GntE"
         /\ chan3[j] # "InvAck"
    /\ exGntd' = FALSE
    /\ UNCHANGED <<cache, chan1, chan2, chan3, invSet, shrSet, curCmd, curPtr>>

-------------------------------------------------------------------------------

Next ==
    \/ \E i \in NODE :
         \/ SendReqS(i)    \/ SendReqE(i)
         \/ RecvReqS(i)    \/ RecvReqE(i)
         \/ SendInv(i)     \/ SendInvAck(i)   \/ RecvInvAck(i)
         \/ SendGntS(i)    \/ SendGntE(i)
         \/ RecvGntS(i)    \/ RecvGntE(i)
    \/ ABS_RecvReqS \/ ABS_RecvReqE
    \/ ABS_SendGntS \/ ABS_SendGntE
    \/ ABS_RecvInvAck

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

Coherence ==
    \A i, j \in NODE :
        i # j =>
            /\ (cache[i] = "E" => cache[j] = "I")
            /\ (cache[i] = "S" => cache[j] \in {"I", "S"})

Lemma_1 ==
    \A i \in NODE :
        (chan3[i] = "InvAck" /\ curCmd # "Empty" /\ exGntd = TRUE) =>
            \A j \in NODE :
                j # i =>
                    /\ cache[j] # "E"
                    /\ chan2[j] # "GntE"
                    /\ chan3[j] # "InvAck"

=============================================================================
