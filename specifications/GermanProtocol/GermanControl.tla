----------------------------- MODULE GermanControl -----------------------------
CONSTANTS
    NODE,
    NoNode

ASSUME NoNodeNotInNODE == NoNode \notin NODE

CacheState == {"I", "S", "E"}

VARIABLES
    cache,
    chan1,
    chan2,
    chan3,
    invSet,
    shrSet,
    exGntd,
    curCmd,
    curPtr

vars == <<cache, chan1, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

-------------------------------------------------------------------------------

TypeOK ==
    /\ cache  \in [NODE -> CacheState]
    /\ chan1  \in [NODE -> {"Empty", "ReqS", "ReqE"}]
    /\ chan2  \in [NODE -> {"Empty", "Inv", "GntS", "GntE"}]
    /\ chan3  \in [NODE -> {"Empty", "InvAck"}]
    /\ invSet \subseteq NODE
    /\ shrSet \subseteq NODE
    /\ exGntd \in BOOLEAN
    /\ curCmd \in {"Empty", "ReqS", "ReqE"}
    /\ curPtr \in NODE \cup {NoNode}

Init ==
    /\ cache  = [i \in NODE |-> "I"]
    /\ chan1  = [i \in NODE |-> "Empty"]
    /\ chan2  = [i \in NODE |-> "Empty"]
    /\ chan3  = [i \in NODE |-> "Empty"]
    /\ invSet = {}
    /\ shrSet = {}
    /\ exGntd = FALSE
    /\ curCmd = "Empty"
    /\ curPtr = NoNode

-------------------------------------------------------------------------------

SendReq(i) ==
    /\ chan1[i] = "Empty"
    /\ \E c \in {"ReqS", "ReqE"} :
         /\ cache[i] \in (IF c = "ReqS" THEN {"I"} ELSE {"I", "S"})
         /\ chan1' = [chan1 EXCEPT ![i] = c]
    /\ UNCHANGED <<cache, chan2, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

RecvReq(i) ==
    /\ curCmd = "Empty"
    /\ chan1[i] \in {"ReqS", "ReqE"}
    /\ curCmd' = chan1[i]
    /\ curPtr' = i
    /\ chan1' = [chan1 EXCEPT ![i] = "Empty"]
    /\ invSet' = shrSet
    /\ UNCHANGED <<cache, chan2, chan3, shrSet, exGntd>>

SendInv(i) ==
    /\ chan2[i] = "Empty"
    /\ i \in invSet
    /\ (curCmd = "ReqE" \/ (curCmd = "ReqS" /\ exGntd = TRUE))
    /\ chan2' = [chan2 EXCEPT ![i] = "Inv"]
    /\ invSet' = invSet \ {i}
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
    /\ shrSet' = shrSet \ {i}
    /\ exGntd' = IF exGntd = TRUE THEN FALSE ELSE exGntd
    /\ UNCHANGED <<cache, chan1, chan2, invSet, curCmd, curPtr>>

SendGnt(i) ==
    /\ curCmd \in {"ReqS", "ReqE"}
    /\ curPtr = i
    /\ chan2[i] = "Empty"
    /\ exGntd = FALSE
    /\ curCmd = "ReqE" => shrSet = {}
    /\ chan2' = [chan2 EXCEPT ![i] = IF curCmd = "ReqS" THEN "GntS" ELSE "GntE"]
    /\ shrSet' = shrSet \cup {i}
    /\ exGntd' = (curCmd = "ReqE")
    /\ curCmd' = "Empty"
    /\ curPtr' = NoNode
    /\ UNCHANGED <<cache, chan1, chan3, invSet>>

RecvGnt(i) ==
    /\ chan2[i] \in {"GntS", "GntE"}
    /\ cache' = [cache EXCEPT ![i] = IF chan2[i] = "GntS" THEN "S" ELSE "E"]
    /\ chan2' = [chan2 EXCEPT ![i] = "Empty"]
    /\ UNCHANGED <<chan1, chan3, invSet, shrSet, exGntd, curCmd, curPtr>>

-------------------------------------------------------------------------------

Next ==
    \E i \in NODE :
        \/ SendReq(i)
        \/ RecvReq(i)
        \/ SendInv(i)     \/ SendInvAck(i)   \/ RecvInvAck(i)
        \/ SendGnt(i)
        \/ RecvGnt(i)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

Coherence ==
    \A i, j \in NODE :
        i # j =>
            /\ (cache[i] = "E" => cache[j] = "I")
            /\ (cache[i] = "S" => cache[j] \in {"I", "S"})

=============================================================================
