------------------------------ MODULE Boulanger ----------------------------
(***************************************************************************)
(* This is a PlusCal encoding of the Boulangerie Algorithm of Yoram Moses  *)
(* and Katia Patkin--a variant of the Bakery Algorithm--and a proof that   *)
(* it implements mutual exclusion.  The bakery algorithm appeared in       *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The PlusCal encoding differs from the Moses-Patkin algorithm in one     *)
(* respect.  To enter the critical section, the PlusCal version examines   *)
(* other processes one at a time--in the while loop at label w1.  The      *)
(* Moses-Patkin algorithm performs those examinations in parallel.         *)
(* Because PlusCal does not allow sub-processes, it would be difficult     *)
(* (but not impossible) to express that algorithm in PlusCal.  It would be *)
(* easy to express their version in TLA+ (for example, by modifying the    *)
(* TLA+ translation of the PlusCal code), and it should be straightforward *)
(* to convert the invariance proof presented here to a proof of the more   *)
(* general version.  I will leave that as an exercise for others.          *)
(*                                                                         *)
(* I started with a PlusCal encoding and invariance proof of the Bakery    *)
(* Algorithm.  The only non-obvious part of that encoding is how it        *)
(* represented the safe registers assumed by the algorithm, which are      *)
(* registers in which reads and writes are not atomic.  A safe register is *)
(* represented by a variable r whose value is written by performing some   *)
(* number of atomic writes of non-deterministically chosen "legal" values  *)
(* to r followed by a single write of the desired value.  A read of the    *)
(* register is performed by a single atomic read of r.  It can be shown    *)
(* that this captures the semantics of a safe register.                    *)
(*                                                                         *)
(* Starting from the PlusCal version of the Bakery Algorithm, it was easy  *)
(* to modify it to the Boulangerie Algorithm (with the simplification      *)
(* described above).  I model checked the algorithm on some small models   *)
(* to convince myself that there were no trivial errors that would be      *)
(* likely to arise from an error in the encoding.  I then modified the     *)
(* invariant by a combination of a bit of thinking and a fair amount of    *)
(* trial and error, finding errors in the invariant by model checking very *)
(* small models.  (I checked it on two processes with chosen numbers       *)
(* restricted to be at most 3.)                                            *)
(*                                                                         *)
(* When checking on a small model revealed no error in the invariant, I    *)
(* checked the proof with TLAPS (the TLA+ proof system).  The high level   *)
(* proof, consisting of steps <1>1 - <1>4, are standard and are the same   *)
(* as for the Bakery Algorithm.  TLAPS checks this simple four-step proof  *)
(* for the Bakery Algorithm with terminal BY proofs that just tell it to   *)
(* use the necessary assumptions and to expand all definitions.  This      *)
(* didn't work for the hard part of the Boulangerie Algorithm--step <1>2   *)
(* that checks inductive invariance.                                       *)
(*                                                                         *)
(* When a proof doesn't go through, one keeps decomposing the proof of the *)
(* steps that aren't proved until one sees what the problem is.  This      *)
(* decomposition is done with little thinking and no typing using the      *)
(* Toolbox's Decompose Proof command.  (The Toolbox is the IDE for the     *)
(* TLA+ tools.) Step <1>2 has the form A /\ B => C, where B is a           *)
(* disjunction, and the Decompose Proof command produces a level-<2> proof *)
(* consisting of subgoals essentially of the form A /\ Bi => C for the     *)
(* disjuncts Bi of B.  Two of those subgoals weren't proved.  I decomposed *)
(* them both for several levels until I saw that in one of them, some step *)
(* wasn't preserving the part of the invariant that asserts                *)
(* type-correctness.  I then quickly found the culprit: a silly error in   *)
(* the type invariant in which I had in one place written the set Proc of  *)
(* process numbers instead of the set Nat of natural numbers.  After       *)
(* correcting that error, only one of the level-<2> subgoals remained      *)
(* unproved: step <2>5.  Using the Decompose Proof command as far as I     *)
(* could on that step, one substep remained unproved.  (I think it was at  *)
(* level <5>.) Looking at what the proof obligations were, the obvious     *)
(* decomposition was a two-way case split, which I did by manually         *)
(* entering another level of subproof.  One of those cases weren't proved, *)
(* so I tried another two-way case split on it.  That worked.  I then made *)
(* that substep to the first step of the (level <3>) proof of <2>5, moving *)
(* its proof with it.  With that additional fact, TLAPS was able to prove  *)
(* <2>5 in one more step (the QED step).                                   *)
(*                                                                         *)
(* The entire proof now is about 70 lines.  I only typed 20 of those 70    *)
(* lines.  The rest either came from the original Bakery Algorithm         *)
(* (8-line) proof or were generated by the Decompose Proof Command.        *)
(*                                                                         *)
(* I don't know how much time I actually spent writing the algorithm and   *)
(* its proof.  Except for the final compaction of the (correct) proof of   *)
(* <2>5, the entire exercise took me two days.  However, most of that was  *)
(* spent tracking down bugs in the Toolbox.  We are in the process of      *)
(* moving the Toolbox to a new version of Eclipse, and there are many bugs *)
(* that must be fixed before it's ready to be released.  I would estimate  *)
(* that it would have taken me less than 4 hours without Toolbox bugs.  I  *)
(* find it remarkable how little thinking the whole thing took.            *)
(*                                                                         *)
(* This whole process was a lot easier than trying to write a convincing   *)
(* hand proof--a proof that I would regard as adequate to justify          *)
(* publication of the proof.                                               *)
(***************************************************************************)

EXTENDS Integers, TLAPS

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
CONSTANT N 
ASSUME N \in Nat

(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)
Procs == 1..N 

(***************************************************************************)
(* \prec is defined to be the lexicographical less-than relation on pairs  *)
(* of numbers.                                                             *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***       this is a comment containing the PlusCal code *

--algorithm Boulanger
{ variable num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1, previous = -1 ;
    { ncs:- while (TRUE) 
            { e1:   either { flag[self] := ~ flag[self] ;
                             goto e1 }
                    or     { flag[self] := TRUE;
                             unchecked := Procs \ {self} ;
                             max := 0
                           } ;     
              e2:   while (unchecked # {}) 
                      { with (i \in unchecked) 
                          { unchecked := unchecked \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              e3:   either { with (k \in Nat) { num[self] := k } ;
                             goto e3 }
                    or     { num[self] := max + 1 } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                               unchecked := IF num[self] = 1
                                              THEN 1..(self-1)
                                              ELSE Procs \ {self} 
                           } ;
              w1:   while (unchecked # {}) 
                      {     with (i \in unchecked) { nxt := i };
                            await ~ flag[nxt];
                            previous := -1 ;
                        w2: if ( \/ num[nxt] = 0
                                 \/ <<num[self], self>> \prec <<num[nxt], nxt>>
                                 \/  /\ previous # -1 
                                     /\ num[nxt] # previous)
                                { unchecked := unchecked \ {nxt};
                                  if (unchecked = {}) {goto cs}
                                  else {goto w1} 
                                }
                              else { previous := num[nxt] ;
                                     goto w2 }
                                                           
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k \in Nat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 } 
            }
    }
}

    this ends the comment containing the PlusCal code
*************)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)
VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ previous = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED <<unchecked, max>>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt, previous >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt, previous >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in Nat:
                       num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ num' = [num EXCEPT ![self] = max[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = IF num[self] = 1
                                                                THEN 1..(self-1)
                                                                ELSE Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt, previous >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ previous' = [previous EXCEPT ![self] = -1]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << nxt, previous >>
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ IF \/ num[nxt[self]] = 0
                  \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                  \/  /\ previous[self] # -1
                      /\ num[nxt[self]] # previous[self]
                  THEN /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
                       /\ IF unchecked'[self] = {}
                             THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "w1"]
                       /\ UNCHANGED previous
                  ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                       /\ UNCHANGED unchecked
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat:
                         num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION   (this ends the translation of the PlusCal code)

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]
          /\ previous \in [Procs -> Nat \cup {-1}]             

(***************************************************************************)
(* Before(i, j) is a condition that implies that num[i] > 0 and, if j is   *)
(* trying to enter its critical section and i does not change num[i], then *)
(* j either has or will choose a value of num[j] for which                 *)
(*                                                                         *)
(*     <<num[i],i>> \prec <<num[j],j>>                                     *)
(*                                                                         *)
(* is true.                                                                *)
(***************************************************************************)
Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                  \/ /\ pc[j] = "e2"
                     /\ \/ i \in unchecked[j]
                        \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] = "e3"
                     /\ \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] \in {"e4", "w1", "w2"}
                     /\ <<num[i],i>> \prec <<num[j],j>>
                     /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])
                  \/ /\ num[i] = 1
                     /\ i < j

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
Inv == /\ TypeOK 
       /\ \A i \in Procs : 
             /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
             /\ (pc[i] \in {"e2", "e3"}) => flag[i] 
             /\ (pc[i] = "w2") => (nxt[i] # i)
             /\ (pc[i] \in {"e2", "w1", "w2"}) => i \notin unchecked[i]
             /\ (pc[i] \in {"w1", "w2"}) =>
                   \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
             /\ /\ pc[i] = "w2"
                /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                   \/ pc[nxt[i]] = "e3"
                => max[nxt[i]] >= num[i]
             /\ /\ pc[i] = "w2"
                /\ previous[i] # -1 
                /\ previous[i] # num[nxt[i]]
                /\ pc[nxt[i]] \in {"e4", "w1", "w2", "cs"}
                => Before(i, nxt[i])             
             /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of Mutual Exclusion                                               *)
(*                                                                         *)
(* This is a standard invariance proof, where <1>2 asserts that any step   *)
(* of the algorithm (including a stuttering step) starting in a state in   *)
(* which Inv is true leaves Inv true.  Step <1>4 follows easily from       *)
(* <1>1-<1>3 by simple temporal reasoning, checked by the PTL              *)
(* (Propositional Temporal Logic) backend prover.                          *)
(***************************************************************************)
THEOREM Spec => []MutualExclusion
<1> USE N \in Nat DEFS Procs, TypeOK, Before, \prec, ProcSet 

<1>1. Init => Inv
  BY SMT DEF Init, Inv
  
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs,
               ncs(self)
        PROVE  Inv'
    BY <2>1, Z3 DEF ncs, Inv
  <2>2. ASSUME NEW self \in Procs,
               e1(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "e1"
         /\ UNCHANGED << num, nxt, previous >>
      BY <2>2 DEF e1
    <3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
               /\ pc' = [pc EXCEPT ![self] = "e1"]
               /\ UNCHANGED <<unchecked, max>>
      BY <3>1 DEF Inv
    <3>2. CASE /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               /\ max' = [max EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "e2"]
      BY <3>2 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>2 DEF e1
  <2>3. ASSUME NEW self \in Procs,
               e2(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "e2"
         /\ UNCHANGED << num, flag, nxt, previous >>
      BY <2>3 DEF e2
    <3>1. ASSUME NEW  i \in unchecked[self],
                 unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
                 num[i] > max[self],
                 max' = [max EXCEPT ![self] = num[i]],
                 pc' = [pc EXCEPT ![self] = "e2"]
          PROVE  Inv'
      BY <3>1, Z3 DEF Inv
    <3>2. ASSUME NEW  i \in unchecked[self],
                 unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
                 ~(num[i] > max[self]),
                 max' = max,
                 pc' = [pc EXCEPT ![self] = "e2"]
          PROVE  Inv'
      BY <3>2, Z3 DEF Inv
    <3>3. CASE /\ unchecked[self] = {}
               /\ pc' = [pc EXCEPT ![self] = "e3"]
               /\ UNCHANGED << unchecked, max >>
      BY <3>3, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3, <2>3 DEF e2
  <2>4. ASSUME NEW self \in Procs,
               e3(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "e3"
         /\ UNCHANGED << flag, unchecked, max, nxt, previous >>
      BY <2>4 DEF e3
    <3>1. CASE /\ \E k \in Nat: num' = [num EXCEPT ![self] = k]
               /\ pc' = [pc EXCEPT ![self] = "e3"]
      BY <3>1, Z3 DEF Inv
    <3>2. CASE /\ num' = [num EXCEPT ![self] = max[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "e4"]
      BY <3>2, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>4 DEF e3
  <2>5. ASSUME NEW self \in Procs,
               e4(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "e4"
         /\ UNCHANGED << num, max, nxt, previous >>
      BY <2>5 DEF e4
    <3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
               /\ pc' = [pc EXCEPT ![self] = "e4"]
               /\ UNCHANGED unchecked
      BY <3>1, Z3 DEF Inv
    <3>2. CASE /\ flag' = [flag EXCEPT ![self] = FALSE]
               /\ num[self] = 1
               /\ unchecked' = [unchecked EXCEPT ![self] = 1..(self-1)]
               /\ pc' = [pc EXCEPT ![self] = "w1"]
      BY <3>2, Z3 DEF Inv
    <3>3. CASE /\ flag' = [flag EXCEPT ![self] = FALSE]
               /\ num[self] # 1
               /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               /\ pc' = [pc EXCEPT ![self] = "w1"]
      BY <3>3, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3, <2>5 DEF e4
  <2>6. ASSUME NEW self \in Procs,
               w1(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "w1"
         /\ UNCHANGED << num, flag, unchecked, max >>
      BY <2>6 DEF w1
    <3>1. CASE /\ unchecked[self] # {}
               /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
               /\ ~ flag[nxt'[self]]
               /\ previous' = [previous EXCEPT ![self] = -1]
               /\ pc' = [pc EXCEPT ![self] = "w2"]
      BY <3>1, Z3 DEF Inv
    <3>2. CASE /\ unchecked[self] = {}
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << nxt, previous >>
      BY <3>2, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>6 DEF w1
  <2>7. ASSUME NEW self \in Procs,
               w2(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "w2"
         /\ UNCHANGED << num, flag, max, nxt >>
      BY <2>7 DEF w2
    <3>1. CASE /\ \/ num[nxt[self]] = 0
                  \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                  \/  /\ previous[self] # -1
                      /\ num[nxt[self]] # previous[self]
               /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
               /\ unchecked'[self] = {}
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED previous
      BY <3>1, Z3 DEF Inv
    <3>2. CASE /\ \/ num[nxt[self]] = 0
                  \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                  \/  /\ previous[self] # -1
                      /\ num[nxt[self]] # previous[self]
               /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
               /\ unchecked'[self] # {}
               /\ pc' = [pc EXCEPT ![self] = "w1"]
               /\ UNCHANGED previous
      BY <3>2, Z3 DEF Inv
    <3>3. CASE /\ ~ \/ num[nxt[self]] = 0
                    \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                    \/  /\ previous[self] # -1
                        /\ num[nxt[self]] # previous[self]
               /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
               /\ pc' = [pc EXCEPT ![self] = "w2"]
               /\ UNCHANGED unchecked
      BY <3>3, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3, <2>7 DEF w2
  <2>8. ASSUME NEW self \in Procs,
               cs(self)
        PROVE  Inv'
    BY <2>8, Z3 DEF cs, Inv
  <2>9. ASSUME NEW self \in Procs,
               exit(self)
        PROVE  Inv'
    <3>. /\ pc[self] = "exit"
         /\ UNCHANGED << flag, unchecked, max, nxt, previous >>
      BY <2>9 DEF exit
    <3>1. CASE /\ \E k \in Nat: num' = [num EXCEPT ![self] = k]
               /\ pc' = [pc EXCEPT ![self] = "exit"]
      BY <3>1, Z3 DEF Inv
    <3>2. CASE /\ num' = [num EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
      BY <3>2, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>9 DEF exit
  <2>10. CASE UNCHANGED vars
    BY <2>10, Z3 DEF vars, Inv
  <2>11. QED
    BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p
  
<1>3. Inv => MutualExclusion
  BY SMT DEF Inv, MutualExclusion
  
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
------------------------------------------------------------------------------ 
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"
DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)
=============================================================================
\* Modification History
\* Last modified Tue Aug 27 12:22:38 PDT 2019 by loki
\* Last modified Thu May 24 20:03:58 CEST 2018 by merz
\* Last modified Thu May 24 13:49:22 CEST 2018 by merz
\* Last modified Tue Jul 21 17:55:23 PDT 2015 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
