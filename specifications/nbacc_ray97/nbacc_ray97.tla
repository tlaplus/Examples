------------------------------ MODULE nbacc_ray97 ------------------------------

(* TLA+ encoding of the algorithm NBAC with crashes in: 

   [1] Raynal, Michel. "A case study of agreement problems in distributed 
   systems: non-blocking atomic commitment." High-Assurance Systems Engineering 
   Workshop, 1997., Proceedings. IEEE, 1997.
 
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this 
   package and can be found in the file LICENSE.
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc,     (* program counters            *)
          rcvd,   (* messages which are received *)
          sent,   (* messages which are sent by  *)
          fd      (* a failure detector reporting to every process 
                     whether some process has crashed              *)

ASSUME N \in Nat

Proc == 1 .. N    (* all processes, including the crashed ones   *)
    

M == { "YES", "NO" }

vars == << pc, rcvd, sent, fd >>

(* Receive new messages *)
Receive(self) ==
  \E r \in SUBSET (Proc \times M):
        /\ r \subseteq sent
        /\ rcvd[self] \subseteq r
        /\ rcvd' = [rcvd EXCEPT ![self] = r ]

(* The failure detectore sends a nondeterministically new prediction to process self. *)
UpdateFailureDetector(self) ==
  \/  fd' = [fd EXCEPT ![self] = FALSE ]
  \/  fd' = [fd EXCEPT ![self] = TRUE ]

(* Process self becomes crash. *)
UponCrash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ sent' = sent

(* Sends a YES message *)
UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc' = [pc EXCEPT ![self] = "SENT"]
  /\ sent' = sent \cup { <<self, "YES">> }

(* Sends a NO message *)
UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc' = [pc EXCEPT ![self] = "SENT"]
  /\ sent' = sent \cup { <<self, "NO">> }

(* - If process self voted and received a NO messages, it aborts.
   - If process self voted and thinks that some process has crashed,
     it aborts. 
   - If process self voted, received only YES messages from all processes, and 
     thinks that all processes are still correct, it commits.
 *)
UponSent(self) ==
  /\ pc[self] = "SENT"
  /\ ( \/ ( /\ fd'[self] = TRUE
            /\ pc' = [pc EXCEPT ![self] = "ABORT"] )
       \/ ( /\ \E msg \in rcvd[self] : msg[2] = "NO"
            /\ pc' = [pc EXCEPT ![self] = "ABORT"] )
       \/ ( /\ fd'[self] = FALSE
            /\ { p \in Proc : ( \E msg \in rcvd'[self] : msg[1] = p /\ msg[2] = "YES") } = Proc
            /\ pc' = [pc EXCEPT ![self] = "COMMIT"] ) )   
  /\ sent' = sent
        
Step(self) ==   
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponSent(self)
     \/ pc' = pc /\ sent' = sent    (* Do nothing but we need this to avoid deadlock *)

(* Some processes vote YES. Others vote NO. *)
Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"YES", "NO"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd \in [ Proc -> {FALSE, TRUE} ]

(* All processes vote YES. *)
InitAllYes == 
  /\ sent = {}
  /\ pc = [ Proc |-> "YES" ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd \in [ i \in Proc |-> {TRUE} ]
      
Next ==  (\E self \in Proc : Step(self))

(* Add the weak fainress condition *)
Spec == Init /\ [][Next]_vars
             /\ WF_vars(\E self \in Proc : /\ Receive(self)
                                           /\ \/ UponYes(self)
                                              \/ UponNo(self)
                                              \/ UponSent(self))


TypeOK == 
  /\ sent \subseteq Proc \times M
  /\ pc \in [ Proc -> {"NO", "YES", "ABORT", "COMMIT", "SENT", "CRASH"} ]
  /\ rcvd \in [ Proc -> SUBSET (Proc \times M) ]
  /\ fd \in [ Proc -> BOOLEAN ]
          
Validity == 
  \/ \A i \in Proc : pc[i] = "YES"
  \/ \A i \in Proc : pc[i] # "COMMIT"
 
 (*
NonTriv ==   
    ( /\ \A i \in Proc : pc[i] = "YES"
      /\ [](\A i \in Proc : pc[i] # "CRASH"
      /\ (<>[](\A self \in Proc : (fd[self] = FALSE)))
  => <>(\A self \in Proc : (pc[self] = "COMMIT"))
  *)
          
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai
\* Created Thu Mar 12 00:46:19 CET 2015 by igor
