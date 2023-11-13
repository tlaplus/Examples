------------------------------- MODULE bosco -------------------------------

(* TLA+ encoding of the algorithm BOSCO considered in: 

   [1] Song, Yee Jiun, and Robbert van Renesse. "Bosco: One-step byzantine asynchronous 
   consensus." International Symposium on Distributed Computing. Springer, Berlin, 
   Heidelberg, 2008.
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

moreNplus3Tdiv2 == (N + 3 * T) \div 2 + 1
moreNminusTdiv2 == (N - T) \div 2 + 1

VARIABLE pc, rcvd, sent

ASSUME  /\ N \in Nat /\ T \in Nat /\ F \in Nat
        /\ moreNplus3Tdiv2 \in Nat /\ moreNminusTdiv2 \in Nat
    
ASSUME (N > 3 * T) /\ (T >= F) /\ (F >= 0)

(* auxiliary parameter
   "more than (N + 3 * T) / 2 VOTE messages"        
   1st case: if (N + 3 * T) is odd, 2nd case: even
 *)
ASSUME  \/ 2 * moreNplus3Tdiv2 = N + 3 * T + 1
        \/ 2 * moreNplus3Tdiv2 = N + 3 * T + 2

(* auxiliary parameter
   "more than (N - T) / 2 VOTE messages"            
   1st case: if (N - T) is odd, 2nd case: even     
 *)    
ASSUME  \/ 2 * moreNminusTdiv2 = N - T + 1
        \/ 2 * moreNminusTdiv2 = N - T + 2

P == 1 .. N                 (* all processes, including the faulty ones    *)
Corr == 1 .. N - F          (* correct processes                            *)
Faulty == N - F + 1 .. N    (* the faulty processes                         *)
                            (* the last F processes are faulty              *)

M == { "ECHO0", "ECHO1" }

vars == << pc, rcvd, sent >>

rcvd0(self) == Cardinality({m \in rcvd'[self] : m[2] = "ECHO0"})         
  
rcvd1(self) == Cardinality({m \in rcvd'[self] : m[2] = "ECHO1"})  

(* Since a byzantine process can send two msgs ECHO0 and ECHO1, we need to count the 
   number of processes from which process self received a message.                                          
 *)
rcvd01(self) == Cardinality({p \in P : (\E m \in rcvd'[self] : m[1] = p)})       

(* All messages in sent are by correct processes.         
   A faulty process can send (two) arbitrary ECHO0 and ECHO1 messages.          
   Line 66: r is a subset of messages which were sent by correct and faulty processes.                      
   Line 68: r is a set of messages which process self has received until this step,
            and therefore, rcvd[self] should be a subset of r.   
   Line 69: update rcvd[self]                                               
 *)
Receive(self) ==
  \E r \in SUBSET (P \times M):
      /\ r \subseteq (sent \cup { <<p, "ECHO0">> : p \in Faulty }
                           \cup { <<p, "ECHO1">> : p \in Faulty })
      /\ rcvd[self] \subseteq r
      /\ rcvd' = [rcvd EXCEPT ![self] = r ]

(* If process self proposed 0, it broadcasts ECHO0 and moves to location S0. *)
UponV0(self) ==
  /\ pc[self] = "V0"
  /\ sent' = sent \cup { <<self, "ECHO0">> }
  /\ pc' = [pc EXCEPT ![self] = "S0"]        

(* If process self proposed 1, it broadcasts ECHO1 and moves to location S1. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "S1"]
  /\ sent' = sent \cup { <<self, "ECHO1">> }
        
(* If process self has
    - send its message (line 90), 
    - received messages from at least N - T processes (line 91), and 
    - received at least (N + 3 * T) / 2 messages with V0 (line 92), 
   then process self decides D0.
 *)                                  
UponOneStep0(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ rcvd01(self) >= N - T
  /\ rcvd0(self) >= moreNplus3Tdiv2
  /\ pc' = [pc EXCEPT ![self] = "D0"]
  /\ sent' = sent

(* If process self has 
    - send its message (line 103), 
    - received messages from at least N - T processes (line 104), and 
    - received at least (N + 3 * T) / 2 messages with V1 (line 105), 
   then process self decides D1.
 *)                                  
UponOneStep1(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ rcvd01(self) >= N - T
  /\ rcvd1(self) >= moreNplus3Tdiv2
  /\ pc' = [pc EXCEPT ![self] = "D1"]
  /\ sent' = sent


(* If process self has 
    - send its message (line 120), 
    - received messages from at least (N - T) / 2 processes (line 121),  
    - received at least (N - T) / 2 messages with V0 (line 122), and
    - received less than (N - T) / 2 messages with V1 (line 123),    
   then process self moves to U0.
   Both UponOneStep0 and UponUnderlying0 can be true, these conditions (lines 126
   and 127) ensure that UponOneStep0 has a higher priority.                                        
 *)                         
UponUnderlying0(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ rcvd01(self) >= N - T 
  /\ rcvd0(self) >= moreNminusTdiv2
  /\ rcvd1(self) < moreNminusTdiv2
  /\ pc' = [pc EXCEPT ![self] = "U0"]
  /\ sent' = sent
  /\ rcvd0(self) < moreNplus3Tdiv2
  /\ rcvd1(self) < moreNplus3Tdiv2 

(* If process self has 
    - send its message (line 139), 
    - received messages from at least (N - T) / 2 processes (line 140),  
    - received at least (N - T) / 2 messages with V0 (line 141), and
    - received less than (N - T) / 2 messages with V1 (line 142),    
   then process self moves to U0.
   Both UponOneStep0 and UponUnderlying0 can be true, these conditions (lines 145
   and 146) ensure that UponOneStep0 has a higher priority.                                        
 *)          
UponUnderlying1(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ rcvd01(self) >= N - T
  /\ rcvd1(self) >= moreNminusTdiv2
  /\ rcvd0(self) < moreNminusTdiv2
  /\ pc' = [pc EXCEPT ![self] = "U1"]   
  /\ sent' = sent     
  /\ rcvd0(self) < moreNplus3Tdiv2
  /\ rcvd1(self) < moreNplus3Tdiv2 
        
(* Process self has send its message (line 153) and received messages from 
   at least N - T processes (line 154). However, neither V0 nor V1 are 
   proposed by a majority of processes (lines 154 and 156). Process self makes
   a nondeterministic choice between moving to U0 and U1 (lines 158 and 159).
   Conditions on lines  164 and 164 ensure that UponUnderlyingUndecided has the
   least priority.                                
 *)
UponUnderlyingUndecided(self) ==
  /\ pc[self] = "S0" \/ pc[self] = "S1"
  /\ rcvd01(self) >= N - T     
  /\ rcvd0(self) >= moreNminusTdiv2 
  /\ rcvd1(self) >= moreNminusTdiv2
  /\  \/ pc[self] = "S0" /\ pc' = [pc EXCEPT ![self] = "U0"]
      \/ pc[self] = "S1" /\ pc' = [pc EXCEPT ![self] = "U1"]       
  /\ sent' = sent          
  /\ rcvd0(self) < moreNplus3Tdiv2
  /\ rcvd1(self) < moreNplus3Tdiv2

(* A transition , the last OR condition is for only receiving messages.   *)                
Step(self) ==   
  /\ Receive(self)
  /\ \/ UponV0(self)
     \/ UponV1(self)
     \/ UponOneStep0(self)
     \/ UponOneStep1(self)                                      
     \/ UponUnderlying0(self)
     \/ UponUnderlying1(self)
     \/ UponUnderlyingUndecided(self)
     \/ pc' = pc /\ sent' = sent

(* Initial step *)
Init ==
  /\ pc \in [ Corr -> {"V0", "V1"} ]  (* Processes can propose V0 and V1. *) 
  /\ sent = {}                        (* No message has sent. *)     
  /\ rcvd = [ i \in Corr |-> {} ]     (* No message has received. *)
 
Next ==  (\E self \in Corr: Step(self))

Spec == Init /\ [][Next]_vars 

(* V0 - the initial state with value 0  
   V1 - the initial state with value 1  
   S0 - sent vote 0 
   S1 - sent vote 1  
   D0 - decided on 0  
   D1 - decided on 1  
   U0 - called underlying consensus with value 0  
   U1 - called underlying consensus with value 1            
 *) 
TypeOK == 
  /\ sent \subseteq P \times M
  /\ pc \in [ Corr -> {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1"} ]
  /\ rcvd \in [ Corr -> SUBSET (P \times M) ]
          
Lemma3_0 == (\E self \in Corr: (pc[self] = "D0")) => (\A self \in Corr: (pc[self] /= "D1"))  
Lemma3_1 == (\E self \in Corr: (pc[self] = "D1")) => (\A self \in Corr: (pc[self] /= "D0"))  

Lemma4_0 == (\E self \in Corr: (pc[self] = "D0")) => (\A self \in Corr: (pc[self] /= "U1"))  
Lemma4_1 == (\E self \in Corr: (pc[self] = "D1")) => (\A self \in Corr: (pc[self] /= "U0"))  

(* If there are at most 7 * T processes, these properties OneStep0 and  *)
(* OneStep1 do not hold.                                                *)
OneStep0 ==
  (\A i \in Corr: pc[i] = "V0")
    => [](\A i \in Corr:
            /\ pc[i] /= "D1"
            /\ pc[i] /= "U0"
            /\ pc[i] /= "U1")

OneStep1 ==
  (\A i \in Corr: pc[i] = "V1")
    => [](\A i \in Corr:
            /\ pc[i] /= "D0"
            /\ pc[i] /= "U0"
            /\ pc[i] /= "U1")

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:28:27 CEST 2018 by tthai
\* Created Tue Jun 23 17:13:29 CEST 2015 by igor
