-------------------------------- MODULE c1cs --------------------------------

(* An encoding of the consensus algorithm with crash faults in one communication 
   step [1]. Here we consider only the algorithm itself (Fig. 1), without looking  
   at the underlying consensus. 
   
   [1] Brasileiro, Francisco, et al. "Consensus in one communication step." 
   Parallel Computing Technologies (2001): 42-50.
                                                               
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 3 * T < N /\ 0 <= F /\ F <= T /\ 0 < N

VARIABLES pc, v, dValue, bcastMsg, rcvdMsg

vars == << pc, v, dValue, bcastMsg, rcvdMsg >>

Proc == 1..N      (* all processes, including the faulty ones *)

(* for program counters *)
Location == { "PROPOSE", "DECIDE", "CALL", "CRASH", "DONE" }  

(* User-defined operators to create messages *)
makeProposedMsg(v_i, i) == [ type |-> "Proposed", value |-> v_i, sndr |-> i ]
makeDecisionMsg(v_i, i ) == [ type |-> "Decision", value |-> v_i, sndr |-> i ]

(* Set of messages *)
PMsg == [ type : {"Proposed"} , value : Values, sndr : Proc ]
DMsg == [ type : {"Decision"}, value : Values, sndr : Proc ]
Msg == PMsg \cup DMsg 

(* Initial step *)
Init ==     
  /\ v \in [ Proc -> Values ]           (* Every process proposes randomly a value. *)
  /\ pc = [ i \in Proc |-> "PROPOSE" ]  (* Every process will vote for its value.   *)
  /\ dValue = [ i \in Proc |-> Bottom ] (* No process decides.                      *)    
  /\ bcastMsg = {}                      (* No messages were sent.                   *)
  /\ rcvdMsg = [ i \in Proc |-> {} ]    (* No messages were received.               *)   
    
(* If there are less than F faulty process, process i crashes. *)    
Crash(i) ==
  /\ Cardinality( { p \in Proc : pc[p] # "CRASH" } ) <  F
  /\ pc[i] # "CRASH"  
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]     
  /\ UNCHANGED << dValue, v, bcastMsg, rcvdMsg >>
        
(* Receives a new message. *)        
Receive(i) ==
  /\ pc[i] # "CRASH"
  /\ \E sndr \in Proc, msg \in Msg:
        /\ msg \in bcastMsg       
        /\ msg \notin rcvdMsg[i]
        /\ rcvdMsg' = [ rcvdMsg EXCEPT ![i] = rcvdMsg[i] \cup { msg } ]             
        /\ UNCHANGED << pc, v, dValue, bcastMsg >>                           
   
(* Broadcasts PROPOSED(v_i) *)    
Propose(i) ==    
  /\ pc[i] = "PROPOSE"
  /\ pc' = [ pc EXCEPT ![i] = "DECIDE" ]
  /\ bcastMsg' = bcastMsg \cup { makeProposedMsg(v[i], i) }
  /\ UNCHANGED << v, dValue, rcvdMsg >>    
   
(* If a process received PHASE1(_, _) from at least N - F processes, 
 * it updates its local view and then estimates the expected value. 
 *)   
Core_T1(i) == 
  /\ pc[i] = "DECIDE"
  /\ Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" }) >= N - T
  /\ IF /\ (\E tV \in Values : \A msg \in rcvdMsg[i] : msg.type = "Proposed" => msg.value = tV) 
     THEN /\ dValue' = [ dValue EXCEPT ![i] = CHOOSE tV \in Values : (Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - T) ]
          /\ bcastMsg' = bcastMsg \cup { makeDecisionMsg(dValue'[i], i) } 
          /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
          /\ UNCHANGED << v >>                 
     ELSE /\ IF \E tV \in Values : Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - 2 * T
             THEN /\ v' = [ v EXCEPT ![i] = CHOOSE tV \in Values : (Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - 2 * T) ]                    
                  /\ UNCHANGED << dValue, bcastMsg >>
             ELSE UNCHANGED << dValue, v, bcastMsg >>
          /\ pc' = [ pc EXCEPT ![i] = "CALL" ]   
  /\ UNCHANGED << rcvdMsg >>                              

(* If process i received a DECISION message, it decides. *)     
T2(i) ==
  /\ pc[i] # "DONE"
  /\ pc[i] # "CRASH"
  /\ \E msg \in rcvdMsg[i]:
        /\ msg.type = "Decision"
        /\ dValue' = [ dValue EXCEPT ![i] = msg.value ]
        /\ bcastMsg' = bcastMsg \cup { makeDecisionMsg(dValue'[i], i) } 
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << v, rcvdMsg >>
    
(* Just to avoid deadlock checking. *)    
DoNothing(i) ==
  /\ \/ pc[i] = "CALL" 
     \/ pc[i] = "DONE"
  /\ UNCHANGED vars                    
            
Next ==  
  \E i \in Proc: \/ Crash(i)            
                 \/ Receive(i)      
                 \/ Propose(i)                                             
                 \/ Core_T1(i)
                 \/ T2(i)       
                 \/ DoNothing(i)     
                                    
Spec == Init /\ [][Next]_<< pc, v, dValue, bcastMsg, rcvdMsg >>
             /\ WF_vars(\E i \in Proc : \/ Receive(i)            
                                        \/ Propose(i)                                                
                                        \/ Core_T1(i)
                                        \/ T2(i))        

TypeOK ==    
  /\ v \in [ Proc -> Values ] 
  /\ pc \in [ Proc -> Location ]       
  /\ bcastMsg \in SUBSET (PMsg \cup DMsg) 
  /\ rcvdMsg \in [ Proc -> SUBSET (PMsg \cup DMsg) ]    
  /\ dValue \in [ Proc -> { Bottom } \cup Values ]  
    
(* If a process decides v, then v was proposed by some process. *)
Validity == \A i \in Proc : ((dValue[i] # Bottom) => (\E j \in Proc : dValue[i] = v[j]))

(* First line: No two processes decide differently. *)
(* Second line: If some process decided v, all process calling the underlying consensus algorithm propose v. *)
Agreement == 
  /\ \A i, j \in Proc : ((dValue[i] # Bottom /\ dValue[j] # Bottom) => (dValue[i] = dValue[j]))
  /\ \A i \in Proc : pc[i] = "CALL" => (\A j \in Proc : pc[j] = "DONE" => v[i] = dValue[j]) 
    
(* Only talk about decided processes*)    
WeakAgreement ==
  /\ \A i, j \in Proc : ((dValue[i] # Bottom /\ dValue[j] # Bottom) => (dValue[i] = dValue[j]))   

(* Every correct process eventually decides on some values. *)
Termination == <>(\A i \in Proc : pc[i] = "CRASH" \/ pc[i] = "DONE" \/ pc[i] = "CALL")

(* Inductive strengthens usually are constraints on:
    - TypeOK,
    - PROPOSED messages and prefer values,            
    - values in messages which have sent,          
    - DECISION values and DECISION messages,    
    - the number of PROPOSED messages and DECISION messages,       
    - program counters and which messages have sent, 
    - DECISION values and processes' decisions,    
    - program counters and DECISION values,          
    - DECISION values and DECISION messages, 
    - DECISION values, and
    - which messages are sent and received.
   However, until now we don't what inductive strengthens are necessary to construct an
   inductive invariant with WeakAgreement. 
 *)
IndStrengthens ==
  /\ TypeOK
  (* Every correct process proposes only its prefer value. *)
  /\ \A msg \in bcastMsg : (msg.type = "Proposed" /\ (pc[msg.sndr] = "PROPOSE" \/ pc[msg.sndr] = "DECIDE"))
                              => msg.value = v[msg.sndr]  
  (* A correct process can send at most one message for each kind of messages.  *)
  /\ \A msg1 \in bcastMsg, msg2 \in bcastMsg : (msg1.sndr = msg2.sndr /\ msg1.type = msg2.type) 
                                                    => msg1.value = msg2.value      
    
  (* All DECISION messages have the same value. *) 
  /\ \A msg1 \in bcastMsg, msg2 \in bcastMsg : (msg1.type = "Decision" /\ msg2.type = "Decision") 
                                                    => msg1.value = msg2.value    
  (* How to detect it automatically?
     Every DECISION message has the same value with at least N - T PROPOSED messages. *)  
  /\ \A msg1 \in bcastMsg : msg1.type = "Decision" => (Cardinality( { msg2 \in bcastMsg : msg2.type = "Proposed" /\ msg1.value = msg2.value} ) >= N - T)
  (* A process has not broadcasted any message before entering the location PROPOSE. *)
  /\ \A i \in Proc : pc[i] = "PROPOSE" => ((\A msg \in bcastMsg : msg.sndr # i) )          
  (* How to detect it automatically?
     DECISION messages are always consistent with processes' decisions.  *)    
  /\ \A i \in Proc : dValue[i] = Bottom => (\A msg \in bcastMsg : msg.type = "Decision" => msg.sndr # i)  
  (* A DECISION value must be different from Bottom *)       
  /\ \A i \in Proc : pc[i] = "DONE" => dValue[i] # Bottom     
  (* After deciding, every correct process needs to broadcast its decision immediately. *)          
  /\ \A i \in Proc : dValue[i] # Bottom => (\E msg \in bcastMsg : msg.sndr = i /\ msg.type = "Decision" /\ msg.value = dValue[i])                                                                                                         
  (* A process decides only after entering the locations PROPOSE and DECIDE. *)  
  /\ \A i \in Proc : dValue[i] # Bottom => (pc[i] # "PROPOSE" /\ pc[i] # "DECIDE")   
  (* A process has not decided before entering the locations PROPOSE and DECIDE. *)
  /\ \A i \in Proc : (pc[i] = "PROPOSE" \/ pc[i] = "DECIDE") => ((\A msg \in bcastMsg : dValue[i] = Bottom) )
  (* Every received message were broadcasted by some process. *)
  /\ \A i \in Proc: rcvdMsg[i] \subseteq bcastMsg   
  
  
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:28:37 CEST 2018 by tthai

