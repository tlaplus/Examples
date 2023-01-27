# SDP_Verification

This project is about the TLA+ Spec of SDP architecture and algorithm written by Luming Dong and Zhi niu based on the open source project fwknop.

The subdirectory  SDP_Attack_Spec  contains the specification based on the following materials:                  
(* https://cloudsecurityalliance.org/artifacts/software-defined-perimeter-zero-trust-specification-v2/  *)                                           
(* http://www.cipherdyne.org/fwknop/                                       *)

The verification results show that current SDP protocol framework has a vulnerability in the scenario of remote access through NAT technology.

The subdirectory  SDP_Attack_New_Solution_Spec  contains the specification for the improved SDP architecture design
which fixed the flaw related to service concealment feature.

The slide  "Specifying and Verifying SDP Protocol Based Zero Trust Architecture Using TLA+.pptx" contains the key description of the reserach work.
For details, please refer to paper :
https://dl.acm.org/doi/10.1145/3558819.3558826

