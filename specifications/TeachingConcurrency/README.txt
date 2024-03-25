This directory contains two versions of an extremely simple example
presented in the note "Teaching Concurrency" published in the March
2009 issue of ACM SIGACT News.  A copy of that note can be found at:

   http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf

The algorithm also appears as an example in Section 7.2 of "Proving
Safety Properties", which is at:

  http://lamport.azurewebsites.net/tla/proving-safety.pdf 

The problem posed in both of these publications is to prove a simple
invariance property, which requires finding a suitable inductive
invariant.  Module Simple contains the algorithm written in PlusCal,
the inductive invariant, and a TLAPS-checked invariance proof.  You
should try to find the inductive invariant and write your own proof
before looking at the one in the module.

In the original algorithm, specified in module Simple, processeses
communication with one another using the customary shared registers
that support atomic reads and writes.  Yuri Abraham suggested
generalizing the algorithm to use a weaker form interprocess
communication using regular registers.  Module SimpleRegular explains
what regular registers are, contains a PlusCal version of the
algorithm using those registers, and shows that a simple modification
of the inductive invariant and invariance proof works for that
algorithm.
