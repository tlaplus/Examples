
  $ wget https://nightly.tlapl.us/dist/tla2tools.jar
  $ wget https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
  $ java -jar tla2tools.jar -config SCCRDT.tla SCCRDT.tla

----------------------------- MODULE SCCRDT -----------------------------
EXTENDS TLC, Naturals, Sequences, IOUtils

CmdLine == 
    <<"java", "-jar", TLCGet("config").install, "-note", "MCCRDT.tla">>

ASSUME \A c \in [ D: 0..3, F: 0..6, G: BOOLEAN, C: BOOLEAN ] : 
    PrintT(<<"conf", c, IOEnvExec(c, CmdLine).exitValue>>)

=============================================================================
---- CONFIG SCCRDT ----
====