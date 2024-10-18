
  $ wget https://nightly.tlapl.us/dist/tla2tools.jar
  $ wget https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
  $ java -jar tla2tools.jar -config SCCRDT.tla SCCRDT.tla

----------------------------- MODULE SCCRDT -----------------------------
EXTENDS TLC, Naturals, Sequences, IOUtils, CSV

CSVFile ==
    "MCCRDT-" \o ToString(JavaTime) \o ".csv"

CmdLine == 
    <<"java", "-jar", TLCGet("config").install, "-note", "MCCRDT.tla">>

ASSUME \A c \in [ D: 0..3, F: 0..7, G: BOOLEAN, C: BOOLEAN, O: {CSVFile} ] : 
            PrintT(c) /\ IOEnvExec(c, CmdLine).exitValue \in {0, 10, 13}

=============================================================================
---- CONFIG SCCRDT ----
====