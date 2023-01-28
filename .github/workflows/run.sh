#!/bin/bash

TLC_COMMAND="java -Dtlc2.TLC.stopAfter=180 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar tlc2.TLC -workers auto -lncheck final -tool -deadlock"

## This spec used to be accepted by Apalache, but since Apalache has started to require type annotations for all variables.
## https://github.com/tlaplus/Examples/pull/31#issuecomment-796354291
#echo Check MCInnerSerial
#$TLC_COMMAND  specifications/SpecifyingSystems/AdvancedExamples/MCInnerSerial
echo Check EWD840_json
sed -i '/^SendMsg/{n;d;}' specifications/ewd840/EWD840.tla ## Cause RealInv to be violated (see EWD840_json.tla)
$TLC_COMMAND specifications/ewd840/EWD840_json

