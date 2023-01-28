#!/bin/bash

TLC_COMMAND="java -Dtlc2.TLC.stopAfter=180 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar tlc2.TLC -workers auto -lncheck final -tool -deadlock"

## This spec used to be accepted by Apalache, but since Apalache has started to require type annotations for all variables.
## https://github.com/tlaplus/Examples/pull/31#issuecomment-796354291
#echo Check MCInnerSerial
#$TLC_COMMAND  specifications/SpecifyingSystems/AdvancedExamples/MCInnerSerial
echo Check EWD840_anim
$TLC_COMMAND -simulate num=1 specifications/ewd840/EWD840_anim || (($? == 12))  ## Expect a safety violation
echo Check EWD840_json
sed -i '/^SendMsg/{n;d;}' specifications/ewd840/EWD840.tla ## Cause RealInv to be violated (see EWD840_json.tla)
$TLC_COMMAND specifications/ewd840/EWD840_json
echo Check EWD998ChanID
$TLC_COMMAND specifications/ewd998/EWD998ChanID
echo Simulate EWD687a_anim
$TLC_COMMAND -simulate num=100 -note specifications/ewd687a/EWD687a_anim || (($? == 12))  ## Expect a safety violation
echo Simulate KnuthYao
$TLC_COMMAND -generate specifications/KnuthYao/SimKnuthYao
echo Check Dijkstra Mutext
$TLC_COMMAND specifications/dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC

