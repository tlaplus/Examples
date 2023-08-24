#!/bin/bash

TLC_COMMAND="java -Dtlc2.TLC.stopAfter=180 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar tlc2.TLC -workers auto -lncheck final -tool -deadlock"

echo Check EWD840
$TLC_COMMAND specifications/ewd840/EWD840
echo Check CarTalkPuzzle Model_1
$TLC_COMMAND specifications/CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_1/MC
echo Check CarTalkPuzzle Model_2
$TLC_COMMAND specifications/CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_2/MC
echo Check MCDieHarder
$TLC_COMMAND specifications/DieHard/MCDieHarder || (($? == 12))  ## Expect a safety violation
echo Check DieHard
$TLC_COMMAND specifications/DieHard/DieHard || (($? == 12))  ## Expect a safety violation
echo Check DiningPhilosophers
$TLC_COMMAND specifications/DiningPhilosophers/DiningPhilosophers
echo Check TransitiveClosure
$TLC_COMMAND specifications/TransitiveClosure/TransitiveClosure
echo Check Hanoi
java -Dtlc2.TLC.stopAfter=600 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar:specifications/tower_of_hanoi/Hanoi.toolbox/Model_1/MC tlc2.TLC -workers auto -lncheck final -tool -deadlock specifications/tower_of_hanoi/Hanoi.toolbox/Model_1/MC
echo Check MCEcho
$TLC_COMMAND specifications/echo/MCEcho
echo Check Prisoners
$TLC_COMMAND specifications/Prisoners/Prisoners
echo Check LSpec-model
$TLC_COMMAND specifications/dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC
echo Check Safety-4-processors
$TLC_COMMAND specifications/dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC
## This spec used to be accepted by Apalache, but since Apalache has started to require type annotations for all variables.
## https://github.com/tlaplus/Examples/pull/31#issuecomment-796354291
#echo Check EinsteinRiddle
#$TLC_COMMAND  specifications/EinsteinRiddle/Einstein
echo Check MCInnerSequential
$TLC_COMMAND specifications/SpecifyingSystems/AdvancedExamples/MCInnerSequential
#echo Check MCInnerSerial
#$TLC_COMMAND  specifications/SpecifyingSystems/AdvancedExamples/MCInnerSerial
echo Check MCLiveWriteThroughCache
$TLC_COMMAND specifications/SpecifyingSystems/Liveness/MCLiveWriteThroughCache
echo Check LiveHourClock
$TLC_COMMAND specifications/SpecifyingSystems/Liveness/LiveHourClock
echo Check MCLiveInternalMemory
$TLC_COMMAND specifications/SpecifyingSystems/Liveness/MCLiveInternalMemory
echo Check SimpleMath
$TLC_COMMAND specifications/SpecifyingSystems/SimpleMath/SimpleMath
echo Check HourClock2
$TLC_COMMAND specifications/SpecifyingSystems/HourClock/HourClock2
echo Check HourClock
$TLC_COMMAND specifications/SpecifyingSystems/HourClock/HourClock
echo Check MCInternalMemory
$TLC_COMMAND specifications/SpecifyingSystems/CachingMemory/MCInternalMemory
echo Check MCWriteThroughCache
$TLC_COMMAND specifications/SpecifyingSystems/CachingMemory/MCWriteThroughCache
echo Check PrintValues
$TLC_COMMAND specifications/SpecifyingSystems/AsynchronousInterface/PrintValues
echo Check AsynchInterface
$TLC_COMMAND specifications/SpecifyingSystems/AsynchronousInterface/AsynchInterface
echo Check Channel
$TLC_COMMAND specifications/SpecifyingSystems/AsynchronousInterface/Channel
echo Check MCAlternatingBit
$TLC_COMMAND specifications/SpecifyingSystems/TLC/MCAlternatingBit
echo Check ABCorrectness
$TLC_COMMAND specifications/SpecifyingSystems/TLC/ABCorrectness
echo Check MCRealTimeHourClock
$TLC_COMMAND specifications/SpecifyingSystems/RealTime/MCRealTimeHourClock || (($? != 1))  ## Stuttering
echo Check MCInnerFIFO
$TLC_COMMAND specifications/SpecifyingSystems/FIFO/MCInnerFIFO
echo Check EWD840_anim
$TLC_COMMAND -simulate num=1 specifications/ewd840/EWD840_anim || (($? == 12))  ## Expect a safety violation
echo Check SyncTerminationDetection
$TLC_COMMAND specifications/ewd840/SyncTerminationDetection
echo Check EWD840
$TLC_COMMAND specifications/ewd840/EWD840
echo Check EWD840_json
sed -i '/^SendMsg/{n;d;}' specifications/ewd840/EWD840.tla ## Cause RealInv to be violated (see EWD840_json.tla)
$TLC_COMMAND specifications/ewd840/EWD840_json
echo Check MCVoting
$TLC_COMMAND specifications/Paxos/MCVoting
echo Check MCConsensus
$TLC_COMMAND specifications/Paxos/MCConsensus
echo Check MCPaxos
$TLC_COMMAND specifications/Paxos/MCPaxos
echo Check EWD998ChanID
$TLC_COMMAND specifications/ewd998/EWD998ChanID
echo Check EWD998Chan
$TLC_COMMAND specifications/ewd998/EWD998Chan
echo Check EWD998
$TLC_COMMAND specifications/ewd998/EWD998
echo Check TestGraphs
$TLC_COMMAND specifications/TLC/TestGraphs
echo Check SchedulingAllocator
$TLC_COMMAND specifications/allocator/SchedulingAllocator
echo Check AllocatorRefinement
$TLC_COMMAND specifications/allocator/AllocatorRefinement
echo Check SimpleAllocator
$TLC_COMMAND specifications/allocator/SimpleAllocator
echo Check AllocatorImplementation
$TLC_COMMAND specifications/allocator/AllocatorImplementation
echo Check FourQueens
$TLC_COMMAND specifications/N-Queens/Queens.toolbox/FourQueens/MC
echo Check FourQueens PlusCal
$TLC_COMMAND specifications/N-Queens/QueensPluscal.toolbox/FourQueens/MC
echo Check ReadersWriters
$TLC_COMMAND specifications/ReadersWriters/MC
echo Check EWD687a
$TLC_COMMAND specifications/ewd687a/MCEWD687a
echo Simulate EWD687a_anim
$TLC_COMMAND -simulate num=100 -note specifications/ewd687a/EWD687a_anim || (($? == 12))  ## Expect a safety violation
echo Check Huang
$TLC_COMMAND specifications/Huang/Huang
