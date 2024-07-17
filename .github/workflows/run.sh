#!/bin/bash

set -ex

TLC_COMMAND="java -ea -XX:+UseParallelGC -Dtlc2.TLC.stopAfter=180 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar tlc2.TLC -workers auto -lncheck final -tool -deadlock"

echo Check specifications/aba-asyn-byz/aba_asyn_byz
$TLC_COMMAND specifications/aba-asyn-byz/aba_asyn_byz
echo Check Constrain_CRDT
$TLC_COMMAND specifications/FiniteMonotonic/Constrain_CRDT
echo Check Finitize_CRDT
$TLC_COMMAND specifications/FiniteMonotonic/Finitize_CRDT
echo Check Finitize_ReplicatedLog
$TLC_COMMAND specifications/FiniteMonotonic/Finitize_ReplicatedLog
echo Check specifications/KeyValueStore/MCKVsnap
$TLC_COMMAND specifications/KeyValueStore/MCKVsnap
echo Check specifications/LoopInvariance/MCBinarySearch
$TLC_COMMAND specifications/LoopInvariance/MCBinarySearch
echo Check specifications/LoopInvariance/MCQuicksort
$TLC_COMMAND specifications/LoopInvariance/MCQuicksort
echo Check specifications/MisraReachability/MCParReach
$TLC_COMMAND specifications/MisraReachability/MCParReach
echo Check specifications/MisraReachability/MCReachable
$TLC_COMMAND specifications/MisraReachability/MCReachable
echo Check specifications/SDP_Verification/SDP_Attack_New_Solution_Spec/MC
$TLC_COMMAND specifications/SDP_Verification/SDP_Attack_New_Solution_Spec/MC
echo Check specifications/SingleLaneBridge/MC
$TLC_COMMAND specifications/SingleLaneBridge/MC
echo Check specifications/SpanningTree/SpanTree
$TLC_COMMAND specifications/SpanningTree/SpanTree
echo Check specifications/acp/ACP_NB_TLC
$TLC_COMMAND specifications/acp/ACP_NB_TLC
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
echo Check MCEcho
$TLC_COMMAND specifications/echo/MCEcho
echo Check Prisoners
$TLC_COMMAND specifications/Prisoners/Prisoners
echo Check LSpec-model
$TLC_COMMAND specifications/dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC
echo Check Safety-4-processors
$TLC_COMMAND specifications/dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC
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
$TLC_COMMAND specifications/N-Queens/Queens.toolbox/FourQueens/MC || (($? == 12))  ## Expect a safety violation
echo Check FourQueens PlusCal
$TLC_COMMAND specifications/N-Queens/QueensPluscal.toolbox/FourQueens/MC || (($? == 12))  ## Expect a safety violation
echo Check ReadersWriters
$TLC_COMMAND specifications/ReadersWriters/MC
echo Check EWD687a
$TLC_COMMAND specifications/ewd687a/MCEWD687a
echo Simulate EWD687a_anim
$TLC_COMMAND -simulate num=100 -note specifications/ewd687a/EWD687a_anim || (($? == 12))  ## Expect a safety violation
echo Check Huang
$TLC_COMMAND specifications/Huang/Huang
