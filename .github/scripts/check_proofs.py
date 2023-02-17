from os.path import dirname, join
import subprocess
from timeit import default_timer as timer
import tla_utils

manifest = tla_utils.load_manifest()

failing_proofs = [
    'specifications/Bakery-Boulangerie/Bakery.tla',
    'specifications/Bakery-Boulangerie/Boulanger.tla',
    'specifications/Paxos/Consensus.tla',
    'specifications/PaxosHowToWinATuringAward/Consensus.tla',
    'specifications/lamport_mutex/LamportMutex_proofs.tla',
    'specifications/ewd998/EWD998_proof.tla'
]

long_running_proofs = [
    'specifications/LoopInvariance/Quicksort.tla',
    'specifications/LoopInvariance/SumSequence.tla',
    'specifications/bcastByz/bcastByz.tla'
]

proof_module_paths = [
    module['path']
    for spec in manifest['specifications']
    for module in spec['modules']
    if 'proof' in module['features']
        #and module['path'] not in failing_proofs
        #and module['path'] not in long_running_proofs
]

success = True
for module_path in proof_module_paths:
    print(module_path)
    start_time = timer()
    tlaps_path = join('tlapm-install', 'bin', 'tlapm')
    module_dir = dirname(module_path)
    tlaps = subprocess.run(
        [
            tlaps_path, module_path,
            '-I', module_dir
        ], capture_output=True
    )
    end_time = timer()
    print(f'Checked proofs in {end_time - start_time:.1f}s')
    if tlaps.returncode != 0:
        print('FAILURE')
        print(tlaps.stderr.decode('utf-8'))
        success = False

exit(0 if success else 1)

