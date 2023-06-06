"""
Validate all proofs in all modules with TLAPM.
"""

from argparse import ArgumentParser
from os.path import dirname, join, normpath
import subprocess
from timeit import default_timer as timer
import tla_utils

parser = ArgumentParser(description='Validate all proofs in all modules with TLAPM.')
parser.add_argument('--tlapm_path', help='Path to TLAPM install dir; should have bin and lib subdirs', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
args = parser.parse_args()

tlapm_path = normpath(args.tlapm_path)
manifest_path = normpath(args.manifest_path)
manifest = tla_utils.load_json(manifest_path)
examples_root = dirname(manifest_path)

# Tracked in https://github.com/tlaplus/Examples/issues/67
failing_proofs = [
    'specifications/Bakery-Boulangerie/Bakery.tla',
    'specifications/Bakery-Boulangerie/Boulanger.tla',
    'specifications/Paxos/Consensus.tla',
    'specifications/PaxosHowToWinATuringAward/Consensus.tla',
    'specifications/lamport_mutex/LamportMutex_proofs.tla',
    'specifications/ewd998/EWD998_proof.tla'
]

# Fingerprint issues; tracked in https://github.com/tlaplus/tlapm/issues/85
long_running_proofs = [
    'specifications/LoopInvariance/Quicksort.tla',
    'specifications/LoopInvariance/SumSequence.tla',
    'specifications/bcastByz/bcastByz.tla',
    'specifications/MisraReachability/ReachabilityProofs.tla'
]

proof_module_paths = [
    module['path']
    for spec in manifest['specifications']
    for module in spec['modules']
    if 'proof' in module['features']
        and module['path'] not in failing_proofs
        and module['path'] not in long_running_proofs
]

success = True
tlapm_path = join(tlapm_path, 'bin', 'tlapm')
for module_path in proof_module_paths:
    print(module_path)
    start_time = timer()
    module_path = tla_utils.from_cwd(examples_root, module_path)
    module_dir = dirname(module_path)
    tlapm = subprocess.run(
        [
            tlapm_path, module_path,
            '-I', module_dir
        ], capture_output=True
    )
    end_time = timer()
    print(f'Checked proofs in {end_time - start_time:.1f}s')
    if tlapm.returncode != 0:
        print('FAILURE')
        print(tlapm.stderr.decode('utf-8'))
        success = False

exit(0 if success else 1)

