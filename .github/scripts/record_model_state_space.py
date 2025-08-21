"""
Records the number of unique & total states encountered by TLC for each small
model where that info is not present, then writes it to a manifest.json file.
"""

from argparse import ArgumentParser
from datetime import timedelta
import logging
from os.path import dirname, normpath, join
from subprocess import CompletedProcess, TimeoutExpired
import tla_utils

parser = ArgumentParser(description='Updates manifest.json with unique & total model states for each small model.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=False, default='deps/tools/tla2tools.jar')
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=False, default='deps/tlapm/library')
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=False, default='deps/community/modules.jar')
parser.add_argument('--examples_root', help='Root directory of the tlaplus/examples repository', required=False, default='.')
parser.add_argument('--skip', nargs='+', help='Space-separated list of models to skip checking', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only check models in this space-separated list', required=False, default=[])
parser.add_argument('--enable_assertions', help='Enable Java assertions (pass -enableassertions to JVM)', action='store_true')
parser.add_argument('--all', help='Redo all state counts, not just missing ones', action='store_true')
args = parser.parse_args()

logging.basicConfig(level=logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
examples_root = args.examples_root
skip_models = args.skip
only_models = args.only
run_all = args.all
enable_assertions = args.enable_assertions

def check_model(module, model):
    module_path = tla_utils.from_cwd(examples_root, module['path'])
    model_path = tla_utils.from_cwd(examples_root, model['path'])
    logging.info(model_path)
    hard_timeout_in_seconds = 60
    tlc_result = tla_utils.check_model(
        tools_jar_path,
        '.',
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
        model['mode'],
        module['features'],
        enable_assertions,
        hard_timeout_in_seconds
    )
    output = ' '.join(tlc_result.args) + '\n' + tlc_result.stdout
    match tlc_result:
        case CompletedProcess():
            expected_result = model['result']
            actual_result = tla_utils.resolve_tlc_exit_code(tlc_result.returncode)
            if expected_result != actual_result:
                logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
                logging.error(output)
                return False
            state_count_info = tla_utils.extract_state_count_info(tlc_result.stdout)
            if state_count_info is None:
                logging.error("Failed to find state info in TLC output")
                logging.error(output)
                return False
            logging.info(f'States (distinct, total, depth): {state_count_info}')
            model['distinctStates'], model['totalStates'], model['stateDepth'] = state_count_info
            return True
        case TimeoutExpired():
            logging.error(f'{model_path} hit hard timeout of {hard_timeout_in_seconds} seconds')
            logging.error(output)
            return False
        case _:
            logging.error(f'Unhandled TLC result type {type(tlc_result)}: {tlc_result}')
            logging.error(output)
            return False

# Ensure longest-running modules go first
manifest = tla_utils.load_all_manifests(examples_root)
small_models = sorted(
    [
        (path, spec, module, model, runtime)
        for path, spec in manifest
        for module in spec['modules']
        for model in module['models']
        if (runtime := tla_utils.parse_timespan(model['runtime'])) <= timedelta(seconds=30)
            and tla_utils.is_state_count_valid(model)
            # This model is nondeterministic due to use of the Random module
            and model['path'] != 'specifications/SpanningTree/SpanTreeRandom.cfg'
            # This model generates the same distinct states but order varies
            and model['path'] != 'specifications/ewd998/EWD998ChanTrace.cfg'
            and model['path'] not in skip_models
            and (only_models == [] or model['path'] in only_models)
            and (run_all or (
                'distinctStates' not in model
                or 'totalStates' not in model
                or 'stateDepth' not in model
            ))
    ],
    key = lambda m: m[4],
    reverse=True
)

for path in skip_models:
    logging.info(f'Skipping {path}')

for manifest_dir, spec, module, model, _ in small_models:
    manifest_path = join(manifest_dir, 'manifest.json')
    success = check_model(module, model)
    if not success:
        exit(1)
    tla_utils.write_json(spec, manifest_path)

exit(0)

