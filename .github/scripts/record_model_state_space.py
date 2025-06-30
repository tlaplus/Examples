"""
Records the number of unique & total states encountered by TLC for each small
model where that info is not present, then writes it to the manifest.json.
"""

from argparse import ArgumentParser
import logging
from os.path import dirname, normpath
from subprocess import CompletedProcess, TimeoutExpired
import tla_utils

parser = ArgumentParser(description='Updates manifest.json with unique & total model states for each small model.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of models to skip checking', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only check models in this space-separated list', required=False, default=[])
parser.add_argument('--enable_assertions', help='Enable Java assertions (pass -enableassertions to JVM)', action='store_true')
args = parser.parse_args()

logging.basicConfig(level=logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_models = args.skip
only_models = args.only
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
        model['features'],
        enable_assertions,
        hard_timeout_in_seconds
    )
    match tlc_result:
        case CompletedProcess():
            expected_result = model['result']
            actual_result = tla_utils.resolve_tlc_exit_code(tlc_result.returncode)
            if expected_result != actual_result:
                logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
                logging.error(tlc_result.stdout)
                return False
            state_count_info = tla_utils.extract_state_count_info(tlc_result.stdout)
            if state_count_info is None:
                logging.error("Failed to find state info in TLC output")
                logging.error(tlc_result.stdout)
                return False
            logging.info(f'States (distinct, total, depth): {state_count_info}')
            model['distinctStates'], model['totalStates'], model['stateDepth'] = state_count_info
            return True
        case TimeoutExpired():
            logging.error(f'{model_path} hit hard timeout of {hard_timeout_in_seconds} seconds')
            logging.error(tlc_result.output.decode('utf-8'))
            return False
        case _:
            logging.error(f'Unhandled TLC result type {type(tlc_result)}: {tlc_result}')
            return False

# Ensure longest-running modules go first
manifest = tla_utils.load_json(manifest_path)
small_models = sorted(
    [
        (module, model, tla_utils.parse_timespan(model['runtime']))
        for spec in manifest['specifications']
        for module in spec['modules']
        for model in module['models']
            if model['size'] == 'small'
            and tla_utils.is_state_count_valid(model)
            and (
                'distinctStates' not in model
                or 'totalStates' not in model
                or 'stateDepth' not in model
            )
            # This model is nondeterministic due to use of the Random module
            and model['path'] != 'specifications/SpanningTree/SpanTreeRandom.cfg'
            # This model generates the same distinct states but order varies
            and model['path'] != 'specifications/ewd998/EWD998ChanTrace.cfg'
            and model['path'] not in skip_models
            and (only_models == [] or model['path'] in only_models)
    ],
    key = lambda m: m[2],
    reverse=True
)

for path in skip_models:
    logging.info(f'Skipping {path}')

for module, model, _ in small_models:
    success = check_model(module, model)
    if not success:
        exit(1)
    tla_utils.write_json(manifest, manifest_path)

exit(0)

