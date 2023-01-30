"""
Smoke-test all models not marked as size "small" in the manifest. This
entails running them for five seconds to ensure they can actually start
and work with the spec they're supposed to be modeling.
"""

import json
import logging
import tla_utils

def check_model(module_path, model_path, config):
    tlc, timeout = tla_utils.check_model(module_path, model_path, config, 5, 10)
    if timeout:
        # Return True here; see https://github.com/tlaplus/tlaplus/issues/788
        logging.info(f'{model_path} hit hard timeout')
        return True
    logging.info(model_path)
    if 0 != tlc.returncode:
        logging.error(f'Model {model_path} expected error code 0 but got {tlc.returncode}')
        logging.error(tlc.stdout.decode('utf-8'))
        return False
    return True

logging.basicConfig(level=logging.INFO)

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

skip_models = [
    # SimKnuthYao requires certain number of states to have been generated
    # before termination or else it fails. This makes it not amenable to
    # smoke testing.
    'specifications/KnuthYao/SimKnuthYao.cfg',
    # These should all work; it is a bug that they do not
    'specifications/SpecifyingSystems/AdvancedExamples/MCInnerSerial.cfg',
    'specifications/ewd426/SimTokenRing.cfg',
    'specifications/ewd840/EWD840_json.cfg',
    'specifications/ewd998/AsyncTerminationDetection_proof.cfg',
    'specifications/ewd998/SmokeEWD998.cfg'
]

large_models = [
    (module['path'], model['path'], model['config'])
    for spec in manifest['specifications']
    for module in spec['modules']
    for model in module['models']
        if model['size'] != 'small'
        and model['path'] not in skip_models
]

success = all([check_model(*model) for model in large_models])
exit(0 if success else 1)

