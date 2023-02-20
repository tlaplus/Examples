"""
Smoke-test all models not marked as size "small" in the manifest. This
entails running them for five seconds to ensure they can actually start
and work with the spec they're supposed to be modeling.
"""

import logging
import os
import tla_utils

def check_model(module_path, model):
    model_path = model['path']
    logging.info(model_path)
    tlc, hit_timeout = tla_utils.check_model(
        module_path,
        model_path,
        model['mode'],
        model['config'],
        5
    )
    if hit_timeout:
        return True
    if 0 != tlc.returncode:
        logging.error(f'Model {model_path} expected error code 0 but got {tlc.returncode}')
        logging.error(tlc.stdout.decode('utf-8'))
        return False
    return True

logging.basicConfig(level=logging.INFO)

manifest = tla_utils.load_manifest()

skip_models = [
    # SimKnuthYao requires certain number of states to have been generated
    # before termination or else it fails. This makes it not amenable to
    # smoke testing.
    'specifications/KnuthYao/SimKnuthYao.cfg',
    # SimTokenRing does not work on Windows systems.
] + (['specifications/ewd426/SimTokenRing.cfg'] if os.name == 'nt' else [])

large_models = [
    (module['path'], model)
    for spec in manifest['specifications']
    for module in spec['modules']
    for model in module['models']
        if model['size'] != 'small'
        and model['path'] not in skip_models
]

success = all([check_model(*model) for model in large_models])
exit(0 if success else 1)

