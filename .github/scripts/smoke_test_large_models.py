"""
Smoke-test all models not marked as size "small" in the manifest. This
entails running them for five seconds to ensure they can actually start
and work with the spec they're supposed to be modeling.
"""

from argparse import ArgumentParser
import logging
import os
from os.path import dirname, join, normpath
import tla_utils

parser = ArgumentParser(description='Smoke-tests all larger TLA+ models in the tlaplus/examples repo using TLC.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
args = parser.parse_args()

tools_jar_path = normpath(args.tools_jar_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root_path = dirname(manifest_path)

def check_model(module_path, model):
    module_path = normpath(join(examples_root_path, module_path))
    model_path = normpath(join(examples_root_path, model['path']))
    logging.info(model_path)
    tlc, hit_timeout = tla_utils.check_model(
        tools_jar_path,
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
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

manifest = tla_utils.load_json(manifest_path)

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

