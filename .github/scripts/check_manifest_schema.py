"""
Checks to ensure manifest.json in each specifications/ subdirectory is valid
according to schema; this can also be done manually at
https://www.jsonschemavalidator.net/

Learn about the JSON schema format at
https://json-schema.org/understanding-json-schema/
"""

from argparse import ArgumentParser
from jsonschema import validate
from jsonschema.exceptions import ValidationError
from os.path import normpath, dirname, join
from sys import stderr
import tla_utils

parser = ArgumentParser(description='Checks tlaplus/examples manifest.json files against JSON schema file.')
parser.add_argument('--schema_path', help='Path to the tlaplus/examples manifest-schema.json file', required=False, default='manifest-schema.json')
args = parser.parse_args()

examples_root = dirname(args.schema_path)
schema = tla_utils.load_json(normpath(args.schema_path))
failures = []
for path, manifest in tla_utils.load_all_manifests(examples_root):
    manifest_path = join(path, 'manifest.json')
    try:
        validate(instance=manifest, schema=schema)
    except ValidationError as error:
        print(f'FAILURE: schema NOT matched by {manifest_path}', file=stderr)
        failures.append((manifest_path, error))
    else:
        print(f'SUCCESS: schema matched by {manifest_path}')

for (manifest_path, manifest_error) in failures:
    print(f'\nSchema failure in {manifest_path}:\n{manifest_error}\n', file=stderr)

exit(1 if any(failures) else 0)

