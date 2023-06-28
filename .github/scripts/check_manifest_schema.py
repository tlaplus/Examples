"""
Checks to ensure manifest.json is valid according to schema; this can also
be done manually at https://www.jsonschemavalidator.net/
Learn about the JSON schema format at
https://json-schema.org/understanding-json-schema/
"""

from argparse import ArgumentParser
from jsonschema import validate
from os.path import normpath
import tla_utils

parser = ArgumentParser(description='Checks tlaplus/examples manifest.json against JSON schema file.')
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--schema_path', help='Path to the tlaplus/examples manifest-schema.json file', required=True)
args = parser.parse_args()

schema = tla_utils.load_json(normpath(args.schema_path))
manifest = tla_utils.load_json(normpath(args.manifest_path))

result = validate(instance=manifest, schema=schema)
if None == result:
    print('SUCCESS: Manifest correctly follows schema')
    exit(0)
else:
    print('ERROR: Manifest does not follow schema')
    print(result)
    exit(1)

