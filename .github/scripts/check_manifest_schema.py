"""
Checks to ensure manifest.json is valid according to schema; this can also
be done manually at https://www.jsonschemavalidator.net/
Learn about the JSON schema format at
https://json-schema.org/understanding-json-schema/
"""

import json
from jsonschema import validate

schema = None
with open('manifest-schema.json', 'rt') as schema_file:
    schema = json.load(schema_file)

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

result = validate(instance=manifest, schema=schema)
if None == result:
    exit(0)
else:
    print(result)
    exit(1)

