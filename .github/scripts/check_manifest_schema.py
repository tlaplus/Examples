"""
Checks to ensure manifest.json is valid according to schema; this can also
be done manually at https://www.jsonschemavalidator.net/
Learn about the JSON schema format at
https://json-schema.org/understanding-json-schema/
"""

import json
from jsonschema import validate
import tla_utils

schema = tla_utils.load_schema()
manifest = tla_utils.load_manifest()

result = validate(instance=manifest, schema=schema)
if None == result:
    exit(0)
else:
    print(result)
    exit(1)

