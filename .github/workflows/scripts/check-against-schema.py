# Checks to ensure manifest.json is valid according to schema

import json
from jsonschema import validate

schema = None
with open('.github/workflows/scripts/manifest-schema.json', 'rt') as schema_file:
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

