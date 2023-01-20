import json
from jsonschema import validate

schema_file = open('.github/workflows/scripts/manifest-schema.json', 'rt')
manifest_file = open('manifest.json', 'rt')
schema = json.load(schema_file)
manifest = json.load(manifest_file)
result = validate(instance=manifest, schema=schema)
if None == result:
    exit(0)
else:
    print(result)
    exit(1)

