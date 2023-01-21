# Checks to ensure all files in manifest.json exist, and that all .tla and
# .cfg files in repo are recorded in manifest.json

import json
from os.path import exists, normpath
import glob

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

module_lists = [spec["modules"] for spec in manifest["specifications"]]
modules = [module for module_list in module_lists for module in module_list]
module_paths = set([normpath(module["path"]) for module in modules])
model_lists = [module["models"] for module in modules]
model_paths = set([normpath(model["path"]) for model_list in model_lists for model in model_list])

missing_module_files = [path for path in module_paths if not exists(path)]
missing_model_files = [path for path in model_paths if not exists(path)]

any_missing = False
if any(missing_module_files):
    any_missing = True
    print('Module files not found:\n' + '\n'.join(missing_module_files))
if any(missing_model_files):
    any_missing = True
    print('Model files not found:\n' + '\n'.join(missing_model_files))

tla_files = set([normpath(path) for path in glob.glob(f"./specifications/**/*.tla", recursive=True)])
cfg_files = set([normpath(path) for path in glob.glob(f"./specifications/**/*.cfg", recursive=True)])
missing_module_paths = tla_files - module_paths
missing_model_paths = cfg_files - model_paths

if any(missing_module_paths):
    any_missing = True
    print('Module files not included in manifest:\n' + '\n'.join(missing_module_paths))
if any(missing_model_paths):
    any_missing = True
    print('Model files not included in manifest:\n' + '\n'.join(missing_model_paths))

exit(1 if any_missing else 0)

