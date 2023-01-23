# Checks to ensure all files in manifest.json exist, and that all .tla and
# .cfg files in repo are recorded in manifest.json

import json
from os.path import normpath
import glob

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

module_lists = [spec["modules"] for spec in manifest["specifications"]]
modules = [module for module_list in module_lists for module in module_list]
model_lists = [module["models"] for module in modules]

# All paths in the manifest
tla_mf_paths = set([normpath(module["path"]) for module in modules])
cfg_mf_paths = set([normpath(model["path"]) for model_list in model_lists for model in model_list])

# All paths on the filesystem
tla_fs_paths = set([normpath(path) for path in glob.glob(f"./specifications/**/*.tla", recursive=True)])
cfg_fs_paths = set([normpath(path) for path in glob.glob(f"./specifications/**/*.cfg", recursive=True)])

success = True
if tla_mf_paths != tla_fs_paths:
    success = False
    print('.tla files not recorded in manifest:\n' + '\n'.join(tla_fs_paths - tla_mf_paths))
    print('Manifest .tla files not found in specifications dir:\n' + '\n'.join(tla_mf_paths - tla_fs_paths))
if cfg_mf_paths != tla_fs_paths:
    success = False
    print('.cfg files not recorded in manifest:\n' + '\n'.join(cfg_fs_paths - cfg_mf_paths))
    print('Manifest .cfg files not found in specifications dir:\n' + '\n'.join(cfg_mf_paths - cfg_fs_paths))

exit(0 if success else 1)

