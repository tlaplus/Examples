"""
Checks to ensure all files in manifest.json exist, that all .tla and .cfg
files in repo are recorded in manifest.json (except for those in .ciignore),
and that no files are present twice in the manifest. Also checks to ensure
no files in .ciignore are in the manifest.json.
"""

from collections import Counter
import json
from os.path import normpath
import glob
import tla_utils

manifest = tla_utils.load_manifest()

module_lists = [spec["modules"] for spec in manifest["specifications"]]
modules = [module for module_list in module_lists for module in module_list]
model_lists = [module["models"] for module in modules]

# Get all .tla and .cfg paths from the manifest
tla_mf_paths_cnt = Counter([normpath(module["path"]) for module in modules])
tla_mf_paths = set(tla_mf_paths_cnt)
cfg_mf_paths_cnt = Counter([normpath(model["path"]) for model_list in model_lists for model in model_list])
cfg_mf_paths = set(cfg_mf_paths_cnt)

# Get ignored directories
ignored_dirs = tla_utils.get_ignored_dirs()
ignore = lambda path : tla_utils.ignore(ignored_dirs, path)

# Get paths of all non-ignored .tla and .cfg files in the specifications dir
tla_fs_paths = set([
    normpath(path) for path in glob.glob(f"./specifications/**/*.tla", recursive=True)
    if '_TTrace_' not in path and not ignore(path)
])
cfg_fs_paths = set([
    normpath(path) for path in glob.glob(f"./specifications/**/*.cfg", recursive=True)
    if not ignore(path)
])

success = True

# Check whether manifest includes any ignored paths
ignored_tla_in_manifest = set(filter(ignore, tla_mf_paths))
ignored_cfg_in_manifest = set(filter(ignore, cfg_mf_paths))
if any(ignored_tla_in_manifest):
    success = False
    print('Ignored .tla paths present in manifest:\n' + '\n'.join(ignored_tla_in_manifest))
    tla_mf_paths = tla_mf_paths - ignored_tla_in_manifest
if any(ignored_cfg_in_manifest):
    success = False
    print('Ignored .cfg paths present in manifest:\n' + '\n'.join(ignored_cfg_in_manifest))
    cfg_mf_paths = cfg_mf_paths - ignored_cfg_in_manifest

# Check for duplicate paths in manifest
duplicate_tla_paths = [k for k, v in tla_mf_paths_cnt.items() if v > 1]
duplicate_cfg_paths = [k for k, v in cfg_mf_paths_cnt.items() if v > 1]
if any(duplicate_tla_paths):
    success = False
    print('.tla file paths duplicated in manifest:\n' + '\n'.join(duplicate_tla_paths))
if any(duplicate_cfg_paths):
    success = False
    print('.cfg file paths duplicated in manifest:\n' + '\n'.join(duplicate_cfg_paths))

# Check paths in manifest match paths on filesystem
if tla_mf_paths < tla_fs_paths:
    success = False
    print('.tla files not recorded in manifest:\n' + '\n'.join(tla_fs_paths - tla_mf_paths))
if tla_fs_paths < tla_mf_paths:
    success = False
    print('Manifest .tla files not found in specifications dir:\n' + '\n'.join(tla_mf_paths - tla_fs_paths))
if cfg_mf_paths < cfg_fs_paths:
    success = False
    print('.cfg files not recorded in manifest:\n' + '\n'.join(cfg_fs_paths - cfg_mf_paths))
if cfg_fs_paths < cfg_mf_paths:
    success = False
    print('Manifest .cfg files not found in specifications dir:\n' + '\n'.join(cfg_mf_paths - cfg_fs_paths))

exit(0 if success else 1)

