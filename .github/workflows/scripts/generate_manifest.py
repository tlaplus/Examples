# Generates a best-effort manifest.json

from check_manifest_features import get_module_features, get_model_features
import json
import os
from os.path import basename, dirname, join, normpath, splitext
import glob

# Generate new manifest drawing info from files in specifications dir

def get_tla_files(dir):
    return [normpath(path) for path in glob.glob(f'{dir.path}/**/*.tla', recursive=True)]

def get_cfg_files(tla_path):
    """Assume a .cfg file in the same directory as the .tla file and with the
    same name is a model of that .tla file; also assume this of any .cfg
    files where the .tla file name is only a prefix of the .cfg file name,
    unless there are other .tla file names in the directory that exactly
    match the .cfg file name.
    """
    parent_dir = dirname(tla_path)
    module_name, _ = splitext(basename(tla_path))
    other_module_names = set(filter(
        lambda other_module_name: other_module_name != module_name,
        [splitext(basename(path))[0] for path in glob.glob(f'{join(parent_dir, module_name)}*.tla')]
    ))
    return [
        normpath(path) for path in glob.glob(f'{join(parent_dir, module_name)}*.cfg')
        if splitext(basename(path))[0] not in other_module_names
    ]

new_manifest = {
    'specifications': [
        {
            'path': normpath(dir.path),
            'title': dir.name,
            'description': '',
            'source': '',
            'authors': [],
            'tags': [],
            'modules': [
                {
                    'path': tla_path,
                    'communityDependencies': [],
                    'tlaLanguageVersion': 2,
                    'features': get_module_features(tla_path),
                    'models': [
                        {
                            'path': cfg_path,
                            'runtime': 'unknown',
                            'size': 'unknown',
                            'features': list(get_model_features(cfg_path)),
                            'result': 'unknown'
                        }
                        for cfg_path in sorted(get_cfg_files(tla_path))
                    ]
                }
                for tla_path in sorted(get_tla_files(dir))
            ]
        }
        for dir in sorted(
            os.scandir('specifications'), key=lambda d: d.name
        ) if dir.is_dir() and any(get_tla_files(dir))
    ]
}

# Integrate human-readable info from existing manifest

def find_corresponding_spec(old_spec, new_manifest):
    old_modules = old_spec['modules']
    old_module_paths = set([normpath(module['path']) for module in old_modules])
    return list(filter(
        lambda new_spec: any(
            [old_module_path.startswith(new_spec['path']) for old_module_path in old_module_paths]
        ),
        new_manifest['specifications']
    ))[0]

def integrate_spec_info(old_spec, new_spec):
    fields = ['title', 'description', 'source', 'authors', 'tags']
    for field in fields:
        new_spec[field] = old_spec[field]

def find_corresponding_module(old_module, new_spec):
    return [
        module for module in new_spec['modules']
        if normpath(module['path']) == normpath(old_module['path'])
    ][0]

def integrate_module_info(old_module, new_module):
    fields = ['communityDependencies', 'tlaLanguageVersion']
    for field in fields:
        new_module[field] = old_module[field]

def find_corresponding_model(old_model, new_module):
    return [
        model for model in new_module['models']
        if normpath(model['path']) == normpath(old_model['path'])
    ][0]

def integrate_model_info(old_model, new_model):
    fields = ['runtime', 'size', 'result']
    for field in fields:
        new_model[field] = old_model[field]

old_manifest = None
with open('manifest.json', 'r') as old_manifest_file:
    old_manifest = json.load(old_manifest_file)

for old_spec in old_manifest['specifications']:
    new_spec = find_corresponding_spec(old_spec, new_manifest)
    integrate_spec_info(old_spec, new_spec)
    for old_module in old_spec['modules']:
        new_module = find_corresponding_module(old_module, new_spec)
        integrate_module_info(old_module, new_module)
        for old_model in old_module['models']:
            new_model = find_corresponding_model(old_model, new_module)
            integrate_model_info(old_model, new_model)

# Writes generated manifest to file

with open('manifest.json', 'w') as new_manifest_file:
    json.dump(new_manifest, new_manifest_file, indent=2, ensure_ascii=False)
