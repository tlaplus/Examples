import glob
import json
from os.path import basename, dirname, splitext
from tree_sitter import Language, Parser

Language.build_library(
  'build/tree-sitter-languages.so',
  ['tree-sitter-tlaplus']
)

TLAPLUS_LANGUAGE = Language('build/tree-sitter-languages.so', 'tlaplus')
parser = Parser()
parser.set_language(TLAPLUS_LANGUAGE)

feature_query = TLAPLUS_LANGUAGE.query(
    '(pcal_algorithm_start) @pluscal'
    + '[(terminal_proof) (non_terminal_proof)] @proof'
)

def parse_module(path):
    module_text = None
    with open(path, 'rb') as module_file:
        module_text = module_file.read()
    tree = parser.parse(module_text)
    return (tree, module_text, tree.root_node.has_error)

def get_tree_features(tree):
    return set([name for _, name in feature_query.captures(tree.root_node)])

def get_module_features(path):
    tree, _, _ = parse_module(path)
    return list(get_tree_features(tree))

model_features = {
    'PROPERTY': 'liveness',
    'PROPERTIES': 'liveness',
    'SYMMETRY': 'symmetry',
    'ALIAS': 'alias',
    'VIEW': 'view',
    'CONSTRAINT': 'state constraint',
    'CONSTRAINTS': 'state constraint',
}

def get_model_features(path):
    """
    This will be a best-effort text search until a tree-sitter grammar is
    created for .cfg files.
    """
    features = []
    model_text = None
    with open(path, 'rt') as model_file:
        model_text = model_file.read()
    for line in model_text.split('\n'):
        tokens = line.split()
        if len(tokens) > 0 and tokens[0] in model_features:
            features.append(model_features[tokens[0]])
    return set(features)

import_query = TLAPLUS_LANGUAGE.query(
    '(extends (identifier_ref) @extends)'
    + '(instance (identifier_ref) @instance)'
)

module_name_query = TLAPLUS_LANGUAGE.query(
    '(module name: (identifier) @module_name)'
)

tlc_modules = {
    'Bags',
    'FiniteSets',
    'Integers',
    'Json',
    'Naturals',
    'Randomization',
    'RealTime',
    'Reals',
    'Sequences',
    'TLC',
    'TLCExt',
    'Toolbox'
}

tlaps_modules = {
    'BagsTheorems',
    'FiniteSetTheorems',
    'FunctionTheorems',
    'NaturalsInduction',
    'SequenceTheorems',
    'SequencesExtTheorems',
    'TLAPS',
    'WellFoundedInduction'
}

tlaps_module_overloads = {
    'Bags',
    'FiniteSets',
    'Functions',
    'RealTime',
    'SequencesExt'
}

def get_module_names_in_dir(dir):
    return set([splitext(basename(path))[0] for path in glob.glob(f'{dir}/*.tla')])

def get_community_imports(tree, text, dir, has_proof):
    imports = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in import_query.captures(tree.root_node)
        ]
    )
    modules_in_file = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in module_name_query.captures(tree.root_node)
        ]
    )
    imports = (
        imports
        - modules_in_file
        - tlc_modules
        - tlaps_modules
        - get_module_names_in_dir(dir)
    )
    return imports - tlaps_module_overloads if has_proof else imports

def get_community_module_imports(path):
    tree, text, _ = parse_module(path)
    dir = dirname(path)
    has_proof = 'proof' in get_tree_features(tree)
    return list(get_community_imports(tree, text, dir, has_proof))

if __name__ == '__main__':
    manifest = None
    with open('manifest.json', 'rt') as manifest_file:
        manifest = json.load(manifest_file)

    success = True
    for spec in manifest['specifications']:
        for module in spec['modules']:
            tree, text, parse_err = parse_module(module['path'])
            if parse_err:
                success = False
                print(f'Module {module["path"]} contains syntax errors')
            expected_features = get_tree_features(tree)
            actual_features = set(module['features'])
            if expected_features != actual_features:
                success = False
                print(
                    f'Module {module["path"]} has incorrect features in manifest; '
                    + f'expected {list(expected_features)}, actual {list(actual_features)}'
                )
            expected_imports = get_community_imports(tree, text, dirname(module['path']), 'proof' in expected_features)
            actual_imports = set(module['communityDependencies'])
            if expected_imports != actual_imports:
                success = False
                print(
                    f'Module {module["path"]} has incorrect community dependencies in manifest; '
                    + f'expected {list(expected_imports)}, actual {list(actual_imports)}'
                )
            for model in module['models']:
                expected_features = get_model_features(model['path'])
                actual_features = set(model['features'])
                if expected_features != actual_features:
                    success = False
                    print(
                        f'Model {model["path"]} has incorrect features in manifest; '
                        + f'expected {list(expected_features)}, actual {list(actual_features)}'
                    )

    exit(0 if success else 1)

