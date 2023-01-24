import json
from tree_sitter import Language, Parser

Language.build_library(
  'build/tree-sitter-languages.so',
  ['tree-sitter-tlaplus']
)

TLAPLUS_LANGUAGE = Language('build/tree-sitter-languages.so', 'tlaplus')
parser = Parser()
parser.set_language(TLAPLUS_LANGUAGE)

query = TLAPLUS_LANGUAGE.query(
    '(pcal_algorithm_start) @pluscal'
    + '[(terminal_proof) (non_terminal_proof)] @proof'
)

def parse_module(path):
    module_text = None
    with open(path, 'rb') as module_file:
        module_text = module_file.read()
    tree = parser.parse(module_text)
    return (tree, tree.root_node.has_error)

def get_tree_features(tree):
    return set([name for _, name in query.captures(tree.root_node)])

def get_module_features(path):
    tree, _ = parse_module(path)
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

if __name__ == '__main__':
    manifest = None
    with open('manifest.json', 'rt') as manifest_file:
        manifest = json.load(manifest_file)

    success = True
    for spec in manifest['specifications']:
        for module in spec['modules']:
            tree, parse_err = parse_module(module['path'])
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

