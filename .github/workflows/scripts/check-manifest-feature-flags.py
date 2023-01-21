import json
from tree_sitter import Language, Parser

Language.build_library(
  'build/tree-sitter-languages.so',
  ['tree-sitter-tlaplus']
)

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

TLAPLUS_LANGUAGE = Language('build/tree-sitter-languages.so', 'tlaplus')
parser = Parser()
parser.set_language(TLAPLUS_LANGUAGE)

query = TLAPLUS_LANGUAGE.query(
    '(pcal_algorithm_start) @pluscal'
    + '[(terminal_proof) (non_terminal_proof)] @proof'
)

success = True
for spec in manifest['specifications']:
    for module in spec['modules']:
        module_text = None
        with open(module['path'], 'rb') as module_file:
            module_text = module_file.read()
        tree = parser.parse(module_text)
        if tree.root_node.has_error:
            success = False
            print(f'Module {module["path"]} contains syntax errors')
        captures = query.captures(tree.root_node)
        expected_features = set([name for _, name in captures])
        actual_features = set(module['features'])
        if expected_features != actual_features:
            success = False
            print(
                f'Module {module["path"]} has incorrect features in manifest; '
                + f'expected {list(expected_features)}, actual {list(actual_features)}'
            )

exit(0 if success else 1)

