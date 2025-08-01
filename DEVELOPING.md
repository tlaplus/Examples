# Overview

This document covers three topics:
1. The role of each CI validation script, how they work, and how to run them locally
1. Tips for consuming this repo as a test corpus for your own TLA⁺ tooling
1. Advice for maintaining & extending the CI validation scripts

## The Scripts

All scripts live in the [`.github/scripts`](.github/scripts) directory.
Here is a brief overview of each script in the order they are run in [the CI](.github/workflows/CI.yml):
1. [`check_manifest_schema.py`](.github/scripts/check_manifest_schema.py): this uses the [jsonschema](https://pypi.org/project/jsonschema/) python package to validate the contents of the `manifest.json` files against their schema, [`manifest-schema.json`](manifest-schema.json).
1. [`check_manifest_files.py`](.github/scripts/check_manifest_files.py): this ensures the modules & models recorded in each `manifest.json` concord with the set of modules & models found under the [`specifications`](specifications) directory, while also respecting the exclusion of any specs in the [`.ciignore`](.ciignore) file.
1. [`check_manifest_features.py`](.github/scripts/check_manifest_features.py`): this uses the [tree-sitter-tlaplus](https://pypi.org/project/tree-sitter-tlaplus/) python package to run queries on all the `.tla` files and ensure their features (`proof`, `pluscal`, `action composition`) are correctly recorded in each `manifest.json`; it also does best-effort regex parsing of all `.cfg` files to ensure their features (`view`, `alias`, etc.) are similarly correctly recorded.
1. [`check_markdown_table.py`](.github/scripts/check_markdown_table.py): this uses the [mistletoe](https://pypi.org/project/mistletoe/) markdown parser python package to parse [`README.md`](README.md), extract the spec table, then validate its format & contents against each `manifest.json`; before this script was developed the table tended to diverge wildly from the actual content of this repo.
1. [`unicode_conversion.py`](.github/scripts/unicode_conversion.py): this script uses [tlauc](https://github.com/tlaplus-community/tlauc) to convert each spec into its Unicode form to ensure TLA⁺ tooling functions identically on ASCII & Unicode specs.
   The CI spawns separate runs with and without conversion of specs to Unicode.
1. [`unicode_number_set_shim.py`](.github/scripts/unicode_number_set_shim.py): since Unicode adoption is not yet fully ratified, Unicode definitions like `ℕ`, `ℤ`, and `ℝ` (as synonyms for `Nat`, `Int`, and `Real` respectively) are not yet included in the standard modules.
   This script works around that by using the [tree-sitter-tlaplus](https://pypi.org/project/tree-sitter-tlaplus/) python package to rewrite all imports of the `Naturals`, `Integers`, and `Reals` modules to import shim modules instead that define `ℕ`, `ℤ`, and `ℝ`.
   Once TLA⁺ fully adopts Unicode this (quite hackish) script will no longer be necessary.
1. [`translate_pluscal.py`](.github/scripts/translate_pluscal.py): this script runs the PlusCal translator on all modules containing PlusCal, to ensure their PlusCal syntax is valid.
1. [`parse_modules.py`](.github/scripts/parse_modules.py): this script runs the SANY parser against all `.tla` files in the repository to ensure they are syntactically & semantically valid.
   This can get quite complicated as many modules import specs defined in Apalache, TLAPM, or the community modules.
1. [`check_small_models.py`](.github/scripts/check_small_models.py): this script runs TLC or Apalache to completion against all models marked as "small", which means they should complete within 30 seconds.
   The script ensures the models don't crash and that their result is as expected, either success or a specific type of failure.
   If applicable, the script also checks the size of the state graph against the values recorded in `manifest.json`.
1. [`smoke_test_large_models.py`](.github/scripts/smoke_test_large_models.py): not all models in this repository can be run to completion within 30 seconds, so this script runs medium & large models for five seconds before terminating their process - just to ensure they basically function and don't immediately crash.
1. [`check_proofs.py`](.github/scripts/check_proofs.py): this script runs TLAPM against all modules that contain formal proofs, to ensure the proofs are valid.

There are also a number of utility scripts:
1. [`generate_manifest.py`](.github/scripts/generate_manifest.py): this can be run by users to automatically generate a new `manifest.json` file for their specs.
   It uses the [tree-sitter-tlaplus](https://pypi.org/project/tree-sitter-tlaplus/) python package to find all required tags and features.
1. [`tla_utils.py`](.github/scripts/tla_utils.py): not a script by itself, but contains common functions used by all the other scripts.
1. [`record_model_state_space.py`](.github/scripts/record_model_state_space.py): this script runs all small models that lack state space info, extracts their state space info, and records it in the relevant `manifest.json` file; useful if a large number of specs need to have this info recorded in a batch.
1. [`format_markdown_table.py`](.github/scripts/format_markdown_table.py): this script is intended for use by developers to script formatting updates to the markdown table (add columns, reorder columns, etc.) to avoid the tedium of having to do this by hand.

### Running the Scripts

Here is how to execute these scripts on your local machine, as they would be executed in a CI run; first, download dependencies to the `deps` directory on Linux & macOS:
```sh
./.github/scripts/linux-setup.sh .github/scripts deps true
```
or Windows:
```sh
.\.github\scripts\windows-setup.sh .github\scripts deps true
```
Activate your Python virtual environment on Linux & macOS:
```sh
source ./bin/activate
```
or Windows:
```sh
.\Scripts\activate.bat
```
Execute your desired scripts as follows; they are provided in individual code blocks for easy copy & paste.
On Windows you might need to use `\` instead of `/` for path separation, but depending on your terminal these snippets could work as-is.
Scripts will output a descriptive error message and nonzero exit code on failure.
Most scripts accept `--skip` and `--only` parameters to skip running on specific files or only run on specific files, which is helpful for quickly testing your changes against the longer-running scripts like `check_small_models.py`.
Many scripts also accept the `--verbose` flag which will output the full command-line arguments and output of any tools they run.
```sh
python .github/scripts/check_manifest_schema.py --schema_path manifest-schema.json
```
```sh
python .github/scripts/check_manifest_files.py --ci_ignore_path .ciignore
```
```sh
python .github/scripts/check_manifest_features.py --examples_root .
```
```sh
python .github/scripts/check_markdown_table.py --readme_path README.md
```
**WARNING:** the `unicode_conversion.py`, `unicode_number_set_shim.py`, and `translate_pluscal.py` scripts make large numbers of changes to files in your local repository, so be sure to run them on a clean branch where your own changes can't be clobbered and you can easily revert with `git reset --hard HEAD`.
```sh
python .github/scripts/unicode_conversion.py --tlauc_path deps/tlauc/tlauc --examples_root .
```
Delete all the shim files generated by `unicode_number_set_shim.py` with `find . -iname "*_UnicodeShim.tla" -delete`.
```sh
python .github/scripts/unicode_number_set_shim.py --examples_root .
```
```sh
python .github/scripts/translate_pluscal.py --tools_jar_path deps/tools/tla2tools.jar --examples_root .
```
```sh
python .github/scripts/parse_modules.py --tools_jar_path deps/tools/tla2tools.jar --apalache_path deps/apalache --tlapm_lib_path deps/tlapm/library --community_modules_jar_path deps/community/modules.jar --examples_root .
```
```sh
python .github/scripts/check_small_models.py --tools_jar_path deps/tools/tla2tools.jar --apalache_path deps/apalache --tlapm_lib_path deps/tlapm/library --community_modules_jar_path deps/community/modules.jar --examples_root .
```
```sh
python .github/scripts/smoke_test_large_models.py --tools_jar_path deps/tools/tla2tools.jar --apalache_path deps/apalache --tlapm_lib_path deps/tlapm/library --community_modules_jar_path deps/community/modules.jar --examples_root .
```
Note: `check_proofs.py` does not run on Windows.
```sh
python .github/scripts/check_proofs.py --tlapm_path deps/tlapm --examples_root .
```
You can also run the non-CI utility scripts as follows:
```sh
python .github/scripts/generate_manifest.py --ci_ignore_path .ciignore
```
```sh
python .github/scripts/record_model_state_space.py --tools_jar_path deps/tools/tla2tools.jar --tlapm_lib_path deps/tlapm/library --community_modules_jar_path deps/community/modules.jar --examples_root .
```
Exit your Python virtual environment by running `deactivate`.

## Consuming the Examples

In addition to its teaching value, this repository is an excellent source of real-world nontrivial TLA⁺ specs ideal for use in tests.
Several TLA⁺ tools already import this repository for testing purposes in their CI:
- The [TLA⁺ Java Tools](https://github.com/tlaplus/tlaplus)
- The [TLA⁺ Proof Manager](https://github.com/tlaplus/tlapm)
- The [TLA⁺ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus)
- The [TLA⁺ Unicode converter](https://github.com/tlaplus-community/tlauc)

Here is some advice for consuming this repo in your own project:
- The most important files to consider are the `manifest.json` metadata files; almost all languages have binding libraries for JSON, and you can use it to get a list of spec/module paths along with various features to filter on.
- Consider using a [release of this repo](https://github.com/tlaplus/Examples/releases) instead of just pulling from the head of the main branch, since the manifest format is occasionally changed and these changes are captured in minor version bumps.
  Releases with a patch version bump only contain new specs or other non-breaking changes.
- If using this repo to test your tool requires additional metadata or scripting that could be commonly useful, consider [opening an issue](https://github.com/tlaplus/Examples/issues) explaining your use case; we are always interested in supporting new TLA⁺ tooling development!

## Maintaining & Extending the Scripts

The scripts are almost all written in Python, so updating the scripts will require Python knowledge.
The scripts do not make use of many fancy language features (other than list comprehensions) so relative newcomers should find them accessible.
There are a few common occasions where it is necessary to update or extend the scripts:
1. **Run another tool or validate a new property**: if a TLA⁺ tool becomes prominent enough, it could be added to the set of tools run in the CI of this repo.
   This would entail writing a new script and adding it to the CI, along with updating the install scripts to pull the new tool.
   Every script follows the same basic format: parse command-line arguments, get a list of applicable files to check from the manifest, then run the tool against the files.
   Most of this can be copied & pasted from existing scripts, with some modifications.
1. **Expose a new feature flag**: while we try to make the manifest data as independent from any specific TLA⁺ tool backend as possible, there are cases where a specific feature flag or command-line argument must be used in only certain cases.
   For example, at one point TLC required the `-Dtlc2.tool.impl.Tool.cdot=true` flag to be passed to it when processing specs using the `\cdot` action composition operator; this was solved by adding another module-level `action composition` feature tag to the manifest, then passing the feature flag to TLC when that feature tag was present (see [this PR](https://github.com/tlaplus/Examples/pull/156)).
   This preserved the independence of the manifest from a specific tooling backend.
   Future developers should endeavor to maintain this independence and, to the extent practical, avoid adding functionality like directly encoding command-line arguments in the manifest.
1. **Follow tree-sitter API updates**: the scripts make heavy use of [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus) for querying spec features.
   The grammar is now largely stable with only occasional bugfixes, so the scripts should not have to update the version they use very often (which is encoded in the [`requirements.txt`](.github/scripts/requirements.txt) file).
   Still, there may come a time when a tree-sitter-tlaplus bugfix is needed *and* the grammar has updated its version of the underlying [`tree-sitter`](https://pypi.org/project/tree-sitter/) package, meaning the tree-sitter python bindings change or break.
   This will likely be a difficult fix for those unfamiliar with the tree-sitter API; [this PR](https://github.com/tlaplus/Examples/pull/156) included an update to changed tree-sitter query bindings, as an example.

