# This script downloads all necessary dependencies to run the CI on Windows.
# It can also be run locally, as long as you have the following dependencies:
#  - python 3.1x
#  - java
#  - curl
#  - 7-zip
#
# The script takes the following positional command line parameters:
#  1. Path to this script directory from the current working directory
#  2. Path to the desired dependencies directory
#  3. Boolean true/false; whether to initialize a python virtual env

main() {
  # Validate command line parameters
  if [ $# -ne 3 ]; then
    echo "Usage: $0 <script dir path> <desired dependency dir path> <bool: use python venv>"
    exit 1
  fi
  SCRIPT_DIR="$1"
  DEPS_DIR="$2"
  USE_VENV=$3
  # Print out tool version information
  java --version
  python --version
  pip --version
  # Install python packages
  if $USE_VENV; then
    python -m venv .
    pwsh Scripts/Activate.ps1
    pip install -r "$SCRIPT_DIR/requirements.txt"
    deactivate
  else
    pip install -r "$SCRIPT_DIR/requirements.txt"
  fi
  # Put all dependencies in their own directory to ensure they aren't included implicitly
  mkdir -p "$DEPS_DIR"
  # Get tree-sitter-tlaplus
  curl -L https://github.com/tlaplus-community/tree-sitter-tlaplus/archive/main.zip --output tree-sitter-tlaplus.zip
  7z x tree-sitter-tlaplus.zip
  mv tree-sitter-tlaplus-main "$DEPS_DIR/tree-sitter-tlaplus"
  rm tree-sitter-tlaplus.zip
  # Get TLA⁺ tools
  mkdir -p "$DEPS_DIR/tools"
  curl http://nightly.tlapl.us/dist/tla2tools.jar --output "$DEPS_DIR/tools/tla2tools.jar"
  # Get TLA⁺ community modules
  mkdir -p "$DEPS_DIR/community"
  curl -L https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar --output "$DEPS_DIR/community/modules.jar"
  # Get TLAPS modules
  curl -L https://github.com/tlaplus/tlapm/archive/main.zip --output tlapm.zip
  7z x tlapm.zip
  mv tlapm-main "$DEPS_DIR/tlapm"
  rm tlapm.zip
}

main "$@"

