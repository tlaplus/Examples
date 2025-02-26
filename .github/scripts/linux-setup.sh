# This script downloads all necessary dependencies to run the CI on Linux.
# It can also be run locally, as long as you have the following dependencies:
#  - python 3.1x
#  - java
#  - C & C++ compiler (aliased to cc and cpp commands respectively)
#  - wget
#  - tar
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
  cc --version
  cpp --version
  # Install python packages
  if $USE_VENV; then
    python -m venv .
    source bin/activate
    pip install -r "$SCRIPT_DIR/requirements.txt"
    deactivate
  else
    pip install -r "$SCRIPT_DIR/requirements.txt"
  fi
  kernel=$(uname -s)
  # Put all dependencies in their own directory to ensure they aren't included implicitly
  mkdir -p "$DEPS_DIR"
  # Get TLA⁺ tools
  mkdir -p "$DEPS_DIR/tools"
  wget -nv http://nightly.tlapl.us/dist/tla2tools.jar -P "$DEPS_DIR/tools"
  # Get Apalache
  wget -nv https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -O /tmp/apalache.tgz
  tar -xzf /tmp/apalache.tgz --directory "$DEPS_DIR"
  # Get TLA⁺ community modules
  mkdir -p "$DEPS_DIR/community"
  wget -nv https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar \
        -O "$DEPS_DIR/community/modules.jar"
  # Get TLAPS modules
  wget -nv https://github.com/tlaplus/tlapm/archive/main.tar.gz -O /tmp/tlapm.tar.gz
  tar -xzf /tmp/tlapm.tar.gz --directory "$DEPS_DIR"
  mv "$DEPS_DIR/tlapm-main" "$DEPS_DIR/tlapm"
  # Install TLAPS
  if [ "$kernel" == "Linux" ]; then
    TLAPM_BIN_TYPE=x86_64-linux-gnu
  elif [ "$kernel" == "Darwin" ]; then
    TLAPM_BIN_TYPE=arm64-darwin
  else
    echo "Unknown OS: $kernel"
    exit 1
  fi
  wget -nv "https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-$TLAPM_BIN_TYPE.tar.gz" -O /tmp/tlapm.tar.gz
  tar -xzf /tmp/tlapm.tar.gz --directory "$DEPS_DIR"
  # Get TLAUC
  mkdir -p "$DEPS_DIR/tlauc"
  if [ "$kernel" == "Linux" ]; then
    TLAUC_OS_STR="linux"
  elif [ "$kernel" == "Darwin" ]; then
    TLAUC_OS_STR="macos"
  else
    echo "Unknown OS: $kernel"
    exit 1
  fi
  wget -nv "https://github.com/tlaplus-community/tlauc/releases/latest/download/tlauc-$TLAUC_OS_STR.tar.gz" -O /tmp/tlauc.tar.gz
  tar -xzf /tmp/tlauc.tar.gz --directory "$DEPS_DIR/tlauc"
}

main "$@"

