#!/bin/sh
# Build OpenVAF with auto-detected LLVM version
#
# Usage:
#   ./build.sh                  # Debug build
#   ./build.sh --release        # Release build
#   ./build.sh --test           # Run tests
#   ./build.sh -- <cargo args>  # Pass additional args to cargo

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
VERSION_FILE="$SCRIPT_DIR/.llvm-version"

# Parse our arguments
CARGO_CMD="build"
RELEASE=""
EXTRA_ARGS=""
while [ $# -gt 0 ]; do
    case "$1" in
        --release)
            RELEASE="--release"
            shift
            ;;
        --test)
            CARGO_CMD="test"
            shift
            ;;
        --clippy)
            CARGO_CMD="clippy"
            shift
            ;;
        --)
            shift
            EXTRA_ARGS="$*"
            break
            ;;
        *)
            EXTRA_ARGS="$EXTRA_ARGS $1"
            shift
            ;;
    esac
done

# Check for configuration
if [ ! -f "$VERSION_FILE" ]; then
    echo "Error: Not configured. Run ./configure first."
    echo ""
    echo "Quick start:"
    echo "  ./configure    # Auto-detect LLVM"
    echo "  ./build.sh     # Build"
    exit 1
fi

# Load configuration
. "$VERSION_FILE"

if [ -z "$LLVM_VERSION" ]; then
    echo "Error: Invalid configuration. Run ./configure again."
    exit 1
fi

# Set environment variable for llvm-sys
case "$LLVM_VERSION" in
    18) export LLVM_SYS_181_PREFIX="$LLVM_PREFIX" ;;
    19) export LLVM_SYS_191_PREFIX="$LLVM_PREFIX" ;;
    20) export LLVM_SYS_201_PREFIX="$LLVM_PREFIX" ;;
    21) export LLVM_SYS_211_PREFIX="$LLVM_PREFIX" ;;
    22) export LLVM_SYS_221_PREFIX="$LLVM_PREFIX" ;;
esac

# Add LLVM to PATH if needed
if [ -d "$LLVM_PREFIX/bin" ]; then
    export PATH="$LLVM_PREFIX/bin:$PATH"
fi

echo "Using LLVM $LLVM_VERSION from $LLVM_PREFIX"
echo ""

# Run cargo
# shellcheck disable=SC2086
exec cargo $CARGO_CMD $RELEASE --features "llvm$LLVM_VERSION" $EXTRA_ARGS
