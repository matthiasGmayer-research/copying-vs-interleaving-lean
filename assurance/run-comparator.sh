#!/bin/bash
# Run comparator on Challenge/Solution (from this directory). Tools: COMPARATOR (binary), COMPARATOR_LANDRUN,
# COMPARATOR_LEAN4EXPORT (and COMPARATOR_NANODA when enable_nanoda is set in the config) — see README.md.
# Optional first argument: the config file (default config.json).
set -euo pipefail
cd "$(dirname "$0")"
TOOLCHAIN=$(sed 's|leanprover/lean4:|leanprover--lean4---|' lean-toolchain)
export PATH="$HOME/.elan/toolchains/$TOOLCHAIN/bin:$PATH"   # the toolchain's own lake/lean (elan shims are not executable in the sandbox)
: "${COMPARATOR:=$HOME/tools/comparator/.lake/build/bin/comparator}"
: "${COMPARATOR_LANDRUN:=$HOME/tools/landrun/landrun}"
: "${COMPARATOR_LEAN4EXPORT:=$HOME/tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export}"
export COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT
[ -n "${COMPARATOR_NANODA:-}" ] && export COMPARATOR_NANODA
echo "comparator: $COMPARATOR"; echo "landrun: $COMPARATOR_LANDRUN"; echo "lean4export: $COMPARATOR_LEAN4EXPORT"; lean --version
exec lake env "$COMPARATOR" "${1:-config.json}"
