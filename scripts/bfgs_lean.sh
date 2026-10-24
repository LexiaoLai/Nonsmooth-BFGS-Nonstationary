#!/bin/sh
# Use installed compiled packages without asking Lake to update dependencies.
set -eu
bfgs_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
bfgs_path="$bfgs_root/.lake/build/lib/lean:$bfgs_root"
for bfgs_pkg in "$bfgs_root"/.lake/packages/*; do
  if [ -d "$bfgs_pkg/.lake/build/lib/lean" ]; then
    bfgs_path="$bfgs_path:$bfgs_pkg/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$bfgs_path"
cd "$bfgs_root"
exec lean "$@"
