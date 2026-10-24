#!/bin/sh
# Run from any working directory. Install dependencies as in README.md first.
set -eu
bfgs_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$bfgs_root"
bfgs_python=${BFGS_PYTHON:-python3}
case "${1:-}" in
  '') bfgs_python_checks=yes; bfgs_lean_checks=yes ;;
  --python-only) bfgs_python_checks=yes; bfgs_lean_checks=no ;;
  --lean-only) bfgs_python_checks=no; bfgs_lean_checks=yes ;;
  *) echo 'Usage: scripts/check.sh [--python-only|--lean-only]' >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo 'Only one option is supported.' >&2
  exit 2
fi
if [ "$bfgs_python_checks" = yes ]; then
  "$bfgs_python" verification/verify.py
  # A complete check must execute the optional suites, not silently skip them.
  "$bfgs_python" -c 'import sympy, nbformat, nbclient, IPython, latex2mathml, mistune, pygments'
  "$bfgs_python" verification/build_notebook.py
  "$bfgs_python" -m unittest discover -s verification -p 'test_*.py' -v
fi
if [ "$bfgs_lean_checks" = yes ]; then
  lake build BFGS --wfail
  "$bfgs_python" verification/check_lean.py --incremental
fi
echo 'All requested checks passed.'
