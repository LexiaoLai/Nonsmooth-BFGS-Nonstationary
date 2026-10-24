#!/usr/bin/env python3
"""Compile and axiom-audit the current scalar-quartic BFGS formalization.

Run from any directory. Uses the pinned Lean installation and existing package
cache through scripts/bfgs_lean.sh; never runs Lake or changes dependencies.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "BFGS/Counterexample"
BUILD = ROOT / ".lake/build/lib/lean"
WRAPPER = ROOT / "scripts/bfgs_lean.sh"
PREFIX = "BFGS.Counterexample."
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|sorryAx)\b|"
    r"set_option\s+(?:debug\.skipKernelTC|debug\.skipNativeTC)\s+true"
)
IMPORT = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)", re.M)


def is_current(name: str) -> bool:
    return name in {"BFGS", "BFGS.MainTheorem"} or name.startswith(PREFIX)


def lean_code(text: str) -> str:
    """Mask nested comments and strings, preserving offsets and line numbers."""
    out = list(text)
    index = depth = 0
    quoted = False
    while index < len(text):
        pair = text[index:index + 2]
        count = 1
        mask = True
        if depth:
            if pair == "/-":
                depth += 1
                count = 2
            elif pair == "-/":
                depth -= 1
                count = 2
        elif quoted:
            if text[index] == "\\":
                count = min(2, len(text) - index)
            elif text[index] == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            count = 2
        elif pair == "--":
            end = text.find("\n", index)
            count = (len(text) if end < 0 else end) - index
        elif text[index] == '"':
            quoted = True
        else:
            mask = False
        if mask:
            for offset in range(index, index + count):
                if text[offset] != "\n":
                    out[offset] = " "
        index += count
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def discover() -> tuple[list[str], dict[str, Path], dict[str, list[str]]]:
    """Topological closure of every current module, including reusable imports."""
    sources: dict[str, Path] = {}
    imports: dict[str, list[str]] = {}
    ordered: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise RuntimeError("Cyclic local import at " + name)
        path = ROOT.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.is_file():
            raise RuntimeError("Missing local module: " + name)
        code = lean_code(path.read_text())
        if match := FORBIDDEN.search(code):
            line = code.count("\n", 0, match.start()) + 1
            raise RuntimeError(f"Forbidden proof escape in {path.relative_to(ROOT)}:{line}")
        sources[name] = path
        imports[name] = [item for line in IMPORT.findall(code) for item in line.split()]
        active.add(name)
        for dependency in imports[name]:
            if dependency == "BFGS" or dependency.startswith("BFGS."):
                visit(dependency)
        active.remove(name)
        done.add(name)
        ordered.append(name)

    visit("BFGS")
    all_sources = set((ROOT / "BFGS").rglob("*.lean")) | {ROOT / "BFGS.lean"}
    unused = all_sources - set(sources.values())
    if unused:
        raise RuntimeError("Unimported source modules: " + ", ".join(
            str(path.relative_to(ROOT)) for path in sorted(unused)))
    if "BFGS.MainTheorem" not in sources:
        raise RuntimeError("Missing public MainTheorem module")
    return ordered, sources, imports


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sources_unchanged(original: dict[Path, str]) -> None:
    changed = [str(path.relative_to(ROOT)) for path, old in original.items()
               if not path.is_file() or digest(path) != old]
    current = set((ROOT / "BFGS").rglob("*.lean")) | {ROOT / "BFGS.lean"}
    expected = {path for path in original if path.suffix == ".lean"}
    changed.extend(str(path.relative_to(ROOT)) for path in sorted(current - expected))
    if changed:
        raise RuntimeError("Sources changed during the check; rerun: " + ", ".join(changed))


def olean(name: str) -> Path:
    return BUILD.joinpath(*name.split(".")).with_suffix(".olean")


def run_lean(arguments: list[str], *, capture: bool = False) -> subprocess.CompletedProcess:
    return subprocess.run([str(WRAPPER), *arguments], cwd=ROOT, check=True,
                          text=True, capture_output=capture)


def audit_source(ordered: list[str]) -> str:
    """Select declarations by defining module, including private/generated names."""
    names = ", ".join("`" + name for name in ordered)
    audit = "\n".join("import " + name for name in ordered) + r'''
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[MODULES]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let selectedModules := env.header.moduleNames.map modules.contains
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
      let moduleName := env.header.moduleNames[index.toNat]!
      if selectedModules[index.toNat]! then names.push (name, moduleName) else names
    | none => names
  let mut current : Nat := 0
  let mut privateNames : Nat := 0
  for (name, moduleName) in names do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name} ({moduleName}): {unexpected}"
    if (`BFGS.Counterexample).isPrefixOf moduleName || moduleName == `BFGS.MainTheorem then
      current := current + 1
    if (`_private).isPrefixOf name then
      privateNames := privateNames + 1
  if current == 0 then
    throwError "Audit selected no Counterexample declarations"
  logInfo m!"Audited {current} Counterexample declarations and {names.size - current} reusable declarations ({privateNames} private names in total)."
  logInfo "Allowed transitive axioms: propext, Classical.choice, Quot.sound."
'''.replace("MODULES", names)
    if "BFGS.MainTheorem" in ordered:
        audit += '''
open BFGS BFGS.Algorithm BFGS.Counterexample Filter Topology in
example :
    Semialgebraic.IsSemialgebraicFunction f ∧ LocallyLipschitz f ∧ Continuous f ∧
    Tendsto f (cocompact Vec) atTop ∧ (∀ a : ℝ, IsCompact {x | f x ≤ a}) ∧
    (0 : Vec →L[ℝ] ℝ) ∉ clarkeSubdifferential f 0 ∧ HasOpenUniformFailureBasin f :=
  concrete_counterexample

#print axioms BFGS.Counterexample.concrete_counterexample
#print axioms BFGS.Counterexample.main_theorem
'''
    return audit


def check_corrupted_interval() -> None:
    """A valid numeric certificate passes; changing only its upper bound fails."""
    source = '''import BFGS.Counterexample.Certificates.IntervalBase
open BFGS
example : (⟨(0 : ℚ), (UPPER : ℚ)⟩ : RationalInterval).Contains (1 : ℝ) := by
  norm_num [RationalInterval.Contains]
'''
    with tempfile.TemporaryDirectory(prefix="bfgs-negative-check-") as directory:
        path = Path(directory) / "IntervalCheck.lean"
        path.write_text(source.replace("UPPER", "1"))
        run_lean(["-DwarningAsError=true", str(path)], capture=True)
        path.write_text(source.replace("UPPER", "0"))
        rejected = subprocess.run([str(WRAPPER), "--json", "-DwarningAsError=true", str(path)],
                                  cwd=ROOT, text=True, capture_output=True)
        messages = [json.loads(line) for line in rejected.stdout.splitlines() if line.strip()]
        errors = [item for item in messages if item.get("severity") == "error"]
        # A missing import, syntax error, or unavailable tactic is not evidence.
        if (rejected.returncode == 0 or not errors or
                any("unsolved goals" not in item.get("data", "") or
                    "⊢ False" not in item.get("data", "") for item in errors)):
            raise RuntimeError("Corrupted interval did not fail for the expected numerical "
                               "contradiction:\n" + rejected.stdout + rejected.stderr)
    print("Negative check passed: changing interval [0,1] to [0,0] rejects 1 ∈ I "
          "with the numerical goal False.", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true",
                        help="check source hygiene and import closure without running Lean")
    parser.add_argument("--incremental", action="store_true",
                        help="also reuse current-module oleans when their inputs are unchanged")
    args = parser.parse_args()
    ordered, sources, imports = discover()
    current = [name for name in ordered if is_current(name)]
    print(f"Source hygiene and import closure passed: {len(current)} current modules, "
          f"{len(ordered) - len(current)} reusable modules.", flush=True)
    if args.static_only:
        print("Static checks only; compilation and the axiom audit were not run.")
        return 0

    expected = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    actual = run_lean(["--short-version"], capture=True).stdout.strip()
    if actual != expected:
        raise RuntimeError(f"Lean version mismatch: expected {expected}, got {actual}")
    print("Lean " + actual + "; using existing dependency cache (no Lake).", flush=True)
    original = {path: digest(path) for path in [*sources.values(), WRAPPER, Path(__file__).resolve(),
                                              ROOT / "lean-toolchain", ROOT / "lake-manifest.json"]}
    lean_library = Path(run_lean(["--print-libdir"], capture=True).stdout.strip())
    external_paths = [BUILD, ROOT, *sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")),
                      lean_library]
    reused = rebuilt = 0
    for name in ordered:
        target = olean(name)
        inputs = [sources[name], WRAPPER, ROOT / "lean-toolchain"]
        missing = []
        for dependency in imports[name]:
            relative = Path(*dependency.split(".")).with_suffix(".olean")
            found = next((base / relative for base in external_paths
                          if (base / relative).is_file()), None)
            if found is None:
                missing.append(dependency)
            else:
                inputs.append(found)
        if missing:
            raise RuntimeError("Missing compiled dependencies for " + name + ": " +
                               ", ".join(missing) + ". Restore the pinned package cache first.")
        fresh = target.is_file() and all(
            path.stat().st_mtime_ns <= target.stat().st_mtime_ns for path in inputs)
        force = is_current(name) and not args.incremental
        if fresh and not force:
            reused += 1
            continue
        print("Compiling " + name, flush=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        # Publish only successful builds. Failed compilations leave no new olean.
        with tempfile.TemporaryDirectory(prefix=".bfgs-build-", dir=target.parent) as directory:
            pending = Path(directory) / target.name
            run_lean(["-DwarningAsError=true", "-o", str(pending), str(sources[name])])
            if digest(sources[name]) != original[sources[name]]:
                raise RuntimeError("Source changed while compiling: " + name + "; rerun the check")
            # Copy rather than rename: moved temporary outputs have disappeared
            # on the local filesystem after successful compilation.
            shutil.copyfile(pending, target)
        rebuilt += 1

    check_sources_unchanged(original)
    BUILD.mkdir(parents=True, exist_ok=True)
    audit = BUILD / "CounterexampleAxiomAudit.lean"
    audit.write_text(audit_source(ordered))
    check_corrupted_interval()
    print("Auditing every declaration in the compiled local import closure.", flush=True)
    run_lean(["-DwarningAsError=true", str(audit)])
    check_sources_unchanged(original)
    print(f"PASS: {rebuilt} modules rebuilt, {reused} cached modules reused; "
          "exhaustive transitive axiom audit passed.", flush=True)
    print("Audit source: " + str(audit.relative_to(ROOT)))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        raise SystemExit(1)
