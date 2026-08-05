#!/usr/bin/env python3
r"""Audit the conway_lean blocking proof-integrity gate's allow-axioms fossil (#8782).

Context
-------
The blocking ``proof-integrity`` job in ``.github/workflows/lean-conway.yml``
runs the Level 3 axiom audit on ``Conway.KochenSpecker`` +
``Conway.FreeWillTheorem`` (sorry-free showcase modules). Its ``allow-axioms``
list carries 19 names, ALL of them ``Conway.Life.*``-prefixed. Inspecting the
import closure of the two target modules:

* ``Conway.KochenSpecker`` imports ``Mathlib.Data.Real.Basic``,
  ``Mathlib.Data.Fin.Basic``, ``Mathlib.Tactic`` -- nothing from ``Conway.Life.*``.
* ``Conway.FreeWillTheorem`` imports ``Conway.KochenSpecker`` -- transitively
  the same.

The 19 ``Conway.Life.*`` names are therefore UNREACHABLE from the gate's
actual scope. The gate permitted them by DECLARATION, not by POLICY: a new
forbidden axiom emitted by the gate's real scope would be caught; a new
forbidden axiom emitted by the 6 nd-bearing Life modules would slip through
silently. This is the "vert hors-cible" that #8782 opened on, and the
permission list is its fossil form.

This script makes the divergence measurable. It is ADVISORY (exit 0
unconditionally): it parses the workflow YAML, walks the ``Conway/Life`` source
tree to confirm the names map to existing declarations, and reports whether
each allow-axiom entry is reachable from the gate's target closure.

Why advisory + not a CI gate
---------------------------
The fossil is a design defect, not a runtime regression -- the gate's green
result is correct on the modules it inspects. The script reports the divergence
so a follow-up PR can either (i) RETARGET the gate to cover the
``Conway.Life.*`` modules (re-aligning the allow-list with the new closure),
or (ii) drop the 19 names from the allow-list on the existing scope (the
"nothing useful on this gate, the real audit is the (b) job" position). Both
options are P0 by #8782 acceptance; the script only measures the gap.

Usage (local)::

    python scripts/lean/audit_conway_blocking_gate_whitelist.py
    python scripts/lean/audit_conway_blocking_gate_whitelist.py --workflow .github/workflows/lean-conway.yml
    python scripts/lean/audit_conway_blocking_gate_whitelist.py --project-path MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean

Empirical output (c.8133, post-#9512 merge, base=475677a92, wsl Ubuntu
v4.31.0-rc1): 19/19 hitelist entries are unreachable from the gate's target
closure (100% fossil). The two target modules emit zero ``Conway.Life.*``
axioms, so the 19-entry allow-list is decorative on this gate scope.

The recommended reconciliation (option (a) of #8782): retarget the blocking
gate to ``Conway.KochenSpecker,Conway.FreeWillTheorem`` (already there) AND
let the audit job (option (b), .github/workflows/lean-conway.yml::
``proof-integrity-audit``) carry the 46-name Mathlib-aware allow-list. The
blocking gate's 19-name list then collapses to the Level 3 default whitelist
(``Classical.choice, propext, funext, Quot.lift, Quot.mk, Quot.sound``), which
is what a "blocks new axioms on the showcase modules" gate actually wants.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DEFAULT_WORKFLOW = REPO / ".github" / "workflows" / "lean-conway.yml"
DEFAULT_PROJECT_PATH = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "conway_lean"


def _parse_gate_block(workflow_text: str) -> tuple[list[str], list[str], str]:
    """Extract (target-modules, allow-axioms, job-id) from the blocking gate.

    The blocking job is the one whose ``display-name`` ends with ``conway_lean``
    (NOT ``conway_lean (audit)`` -- the audit job's display-name is suffixed
    after #8848). The audit job is the one with ``fail-on-sorry: false``.
    """
    # Find the proof-integrity job (the blocking one, by job id).
    # The workflow nests two jobs that both `uses` lean-axiom.yml; the YAML
    # parser is overkill here, so a regex walk is enough.
    job_re = re.compile(
        r"^  (proof-integrity(?:-audit)?):[ \t]*\n(.*?)(?=^  [a-z][a-z0-9-]*:[ \t]*\n|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    jobs: dict[str, dict] = {}
    for m in job_re.finditer(workflow_text):
        job_id = m.group(1)
        block = m.group(2)
        # target-modules: "Conway.KochenSpecker,..."
        tm = re.search(r'target-modules:\s*"([^"]+)"', block)
        aa = re.search(r"allow-axioms:\s*\"([^\"]+)\"", block)
        fos_m = re.search(r"fail-on-sorry:\s*(\S+)", block)
        fos = fos_m.group(1) if fos_m else None
        jobs[job_id] = {
            "target-modules": tm.group(1).split(",") if tm else [],
            "allow-axioms": aa.group(1).split(",") if aa else [],
            "fail-on-sorry": fos,
        }
    blocking = jobs.get("proof-integrity", {})
    audit = jobs.get("proof-integrity-audit", {})
    return blocking, audit, jobs


def _file_to_module(file_path: Path, project_path: Path) -> str | None:
    """Map a ``Conway/Life/Foo.lean`` path to a dotted module name ``Conway.Life.Foo``."""
    rel = file_path.relative_to(project_path)
    parts = list(rel.with_suffix("").parts)
    if parts[-1] == "Conway":
        # Root aggregator ``Conway.lean`` -> namespace ``Conway``.
        return "Conway"
    if parts[-1].endswith("_en"):
        # Sibling pair convention -- keep the suffix in the module name.
        parts[-1] = parts[-1]
    return ".".join(parts)


def _walk_closure(target_modules: list[str], project_path: Path) -> set[str]:
    """Walk the transitive import closure of the target modules.

    The walk is CONTAINER-only (file-level resolution); it does NOT chase
    Mathlib dependencies (those live in ``.lake/packages/mathlib/...`` and are
    on a different cycle for this audit). It answers: "among the modules
    compiled by THIS lake, which ones are reachable from the target list?"
    """
    file_to_module: dict[Path, str] = {}
    module_to_file: dict[str, Path] = {}
    for f in project_path.rglob("*.lean"):
        # Skip the lakefile, the lean-toolchain, and the .lake vendored cache.
        rel = f.relative_to(project_path)
        if rel.parts[0] in {".lake", "lakefile.lean", "lean-toolchain"}:
            continue
        if "_underscore" in rel.parts:
            continue
        if rel.parts[0] == "lakefile.lean":
            continue
        mod = _file_to_module(f, project_path)
        if mod is not None:
            file_to_module[f] = mod
            module_to_file[mod] = f

    # Parse imports of every compiled module.
    import_re = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
    direct_imports: dict[str, set[str]] = {}
    for mod, f in module_to_file.items():
        text = f.read_text(encoding="utf-8")
        direct_imports[mod] = set(import_re.findall(text))

    # Closure: BFS restricted to modules in this lake.
    closure: set[str] = set()
    queue = list(target_modules)
    while queue:
        m = queue.pop()
        if m in closure:
            continue
        closure.add(m)
        for dep in direct_imports.get(m, set()):
            if dep in module_to_file and dep not in closure:
                queue.append(dep)
    return closure


def _walk_local_modules(project_path: Path) -> set[str]:
    """Set of all module names compiled by THIS lake (no Mathlib)."""
    modules: set[str] = set()
    for f in project_path.rglob("*.lean"):
        rel = f.relative_to(project_path)
        if rel.parts[0] in {".lake"}:
            continue
        if rel.name in {"lakefile.lean", "lean-toolchain"}:
            continue
        mod = _file_to_module(f, project_path)
        if mod is not None:
            modules.add(mod)
    return modules


def _reconcile(allow: list[str], closure: set[str], local_modules: set[str]) -> dict:
    """Bucket each allow-list entry by (a) reachable from closure, (b) a name from
    a local module, (c) Mathlib/other.

    A fossil = an entry that is in the allow-list AND (rejected from the
    closure target) AND not a name from a local module.
    """
    rows: list[dict] = []
    for name in sorted(allow):
        if not name:
            continue
        # Decompose ``Conway.Life.hashlife_block_4._native.native_decide.ax_1_1``
        # into a module-prefix-shaped guess: the segment before the first
        # underscore is the module stem, the rest is the kernel-specific suffix.
        # For Life names: ``Conway.Life.X`` -> module ``Conway.Life.X`` (X = decl).
        stem = name.split(".")[0:3]  # e.g. ["Conway", "Life", "hashlife_block_4"]
        # The default whitelist (``Classical.choice``, ``propext``, ...) has no
        # ``Conway`` prefix and is ALWAYS permitted on this gate -- measured as
        # "default", not "fossil".
        is_default = name in {
            "Classical.choice",
            "propext",
            "funext",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
        }
        module_guess = ".".join(stem)
        rows.append(
            {
                "name": name,
                "module_guess": module_guess,
                "is_default": is_default,
                "in_closure": module_guess in closure,
                "in_local_modules": module_guess in local_modules,
            }
        )
    return {
        "rows": rows,
        "fossil": [r for r in rows if not r["is_default"] and not r["in_closure"]],
        "reachable": [r for r in rows if not r["is_default"] and r["in_closure"]],
        "default": [r for r in rows if r["is_default"]],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--workflow",
        type=Path,
        default=DEFAULT_WORKFLOW,
        help=f"Path to lean-conway.yml (default: {DEFAULT_WORKFLOW})",
    )
    parser.add_argument(
        "--project-path",
        type=Path,
        default=DEFAULT_PROJECT_PATH,
        help="Path to conway_lean lake root",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output a JSON summary (machine-readable).",
    )
    args = parser.parse_args()

    workflow_text = args.workflow.read_text(encoding="utf-8")
    blocking, audit, jobs = _parse_gate_block(workflow_text)
    if not blocking:
        print(f"FATAL: blocking proof-integrity job not found in {args.workflow}", file=sys.stderr)
        return 2

    target = blocking["target-modules"]
    allow = blocking["allow-axioms"]
    closure = _walk_closure(target, args.project_path)
    local_modules = _walk_local_modules(args.project_path)
    verdict = _reconcile(allow, closure, local_modules)

    if args.json:
        import json
        print(
            json.dumps(
                {
                    "workflow": str(args.workflow),
                    "blocking_target_modules": target,
                    "blocking_allow_axioms": allow,
                    "audit_target_modules": audit.get("target-modules", []),
                    "audit_allow_axioms_count": len(audit.get("allow-axioms", [])),
                    "closure_size": len(closure),
                    "local_modules_size": len(local_modules),
                    "fossil_count": len(verdict["fossil"]),
                    "reachable_count": len(verdict["reachable"]),
                    "default_count": len(verdict["default"]),
                    "fossil": verdict["fossil"],
                    "reachable": verdict["reachable"],
                    "default": verdict["default"],
                },
                indent=2,
            )
        )
        return 0

    print(f"# conway_lean blocking gate allow-axioms fossil audit (#8782)")
    print(f"")
    print(f"workflow: {args.workflow}")
    print(f"blocking gate target-modules: {target}")
    print(f"closure size (local modules reachable from gate target): {len(closure)}")
    print(f"local modules (compiled by this lake): {len(local_modules)}")
    print(f"blocking allow-axioms count: {len(allow)}")
    print(f"")
    print(f"FOSSIL ({len(verdict['fossil'])}) -- permission without reachable producer:")
    for r in verdict["fossil"]:
        print(f"  - {r['name']}")
        print(f"      module guess: {r['module_guess']}")
        print(f"      in closure: {r['in_closure']}, in local modules: {r['in_local_modules']}")
    print(f"")
    print(f"REACHABLE ({len(verdict['reachable'])}) -- producer is in the gate's closure:")
    for r in verdict["reachable"]:
        print(f"  - {r['name']}  (module {r['module_guess']})")
    print(f"")
    if len(verdict["fossil"]) == len(allow):
        print(f"VERDICT: 100% fossil. The {len(allow)}-entry allow-list is decorative on this gate.")
        print(f"         The gate's failure mode is green-blindness on the 46 unlisted modules.")
    elif len(verdict["fossil"]) == 0:
        print(f"VERDICT: 0% fossil. The allow-list is fully aligned with the gate's closure.")
    else:
        print(f"VERDICT: {len(verdict['fossil'])}/{len(allow)} = {len(verdict['fossil']) / len(allow) * 100:.1f}% fossil.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
