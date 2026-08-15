#!/usr/bin/env python3
r"""Advisory check: lake compiled modules vs proof-integrity gate `target-modules`.

Context (#8782): the reusable CI workflow ``lean-axiom.yml`` receives a
hand-written ``target-modules`` list (the dotted module names whose axioms the
gate actually inspects) and a ``project-path`` (the lake root). Nothing compares
that list to what the lake *compiles*: the lakefile glob (e.g.
``globs := #[.submodules `Conway, `Conway_en]``) grows as modules are added,
while ``target-modules`` stays static. A gate can therefore be green while
inspecting a vanishing fraction of the lake -- a "vert hors-cible" that is
visually indistinguishable from a targeted green in the CI check-rollup.

This script makes the gap visible. It is **advisory and never fails a CI run**
(exit 0 unconditionally): it walks the lake's ``.lean`` files to infer the
compiled module set, compares it to ``target-modules``, and prints the delta.

Usage (local)::

    python scripts/lean/check_target_coverage.py \
        --project-path MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean \
        --from-workflow .github/workflows/lean-conway.yml \
        --lib-root Conway \
        --name conway_lean

Wired as a non-blocking final step in ``lean-axiom.yml`` (``if: always()``) so
the coverage report lands in every Lean PR's CI log regardless of the blocking
axiom verdict.

``--from-workflow`` vs ``--target-modules`` (#8782)
---------------------------------------------------
``--target-modules`` takes the list literally, which means the caller keeps a
copy. That is how this tool acquired the very defect it was built to detect: a
tool that flags the drift of a hand-maintained list introduced a *second*
hand-maintained copy of it, and the copies diverged the moment option (b) of
#8782 landed. ``lean-conway.yml`` ended up with three copies -- the blocking
gate (``Conway.KochenSpecker,Conway.FreeWillTheorem``), the advisory audit job
(``Conway.Life.HashlifeCorrectness``), and this script's own ``--target-modules``
flag, which had only ever been given the *blocking* job's list. The report then
printed ``Conway.Life.HashlifeCorrectness`` under "the gate never inspects their
axioms" -- a statement that was false about precisely the module the design
decision had been taken to cover.

``--from-workflow`` removes the copy by construction: it reads the workflow YAML
and unions ``with.target-modules`` across **every** job whose ``uses:`` resolves
to ``lean-axiom.yml`` (both the ``owner/repo/.github/...@ref`` and the local
``./.github/...`` forms). Adding, retargeting or deleting a gate job moves the
coverage report with it, and no third list exists to fall out of date.

GitHub Actions forbids the ``env`` context inside ``jobs.<id>.with``, so sharing
the list through a workflow-level variable is closed; reading the YAML is what
remains. ``--target-modules`` is kept for ad-hoc local runs and for lakes whose
gate is not (yet) expressed as a workflow job.

Module discovery is filesystem-based (no ``lake build`` required): every
``.lean`` file under ``--project-path`` (excluding ``.lake/``, ``lakefile*``,
``lean-toolchain``) is mapped to its dotted module name
(``Conway/Life/Foo.lean`` -> ``Conway.Life.Foo``). With ``--lib-root Conway``
the walk is scoped to ``<project>/Conway/`` plus the root sibling
``<project>/Conway_en.lean``, matching the typical ``.submodules`` + sibling
glob precisely. Without ``--lib-root`` the walk is maximal (every ``.lean``
file), which is deliberately over-inclusive -- an advisory "you might be
missing these" signal beats a silent miss. The walk counts ``_en`` i18n
siblings as compiled modules, which they are (the lakefile glob compiles them);
a gate that omits them has the same blind spot as one that omits an FR module.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Directories that never contain lake modules (build cache, VCS, tooling).
_EXCLUDE_TOP_DIRS = {".lake", ".git", "node_modules", ".venv"}


def discover_modules(project_path: Path, lib_root: str | None) -> set[str]:
    """Return the dotted module names of every compiled ``.lean`` source file.

    ``lib_root`` (e.g. ``"Conway"``) scopes the walk to ``<project>/<lib_root>/``
    plus the root sibling ``<project>/<lib_root>_en.lean`` -- the two pieces of a
    standard ``.submodules NAME`` + ``NAME_en`` glob. ``None`` walks everything.
    """
    project_path = project_path.resolve()
    modules: set[str] = set()

    candidates: list[Path] = []
    if lib_root:
        # The three pieces of a standard `.submodules NAME` + `NAME_en` glob:
        lib_dir = project_path / lib_root
        if lib_dir.is_dir():
            candidates.extend(lib_dir.rglob("*.lean"))
        # ...the root umbrella module itself (`NAME.lean`, not under `NAME/`).
        umbrella = project_path / f"{lib_root}.lean"
        if umbrella.is_file():
            candidates.append(umbrella)
        # ...and the `_en` i18n sibling (`NAME_en.lean`).
        sibling = project_path / f"{lib_root}_en.lean"
        if sibling.is_file():
            candidates.append(sibling)
    else:
        for p in project_path.rglob("*.lean"):
            parts = p.relative_to(project_path).parts
            if parts and parts[0] in _EXCLUDE_TOP_DIRS:
                continue
            candidates.append(p)

    for p in candidates:
        rel = p.relative_to(project_path)
        if rel.name.startswith("lakefile") or rel.name == "lean-toolchain":
            continue
        # Skip anything inside an excluded top dir (only reachable in the
        # maximal-walk branch; the scoped branch is already clean).
        if rel.parts[0] in _EXCLUDE_TOP_DIRS:
            continue
        module = ".".join(rel.parts[:-1]) + ("" if not rel.parts[:-1] else ".") + rel.stem
        # rel.parts[:-1] empty for a root-level file (e.g. Conway_en.lean).
        if not rel.parts[:-1]:
            module = rel.stem
        modules.add(module)
    return modules


def filter_i18n_siblings(modules: set[str]) -> set[str]:
    """Drop i18n ``_en`` siblings from a module set, by PATH SEGMENT.

    A segment ending in ``_en`` covers both root stems (``Conway_en``) and
    non-root directories (``Conway/Life_en/Foo.lean`` -> ``Conway.Life_en.Foo``).
    Used by lean-axiom.yml's runtime derivation (issue #10889); kept here so the
    exact filter the gate applies is unit-tested against the walk.
    """
    return {m for m in modules
            if not any(part.endswith("_en") for part in m.split("."))}


def parse_target_modules(raw: str) -> set[str]:
    return {m.strip() for m in raw.split(",") if m.strip()}


def _uses_lean_axiom(uses: str) -> bool:
    """True if a job's ``uses:`` resolves to the reusable ``lean-axiom.yml``.

    Both call forms occur in the repo and must match:
    ``jsboige/CoursIA/.github/workflows/lean-axiom.yml@main`` (lean-conway.yml)
    and ``./.github/workflows/lean-axiom.yml`` (lean-knot.yml, per-PR resolution).
    """
    if not isinstance(uses, str):
        return False
    ref = uses.split("@", 1)[0].strip()  # drop @main / @sha
    return ref.rsplit("/", 1)[-1] == "lean-axiom.yml"


def targets_from_workflow(workflow_path: Path) -> tuple[set[str], dict[str, set[str]]]:
    """Union ``with.target-modules`` over every lean-axiom job in a workflow.

    Returns ``(union, per_job)``. An **empty** ``per_job`` means no job in the
    file calls ``lean-axiom.yml`` -- reported by the caller as an explicit
    "no gate wired" line, never folded into a 0%-coverage figure: those two
    states have opposite meanings and a number that conflates them would be a
    computed value measuring the wrong thing.
    """
    import yaml  # local import: only --from-workflow needs the dependency

    doc = yaml.safe_load(workflow_path.read_text(encoding="utf-8")) or {}
    jobs = doc.get("jobs") or {}

    per_job: dict[str, set[str]] = {}
    for job_id, job in jobs.items():
        if not isinstance(job, dict) or not _uses_lean_axiom(job.get("uses", "")):
            continue
        raw = (job.get("with") or {}).get("target-modules", "")
        # A gate job with an empty target list is still a gate job: record it so
        # the report shows it contributed nothing, rather than hiding it.
        per_job[str(job_id)] = parse_target_modules(str(raw))

    union: set[str] = set()
    for mods in per_job.values():
        union |= mods
    return union, per_job


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Advisory: lake compiled modules vs proof-integrity target-modules."
    )
    parser.add_argument("--project-path", required=True, help="Repo-relative lake root.")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument(
        "--target-modules",
        help="Comma-separated dotted modules the gate inspects (lean-axiom.yml input). "
        "Literal list -- keeps a copy; prefer --from-workflow in CI.",
    )
    source.add_argument(
        "--from-workflow",
        help="Path to a workflow YAML; union target-modules over every job whose "
        "`uses:` resolves to lean-axiom.yml. No second copy of the list to drift.",
    )
    parser.add_argument("--name", default="lake", help="Display name for the report header.")
    parser.add_argument(
        "--lib-root",
        default=None,
        help="Scope the walk to <project>/<lib-root>/ + <lib-root>_en.lean (precise). "
        "Omit for a maximal walk of every .lean file (advisory, over-inclusive).",
    )
    args = parser.parse_args(argv)

    project_path = Path(args.project_path)
    if not project_path.is_dir():
        print(f"ADVISORY target-coverage ({args.name}): project-path not found: {project_path}")
        return 0  # advisory: never fail CI on a missing path

    compiled = discover_modules(project_path, args.lib_root)

    per_job: dict[str, set[str]] = {}
    if args.from_workflow:
        wf = Path(args.from_workflow)
        if not wf.is_file():
            print(f"ADVISORY target-coverage ({args.name}): workflow not found: {wf}")
            return 0  # advisory: never fail CI on a missing path
        targeted, per_job = targets_from_workflow(wf)
    else:
        targeted = parse_target_modules(args.target_modules)

    runtime_derived = "*" in targeted
    if runtime_derived:
        # "*" (issue #10889) = the gate derives its module list at runtime by
        # walking the lake itself, so every compiled module is inspected by
        # construction: no blind spot can exist, and nothing is a phantom
        # ("*" is a directive, not a module name).
        covered = set(compiled)
        blind_spot = []
        phantom = []
    else:
        covered = compiled & targeted
        blind_spot = sorted(compiled - targeted)  # compiled but gate never inspects
        phantom = sorted(targeted - compiled)  # targeted but no source on disk

    coverage_pct = (len(covered) / len(compiled) * 100) if compiled else 0.0

    print(f"=== ADVISORY: proof-integrity target coverage ({args.name}) ===")
    print(f"Project: {project_path}")
    print(f"lib-root scope: {args.lib_root or '(maximal walk of every .lean)'}")

    if args.from_workflow:
        print(f"Target source: {args.from_workflow} (union over lean-axiom jobs)")
        if not per_job:
            # NOT the same thing as 0% coverage, and must not be printed as such:
            # "no gate job in this file" means the report has nothing to measure,
            # whereas "0% covered" would assert the gate inspects nothing. Emitting
            # the latter for the former is the failure this tool exists to catch.
            print()
            print(
                "NO GATE WIRED -- no job in this workflow has `uses:` resolving to\n"
                "      lean-axiom.yml, so there is no target list to compare against.\n"
                "      This is not a coverage figure: nothing was measured. Check the\n"
                "      workflow path, or whether the gate job was renamed/removed."
            )
            return 0
        for job_id in sorted(per_job):
            mods = per_job[job_id]
            shown = ", ".join(sorted(mods)) if mods else "(none)"
            print(f"  job {job_id}: {len(mods)} -> {shown}")
    else:
        print("Target source: --target-modules (literal list passed by the caller)")

    print(f"Compiled modules (filesystem walk): {len(compiled)}")
    print(f"Gate target-modules:                {len(targeted)}")
    if runtime_derived:
        print('     ("*" -- derived at runtime from the lake walk, #10889;')
        print("      every compiled module is inspected by construction)")
    print(f"Covered (in both):                  {len(covered)}  ({coverage_pct:.1f}% of compiled)")
    print()
    if phantom:
        print(f"PHANTOM targets ({len(phantom)}) -- named in target-modules but no source file:")
        for m in phantom:
            print(f"  - {m}")
        print()
    if blind_spot:
        print(
            f"BLIND SPOT ({len(blind_spot)}) -- compiled by the lake but the gate never inspects "
            f"their axioms:"
        )
        for m in blind_spot:
            print(f"  - {m}")
        print()
        print(
            "NOTE: a green proof-integrity check that covers <100% of compiled modules\n"
            "      is a 'vert hors-cible' -- it says nothing about the unlisted modules.\n"
            "      This is advisory; it does not fail the build. See #8782."
        )
    else:
        if runtime_derived:
            print(
                'OK: target-modules="*" -- module list derived at runtime from the lake '
                "walk (issue #10889); every compiled module is inspected."
            )
        else:
            print("OK: every compiled module is in target-modules (or the walk found none).")

    return 0  # advisory: always exit 0, never gate CI


if __name__ == "__main__":
    sys.exit(main())
