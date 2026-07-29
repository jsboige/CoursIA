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
        --target-modules "Conway.KochenSpecker,Conway.FreeWillTheorem" \
        --name conway_lean

Wired as a non-blocking final step in ``lean-axiom.yml`` (``if: always()``) so
the coverage report lands in every Lean PR's CI log regardless of the blocking
axiom verdict.

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


def parse_target_modules(raw: str) -> set[str]:
    return {m.strip() for m in raw.split(",") if m.strip()}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Advisory: lake compiled modules vs proof-integrity target-modules."
    )
    parser.add_argument("--project-path", required=True, help="Repo-relative lake root.")
    parser.add_argument(
        "--target-modules",
        required=True,
        help="Comma-separated dotted modules the gate inspects (lean-axiom.yml input).",
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
    targeted = parse_target_modules(args.target_modules)

    covered = compiled & targeted
    blind_spot = sorted(compiled - targeted)  # compiled but gate never inspects
    phantom = sorted(targeted - compiled)  # targeted but no source on disk

    coverage_pct = (len(covered) / len(compiled) * 100) if compiled else 0.0

    print(f"=== ADVISORY: proof-integrity target coverage ({args.name}) ===")
    print(f"Project: {project_path}")
    print(f"lib-root scope: {args.lib_root or '(maximal walk of every .lean)'}")
    print(f"Compiled modules (filesystem walk): {len(compiled)}")
    print(f"Gate target-modules:                {len(targeted)}")
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
        print("OK: every compiled module is in target-modules (or the walk found none).")

    return 0  # advisory: always exit 0, never gate CI


if __name__ == "__main__":
    sys.exit(main())
