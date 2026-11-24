#!/usr/bin/env python3
r"""Strict gate (issue #19015): catch ``.lean`` files that no ``lean_lib`` builds.

Context (#19015): ``lake -R build`` with no argument compiles only the
``@[default_target]`` libs. A file ``Foo.lean`` that is (a) not in any
``lean_lib``'s ``globs`` (or ``roots``) list, and (b) not ``import``-ed by any
other source that IS built, is never elaborated -- and a green CI on the
lake says nothing about it. Instance measured 2026-10-03: ``ApprovalDefs``
on ``social_choice_lean_peters`` passed every gate while compiling nothing.

This script closes that gap by parsing ``lakefile.lean`` or ``lakefile.toml``, unioning the globs
of every ``lean_lib`` declared, walking ``<project>/**/*.lean``, and reporting
any file not covered. Default mode is advisory (orphans listed, ``exit 0``);
the ``--strict`` flag turns the report into a hard gate (``exit 1`` on any
orphan). The CLI defaults to advisory to keep callers that have not opted into
strict gating from breaking — CI wiring in ``lean-axiom.yml`` flips the gate on
explicitly per job.

Scope:
- ``lean_lib`` only (the Lake construct that defines a compilation unit).
  ``lean_exe`` is an executable target, not a lib, and the defect of #19015
  is library-scoped. Callers can extend if/when needed.
- Literal ``roots`` and ``globs`` are read by the shared Lake selector parser.
  The Lean DSL is not evaluated; unsupported expressions fail explicitly.
- ``import`` reachability: a file not in any glob but ``import``-ed by a
  file that IS in a glob is reachable (Lean's elaboration follows imports).
  We scan the source text of in-glob files for ``^import Foo`` and union.

Cabling (proposal): add as a non-``if: always()`` step in
``.github/workflows/lean-axiom.yml`` (and ``lean-build.yml``) so the gate is
executed on every Lean PR. Opt-out via ``--advisory`` for lakes that
deliberately carry unbuilt files (e.g. reference docs in
``agent_tests/prover/session_state/reference_docs/`` -- but those are
excluded by the path scope).

Usage::

    python scripts/lean/check_lean_orphans.py \
        --project-path MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters \
        --lakefile  MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters/lakefile.lean
        [--strict] [--exclude REL_PATH]...

Default is advisory: orphans are reported but exit is 0. ``--strict`` turns
the report into a hard gate (exit 1 on any orphan). ``--exclude`` whitelists
known intentional orphans (e.g. ``GameTheory.lean`` on ``game_theory_lean``,
the EPIC #4365 skeleton aggregator).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from lake_selectors import LakefileError, lake_selectors, selected

# Same excludes as check_target_coverage.py -- the "compiled module" walk
# agrees on what is and is not a Lake source file.
_EXCLUDE_TOP_DIRS = {".lake", ".git", "node_modules", ".venv", "_peters"}


def _discover_lean_files(lake_root: Path) -> list[Path]:
    files: list[Path] = []
    for p in lake_root.rglob("*.lean"):
        parts = p.relative_to(lake_root).parts
        if parts and parts[0] in _EXCLUDE_TOP_DIRS:
            continue
        if p.name.startswith("lakefile") or p.name == "lean-toolchain":
            continue
        files.append(p)
    return files


def _imports_reachable_from(
    lake_root: Path, covered: set[Path], all_lean: list[Path]
) -> set[Path]:
    r"""Union of files reachable by ``^import Foo`` from any covered file.

    This handles the second channel by which a file gets compiled: it is
    ``import``-ed by a file that is. The path->module mapping mirrors
    ``check_target_coverage.discover_modules``'s dotted convention.
    """
    file_to_module: dict[Path, str] = {}
    for p in all_lean:
        rel = p.relative_to(lake_root)
        mod = ".".join(rel.parts[:-1]) + (("." + rel.stem) if rel.parts[:-1] else rel.stem)
        file_to_module[p] = mod
    module_to_files: dict[str, list[Path]] = {}
    for p, m in file_to_module.items():
        module_to_files.setdefault(m, []).append(p)

    import_re = re.compile(r"^\s*import\s+([A-Za-z_][\w'.]*)", re.MULTILINE)

    reachable: set[Path] = set()
    visited: set[str] = set()
    stack: list[str] = [file_to_module[p] for p in covered]
    while stack:
        mod = stack.pop()
        if mod in visited:
            continue
        visited.add(mod)
        for p in module_to_files.get(mod, []):
            reachable.add(p)
        for p in reachable:
            try:
                text = p.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            for m in import_re.finditer(text):
                imported_mod = m.group(1)
                if imported_mod not in visited:
                    stack.append(imported_mod)
    return reachable


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Strict gate (#19015): .lean files that no lean_lib builds."
    )
    parser.add_argument("--project-path", required=True, help="Repo-relative lake root.")
    parser.add_argument(
        "--lakefile",
        required=True,
        help="Path to the lakefile.lean or lakefile.toml declaring the libs.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit 1 on any orphan. Use when a lake has been audited and no "
        "intentional orphans remain (the gate then blocks any regression).",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="REL_PATH",
        help="Lake-relative path of a .lean file to whitelist as an "
        "intentional orphan (e.g. ``GameTheory.lean`` for EPIC #4365's "
        "skeleton aggregator). Repeatable. Excluded files are still listed "
        "in the report under ``EXCLUDED`` but do not cause a non-zero exit.",
    )
    parser.add_argument(
        "--name", default="lake", help="Display name for the report header."
    )
    args = parser.parse_args(argv)

    lake_root = Path(args.project_path).resolve()
    lakefile = Path(args.lakefile).resolve()
    if not lake_root.is_dir():
        print(f"ERROR ({args.name}): project-path not found: {lake_root}")
        return 2
    if not lakefile.is_file():
        print(f"ERROR ({args.name}): lakefile not found: {lakefile}")
        return 2

    try:
        if lakefile.parent != lake_root:
            raise LakefileError("lakefile outside project directory")
        selectors = lake_selectors(lake_root)
    except LakefileError as exc:
        print(f"ERROR ({args.name}): {exc}")
        return 2
    all_lean = _discover_lean_files(lake_root)
    covered = {p for p in all_lean if selected(
        ".".join(p.relative_to(lake_root).with_suffix("").parts), selectors
    )}
    reachable = _imports_reachable_from(lake_root, covered, all_lean)

    orphans = sorted(
        p for p in all_lean if p not in covered and p not in reachable
    )

    # Apply --exclude whitelist (lake-relative paths).
    excluded: list[Path] = []
    if args.exclude:
        exclude_set = {Path(e) for e in args.exclude}
        kept: list[Path] = []
        for p in orphans:
            try:
                rel = p.relative_to(lake_root)
            except ValueError:
                rel = p
            if rel in exclude_set or rel.as_posix() in exclude_set:
                excluded.append(p)
            else:
                kept.append(p)
        orphans = kept

    print(f"=== STRICT: lean_lib orphan gate ({args.name}) ===")
    print(f"Project: {lake_root}")
    print(f"Lakefile: {lakefile}")
    print(f"Selectors: {sorted(set(selectors))}")
    print(f"Files covered by globs: {len(covered)}")
    print(f"Files reachable via import from covered: {len(reachable)}")
    print(f"Total .lean walked: {len(all_lean)}")
    print()

    if excluded:
        print(
            f"EXCLUDED ({len(excluded)}) -- intentional orphans whitelisted via --exclude\n"
            f"  (e.g. skeleton aggregators declared in an EPIC's acceptance):\n"
        )
        for p in excluded:
            try:
                rel = p.relative_to(lake_root)
            except ValueError:
                rel = p
            print(f"  - {rel}")
        print()

    if not orphans:
        print("OK: every .lean file is either in a lean_lib globs, or imported from one.")
        return 0

    print(
        f"ORPHAN ({len(orphans)}) -- .lean file present in the lake but neither in a\n"
        f"  globs list, nor imported by a globs-covered file. ``lake build`` will not\n"
        f"  elaborate it; a green CI on the lake does not cover its axioms.\n"
        f"  Fix: add the file to an existing lean_lib's globs, ``import`` it from a\n"
        f"  covered file, or convert it to a documentation file outside the lake.\n"
    )
    for p in orphans:
        try:
            rel = p.relative_to(lake_root)
        except ValueError:
            rel = p
        print(f"  - {rel}")

    if args.strict:
        return 1
    return 0  # advisory default


if __name__ == "__main__":
    sys.exit(main())
