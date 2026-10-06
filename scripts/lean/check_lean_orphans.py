#!/usr/bin/env python3
r"""Strict gate (issue #19015): catch ``.lean`` files that no ``lean_lib`` builds.

Context (#19015): ``lake -R build`` with no argument compiles only the
``@[default_target]`` libs. A file ``Foo.lean`` that is (a) not in any
``lean_lib``'s ``globs`` (or ``roots``) list, and (b) not ``import``-ed by any
other source that IS built, is never elaborated -- and a green CI on the
lake says nothing about it. Instance measured 2026-10-03: ``ApprovalDefs``
on ``social_choice_lean_peters`` passed every gate while compiling nothing.

This script closes that gap by parsing ``lakefile.lean``, unioning the globs
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
- ``globs`` is parsed as the literal Lean list ``#[`Name, `Name2, ...]`` or
  the legacy ``roots`` form ``#[`Name]`` (``Name`` as the umbrella). The
  script does not evaluate the Lake DSL; the form is the same on every
  lakefile in this repo as of 2026-10-03 (audited on ``origin/main``).
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

# Same excludes as check_target_coverage.py -- the "compiled module" walk
# agrees on what is and is not a Lake source file.
_EXCLUDE_TOP_DIRS = {".lake", ".git", "node_modules", ".venv", "_peters"}


def _read_libs_and_globs(lakefile_text: str) -> list[tuple[str, list[str]]]:
    r"""Parse every ``lean_lib NAME [where ... globs := #[...]]`` block.

    Returns a list of ``(name, globs)`` pairs in declaration order. The
    ``globs`` list contains the literal Lean tokens between the backticks;
    e.g. ``#[`Conway, `Conway_en]`` -> ``["Conway", "Conway_en"]``.

    Also recognises the Lake ``.submodules `Name`` directive, which expands
    to every submodule of namespace ``Name`` (incl. all sibling subnamespaces,
    e.g. ``Knots.Foo``, ``Knots_en.Bar``). The literal token ``.submodules``
    is NOT a glob but a directive that pre-expands to a recursive glob; we
    record it as a synthetic ``__submodules__\`Knots`` marker that the
    ``_covered_modules`` helper handles separately.

    The Lake DSL permits comments between the ``where`` keyword and the
    ``globs := #[...]`` assignment; the body of the where block is matched
    greedily up to the next ``lean_lib`` / ``lean_exe`` / top-level decl
    or the file end. The regex is intentionally narrow: every lakefile
    in the repo (2026-10-03 audit) uses the same form, and broadening
    it would risk silently mis-parsing a future construct.
    """
    # Step 1: locate every ``lean_lib <name>`` (with optional ``@[default_target]``).
    # The ``@[default_target]`` attribute is OPTIONAL — the Lake native default
    # is ``roots := #[name], globs := roots.map Glob.one`` (LeanLibConfig.lean:30-46
    # on Lean 4 v4.33.0), so a ``lean_lib Foo where`` without ``globs`` already
    # builds ``Foo.lean`` at the lake root. Accepting both forms keeps the parser
    # faithful to the source.
    decl_re = re.compile(
        r"(?:@\[default_target\]\s*)?lean_lib\s+(?P<name>[«`]?[\w«»`-]+[»`]?)",
        re.MULTILINE,
    )
    # Step 2: extract the globs list ``#[`Foo, `Bar, .submodules `Baz, ...]``
    # from a chunk of text. The inner of ``#``[ ... ``]`` is everything up
    # to the matching ``]``; backticks and commas inside the inner are token
    # separators, not regex delimiters. A simple split on commas is more
    # robust than nested regex capture of ``\`[^\`]+\`` (which greedily eats
    # past the first comma). The ``.submodules`` directive is preserved as
    # one ``.submodules \`Knots`` token and post-processed below.
    globs_re = re.compile(
        r"globs\s*:=\s*#\[\s*(?P<inner>[^\]]*)\]",
        re.MULTILINE,
    )
    decls = list(decl_re.finditer(lakefile_text))
    libs: list[tuple[str, list[str]]] = []
    for i, m in enumerate(decls):
        name = m.group("name").strip("«»`").strip()
        # Body of the where block = from the end of this decl to the
        # start of the next ``lean_lib`` / ``lean_exe`` / top-level decl.
        body_start = m.end()
        body_end = decls[i + 1].start() if i + 1 < len(decls) else len(lakefile_text)
        # Also stop at any other top-level Lake decl that ends the block.
        for stop in ("lean_exe ", "require ", "package ", "script ", "extern_lib "):
            idx = lakefile_text.find(stop, body_start)
            if idx > 0 and idx < body_end:
                body_end = idx
                break
        body = lakefile_text[body_start:body_end]
        # Strip Lake ``--`` line comments before matching ``globs := #[...]``.
        # Some lakefiles in this repo carry an in-body example of the very
        # construct (``-- \`globs := #[`Foo, `Foo_en]``), and the naive
        # regex would silently pick that example up instead of the real
        # clause (c27 regression found by reading the c26 adjoint reserve
        # verbatim against ``conway_cgt_lean/lakefile.lean:62``).
        body_no_comments = re.sub(r"--[^\n]*", "", body)
        g = globs_re.search(body_no_comments)
        if not g:
            # No ``globs := #[...]`` clause — apply the Lake native default
            # (``LeanLibConfig.lean:30-46`` on v4.33.0): ``globs = roots.map Glob.one``
            # with ``roots = #[name]``. So ``lean_lib Foo where`` builds ``Foo.lean``
            # at the lake root by default; treating this as ``globs = []`` would
            # mis-report ``Foo.lean`` as an orphan on every lib without an explicit
            # ``globs := #[...]`` clause.
            libs.append((name, [name]))
            continue
        globs_raw = g.group("inner")
        # Split on top-level commas only (not on commas inside ``[...]``).
        # The ``#[...]`` inner is flat in every lakefile in the repo (no
        # nested lists), so a plain ``split(",")`` is correct; we strip
        # backticks and whitespace per token, dropping empties.
        raw_tokens = [tok.strip() for tok in globs_raw.split(",")]
        globs: list[str] = []
        for tok in raw_tokens:
            tok = tok.strip()
            if not tok:
                continue
            # ``.submodules `Name`` directive -- encode as a synthetic glob
            # ``__submodules__\`Name`` that the coverage helper recognises.
            m_sub = re.match(r"\.submodules\s+`?([\w«»`-]+)`?", tok)
            if m_sub:
                sub_name = m_sub.group(1)
                globs.append(f"__submodules__`{sub_name}")
                continue
            # Backtick-quoted token: ``\`Foo`` or ``\`Foo\``` (one or two
            # backticks). Lake accepts both forms. The repo (2026-10-03
            # audit) uses the single-backtick form predominantly.
            m_bt = re.match(r"`+([^`]+)`*", tok)
            if m_bt:
                globs.append(m_bt.group(1))
                continue
            # Bare token (no backticks): keep as-is.
            globs.append(tok)
        libs.append((name, globs))
    return libs


def _glob_covers_file(glob_token: str, rel_path: Path) -> bool:
    r"""Match a single .lean file path against one ``globs`` token.

    The tokens come in three flavours observed in the repo (2026-10-03 audit):
    - ``Name``        : the umbrella root ``Name.lean`` (file at lake root).
    - ``Name.*``      : every file under ``Name/`` (recursive, ``.lean`` only).
    - ``Name_en``     : the bilingual sibling ``Name_en.lean`` at lake root.
    Anything else is treated as a literal stem match in the lake root.
    """
    parts = rel_path.parts
    stem = rel_path.stem
    if glob_token == stem:
        return True
    if glob_token.endswith(".*"):
        prefix = glob_token[:-2]
        if parts and (parts[0] == prefix or parts[0] == prefix + "_en"):
            return True
    if glob_token == stem + "_en" and rel_path == Path(stem + "_en.lean"):
        return True
    # Plain token: only matches the umbrella ``<Name>.lean`` at lake root.
    if "." not in glob_token and "/" not in glob_token:
        if len(parts) == 1 and parts[0] == glob_token + ".lean":
            return True
    return False


def _covered_modules(lake_root: Path, globs: list[str]) -> set[Path]:
    r"""Return the set of .lean files explicitly listed by the union of globs.

    Faithful to Lake's native ``Glob.matches`` (Lake/Config/Glob.lean:46-50 on
    Lean 4 v4.33.0) and ``LeanLibConfig.isBuildableModule``
    (Lake/Config/LeanLibConfig.lean:75-77):

      - ``Glob.one n``         : ``m == n`` (single leaf at lake root)
      - ``Glob.submodules n``  : ``n.isPrefixOf m && n != m`` (strict)
      - ``Glob.andSubmodules n``: ``n.isPrefixOf m`` (non-strict: leaf + submodules)

    The DSL sugar ``\`Name.*`` desugars to ``Glob.andSubmodules \`Name``
    (Lake/Config/Glob.lean:30-32), and ``.submodules \`Name`` to
    ``Glob.submodules \`Name``.

    Crucially, **none of these constructs perform any implicit i18n expansion**:
    ``_en`` siblings must be declared as separate tokens in ``globs := #[...]``
    (``Foo`` covers only ``Foo.lean``; ``Foo_en`` is a different plain token
    covering ``Foo_en.lean``). An earlier version of this helper added
    ``_en`` siblings implicitly, which silently turned orphans into covered
    files on lakes that happened to declare the FR token only — a false
    negative against the very gate the script exists to provide.

    Three token flavours are recognised here, mapped from the regex above:

      - ``Name``        (plain):         covers ``<lake_root>/<Name>.lean`` only.
      - ``Name.*``      (andSubmodules): covers ``<lake_root>/<Name>.lean`` and
                                        every ``<lake_root>/<Name>/X.lean`` for
                                        ``X != Name`` (non-strict prefix).
      - ``__submodules__\`Name`` (DSL): covers every ``<lake_root>/<Name>/X.lean``
                                        for ``X != Name`` (strict prefix).
    """
    covered: set[Path] = set()
    for g in globs:
        if g.startswith("__submodules__`"):
            # ``.submodules `Name`` (DSL sugar for ``Glob.submodules \`Name``) :
            # strict-prefix submodule glob, the leaf ``Name.lean`` at the lake
            # root is NOT covered (matches would require ``Name != Name``).
            prefix = g[len("__submodules__`"):].rstrip("`")
            candidate_dir = lake_root / prefix
            if candidate_dir.is_dir():
                for p in candidate_dir.rglob("*.lean"):
                    covered.add(p)
            continue
        if g.endswith(".*"):
            # ``\`Name.*`` desugars to ``Glob.andSubmodules \`Name``: the leaf
            # ``Name.lean`` at the lake root IS covered (``Name IS prefix of
            # Name``) and every ``Name/X.lean`` for ``X != Name`` is too.
            prefix = g[:-2]
            leaf = lake_root / f"{prefix}.lean"
            if leaf.is_file():
                covered.add(leaf)
            candidate_dir = lake_root / prefix
            if candidate_dir.is_dir():
                for p in candidate_dir.rglob("*.lean"):
                    covered.add(p)
            continue
        # Plain token (``\`Name``) : ``Glob.one Name`` matches ``Name == m``
        # only — covers the single leaf ``<lake_root>/<Name>.lean``.
        leaf = lake_root / f"{g}.lean"
        if leaf.is_file():
            covered.add(leaf)
    return covered


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
        help="Path to the lakefile.lean declaring the libs. Read for the globs.",
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
        lakefile_text = lakefile.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        print(f"ERROR ({args.name}): cannot read {lakefile}: {e}")
        return 2

    libs = _read_libs_and_globs(lakefile_text)
    all_globs = [g for _, globs in libs for g in globs]
    covered = _covered_modules(lake_root, all_globs)
    all_lean = _discover_lean_files(lake_root)
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
    print(f"Declared lean_libs: {len(libs)}  ->  globs union: {sorted(set(all_globs))}")
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
