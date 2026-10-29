#!/usr/bin/env python3
r"""Gate: keep ``LEAN_INVENTORY.md`` in sync with the declared ``lean_lib``s.

Context (issue #21765): ``MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md`` is
the reference map of the Lean perimeter of ``GameTheory/``. It was reconciled on
2026-08-26 and never re-derived since: the ``lean_lib`` declarations added
afterwards -- ``Abstraction``, ``ProgramGames``, ``StackelbergBilevel`` and the
six ``Approval*`` libraries of ``social_choice_lean_peters`` -- never reached
the map. Measured on ``origin/main`` (2026-10-29): 9 libraries and 20 proof
files were invisible to any reader of the map.

A map that is only re-derived by hand drifts. This script re-derives the
library set mechanically and reports every gap: a library declared in a
lakefile that the map does not name (``MISSING_FROM_INVENTORY``).

Scope and deliberate limits:

* both lakefile dialects are read -- ``lakefile.lean`` (``lean_lib Name``,
  bare or quoted with ``« »``) and ``lakefile.toml`` (``[[lean_lib]]`` with a
  ``name`` key);
* a library counts as named in the map when the map contains a **code span**
  whose content starts with the library name (`` `Abstraction/`` ``,
  `` `ApprovalDefs` ``, `` `PetersTour.lean` ``, ...). A code span, not a bare
  word: prose must never satisfy the gate;
* the gate asks "is this library documented", not "does the map agree on every
  number". Re-deriving every count of the document is a re-writing of the
  document, not a gate, and it would fail on harmless edits;
* the reverse direction -- a library named in the map that no longer exists --
  is deliberately **not** checked: the map names lakes, module directories and
  files besides libraries, and separating them is a re-reading of the document.
  The complementary check (a declared library whose globs elaborate nothing) is
  already owned by ``check_lean_orphans.py --strict`` (#19015).

Usage::

    python scripts/lean/check_lean_inventory.py [--repo-root PATH]
        [--inventory REL_PATH] [--root REL_PATH] [--json]

Exit code: 0 when the map covers every declared library, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DEFAULT_ROOT = "MyIA.AI.Notebooks/GameTheory"
DEFAULT_INVENTORY = "MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md"

# Directories that never hold a lake of their own.
_EXCLUDE_TOP_DIRS = {".lake", ".git", "node_modules", ".venv", "__pycache__"}

# `lean_lib Name where` -- Name is bare, «quoted» or "quoted".
_LEAN_LIB_RE = re.compile(
    r"^[ \t]*lean_lib[ \t]+"
    r"(?:«(?P<guillemet>[^»]+)»|\"(?P<dquote>[^\"]+)\"|(?P<bare>[A-Za-z_][A-Za-z0-9_'.]*))",
    re.MULTILINE,
)

# Lean block comments, both `/-- ... -/` and `/! ... !/`.
_BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)

# A line comment runs to the end of the line.
_LINE_COMMENT_RE = re.compile(r"--[^\n]*")

# A Lean code span in markdown: `Abstraction/`, `PetersTour.lean`, ...
_CODE_SPAN_RE = re.compile(r"`([^`\n]+)`")

_TOML_LIB_BLOCK_RE = re.compile(r"\[\[lean_lib\]\](.*?)(?=\n\[|\Z)", re.DOTALL)
_TOML_NAME_RE = re.compile(r"^[ \t]*name[ \t]*=[ \t]*\"([^\"]+)\"", re.MULTILINE)


def strip_comments(text: str) -> str:
    """Remove Lean block comments, then line comments.

    Block comments are stripped first: a ``/-`` inside a block comment must
    not open a second one. The lakefiles of this repo carry no ``/-`` inside
    a line comment (checked 2026-10-29), so the order is unambiguous here.
    """
    return _LINE_COMMENT_RE.sub(" ", _BLOCK_COMMENT_RE.sub(" ", text))


def parse_lean_libs(text: str) -> list[str]:
    """Return the library names declared by a ``lakefile.lean``, in order.

    Duplicates are collapsed (a name may legitimately be declared twice, e.g.
    a second ``lean_lib`` for a different glob set).
    """
    names: list[str] = []
    for match in _LEAN_LIB_RE.finditer(strip_comments(text)):
        name = match.group("guillemet") or match.group("dquote") or match.group("bare")
        if name and name not in names:
            names.append(name)
    return names


def parse_toml_libs(text: str) -> list[str]:
    """Return the library names declared by a ``lakefile.toml``, in order."""
    names: list[str] = []
    for block in _TOML_LIB_BLOCK_RE.findall(text):
        match = _TOML_NAME_RE.search(block)
        if match and match.group(1) not in names:
            names.append(match.group(1))
    return names


def iter_lakefiles(root: Path) -> list[Path]:
    """Return every lakefile under ``root`` (``.lean`` and ``.toml``)."""
    found: list[Path] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file() or path.name not in ("lakefile.lean", "lakefile.toml"):
            continue
        if _EXCLUDE_TOP_DIRS.intersection(path.relative_to(root).parts):
            continue
        found.append(path)
    return found


def libs_of_lakefile(path: Path) -> list[str]:
    """Return the library names declared by one lakefile."""
    text = path.read_text(encoding="utf-8")
    if path.name.endswith(".toml"):
        return parse_toml_libs(text)
    return parse_lean_libs(text)


def inventory_mentions(inventory_text: str, name: str) -> bool:
    """Tell whether the map names a library, by code span.

    Only a code span counts: `` `Abstraction/`` ``, `` `ApprovalDefs` ``,
    `` `PetersTour.lean` `` or `` `ApprovalCore_en.lean` ``. A library name
    that appears in prose only is not a documented library.
    """
    prefixes = (name + "/", name + ".", name + "_")
    for span in _CODE_SPAN_RE.findall(inventory_text):
        span = span.strip()
        if span == name or span.startswith(prefixes):
            return True
    return False


def check(repo_root: Path, inventory_rel: str = DEFAULT_INVENTORY,
          root_rel: str = DEFAULT_ROOT) -> dict:
    """Compare the declared libraries with the map.

    Returns a report dict with the libraries found per lake and the libraries
    the map does not name.
    """
    inventory_path = repo_root / inventory_rel
    root = repo_root / root_rel
    report: dict = {
        "repo_root": str(repo_root),
        "inventory": inventory_rel,
        "root": root_rel,
        "lakes": [],
        "declared_libs": 0,
        "missing_from_inventory": [],
    }

    if not inventory_path.is_file():
        report["verdict"] = "ERROR"
        report["error"] = f"inventory not found: {inventory_rel}"
        return report
    if not root.is_dir():
        report["verdict"] = "ERROR"
        report["error"] = f"root not found: {root_rel}"
        return report

    inventory_text = inventory_path.read_text(encoding="utf-8")

    for lakefile in iter_lakefiles(root):
        lake_dir = lakefile.parent
        try:
            lake_rel = str(lake_dir.relative_to(repo_root)).replace("\\", "/")
        except ValueError:
            lake_rel = str(lake_dir)
        libs = libs_of_lakefile(lakefile)
        report["lakes"].append({"lake": lake_rel, "libs": libs})
        report["declared_libs"] += len(libs)
        for lib in libs:
            if not inventory_mentions(inventory_text, lib):
                report["missing_from_inventory"].append({"lake": lake_rel, "lib": lib})

    findings = len(report["missing_from_inventory"])
    report["findings"] = findings
    report["verdict"] = "OK" if findings == 0 else "DRIFT"
    return report


def render_text(report: dict) -> str:
    """Render the report as the human-readable form of the gate."""
    lines: list[str] = []
    if report.get("verdict") == "ERROR":
        lines.append(f"ERROR: {report.get('error')}")
        return "\n".join(lines)

    lines.append(f"INVENTORY: {report['inventory']}")
    lines.append(f"ROOT: {report['root']}")
    lines.append(f"LAKES: {len(report['lakes'])} | LIBS DECLARES: {report['declared_libs']}")
    lines.append("")

    missing = report["missing_from_inventory"]
    if missing:
        lines.append(
            f"MISSING_FROM_INVENTORY ({len(missing)}) -- bibliotheque declaree dans un "
            "lakefile, absente de la carte :"
        )
        for item in missing:
            lines.append(f"  - {item['lib']}  (lake: {item['lake']})")
        lines.append("")

    if not missing:
        lines.append(
            "OK: chaque bibliotheque declaree dans un lakefile est nommee dans la carte."
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie que LEAN_INVENTORY.md couvre les lean_lib declarees.")
    parser.add_argument("--repo-root", default=None,
                        help="racine du depot (defaut: la racine de ce fichier)")
    parser.add_argument("--inventory", default=DEFAULT_INVENTORY,
                        help="chemin de la carte, relatif a la racine du depot")
    parser.add_argument("--root", default=DEFAULT_ROOT,
                        help="perimetre GameTheory a inspecter, relatif a la racine")
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root) if args.repo_root else Path(__file__).resolve().parents[2]
    report = check(repo_root, args.inventory, args.root)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(render_text(report))
    return 1 if report["verdict"] == "DRIFT" else 0


if __name__ == "__main__":
    sys.exit(main())
