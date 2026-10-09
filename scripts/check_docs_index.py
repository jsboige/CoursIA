#!/usr/bin/env python3
"""Check that every live doc under ``docs/`` is reachable from the docs index.

The docs index (``docs/README.md``) states its own metric: a doc counts as
indexed when a reader can *reach* it from the index -- directly, or through a
sub-directory index such as ``docs/lean/README.md``. This organ measures that
metric, and only that one:

* an **orphan** (no inbound link from any scanned file) is
  ``scripts/check_docs_links.py --orphans``;
* a **broken link** is ``scripts/check_docs_links.py --check``;
* this organ answers a third, distinct question: *can a reader find this doc
  from the index at all?* A doc linked from one sibling notebook report is not
  an orphan, yet it remains unfindable from the index.

Traversal is deliberately restricted to files under ``docs/``: the closure
cannot escape to the repository root and come back, so the organ can only
under-credit reachability, never over-credit it (fail-closed).

Usage:
    python scripts/check_docs_index.py                      # Report unreachable docs
    python scripts/check_docs_index.py --json               # Machine-readable verdict
    python scripts/check_docs_index.py --expect-unreachable 3   # Positive control

Positive control
----------------
``--expect-unreachable N`` arms an in-band control: the scan must find AT LEAST
``N`` unreachable docs, otherwise it exits 2. Without it, "every doc is
reachable" is indistinguishable from a dead detection path (same model as
``scripts/check_docs_links.py --expect-broken``). Point it at a tree where a
doc link was deliberately removed: a healthy organ renders rc=1 with the
finding, a dead one renders rc=2.

Exit codes:
    0 = every live doc is reachable (or the run is a positive control that held)
    1 = at least one live doc is unreachable
    2 = error during execution, or positive control unmet
"""

import argparse
import json
import re
import sys
from collections import deque
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent

# The index that owns the reachability claim. Its `## Racine (docs/)` table
# carries the metric in prose; this organ is what holds the claim true.
INDEX_REL = "docs/README.md"

# Frozen by design: `docs/archive/` is a stock to drain, not documentation to
# navigate (#13748). Sub-directory `_archive/` follows the repo-wide
# `_archive/` convention and is out of the live set for the same reason.
FROZEN_PARTS = {"archive", "_archive"}

# Markdown link targets, resolved relative to the linking file.
LINK_RE = re.compile(r"\]\(([^)]+)\)")


def is_live_doc(path: Path, docs_root: Path) -> bool:
    """A live doc is any ``*.md`` under ``docs/`` outside the frozen dirs."""
    try:
        parts = path.relative_to(docs_root).parts
    except ValueError:
        return False
    return not (set(parts) & FROZEN_PARTS)


def link_targets(source: Path) -> list[Path]:
    """Resolve the relative markdown targets of ``source`` (absolute paths)."""
    try:
        text = source.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    out = []
    for match in LINK_RE.finditer(text):
        raw = match.group(1).split("#")[0].split("?")[0].strip()
        if not raw or raw.startswith(("http:", "https:", "mailto:", "tel:")):
            continue
        try:
            out.append((source.parent / unquote(raw)).resolve())
        except (OSError, ValueError):
            continue
    return out


def find_unreachable(root: Path | None = None) -> tuple[list[str], int]:
    """Return ``(unreachable_rel_paths, live_count)`` for the tree at ``root``.

    ``root`` defaults to :data:`REPO_ROOT`, resolved at call time so tests can
    point the organ at a synthetic tree. Breadth-first closure from the index,
    following markdown links between files under ``docs/`` only.
    Deterministic: the returned list is sorted.
    """
    root = REPO_ROOT if root is None else Path(root)
    docs_root = (root / "docs").resolve()
    index = root / INDEX_REL
    if not index.is_file():
        raise FileNotFoundError(f"index introuvable : {INDEX_REL}")

    live = sorted(p for p in docs_root.rglob("*.md") if is_live_doc(p, docs_root))

    seen: set[Path] = {index.resolve()}
    queue: deque[Path] = deque([index.resolve()])
    while queue:
        current = queue.popleft()
        for target in link_targets(current):
            if target in seen or target.suffix != ".md" or not target.is_file():
                continue
            try:
                target.relative_to(docs_root)
            except ValueError:
                continue  # outside docs/: never followed (fail-closed)
            if not is_live_doc(target, docs_root):
                continue
            seen.add(target)
            queue.append(target)

    unreachable = sorted(
        p.relative_to(root).as_posix() for p in live if p.resolve() not in seen
    )
    return unreachable, len(live)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Verifie que chaque doc vivant sous docs/ est atteignable "
                    "depuis l'index docs/README.md.")
    parser.add_argument("--json", action="store_true",
                        help="Verdict machine (unreachable, live, ok)")
    parser.add_argument("--expect-unreachable", type=int, default=None,
                        metavar="N",
                        help="Controle positif : exiger au moins N docs "
                             "inatteignables, sinon exit 2")
    args = parser.parse_args()

    try:
        unreachable, live = find_unreachable()
    except Exception as exc:  # noqa: BLE001 - any failure is exit 2, per contract
        print(f"Error: {exc}", file=sys.stderr)
        sys.exit(2)

    reached = live - len(unreachable)
    ok = not unreachable

    if args.json:
        print(json.dumps({"ok": ok, "live": live, "reachable": reached,
                          "unreachable": unreachable}, ensure_ascii=False,
                         indent=2))

    if args.expect_unreachable is not None and len(unreachable) < args.expect_unreachable:
        print(f"CONTROLE POSITIF NON ATTEINT : {len(unreachable)} inatteignable(s) "
              f"trouve(s), {args.expect_unreachable} exige(s) -- chemin de "
              f"detection suspect.", file=sys.stderr)
        sys.exit(2)

    if not args.json:
        if unreachable:
            print(f"{len(unreachable)} doc(s) vivant(s) inatteignable(s) depuis "
                  f"{INDEX_REL} ({reached}/{live} atteignables) :")
            for rel in unreachable:
                print(f"  {rel}")
        else:
            print(f"OK: {live} doc(s) vivant(s) sous docs/, tous atteignables "
                  f"depuis {INDEX_REL}.")

    sys.exit(1 if unreachable else 0)


if __name__ == "__main__":
    main()
