#!/usr/bin/env python3
"""Per-PR cell-ordering REGRESSION gate (Epic #3240).

Compares the HIGH cell-ordering findings of a notebook between its base revision
and its PR (head) revision and fails only on a *regression* -- a HIGH finding
present in head that was NOT already present in base. Pre-existing HIGH findings
in legacy notebooks therefore do NOT block unrelated PRs; they are tracked
separately under Epic #3240. A brand-new notebook (no base) must be clean: with
an empty base, every HIGH finding counts as a regression.

A finding's identity is its (category, message) pair -- the message embeds the
offending section/exercise numbers, so it is specific enough that moving a bug
around does not mask a newly introduced one.

Usage:
    cell_order_ci.py --base <base.ipynb|NONE> --head <head.ipynb>
    cell_order_ci.py --base-ref <git-ref> --head <head.ipynb>

--base and --head are FILE PATHS to the notebook revisions on disk -- NOT git
refs. Passing a git ref (e.g. `--head HEAD` or `--base main`) is a usage error:
the path does not exist, and the gate fails loudly with a SystemExit naming the
cause, instead of silently reporting "no regression". `NONE` is the only
accepted non-path value for --base; it means "new notebook, no base".

--base-ref (#22209, absorption dans la voie rapide) is the second entry point:
the base revision is read from the git blob `<ref>:<head path>`, reproducing
the loop the standalone workflow ran (`git show "$BASE:$nb"`). A blob absent
from the ref means "new notebook": the base signature set is empty, exactly the
`NONE` semantics of the original loop (`git cat-file -e` guard). The fast lane
passes `{base_ref}` = `origin/<base branch>`; `--base` and `--base-ref` are
mutually exclusive.

Exit codes:
    0 - no new HIGH findings in head (or head file present but unreadable -> nothing to gate)
    1 - one or more NEW HIGH findings introduced by head (regression)
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from scan_cell_ordering import scan_notebook  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]


def high_signatures(path: str | None) -> set[tuple[str, str]]:
    """Set of (category, message) for HIGH findings of a notebook, or empty.

    `None`/`"NONE"` mean "no base revision" and yield the empty set. A path
    that was provided but does not exist is a usage error (a git ref is not a
    file path): it raises SystemExit instead of silently reporting nothing.
    """
    if not path or path == "NONE":
        return set()
    p = Path(path)
    if not p.exists():
        raise SystemExit(
            "cell_order_ci: --base/--head attend un CHEMIN de fichier, "
            f"reçu {path!r} qui n'existe pas (une ref git ne convient pas)"
        )
    return _high_signatures_of_file(p)


def _high_signatures_of_file(p: Path) -> set[tuple[str, str]]:
    rep = scan_notebook(p)
    if rep.get("error"):
        return set()
    return {(f["category"], f["message"]) for f in rep["findings"] if f["severity"] == "HIGH"}


def high_signatures_from_ref(ref: str, head_path: str) -> set[tuple[str, str]]:
    """Base signature set read from the git blob `<ref>:<head_path>` (#22209).

    Fidelity to the standalone workflow's loop: `git cat-file -e "$BASE:$nb"`
    decided base-vs-new-file, and a blob absent from the base ref means a NEW
    notebook (empty base -- every HIGH finding counts). An unreadable blob
    (unreadable JSON) yields the empty set too, same as `high_signatures` on
    an unreadable base file.
    """
    proc = subprocess.run(
        ["git", "show", f"{ref}:{head_path}"],
        cwd=REPO_ROOT, capture_output=True,
    )
    if proc.returncode != 0:
        return set()
    tmp = tempfile.NamedTemporaryFile(suffix=".ipynb", delete=False)
    try:
        tmp.write(proc.stdout)
        tmp.close()
        return _high_signatures_of_file(Path(tmp.name))
    finally:
        Path(tmp.name).unlink(missing_ok=True)


def regressions(base_path: str | None, head_path: str | None) -> list[tuple[str, str]]:
    """HIGH findings present in head but not in base (sorted, deterministic)."""
    base = high_signatures(base_path)
    head = high_signatures(head_path)
    return sorted(head - base)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Cell-ordering per-PR regression gate.")
    group = ap.add_mutually_exclusive_group()
    group.add_argument("--base", help="base revision of the notebook, or NONE for a new file")
    group.add_argument("--base-ref", dest="base_ref",
                       help="git ref whose blob <ref>:<head path> is the base "
                            "revision (absent from the ref = new file). "
                            "Entree de la voie rapide (#22209).")
    ap.add_argument("--head", required=True, help="head (PR) revision of the notebook")
    args = ap.parse_args(argv)

    if args.base_ref:
        base = high_signatures_from_ref(args.base_ref, args.head)
        head = high_signatures(args.head)
        new = sorted(head - base)
    else:
        new = regressions(args.base, args.head)
    if not new:
        return 0

    print(f"REGRESSION in {args.head}: {len(new)} new HIGH cell-ordering finding(s):")
    for category, message in new:
        print(f"  [{category}] {message}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
