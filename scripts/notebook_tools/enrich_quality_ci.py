#!/usr/bin/env python3
"""Per-PR enrich-quality REGRESSION gate (CoursIA #13410 / roo-extensions #3374).

Sibling of cell_order_ci.py (Epic #3240): compares the HIGH enrich-quality
findings of a notebook (scripts/notebook_tools/scan_enrich_quality.py)
between its base revision and its PR (head) revision, and fails only on a
*regression* -- a HIGH finding present in head that was NOT already present
in base. Pre-existing findings (legacy leaks, main-space anchors of earlier
enrich waves) do not block unrelated PRs; a brand-new notebook (no base)
must be clean.

Base-vs-head findings (classes (b) MD_REWRITE / MD_SURVIVAL_LOW and (c)
DIACRITICS_LOSS) only exist when a --base is given and are inherently
relative to it, so they always count as new.

A finding's identity is its (category, message) pair. Messages embed the
anchor index / href / shared tokens / survival counts, so they are specific
enough that moving a defect around does not mask a newly introduced one.

Body marker (#17744, symmetric to #13491/#14532): an ANNOUNCED rewrite --
the deliverable of Epic #14442's D3 grains, which deliberately rewrite
introductions to strip Git chronology -- trips MD_REWRITE by construction
(no honest rewrite keeps 25% of the base verbatim). The marker

    enrich-quality: reecriture assumee -- <notebook> : <raison>

downgrades ONLY the base-vs-head rewrite-signature categories
(MD_REWRITE / MD_SURVIVAL_LOW) for the named notebook. Absolute defect
classes (anchors, hrefs, diacritics loss, ...) remain blocking: a marker
can never mask a real defect, only the "this is a rewrite" signature which
is the announced intent. Trace preserved: downgraded findings print as
MD_REWRITE_JUSTIFIED_BY_BODY, never silently dropped.

Usage:
    enrich_quality_ci.py --base <base.ipynb|NONE> --head <head.ipynb> [--repo-root <dir>]
                          [--pr-body-file <file>]

The PR body can also be supplied via the ENRICH_QUALITY_PR_BODY env var
(the CI-recommended channel, same policy as MD_CONTENT_LOSS_PR_BODY).

Exit codes:
    0 - no new HIGH findings in head (or head unreadable -> nothing to gate)
    1 - one or more NEW HIGH findings introduced by head (regression)
"""

import argparse
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from scan_enrich_quality import scan_notebook  # noqa: E402


def high_signatures(nb_path: str | None, base_path: str | None, repo_root: Path) -> set[tuple[str, str]]:
    """Set of (category, message) for HIGH findings of a notebook, or empty."""
    if not nb_path or nb_path == "NONE" or not Path(nb_path).exists():
        return set()
    rep = scan_notebook(Path(nb_path), base=Path(base_path) if base_path else None,
                        repo_root=repo_root)
    if rep.get("error"):
        return set()
    return {(f["category"], f["message"]) for f in rep["findings"] if f["severity"] == "HIGH"}


# Base-vs-head rewrite-signature categories (#17744): these only exist when a
# --base is given and say "the head rewrote the base", which is the announced
# deliverable of Epic #14442's D3 grains. DIACRITICS_LOSS is also base-vs-head
# but signals a real content defect (accents lost), never exempted.
JUSTIFIED_BY_BODY_CATEGORIES = {"MD_REWRITE", "MD_SURVIVAL_LOW"}

_MARKER_RE = re.compile(
    r"^enrich-quality\s*:\s*re[eé]criture\s+assum[eé]+\s*(?:--|—)\s*"
    r"(?P<nb>[^\s:]+)"
    r"\s*:\s*(?P<reason>\S.*?)$",
    re.MULTILINE,
)


def _parse_pr_body_markers(pr_body: str, notebook_path: Path) -> bool:
    """Parse ``enrich-quality: reecriture assumee -- <nb> : <raison>`` markers.

    Returns True when the body carries a valid marker for THIS notebook.
    Same policy as the sibling gates (#13491 / #14532): em-dash tolerated
    (GitHub editors transpose ``--``), notebook token compared as basename
    OR path ending in ``/basename`` (absorbs CI-runner cwd variants), reason
    must be non-empty. A malformed marker is inert (returns False).
    """
    if not pr_body:
        return False
    nb_name = notebook_path.name
    for m in _MARKER_RE.finditer(pr_body):
        nb_token = m.group("nb").rstrip("/").rstrip(":")
        if nb_token == nb_name or nb_token.endswith("/" + nb_name):
            return True
    return False


def _read_pr_body(cli_value: str | None) -> str:
    """Resolve the PR body from --pr-body-file or ENRICH_QUALITY_PR_BODY.

    The env var is the CI-recommended channel (avoids the CodeQL
    actions/code-injection pattern of interpolating the body into the shell,
    same rationale as MD_CONTENT_LOSS_PR_BODY); the flag serves local
    invocations and tests.
    """
    if cli_value:
        try:
            return Path(cli_value).read_text(encoding="utf-8", errors="replace")
        except OSError:
            return ""
    env_body = os.environ.get("ENRICH_QUALITY_PR_BODY", "")
    # An env-file indirection keeps long bodies out of the workflow YAML.
    env_file = os.environ.get("ENRICH_QUALITY_PR_BODY_FILE", "")
    if not env_body and env_file:
        try:
            return Path(env_file).read_text(encoding="utf-8", errors="replace")
        except OSError:
            return ""
    return env_body


class BaseNotResolvedError(RuntimeError):
    """Raised when --base was provided but its content could not be located.

    Distinguishes the silent-empty-base case (which fabricates new REGRESSION
    verdicts) from the legitimate NONE case (brand-new notebook, no baseline).
    The CI workflow (enrich-quality-gate.yml) already extracts `git show` to a
    temp file before invoking this script, so it is immune; the bug bites the
    worktree CLI invocation `--base HEAD`. See issue #17424.
    """


def resolve_base(base_arg: str | None, head_path: str, repo_root: Path) -> str | None:
    """Return a path-like string usable by ``high_signatures``, or raise.

    Accepts ``None`` (no baseline), ``NONE`` (literal brand-new notebook), or
    a filesystem path that exists. Anything else (a git ref like ``HEAD`` or
    ``HEAD~1``) raises :class:`BaseNotResolvedError` so the caller fails loudly
    instead of rendering the base silently empty.
    """
    if base_arg is None or base_arg == "" or base_arg == "NONE":
        return base_arg
    if Path(base_arg).exists():
        return base_arg
    raise BaseNotResolvedError(
        f"--base {base_arg!r} is neither a readable path nor the literal NONE. "
        f"Pass an extracted notebook file (e.g. `git show {base_arg}:<head_path> > /tmp/base.ipynb`), "
        f"or use --base NONE for a brand-new notebook. See issue #17424."
    )


def regressions(base_path: str | None, head_path: str | None, repo_root: Path) -> list[tuple[str, str]]:
    """HIGH findings present in head but not in base (sorted, deterministic)."""
    # The base is scanned STANDALONE (no base-of-base): head-only checks run
    # on it, relative checks ((b)/(c)) cannot apply to it.
    base = high_signatures(base_path, None, repo_root)
    head = high_signatures(head_path, base_path, repo_root)
    return sorted(head - base)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Enrich-quality per-PR regression gate.")
    ap.add_argument("--base", help="path to the base notebook (already extracted to disk), or NONE for a new file. Issue #17424: --base does NOT resolve git revs.")
    ap.add_argument("--head", required=True, help="head (PR) revision of the notebook, at its repo path")
    ap.add_argument("--repo-root", default=None,
                    help="tree against which hrefs resolve (default: the repo containing this script)")
    ap.add_argument("--pr-body-file", default=None,
                    help="PR body to read 'enrich-quality: reecriture assumee' markers from "
                         "(#17744); falls back to ENRICH_QUALITY_PR_BODY[_FILE] env.")
    args = ap.parse_args(argv)

    repo_root = Path(args.repo_root).resolve() if args.repo_root else Path(__file__).resolve().parent.parent.parent

    try:
        resolved_base = resolve_base(args.base, args.head, repo_root)
    except BaseNotResolvedError as exc:
        print(f"enrich_quality_ci: {exc}", file=sys.stderr)
        return 2  # distinct from REGRESSION=1 and OK=0 so CI can branch on it.

    new = regressions(resolved_base, args.head, repo_root)
    if not new:
        return 0

    body_justifies = _parse_pr_body_markers(_read_pr_body(args.pr_body_file), Path(args.head))
    justified = [f for f in new if body_justifies and f[0] in JUSTIFIED_BY_BODY_CATEGORIES]
    blocking = [f for f in new if f not in justified]

    if justified:
        print(f"[JUSTIFIED_BY_BODY] {len(justified)} base-vs-head rewrite finding(s) assumee(s)"
              f" par marqueur de body (#17744):")
        for category, message in justified:
            print(f"  [{category}_JUSTIFIED_BY_BODY] {message}")

    if not blocking:
        return 0

    print(f"REGRESSION in {args.head}: {len(blocking)} new HIGH enrich-quality finding(s):")
    for category, message in blocking:
        print(f"  [{category}] {message}")
    print("\nGround-truth each finding (the signal is not a verdict, rule G.1). The anchor")
    print("convention is: code[N] = the N-th CODE cell, 0-based, counted at HEAD.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
