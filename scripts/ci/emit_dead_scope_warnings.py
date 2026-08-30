#!/usr/bin/env python3
"""emit_dead_scope_warnings.py -- GitHub Actions annotation emitter for #13129.

The lane-claim-guard advisory job (#10223) calls this helper with the PR body
file. The helper extracts the Grain: lane, walks the PR body for any
`paths: <glob>, ...` clause (the lane's declared scope), and emits one GitHub
`::warning::` annotation per glob that matches zero tracked files in the repo.
A SECOND channel emits `::notice::` annotations for the missing-comma motif
(B of #13129): when a glob is SPACE-separated and at least two of its
fragments LOOK path-shaped, the parser treated the whole string as ONE glob
that matches nothing -- the lane almost certainly meant a comma between them.

The annotation format `::warning file=<path>,title=...::msg` is rendered by
GitHub Actions in the PR Checks panel and the Files tab. The lane sees the
hint where they can still correct the typo before pushing again.

Non-blocking by design: a missing path can be a typo (motif A/C of #13129)
or a legitimate future file (#12740). The helper calls into `check_lane_claim.py`
directly for the `_empty_scope_in` walker (which uses the same `git ls-files`
mechanism as `_run_check`) and `_suggest_path_correction` (which mirrors the
proximity heuristic introduced by this PR). The caller shell iterates over
the printed lines and emits them; the helper never blocks the advisory job.

#13486: motif B detection (missing comma between globs) lives HERE -- the
SINGLE machinerie for hints. `check_lane_claim.py` was historically the
first host (it had `_looks_like_missing_comma`), but the #13129 acceptance
specifies a single pipeline; the helper exposes the function as
`_missing_comma_tokens(glob)` and `check_lane_claim.py` delegates.

#13486 acceptance (3) : `dead_scope_suggestions` is a JSON line emitted on
stdout AFTER the GitHub annotations, structured as
`{"dead_scope_suggestions": [{"glob": "<g>", "hint": "<h>", "tokens": [...]}]}`
consumable by lane scripts / `pick_idle_grain.py`. When no suggestion fires,
the line is `{"dead_scope_suggestions": []}` -- consumers can rely on the
key being present (cheap parser), not on its non-emptiness.

Exit codes:
  0  annotations printed (or no dead globs found)
  1  body file unreadable, or git walk failed -- the caller should still
     exit 0 (advisory job, fail-CLOSED via `|| true`).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
_SCRIPTS_DIR = _REPO_ROOT / "scripts"

# Inline a minimal `paths:` clause extractor. The full parser lives in
# `check_lane_claim._extract_paths_clause`; we re-implement it here so the
# helper does not depend on the GRAIN marker-line grammar (the PR body
# marks `Grain:` on line 1 but the actual `paths:` clause lives in the
# trailing intent of any [CLAIMED] / [OVERRIDE] / [RELEASED] / [CLAIMED-AMEND]
# marker line in the body). For the advisory case we only need glob lists.
# Two shapes are accepted: inline (`-- paths: a, b`) and on the next line
# (the writer broke the marker line for readability). The terminating class
# matches end-of-line, the annotation separator (` -- <prose>`), or end of
# string -- the regex stops greedily at the FIRST such terminator.
_PATHS_INLINE_RE = re.compile(
    r"--\s*paths\s*:\s*(.+?)(?=\s*(?:--|—|–)|\n\s*\n|$)",
    re.IGNORECASE | re.DOTALL,
)
_PATHS_LINE_RE = re.compile(
    r"(?:^|\n)\s*paths\s*:\s*(.+?)(?=\s*(?:--|—|–)|\n\s*\n|$)",
    re.IGNORECASE,
)

# #13129 motif B (canonical home: this file -- #13486). The mistake pattern
# is `paths: a.py b.py` where the writer forgot the comma; the parser treats
# the whole thing as ONE glob that matches nothing. We flag when a glob
# contains a SPACE and at least two SPACE-separated tokens each LOOK like a
# path (contain a `/` OR end with a tracked-file extension).
_PATHLIKE_TOKEN_RE = re.compile(
    r"[^\s/]+(?:/[^\s/]+)+|\S+\.(?:py|yml|yaml|md|ipynb|lean|ps1|sh|json|cs|cpp|hpp|go|rs|ts|tsx|js|jsx|txt|csv)"
)


def _missing_comma_tokens(glob: str) -> list[str] | None:
    """Return the SPACE-separated tokens if the glob looks like a missing-comma typo (#13129 motif B).

    Heuristic: the glob has whitespace AND `>=2` tokens each look path-shaped
    (slashed OR ending in a tracked-file extension). Returns None when the
    heuristic does not fire -- the glob is a single path with possible
    whitespace, not a typo. Conservative: a single path-shaped token does
    NOT trigger the suggestion (a space inside a filename is rare but
    legal; the cost of a false positive is a confusing suggestion, the cost
    of a false negative is silent dead-glob, which is the existing bug we
    are not making worse).

    This is the SINGLE machinerie for motif B detection (#13486). The
    previous duplicate in `check_lane_claim.py` now delegates here.
    """
    if not glob or " " not in glob:
        return None
    tokens = glob.split()
    if len(tokens) < 2:
        return None
    pathlike = [t for t in tokens if _PATHLIKE_TOKEN_RE.match(t)]
    if len(pathlike) < 2:
        return None
    return pathlike


def _extract_paths_in_body(body: str) -> list[str]:
    """Mine every `paths: <list>` clause in the body and return the globs.

    Mirrors the comma-split of `_split_paths_brace_aware` without the brace
    handling (PR bodies rarely carry brace groups). Each match is stripped
    and returned as a flat list. Empty when no `paths:` clause is present.
    """
    out: list[str] = []
    for m in _PATHS_INLINE_RE.finditer(body or ""):
        raw = m.group(1).strip()
        for token in raw.split(","):
            token = token.strip()
            if token and token not in out:
                out.append(token)
    for m in _PATHS_LINE_RE.finditer(body or ""):
        raw = m.group(1).strip()
        for token in raw.split(","):
            token = token.strip()
            if token and token not in out:
                out.append(token)
    return out


def _extract_lane(body: str) -> str:
    """Best-effort Grain: lane extractor. Mirrors `grain_tag.extract_lane`."""
    import sys as _sys
    _sys.path.insert(0, str(_SCRIPTS_DIR))
    try:
        from grain_tag import extract_lane  # type: ignore

        return extract_lane(body) or ""
    except Exception:
        return ""


def _git_tracked() -> list[str] | None:
    """Return the list of tracked files, or None if the walk failed.

    Best-effort: a None result silences the advisory (we cannot prove
    deadness, mirroring `_empty_scope_in`'s contract)."""
    try:
        import sys as _sys
        _sys.path.insert(0, str(_SCRIPTS_DIR))
        from check_lane_claim import _git_tracked_files  # type: ignore
        return _git_tracked_files()
    except Exception:
        return None


def _emit_annotations(
    dead_globs: list[str],
) -> tuple[list[str], list[dict]]:
    """Render one annotation line per dead glob + collect suggestions.

    Returns ``(annotation_lines, suggestions)``. Each suggestion is a dict
    ``{"glob": <str>, "hint": <str>, "tokens": [<str>, ...]}`` consumable
    by `dead_scope_suggestions` JSON (see module docstring, #13486).

    Motif B (`paths: a.py b.py` missing comma) is detected BEFORE the
    dead-glob check: when the glob trips the missing-comma heuristic, the
    annotation is `::notice::` (not `::warning::`) because the deadness is
    *explained* by the typo, not by an unrecoverable gap. The lane is told
    to ADD A COMMA -- the path-shaped tokens are valid, the glob is wrong.
    """
    annotations: list[str] = []
    suggestions: list[dict] = []
    for g in dead_globs:
        pathlike_tokens = _missing_comma_tokens(g)
        if pathlike_tokens:
            candidates = ", ".join(repr(t) for t in pathlike_tokens)
            annotations.append(
                f"::notice file={g},title=Missing comma in scope glob "
                f"(#13129 motif B)::"
                f"glob looks like {len(pathlike_tokens)} separate paths "
                f"joined by SPACE instead of COMMA: {candidates}. "
                f"Rewrite as `paths: <comma-separated>`."
            )
            suggestions.append({
                "glob": g,
                "hint": "missing_comma",
                "tokens": list(pathlike_tokens),
            })
        else:
            annotations.append(
                f"::warning file={g},title=Dead scope glob (#13129)::"
                f"your declared scope contains a glob that matches zero tracked "
                f"files in this repo. Reissue with a valid path. Live globs in "
                f"the same scope continue to carry disjointness."
            )
            suggestions.append({
                "glob": g,
                "hint": "dead_glob",
                "tokens": [],
            })
    return annotations, suggestions


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--body-file", required=True, type=Path)
    args = parser.parse_args(argv)

    if not args.body_file.is_file():
        print(f"body file not found: {args.body_file}", file=sys.stderr)
        return 1

    body = args.body_file.read_text(encoding="utf-8", errors="replace")
    lane = _extract_lane(body)
    if not lane:
        return 0  # no declared lane -> nothing to anchor

    paths = _extract_paths_in_body(body)
    if not paths:
        return 0  # no declared scope -> no dead-glob check needed

    tracked = _git_tracked()
    if tracked is None:
        return 1  # walk failed -- bail silently per #12740 contract

    try:
        import sys as _sys
        _sys.path.insert(0, str(_SCRIPTS_DIR))
        from check_lane_claim import _empty_scope_in  # type: ignore
        dead = _empty_scope_in(paths, tracked)
    except Exception:
        return 1

    annotations, suggestions = _emit_annotations(dead)
    for line in annotations:
        print(line)
    # #13486 acceptance (3): emit JSON line so lane scripts / pick_idle_grain
    # can consume the structured suggestions without re-parsing stdout.
    # Key always present (cheap consumer), value [] when nothing fires.
    print(json.dumps({"dead_scope_suggestions": suggestions}, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
