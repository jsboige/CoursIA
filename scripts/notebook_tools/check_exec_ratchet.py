"""Ratchet gate: a PR must not soil a notebook whose sequence was clean.

Issue #11112 tier 2. The tier-1 organ (check_exec_sequence.py) measures the
corpus; this gate enforces only the non-regression half: for every .ipynb
changed between BASE and HEAD, a verdict that was CLEAN at BASE must still be
CLEAN at HEAD. A notebook already dirty at BASE is free to stay dirty (no
retroactive catch-up), so the gate is green on main from day one despite the
legacy dirty notebooks that the tier-3 rollout is re-executing family by
family. Improvements (DIRTY -> CLEAN) are reported but never required.

Added notebooks (no base blob) carry no ratchet: their execution evidence is
already enforced by notebook-execution-required.yml (H.3). They are reported
for visibility only.

Usage:
    python check_exec_ratchet.py <base-ref> [--json]

    base-ref      base branch ref (CI: origin/<base branch>). Resolved
                  internally to merge-base(base-ref, HEAD), so a branch
                  behind its base is judged on its own diff only.

Head verdicts read the working tree (in CI the checkout IS the head), base
verdicts read the blob via `git show`. Exit code 1 iff at least one
CLEAN -> non-CLEAN regression exists. Exit code 2 iff git could not be
spawned at all (instrument unavailable, #16164) -- never confuse "could not
measure" with "measured 0".
"""

import argparse
import errno
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_exec_sequence import code_exec_counts, sequence_verdict

# Same exclusions as notebook-execution-required.yml's detect step plus the
# checkpoints rule of the tier-1 scanner: archived, papermill-output and
# research copies are not deliverable notebooks.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")

# EAGAIN au spawn (contention de processus, p.ex. pytest-xdist -n 4 sur le
# runner) est transitoire : le `except OSError: return None` historique
# transformait ce pic de charge en "changed notebooks : 0" -> faux vert CI
# (flake diagnostique sur #16125, tentative 3). On retente borne avant de
# rendre l'echec.
_EAGAIN_ERRNOS = (errno.EAGAIN, getattr(errno, "EWOULDBLOCK", errno.EAGAIN))
_EAGAIN_ATTEMPTS = 3
_EAGAIN_BACKOFF = (0.05, 0.15)  # avant les 2e et 3e tentatives


def _est_eagain(exc):
    return isinstance(exc, OSError) and exc.errno in _EAGAIN_ERRNOS


class InstrumentUnavailable(RuntimeError):
    """git n'a pas pu etre lance : le ratchet n'a rien mesure (#16164).

    Epuisement des retries EAGAIN, ou OSError non transitoire au spawn
    (ENOENT, EACCES, ...). Distinct de ``returncode != 0`` (git A repondu :
    l'instrument a tourne, sa reponse vaut None). Decision #16164 :
    fail-closed sur instrument indisponible, en convergence avec le canon
    (check_kernel_suffix_canon.py, dont l'OSError propage) -- un garde ne
    rend jamais un verdict sur un arbre qu'il n'a pas lu.
    """

    def __init__(self, exc):
        super().__init__(
            f"git spawn failed ({exc.__class__.__name__}: "
            f"errno={getattr(exc, 'errno', None)} {exc})")


def git(*args, cwd=None):
    """Run a git command, returning stdout (utf-8), None on git-level
    failure (returncode != 0), or raising InstrumentUnavailable when the
    spawn itself failed after bounded EAGAIN retries."""
    for tentative in range(_EAGAIN_ATTEMPTS):
        try:
            out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                                 encoding="utf-8", errors="replace",
                                 check=False)
            return out.stdout if out.returncode == 0 else None
        except OSError as exc:
            if not _est_eagain(exc) or tentative == _EAGAIN_ATTEMPTS - 1:
                raise InstrumentUnavailable(exc) from exc
            time.sleep(_EAGAIN_BACKOFF[tentative])
    return None


def resolve_base(base, cwd=None):
    """Resolve `base` to merge-base(base, HEAD).

    The gate must judge what the branch CHANGED, not how far behind it is.
    Comparing a stale branch tree-to-tree against the tip of its base branch
    reports every notebook the base advanced meanwhile -- and, since the
    branch still holds the older blob, reports them with the sign reversed:
    a notebook cleaned on main reads as CLEAN -> DIRTY here.  Measured on
    #11627 (jumeau de #11532): five PRs red on this check without any of
    them having touched a notebook sequence.

    The false verdict is the dangerous kind -- it sends an author to
    "re-execute" notebooks they never opened, which is exactly the gesture
    that destroyed 8 SVG renders on #11351.

    Falls back to the ref as given when no merge base exists (shallow clone,
    unrelated histories), i.e. the previous behaviour.
    """
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


def changed_notebooks(base, cwd=None):
    """Notebooks added/copied/modified/renamed between base and HEAD."""
    out = git("diff", "--name-only", "--diff-filter=ACMR",
              base, "HEAD", "--", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace("\\", "/")
        if posix and not any(m in f"/{posix}" for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def verdict_at_base(base, path, cwd=None):
    """Verdict of the notebook blob at base ref.

    ABSENT: the file does not exist at base (added by the PR).
    PARSE_ERROR: not valid JSON."""
    content = git("show", f"{base}:{path}", cwd=cwd)
    if content is None:
        return "ABSENT", []
    try:
        ec = code_exec_counts(json.loads(content))
    except Exception:
        return "PARSE_ERROR", []
    return sequence_verdict(ec), ec


def verdict_at_head(path, cwd=None):
    """Verdict of the working-tree notebook."""
    try:
        ec = code_exec_counts(json.loads(
            (Path(cwd or ".") / path).read_text(encoding="utf-8")))
    except Exception:
        return "PARSE_ERROR", []
    return sequence_verdict(ec), ec


def ratchet(base, cwd=None):
    """One record per changed notebook; regression = CLEAN soiled."""
    base = resolve_base(base, cwd=cwd)
    records = []
    for path in changed_notebooks(base, cwd=cwd):
        base_verdict, _ = verdict_at_base(base, path, cwd=cwd)
        head_verdict, _ = verdict_at_head(path, cwd=cwd)
        records.append({
            "notebook": path,
            "base": base_verdict,
            "head": head_verdict,
            "regression": base_verdict == "CLEAN" and head_verdict != "CLEAN",
        })
    return records


def main():
    ap = argparse.ArgumentParser(
        description="Ratchet gate: PR must not soil a clean sequence "
                    "(issue #11112 tier 2)")
    ap.add_argument("base", help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="Machine-readable output")
    args = ap.parse_args()

    try:
        resolved = resolve_base(args.base)
        records = ratchet(args.base)
    except InstrumentUnavailable as exc:
        # #16164 : "n'a pas pu mesurer" n'est pas "a mesure 0". Le faux vert
        # historique (changed notebooks : 0 + exit 0) confondait les deux ;
        # exit 2 est distinct de 1 (regression) pour que CI comme humains
        # distinguent l'instrument en panne de l'arbre propre.
        print(f"instrument indisponible : {exc}", file=sys.stderr)
        print("le ratchet n'a rien mesure -- contention de processus "
              "(EAGAIN, p.ex. pytest-xdist -n 4) ou git absent du PATH ; "
              "relancer le job, ne pas lire ceci comme « 0 changements ».",
              file=sys.stderr)
        sys.exit(2)
    regressions = [r for r in records if r["regression"]]

    if args.as_json:
        print(json.dumps({
            "base": args.base,
            "base_resolved": resolved,
            "changed": len(records),
            "regressions": len(regressions),
            "records": records}, ensure_ascii=False, indent=1))
    else:
        print(f"execution_count ratchet -- base {args.base} "
              f"(merge-base {resolved[:12]})")
        print(f"changed notebooks : {len(records)}")
        print(f"regressions       : {len(regressions)}")
        for r in records:
            mark = "REGRESSION" if r["regression"] else ""
            print(f"  {r['base']}->{r['head']} {r['notebook']} {mark}")

    if regressions:
        for r in regressions:
            print(f"::error file={r['notebook']}::sequence was CLEAN at "
                  f"{args.base}, is {r['head']} in this PR — re-execute the "
                  f"notebook end-to-end on a fresh kernel before commit",
                  file=sys.stderr)
        print("If this is an acknowledged single-cell re-exec (RECOVERABLE-"
              "MACHINE, gitignored downstream artifact): never hand-edit "
              "execution_count — document the degraded sequence in the PR "
              "body with the template from docs/reference/regles-validation-"
              "detail.md 'Ratchet exec-sequence fail-by-design' (#11577) and "
              "get an explicit reviewer ack before merge.",
              file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
