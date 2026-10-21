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
import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_exec_sequence import code_exec_counts, sequence_verdict
from fork_retry import run_with_fork_retry

# Fail-by-design ack (#11577, #21273): when regressions are detected AND the
# workflow passes --pr-number + --head-sha, the gate delegates to the ack
# organ. The dual-key (label `exec-sequence-ack` + comment/review
# `[EXEC-SEQ-ACK] head=<sha40>` from `myia-ai-01` at the EXACT head) lifts
# the regression block. Anything else keeps the gate red as before.

# Same exclusions as notebook-execution-required.yml's detect step plus the
# checkpoints rule of the tier-1 scanner: archived, papermill-output and
# research copies are not deliverable notebooks.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")


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
    spawn itself failed after bounded fork retries (#16217 primitive)."""
    try:
        out = run_with_fork_retry(
            ["git", *args], cwd=cwd, capture_output=True,
            encoding="utf-8", errors="replace", check=False)
    except OSError as exc:
        raise InstrumentUnavailable(exc) from exc
    return out.stdout if out.returncode == 0 else None


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
    """Verdict of the working-tree notebook.

    MISSING: the file is absent from the working tree. That is a WORKSPACE
    defect (amputed checkout, persistent runner slot carrying a leftover
    sparse-checkout pattern), never a content defect (#20174). Naming it
    apart is the whole point: conflated into PARSE_ERROR, the verdict tells
    a lane "your notebook is corrupt" and sends it hunting a defect the file
    does not carry -- measured twice on 2026-10-10 (#20158, #20118), where
    the notebooks were valid JSON and identical to origin/main.

    PARSE_ERROR: the file is present but its content is not usable JSON."""
    try:
        text = (Path(cwd or ".") / path).read_text(encoding="utf-8")
    except (FileNotFoundError, NotADirectoryError, IsADirectoryError):
        return "MISSING", []
    except OSError:
        # Permission denied, transient I/O: no readable file either, same class.
        return "MISSING", []
    try:
        ec = code_exec_counts(json.loads(text))
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


def _consult_ack_organ(pr_number: int, head_sha: str,
                         regressions: list[dict]) -> tuple[bool, dict | None]:
    """Delegate the fail-by-design ack decision (#11577, #21273).

    Invokes ``scripts/ci/exec_sequence_ack_required.py`` as a subprocess and
    parses its JSON verdict. The script handles its own fetcher errors
    (#15342 fail-closed semantics); this wrapper just shapes the result for
    the ratchet's exit logic.

    Args:
        pr_number: the PR number, from ``--pr-number``.
        head_sha: 40-char hex SHA of the PR head, from ``--head-sha``.
        regressions: list of content regressions (head != "MISSING") the
            ack organ is asked to acknowledge. Currently unused by the
            organ (the dual-key applies to the PR as a whole) but kept in
            the signature for future per-notebook acks.

    Returns:
        ``(ack_accepted, verdict)``: ``ack_accepted`` is True iff the dual-key
        was satisfied AND the head matched. ``verdict`` is the parsed JSON
        from the organ (or ``None`` if the subprocess failed to start).
    """
    # Locate the ack organ: it lives in scripts/ci/. Both this script and
    # the organ are under scripts/, so a relative import is reliable.
    here = Path(__file__).resolve().parent
    ack_script = here.parent / "ci" / "exec_sequence_ack_required.py"
    if not ack_script.exists():
        # Missing organ is a build defect: the gate stays fail-closed.
        print(f"::error::exec-sequence ack organ absent: {ack_script} -- "
              f"le gate reste rouge (fail-closed, #21273).",
              file=sys.stderr)
        return False, None
    try:
        proc = subprocess.run(
            [
                sys.executable, str(ack_script),
                "--pr-number", str(pr_number),
                "--head", head_sha,
            ],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", check=False, timeout=45,
        )
    except (OSError, subprocess.SubprocessError) as e:
        print(f"::error::exec-sequence ack organ subprocess failed: "
              f"{type(e).__name__}: {e} -- gate reste rouge (fail-closed, "
              f"#21273).", file=sys.stderr)
        return False, None
    if proc.returncode not in (0, 1):
        stderr = (proc.stderr or "").strip()[:200]
        print(f"::error::exec-sequence ack organ rc={proc.returncode}: "
              f"{stderr} -- gate reste rouge (fail-closed, #21273).",
              file=sys.stderr)
        return False, None
    try:
        verdict = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError as e:
        print(f"::error::exec-sequence ack organ output is not JSON: {e} -- "
              f"gate reste rouge (fail-closed, #21273).", file=sys.stderr)
        return False, None
    if not isinstance(verdict, dict) or "guard_pass" not in verdict:
        print(f"::error::exec-sequence ack organ verdict missing guard_pass: "
              f"keys={list(verdict.keys()) if isinstance(verdict, dict) else 'n/a'}"
              f" -- gate reste rouge (fail-closed, #21273).", file=sys.stderr)
        return False, None
    accepted = bool(verdict.get("guard_pass"))
    # Surface the organ's reasoning to the job log so the ack audit trail is
    # not buried inside the subprocess.
    reason = verdict.get("reason", "")
    if reason:
        print(f"exec-sequence ack organ: {reason}", file=sys.stderr)
    return accepted, verdict


def main():
    # Sibling pattern (#12811, #13191, #14154, #15185, #15668) : l'organe est
    # consomme en subprocess par la CI et les tests, qui decodent stdout/stderr
    # en UTF-8 (encoding="utf-8"). Sur Windows ACP 1252, un pipe sans
    # reconfigure emet l'em-dash des annotations ::error en byte 0x97 cp1252 --
    # UnicodeDecodeError dans le reader thread, stderr=None, verdict masque
    # (#17427). Le hasattr couvre Python < 3.7 et les flux captes sans
    # reconfigure (pytest).
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(
        description="Ratchet gate: PR must not soil a clean sequence "
                    "(issue #11112 tier 2)")
    ap.add_argument("base", help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="Machine-readable output")
    ap.add_argument("--pr-number", type=int, default=None,
                    help="PR number (CI: ${{ github.event.pull_request.number }}). "
                         "When set with --head-sha, the gate delegates to "
                         "scripts/ci/exec_sequence_ack_required.py on regression "
                         "(#11577, #21273). Without these flags, the gate behaves "
                         "as before (regression => exit 1).")
    ap.add_argument("--head-sha", default=None,
                    help="40-char hex SHA of the PR head (the ack marker must "
                         "match this exact value; any push after the ack "
                         "invalidates it).")
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

    if not regressions:
        # Clean path. The JSON / human-readable summary is printed here, ONCE.
        if args.as_json:
            print(json.dumps({
                "base": args.base,
                "base_resolved": resolved,
                "changed": len(records),
                "regressions": 0,
                "records": records}, ensure_ascii=False, indent=1))
        else:
            print(f"execution_count ratchet -- base {args.base} "
                  f"(merge-base {resolved[:12]})")
            print(f"changed notebooks : {len(records)}")
            print(f"regressions       : 0")
            for r in records:
                print(f"  {r['base']}->{r['head']} {r['notebook']}")
        sys.exit(0)

    # Regressions found. The human-readable summary prints FIRST so the lane
    # sees what soiled, then the ::error annotations, then the JSON payload
    # (if --json), then exit. The JSON is printed ONCE per run -- never at the
    # top (that would dup the payload on regression).
    if not args.as_json:
        print(f"execution_count ratchet -- base {args.base} "
              f"(merge-base {resolved[:12]})")
        print(f"changed notebooks : {len(records)}")
        print(f"regressions       : {len(regressions)}")
        for r in records:
            mark = "REGRESSION" if r["regression"] else ""
            print(f"  {r['base']}->{r['head']} {r['notebook']} {mark}")

    if regressions:
        # Fail-by-design ack delegation (#11577, #21273). Only valid on
        # content regressions, not on MISSING files: a workspace defect is
        # NOT a notebook defect, and acknowledging it would invert the
        # fail-by-design into a workaround of the workspace itself.
        content_regressions = [r for r in regressions if r["head"] != "MISSING"]
        ack_accepted = False
        ack_verdict: dict | None = None
        if content_regressions and args.pr_number and args.head_sha:
            ack_accepted, ack_verdict = _consult_ack_organ(
                args.pr_number, args.head_sha, regressions=content_regressions)
        for r in regressions:
            if r["head"] == "MISSING":
                # #20174 : un arbre ampute n'est pas un carnet casse. L'annotation
                # doit le dire, sinon la lane cherche un defaut de contenu que le
                # fichier ne porte pas.
                print(f"::error file={r['notebook']}::notebook absent from the "
                      f"working tree (CLEAN at {args.base}) — incomplete "
                      f"checkout, NOT a content defect: re-run the job on a "
                      f"clean workspace", file=sys.stderr)
            else:
                print(f"::error file={r['notebook']}::sequence was CLEAN at "
                      f"{args.base}, is {r['head']} in this PR — re-execute the "
                      f"notebook end-to-end on a fresh kernel before commit",
                      file=sys.stderr)
        if any(r["head"] != "MISSING" for r in regressions):
            print("If this is an acknowledged single-cell re-exec (RECOVERABLE-"
                  "MACHINE, gitignored downstream artifact): never hand-edit "
                  "execution_count — document the degraded sequence in the PR "
                  "body with the template from docs/reference/regles-validation-"
                  "detail.md 'Ratchet exec-sequence fail-by-design' (#11577) and "
                  "get an explicit reviewer ack before merge.",
                  file=sys.stderr)
        else:
            # Servir l'avis « fail-by-design » sur un arbre ampute ferait signer
            # un accord pour un defaut inexistant -- c'est ainsi qu'un faux rouge
            # devient un faux accord.
            print("Every regression above is a MISSING file: the working tree is "
                  "incomplete. Do not open a fail-by-design ack for a file that "
                  "is not on disk — repair the workspace (#20174).",
                  file=sys.stderr)
        if ack_accepted:
            # #21273 : ack accepted at exact head by myia-ai-01. The ratchet
            # bypasses with a structured notice; the ack is auditable in the
            # job log. The override does NOT create a new right: it executes
            # the rule already written since #11577.
            notebooks = ", ".join(sorted(r["notebook"] for r in content_regressions))
            # The dual-key protocol (#21273) restricts ack authorship to
            # `myia-ai-01`. The verdict carries `ack_author` (the comment/review
            # author login), which is read from the API at run time; when the
            # fetch is bodies-only, the field is None and we fall back to the
            # protocol's sole authorised author. The organ's reason field is
            # the human-readable surface, this line is the audit trail.
            ack_author = (ack_verdict or {}).get("ack_author") or "myia-ai-01"
            print(f"::notice title=Exec-sequence ratchet ACK::accepted at "
                  f"head={args.head_sha[:12] if args.head_sha else '?'} "
                  f"by {ack_author} "
                  f"-- notebooks: {notebooks}",
                  file=sys.stderr)
            print(f"exec-sequence ratchet: ACK accepted, gate passes "
                  f"(label + marker from myia-ai-01 at head "
                  f"{args.head_sha[:12] if args.head_sha else '?'}; "
                  f"see #21273).",
                  file=sys.stderr)
            if args.as_json:
                print(json.dumps({
                    "base": args.base,
                    "base_resolved": resolved,
                    "changed": len(records),
                    "regressions": len(regressions),
                    "ack_applied": True,
                    "ack_verdict": ack_verdict,
                    "records": records}, ensure_ascii=False, indent=1))
            sys.exit(0)
        if args.as_json:
            print(json.dumps({
                "base": args.base,
                "base_resolved": resolved,
                "changed": len(records),
                "regressions": len(regressions),
                "ack_applied": False,
                "ack_verdict": ack_verdict,
                "records": records}, ensure_ascii=False, indent=1))
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
