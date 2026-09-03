"""Mesure tranche 1 -- prevalences STALE_OUTPUT par fenetre glissante.

Issue #13562, tranche 3 (passage en REQUIS). Cette mesure ne change aucun
comportement CI : elle observe N commits sur origin/main avec l'organe
``check_source_output_ratchet.py`` deja livre (tranche 1, #13608 MERGED) et
rapporte le nombre de notebooks/cellules en STALE_OUTPUT detectes.

Le verdict du passage en REQUIS depend de la proportion de cellules
detectees qui relevent du cas commentaire-seul / reindentation (FP legitimes
qu'il faudrait ensuite exonerer par phrase dans le body PR cf clause
d'exemption de l'organe). Le ratio n'est pas decide par ce script -- il
laisse 5-10 cas echantillon a la revue humaine pour calibrage.

Usage :
    python scripts/notebook_tools/meas_source_output_ratchet_t1.py \
        --out-dir .claude/agent-memory-local/ --branch origin/main \
        --window-commits 50 200 600
"""

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def _run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)


def _run_stderr_capture(cmd, cwd):
    """Like _run but keeps stderr (we read it independently after)."""
    return subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, check=False)


def _base_for_window(branch, n_commits):
    """Return the OID of branch~n_commits, or branch if fewer ancestors."""
    proc = _run(["git", "rev-parse", f"{branch}~{n_commits}"], cwd=REPO_ROOT)
    if proc.returncode != 0:
        return branch  # fallback: full history
    return proc.stdout.strip()


def _changed_notebooks(base_ref, head_ref):
    """List .ipynb paths changed between base_ref and head_ref."""
    proc = _run(
        ["git", "diff", "--name-only", "--diff-filter=ACMRT", f"{base_ref}..{head_ref}",
         "--", "*.ipynb"],
        cwd=REPO_ROOT,
    )
    if proc.returncode != 0:
        return []
    return [p for p in proc.stdout.splitlines() if p.strip() and p.endswith(".ipynb")]


def _run_ratchet(base_ref):
    """Invoke check_source_output_ratchet.py with --json, return records.

    Note : l'organe imprime aussi le recap texte avant le JSON quand des
    annotations `::error` sont produites (cf #13608 -- le recap apparait
    apres le bloc JSON quand exit=1). On isole le bloc JSON via
    `json.JSONDecoder.raw_decode` (le plus en avant) sur stdout, et on
    garde stderr comme diagnostics si l'organe sort sans bloc.
    """
    proc = _run_stderr_capture(
        ["python", "scripts/notebook_tools/check_source_output_ratchet.py",
         base_ref, "--json"],
        cwd=REPO_ROOT,
    )
    if proc.returncode not in (0, 1, 2):
        return {"error": f"ratchet exit={proc.returncode}: "
                          f"{(proc.stderr or '').strip()[:200]}",
                "records": []}
    text = proc.stdout
    decoder = json.JSONDecoder()
    idx = text.find("{")
    if idx == -1:
        return {"error": f"no JSON object in output (rc={proc.returncode}): "
                          f"{(proc.stderr or '').strip()[:200]}",
                "records": []}
    try:
        payload, _ = decoder.raw_decode(text[idx:])
    except json.JSONDecodeError as exc:
        return {"error": f"JSON decode: {exc}", "records": []}
    return payload


def measure_window(window_commits, branch, head_oid):
    base_ref = _base_for_window(branch, window_commits)
    head_ref = head_oid
    payload = _run_ratchet(base_ref)
    records = payload.get("records", [])
    n_changed = len(records)
    n_stale = sum(r.get("regressions", 0) for r in records)
    n_failing_notebooks = sum(1 for r in records if r.get("regressions", 0) > 0)
    return {
        "window_commits": window_commits,
        "base_ref": base_ref,
        "head_ref": head_ref,
        "changed_notebooks": n_changed,
        "failing_notebooks": n_failing_notebooks,
        "stale_cells_total": n_stale,
        "records": records,
        "error": payload.get("error"),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--branch", default="origin/main")
    ap.add_argument("--head", default=None, help="HEAD ref (default = branch)")
    ap.add_argument("--out-dir", required=True)
    ap.add_argument(
        "--window-commits",
        type=int,
        nargs="+",
        default=[50, 200, 600],
        help="Sliding-window sizes (commits) from branch~N to branch. "
             "Three values give a short/medium/long signal.",
    )
    args = ap.parse_args()

    head_oid = args.head or args.branch
    head_check = _run(["git", "rev-parse", head_oid], cwd=REPO_ROOT)
    if head_check.returncode != 0:
        print(f"cannot resolve HEAD {head_oid}: {head_check.stderr}", file=sys.stderr)
        sys.exit(2)
    head_oid = head_check.stdout.strip()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out_path = out_dir / f"meas-source-output-ratchet-t1-{ts}.json"

    windows_full = []
    for n in args.window_commits:
        print(f"== window {n} commits (base {args.branch}~{n}) ==", file=sys.stderr)
        result = measure_window(n, args.branch, head_oid)
        windows_full.append(result)
        print(
            f"  changed={result['changed_notebooks']} "
            f"failing_nb={result['failing_notebooks']} "
            f"stale_cells={result['stale_cells_total']} "
            f"err={result['error']}",
            file=sys.stderr,
        )

    # Verdict: ratchet ready? Threshold is conservative -- if no STALE cells
    # in any window, the SOURCE side seems clean (no current regressions on
    # the codepath the ratchet guards). If cells appear, they need human
    # review on 5-10 samples to estimate FP rate (case 'comment-only edit
    # with bytes identical' expected per issue body as a known FP class).
    no_stale = all(w["stale_cells_total"] == 0 for w in windows_full)
    verdict = (
        "READY_TO_UPGRADE_TO_REQUIS" if no_stale
        else "ATTENDRE_REVUE_HUMAINE_5_CAS_MIN"
    )

    windows_summary = [
        {k: w[k] for k in ("window_commits", "base_ref", "head_ref",
                           "changed_notebooks", "failing_notebooks",
                           "stale_cells_total", "error")}
        for w in windows_full
    ]

    report = {
        "issue": 13562,
        "tranche": 3,
        "purpose": "fenetre d'observation passage advisory -> REQUIS",
        "branch": args.branch,
        "head_oid": head_oid,
        "generated_at_utc": ts,
        "windows_summary": windows_summary,
        "windows_full": windows_full,
        "verdict_draft": verdict,
    }

    out_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"wrote {out_path}", file=sys.stderr)
    print(f"verdict_draft : {verdict}", file=sys.stderr)


if __name__ == "__main__":
    main()
