"""Preflight tool : detect "already-delivered" issues (false-premise pattern).

Cross-cycle lesson (cycles 14, 16, 18, 20, 22, 23 + present = 7+ occurrences) :
when an issue #N has title like "fix X" but X was already delivered on origin/main
via a PR using `Refs #N` (partial contribution) instead of `Closes #N` (full
close), GitHub does NOT auto-close the issue. The issue stays OPEN forever by
administrative oversight, and a worker claiming it will spend 5-15 min on a
preflight that ultimately shows the work is already merged.

This script encodes that preflight as a one-shot CLI :

    python scripts/check_already_delivered.py 13850

Exit codes :
    0 -- not delivered (safe to claim)
    1 -- delivered (refuse the claim, read the report)
    2 -- ambiguous (manual decision required)

Sources crossed (3 axes) :
    1. `git log origin/main --grep="#N"`           -- commits referencing the issue
    2. `gh search prs "<N>" --state all --json ...` -- PRs mentioning the issue
    3. For rename-shaped issues (heuristic on title tokens):
       `git log origin/main --diff-filter=R -- <dir>` -- renames already merged

Usage :
    $ python scripts/check_already_delivered.py 13850
    [LIVRÉ] #13850 — 1 PR merged, 2 commits, ref #13824 trouvé sur main.
    PR #13824 (MERGED 2026-08-30T19:51Z) : refactor(notebooks,#13753): reclasser Infer-6-Debugging en Infer-2b-Debugging-Bonnes-Pratiques (accretion transversale).
    Commit e821d5290 trouvé sur origin/main.
    >>> Verdict : LIVRÉ — refuser le claim, émettre un commentaire no-op.

    $ echo $?
    1
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Tokens heuristiques : si le titre les contient, l'issue est probablement un
# rename / reclass / zero-padding, et il faut aussi vérifier --diff-filter=R.
RENAME_HINTS = (
    "renum",
    "rename",
    "reclass",
    "zero-pad",
    "padding",
    "merge ",
    "absorb",
    "consolid",
    "reorgani",
    "rangement",
)

RENAME_PATHS_HINT = (
    "MyIA.AI.Notebooks/Probas",
    "MyIA.AI.Notebooks/SemanticWeb",
    "MyIA.AI.Notebooks/GameTheory",
    "MyIA.AI.Notebooks/Search",
    "MyIA.AI.Notebooks/GenAI",
    "MyIA.AI.Notebooks/SymbolicAI",
    "MyIA.AI.Notebooks/ML",
    "MyIA.AI.Notebooks/Sudoku",
    "scripts/notebook_tools/twin_pairs.d",
)


def _run(cmd: list[str], cwd: Path | None = None) -> tuple[int, str, str]:
    """Run a command, return (returncode, stdout, stderr). Decoded as utf-8 with errors=replace."""
    try:
        out = subprocess.run(
            cmd,
            cwd=cwd or REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
        )
        return out.returncode, out.stdout, out.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"


_REF_PATTERN = re.compile(r"(?<![0-9])#(\d+)\b")


def _ref_id_to_subject(text: str, issue: int) -> bool:
    """Word-boundary check : #issue appears as an isolated reference, not as a
    prefix of a longer number (e.g. `#1` != `#10` != `#13850`). Operates on the
    commit subject line — the leading ``<sha>`` from ``git log --oneline`` is
    ignored (no digits follow a SHA alphafragment, so the regex won't false-
    trigger on it).
    """
    return any(m.group(1) == str(issue) for m in _REF_PATTERN.finditer(text))


def source_git_log(issue: int) -> dict:
    """Source 1: commits referencing the issue on origin/main.

    Note: only finds commits whose SUBJECT contains `#N`. Commits that fix the
    issue but use a different reference number (e.g. issue #13850 fixed via
    PR #13824 whose subject mentions #13753) will NOT appear here. This source
    is therefore a *weak* signal — useful for direct references only.

    Word-boundary filter : ``git log --grep="#N"`` is substring-based and matches
    every commit whose subject CONTAINS ``#N`` (e.g. ``#1`` also matches
    ``#10``, ``#11`, ..., ``#13850``). We post-filter with a word-boundary regex
    to keep only commits where ``#issue`` appears as an isolated token.
    """
    rc, out, _ = _run(["git", "log", "origin/main", f"--grep=#{issue}", "--oneline"])
    raw = [line.strip() for line in out.splitlines() if line.strip()]
    commits = [line for line in raw if _ref_id_to_subject(line, issue)]
    return {
        "commits": commits,
        "count": len(commits),
        "raw_count": len(raw),
        "note": "subject-only + word-boundary",
    }


def source_gh_issue_body(issue: int) -> dict:
    """Source 3: lire le body de l'issue #N et y chercher des refs PRs/commits.

    Couvre l'angle mort de source_gh_search : PR #13824 ferme #13850 par rider
    en mentionnant `#13753` dans le titre, PAS `#13850`. Seule la lecture du
    body de l'issue (qui contient typiquement la liste des PRs/PR-riders) peut
    relier #13850 à sa livraison effective.
    """
    rc, out, err = _run(
        ["gh", "issue", "view", str(issue), "--json", "number,title,body,state"]
    )
    if rc != 0:
        return {"error": err.strip()[:200], "body_excerpt": "", "pr_refs": [], "commit_refs": []}
    try:
        data = json.loads(out) if out.strip() else {}
    except json.JSONDecodeError:
        return {"error": "JSON parse fail", "body_excerpt": "", "pr_refs": [], "commit_refs": []}
    body = data.get("body", "") or ""
    # Trouver les refs PRs (#NNNN) et SHAs (7+ chars hex)
    pr_refs = sorted(set(int(m.group(1)) for m in re.finditer(r"#(\d{4,})\b", body)))
    # 7+ chars hex précédés/escapés par espace, début, ou fin de mot
    commit_refs = sorted(set(m.group(0) for m in re.finditer(r"(?<![0-9a-f])([0-9a-f]{7,40})(?![0-9a-f])", body, flags=re.IGNORECASE)))
    return {
        "body_excerpt": body[:200],
        "title": data.get("title", ""),
        "state": data.get("state", ""),
        "pr_refs": pr_refs,
        "commit_refs": commit_refs,
    }


def source_gh_search(issue: int) -> dict:
    """Source 2: PRs in current repo referencing the issue number.

    Strategy : use `gh pr list --search "N"` (NO `#` prefix — that's the only
    way to catch indirect references like PR #13824 which fixes issue #13850
    by mentioning #13753 instead). We run two queries (open + closed) to catch
    both states, since `--state all` is not valid for `gh pr list`.
    """
    prs: list[dict] = []
    errors: list[str] = []
    for state in ("open", "closed"):
        rc, out, err = _run(
            ["gh", "pr", "list", "--state", state, "--search", str(issue), "--json", "number,title,state,mergedAt,url", "--limit", "50"]
        )
        if rc != 0:
            errors.append(f"{state}: {err.strip()[:120]}")
            continue
        try:
            prs.extend(json.loads(out) if out.strip() else [])
        except json.JSONDecodeError:
            errors.append(f"{state}: JSON parse fail: {out[:120]}")
    # Deduplicate by PR number
    seen: set[int] = set()
    deduped: list[dict] = []
    for pr in prs:
        n = pr.get("number")
        if n in seen:
            continue
        seen.add(n)
        deduped.append(pr)
    return {"prs": deduped, "count": len(deduped), "errors": errors}


def source_diff_filter_rename(issue: int, title: str | None = None) -> dict:
    """Source 3: rename-shaped issues — check git log --diff-filter=R on suspect dirs."""
    # Toujours vérifier RENAME_PATHS_HINT (les directories cibles de renommage)
    # car c'est peu coûteux et on a déjà vu des titres non explicites.
    candidates = list(RENAME_PATHS_HINT)
    if title:
        low = title.lower()
        if any(h in low for h in RENAME_HINTS):
            # Title has rename hint, add RENAME_PATHS_HINT candidates (déjà in)
            pass
    seen: set[str] = set()
    results: list[dict] = []
    for path in candidates:
        if path in seen:
            continue
        seen.add(path)
        rc, out, _ = _run(["git", "log", "origin/main", "--diff-filter=R", "--oneline", "--", path])
        if rc != 0:
            continue
        # Filtrer par proximité numérique au issue number (heuristique faible mais utile)
        hits = []
        for line in out.splitlines():
            # Match either #N or hex SHA — on garde tout, on laisse le verdict trancher
            sha = line.split()[0] if line else ""
            hits.append({"sha": sha, "subject": line.strip()})
        if hits:
            results.append({"path": path, "renames": hits[:20], "count": len(hits)})
    return {"candidates": results}


def check(issue: int, title: str | None = None, *, json_output: bool = False) -> dict:
    """Run the 4 sources, return a verdict dict."""
    sources = {
        "git_log": source_git_log(issue),
        "gh_search_prs": source_gh_search(issue),
        "gh_issue_body": source_gh_issue_body(issue),
    }
    # Always pull the canonical title from gh if not provided or if user
    # passed a wrong/short title — the indirect-PR keyword filter needs the
    # REAL title to match against PR titles.
    if not title and not sources["gh_issue_body"].get("error"):
        title = sources["gh_issue_body"].get("title", "") or title
    if title and any(h in title.lower() for h in RENAME_HINTS):
        sources["diff_filter_R"] = source_diff_filter_rename(issue, title)

    # Verdict logic
    commit_hits = sources["git_log"]["count"]
    pr_hits = sources["gh_search_prs"]["prs"]
    body_data = sources.get("gh_issue_body", {})
    body_pr_refs: list[int] = body_data.get("pr_refs", []) if not body_data.get("error") else []
    rename_hits: list[dict] = sources.get("diff_filter_R", {}).get("candidates", [])  # type: ignore[assignment]

    # Filter PRs to those whose state is MERGED or whose body likely closes the issue
    closed_prs = [pr for pr in pr_hits if pr.get("state") in ("MERGED", "CLOSED")]
    merged_prs = [pr for pr in pr_hits if pr.get("state") == "MERGED"]
    open_prs = [pr for pr in pr_hits if pr.get("state") == "OPEN"]

    # PRs referenced in the issue body (indirect signal — PR mentions #N even
    # if its own subject doesn't). Cross-check their state via gh.
    indirect_prs: list[dict] = []
    for pr_num in body_pr_refs:
        rc, out, _ = _run(
            ["gh", "pr", "view", str(pr_num), "--json", "number,state,mergedAt,title,url,body"]
        )
        if rc == 0 and out.strip():
            try:
                indirect_prs.append(json.loads(out))
            except json.JSONDecodeError:
                pass
    indirect_merged = [pr for pr in indirect_prs if pr.get("state") == "MERGED"]
    # Indirect PR credited as delivering THIS issue: if the issue body cites
    # the PR AND the PR is MERGED, AND its title shares at least one keyword
    # (>= 4 chars) with the issue title, it's a rider delivery. We need the
    # title keyword check to avoid false positives from old historical refs
    # (e.g. #13876's body cites 8 PRs but none actually delivers a fix for the
    # workspace cwd missing env). Cross-check via title tokens.
    issue_title_tokens = set()
    if title:
        issue_title_tokens = {
            t.lower().strip(".,;:()[]{}") for t in title.split() if len(t) >= 4
        }
    # Also pull from the issue body itself if title wasn't passed
    if not issue_title_tokens and not body_data.get("error"):
        body_title = body_data.get("title", "")
        issue_title_tokens = {
            t.lower().strip(".,;:()[]{}") for t in body_title.split() if len(t) >= 4
        }

    def _shares_keyword(pr: dict) -> bool:
        if not issue_title_tokens:
            # Pas de titre fourni — fallback permissif (assume LIVRÉ si MERGED)
            return True
        pr_title = (pr.get("title") or "").lower()
        return any(tok in pr_title for tok in issue_title_tokens)

    indirect_credited = [pr for pr in indirect_merged if _shares_keyword(pr)]

    has_strong_signal = (
        len(merged_prs) > 0
        or (commit_hits >= 2)
        or (rename_hits and any(r["count"] > 0 for r in rename_hits))
        or (len(indirect_credited) > 0)
    )
    has_weak_signal = commit_hits > 0 or len(pr_hits) > 0 or len(body_pr_refs) > 0

    if has_strong_signal:
        verdict = "LIVRÉ"
        rc = 1
        reasons = []
        if commit_hits > 0:
            reasons.append(f"{commit_hits} commit(s) sur origin/main référencent #{issue}")
        if merged_prs:
            reasons.append(f"{len(merged_prs)} PR merged référencent #{issue} (ex: #{merged_prs[0]['number']})")
        elif closed_prs:
            reasons.append(f"{len(closed_prs)} PR closed référencent #{issue}")
        if indirect_credited:
            reasons.append(f"{len(indirect_credited)} PR merged LIVRANT #{issue} via body ref (ex: #{indirect_credited[0]['number']})")
        if rename_hits:
            for r in rename_hits:
                reasons.append(f"{r['count']} renames sur `{r['path']}` (échantillon: {r['renames'][:1]})")
    elif has_weak_signal:
        verdict = "AMBIGU"
        rc = 2
        reasons = [
            f"{commit_hits} commit(s) sur {len(pr_hits)} PR(s) référencent #{issue} mais aucun merged/closed"
        ]
    else:
        verdict = "NON LIVRÉ"
        rc = 0
        reasons = [f"0 commit, 0 PR sur #{issue} — sûr de claim"]

    report = {
        "issue": issue,
        "title": title,
        "verdict": verdict,
        "exit_code": rc,
        "reasons": reasons,
        "sources": sources,
        "merged_prs": [pr.get("number") for pr in merged_prs],
        "closed_prs": [pr.get("number") for pr in closed_prs],
        "open_prs": [pr.get("number") for pr in open_prs],
        "indirect_merged_prs": [pr.get("number") for pr in indirect_merged],
        "indirect_credited_prs": [pr.get("number") for pr in indirect_credited],
    }
    return report


def format_human(report: dict) -> str:
    v = report["verdict"]
    issue = report["issue"]
    lines: list[str] = []
    if v == "LIVRÉ":
        lines.append(f"[LIVRÉ] #{issue} — travail déjà livré sur origin/main.")
    elif v == "AMBIGU":
        lines.append(f"[AMBIGU] #{issue} — preuves insuffisantes, trancher manuellement.")
    else:
        lines.append(f"[NON LIVRÉ] #{issue} — sûr de claim.")
    for r in report["reasons"]:
        lines.append(f"  • {r}")
    gl = report["sources"]["git_log"]
    if gl["commits"]:
        lines.append(f"  Commits ({gl['count']}):")
        for c in gl["commits"][:3]:
            lines.append(f"    - {c}")
        if gl["count"] > 3:
            lines.append(f"    ... ({gl['count'] - 3} de plus)")
    prs = report["sources"]["gh_search_prs"]["prs"]
    if prs:
        lines.append(f"  PRs ({len(prs)}):")
        for pr in prs[:3]:
            st = pr.get("state", "?")
            ma = pr.get("mergedAt", "")
            lines.append(f"    - #{pr.get('number')} [{st}] {pr.get('title', '')[:80]} (merged: {ma[:10] if ma else '—'})")
        if len(prs) > 3:
            lines.append(f"    ... ({len(prs) - 3} de plus)")
    if v == "LIVRÉ":
        lines.append(">>> Verdict : LIVRÉ — refuser le claim, émettre un commentaire no-op.")
    elif v == "AMBIGU":
        lines.append(">>> Verdict : AMBIGU — lire le rapport, trancher à la main.")
    else:
        lines.append(">>> Verdict : NON LIVRÉ — claim autorisé (vérifier quand même scope).")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Preflight : détecte les issues déjà livrées sur origin/main (false-premise pattern).",
    )
    parser.add_argument("issue", type=int, help="Numéro d'issue GitHub à vérifier")
    parser.add_argument("--title", default=None, help="Titre de l'issue (active la branche rename)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON structurée")
    args = parser.parse_args(argv)

    report = check(args.issue, title=args.title, json_output=args.json)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(format_human(report))
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
