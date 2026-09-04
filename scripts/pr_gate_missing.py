#!/usr/bin/env python3
"""PR-gate-absent detector -- the missing ORGAN for issue #10928.

The required check ``PR gate`` (scripts/pr_gate.py, workflow pr-gate.yml) is the
single status check that main's branch protection requires. When it is absent
from a PR's status-check rollup -- never reported, not red -- the PR is
``BLOCKED`` while *every* visible signal reads green: ``gh pr checks`` shows 0
failures, 0 pending, ``mergeable: MERGEABLE``. A required context that is never
reported blocks without displaying anything.

Three distinct causes were measured firsthand on 2026-08-14 (issue #10928):

  - #10898 : the head commit's SUBJECT contained the literal ``[skip ci]`` --
    GitHub skipped every ``pull_request`` workflow (only CodeQL ran). Fixed by a
    re-push whose message does not carry the token.
  - #10558 : PR opened by the bot (``app/github-actions``). A push made with
    ``GITHUB_TOKEN`` does not create a new workflow run (GitHub anti-recursion)
    -- structural, by design, but nowhere written.
  - #10902 : unknown cause; the PR was ``DIRTY`` and its rebase re-triggered CI.

This tool is an ADVISORY organ, never blocking (it cannot block: the missing
context IS the blocker). On each sweep it:

  - flags OPEN non-draft PRs whose rollup has NO ``PR gate`` check-run, and
  - labels ``pr-gate-missing`` (regular) / ``pr-gate-missing-bot`` (bot PRs),
    and posts a remediation comment once (marker-guarded, no spam on re-runs).

PRs whose ``PR gate`` is present but queued/in_progress are NOT flagged:
presence is the signal, conclusion is not (acceptance #1 -- a young PR has the
check-run with no conclusion yet, which is normal).

The classification core (``classify``) is a PURE function -- no network -- so it
is unit-tested with fixtures in ``scripts/tests/test_pr_gate_missing.py``. The
``main`` driver wires it to ``gh`` and applies/removes labels and comments
idempotently.

Usage::

    python scripts/pr_gate_missing.py --dry-run        # log only, no labels
    python scripts/pr_gate_missing.py                  # apply (CI cron)
    python scripts/pr_gate_missing.py --label NAME     # override label name

Exit code is always 0 (advisory). The actionable payload is the set of labeled
PRs and their comments, NEVER the green conclusion.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from typing import Iterable

LABEL_DEFAULT = "pr-gate-missing"
LABEL_BOT_DEFAULT = "pr-gate-missing-bot"
LABEL_COLOR = "b60205"  # red -- "invisible required-context blocker, needs a push"
LABEL_BOT_COLOR = "d93f0b"  # orange -- "structural bot case (GITHUB_TOKEN anti-recursion)"
LABEL_DESC = ("PR gate absent du rollup: contexte requis jamais rapporte -- "
              "PR verrouillee malgre des checks verts (#10928)")
LABEL_BOT_DESC = ("PR du bot sans PR gate: structural (push GITHUB_TOKEN ne cree "
                  "pas de workflow run) -- merge admin ou push humain (#10928)")

# Issue #14477 (cause 5, mesuree 2026-09-03 sur #14220) : une PR en conflit
# avec main ne recoit AUCUN run `pull_request` -- GitHub ne calcule pas de
# merge-ref, donc ne dispatche rien. La re-poussee a vide, remede des causes
# 1/3/4, y est INERTE (mesuree : un commit vide sous identite humaine n'a cree
# aucun run). Label distinct : le remede n'est pas un push, c'est un conflit.
LABEL_CONFLICT_DEFAULT = "pr-gate-conflict"
LABEL_CONFLICT_COLOR = "fdd0a2"  # saumon -- "PR dirty, remede = resoudre le conflit"
LABEL_CONFLICT_DESC = ("PR gate absent car la PR est en conflit avec main "
                       "(mergeable_state=dirty) -- aucun run pull_request tant "
                       "que le conflit n'est pas resolu (#14477)")

# The exact check-run name posted by pr_gate.py --self-name "PR gate" and
# required by main's branch protection. Renaming here silently detaches the
# detector (same invariant as pr-gate.yml: keep the string stable).
GATE_NAME = "PR gate"
BOT_LOGIN = "app/github-actions"

# Marker framing the advisory comment, so re-runs can find and update it.
COMMENT_MARKER_START = "<!-- PR-GATE-MISSING:START -->"
COMMENT_MARKER_END = "<!-- PR-GATE-MISSING:END -->"

# Issue #14477 -- the remediation is now CAUSE-DEPENDENT (design-gate tranche
# par le coordinateur, acceptance : "la prescription est fonction de la cause,
# jamais un texte unique"). Une re-poussee a vide est le bon remede pour
# `skip_ci` / `retarget`, le MAUVAIS pour `conflict` (inerte, mesuree #14220).
# Les textes doivent nommer la cause mesuree, jamais une cause supposee --
# `prescribe()` produit le detail, `remediation_for()` le texte.

REMEDIATION_SKIP_CI = (
    "`PR gate` est absent du rollup de cette PR : elle est bloquee par un "
    "contexte requis qui n'a jamais ete rapporte, malgre des checks verts "
    "(issue #10928). Cause mesuree : le sujet du commit de tete porte le token "
    "`[skip ci]` -- GitHub a ignore tous les workflows `pull_request`.\n\n"
    "- Remede : **un nouveau push** dont le message ne porte pas le token "
    "(`git merge origin/main` puis push, ou un commit a message nu).\n"
    "- `close` / `reopen` **ne relance rien** : seul un evenement `synchronize` "
    "refait partir les workflows `pull_request`."
)

REMEDIATION_CONFLICT = (
    "`PR gate` est absent du rollup de cette PR car elle est **en conflit "
    "avec `main`** (`mergeable_state = dirty`). Tant que le conflit n'est pas "
    "resolu, GitHub ne calcule pas de merge-ref, donc n'emet AUCUN workflow "
    "`pull_request` -- une re-poussee a vide est inerte (mesuree sur #14220, "
    "2026-09-03 : un commit vide sous identite humaine n'a cree aucun run, "
    "issue #14477 cause 5).\n\n"
    "- Remede : resoudre le conflit -- `git merge origin/main`, resolution "
    "deliberee, push.\n"
    "- Ne pas depenser un commit vide : il ne sera pas lu tant que la PR "
    "reste `dirty`."
)

REMEDIATION_RETARGET = (
    "`PR gate` est absent du rollup de cette PR : sa base a change apres son "
    "dernier run `pull_request` (issue #14477 cause 4). Le retarget emet "
    "l'action `edited`, que pr-gate.yml n'ecoute pas (types par defaut "
    "`opened` / `synchronize` / `reopened`) : aucune fenetre n'a rerendu le "
    "check.\n\n"
    "- Remede : **commit vide a arbre identique** (declenche un `synchronize` "
    "sans toucher au contenu) -- mesure efficace sur #14441 : 7 runs -> 31 "
    "runs, le `PR gate` et `Secret Scan` sont re-dispatchs.\n"
    "  TREE=$(git rev-parse HEAD^{tree}); PARENT=$(git rev-parse HEAD)\n"
    "  NEW=$(git commit-tree \"$TREE\" -p \"$PARENT\" -m \"chore: wake pull_request workflows after base retarget\")\n"
    "  git push origin \"$NEW:<branche>\"\n"
    "- `close` / `reopen` ne relance rien : seul un `synchronize` refait "
    "partir les workflows `pull_request`."
)

REMEDIATION_UNKNOWN = (
    "`PR gate` est absent du rollup de cette PR et **la cause n'est pas "
    "determinee** : les mesures suivantes ont ete faites, aucune ne tranche.\n"
    "- `mergeable_state` = {ms} (pas `dirty`) ;\n"
    "- aucun evenement `base_ref_changed` dans la timeline ;\n"
    "- le sujet du commit de tete ne porte pas le token `[skip ci]` ;\n"
    "- auteur : {author} (pas une PR bot).\n\n"
    "Un remede au hasard coute un commit sans effet (issue #14477 : la "
    "prescription est fonction de la cause). Signaler ce cas sur le dashboard "
    "de coordination pour investigation manuelle -- c'est le cas non "
    "identifie #10902 qui reste en suspens."
)

REMEDIATION_BOT = (
    "PR ouverte par le bot (`app/github-actions`) sans `PR gate` dans son "
    "rollup : cas **structurel** (issue #10928). Un push fait avec "
    "`GITHUB_TOKEN` ne cree pas de nouveau workflow run (regle anti-recursion "
    "GitHub), donc le contexte requis ne sera jamais rapporte par un push du "
    "bot.\n\n"
    "- Remede : un **push humain** sur la branche (commit par un compte "
    "personnel), ou un **merge admin** via `gh auth switch -u jsboige`.\n"
    "- `close` / `reopen` ne relance rien."
)


def rollup_names(pr: dict) -> list[str]:
    """Check-run names / status contexts present in the PR's rollup.

    ``statusCheckRollup`` entries are either check-runs (carry ``name``) or
    status contexts (carry ``context``). Presence -- regardless of conclusion --
    is what matters: a queued/in_progress ``PR gate`` is not a defect.
    """
    names = []
    for entry in (pr.get("statusCheckRollup") or []):
        name = entry.get("name") or entry.get("context")
        if name:
            names.append(name)
    return names


def classify(pr: dict) -> tuple[str, str]:
    """Classify one open PR against its status-check rollup.

    Args:
        pr: ``{"number", "base_ref_name", "is_draft", "author_login",
               "statusCheckRollup": [...]}``

    Returns:
        ``(verdict, detail)`` where verdict is one of:
        ``"excluded_base"`` -- base branch != main: ``pr-gate.yml`` only fires on
            ``pull_request: branches: [main]``, so the check never appears here
            by design (false positive if flagged)
        ``"draft"``         -- draft PR: not mergeable yet, flagging is noise
        ``"has_gate"``      -- ``PR gate`` present (any conclusion) -- not a defect
        ``"bot_missing"``   -- bot PR, no ``PR gate`` (structural GITHUB_TOKEN case)
        ``"missing"``       -- the defect: no ``PR gate``, non-bot, non-draft
    """
    number = pr.get("number")
    if pr.get("base_ref_name") and pr["base_ref_name"] != "main":
        return ("excluded_base", f"#{number} base={pr['base_ref_name']} (pr-gate.yml ne tire que sur main)")
    if pr.get("is_draft"):
        return ("draft", f"#{number} draft PR, non mergeable")
    if GATE_NAME in rollup_names(pr):
        return ("has_gate", f"#{number} PR gate present (conclusion: {len(rollup_names(pr))} checks)")
    if pr.get("author_login") == BOT_LOGIN:
        return ("bot_missing", f"#{number} bot PR, no PR gate (structural)")
    return ("missing", f"#{number} PR gate absent du rollup")


def head_subject(pr: dict) -> str:
    """Sujet du commit de tete (champ ``head_subject``, fourni par le driver)."""
    return (pr.get("head_subject") or "").strip()


def prescribe(pr: dict) -> tuple[str, str]:
    """Prescrire le remede par cause -- design-gate #14477.

    Entrees mesurees par le driver (noms du contrat, valeur lue jamais
    supposee : ``mergeable_state``, ``base_changed_at`` (horodatage du dernier
    evenement ``base_ref_changed``, None si jamais), ``last_pr_run_at``
    (horodatage du dernier run ``pull_request`` du workflow PR gate sur la
    tete, None si aucun), ``head_subject``, ``author_login``).

    Ordre impose par #14477 (le dirty domine : il supprime TOUT run
    ``pull_request``, meme apres re-push -- mesure sur #14220 ; les causes
    suivantes agissent ensuite) :

        conflict  -> ``mergeable_state == "dirty"`` : remede = resoudre le
                     conflit, JAMAIS la re-poussee a vide
        retarget  -> un ``base_ref_changed`` postérieur au dernier run
                     ``pull_request`` : remede = commit vide a arbre identique
        skip_ci   -> token ``[skip ci]`` dans le sujet de tete (cause #10898)
        bot       -> PR ``app/github-actions`` (cause #10558)
        unknown   -> aucune des quatre : nommer les mesures, ne rien prescrire

    Returns:
        ``(cause, detail)`` ou ``detail`` porte les VALEURS lues.
    """
    ms = pr.get("mergeable_state")
    if ms == "dirty":
        return ("conflict", "mergeable_state=dirty (PR en conflit avec main)")
    changed = pr.get("base_changed_at")
    last = pr.get("last_pr_run_at")
    if changed and (not last or changed > last):
        return ("retarget",
                f"base_ref_changed={changed}, dernier run PR gate={last or 'aucun'}")
    if "[skip ci]" in head_subject(pr):
        return ("skip_ci", f"sujet de tete porte le token [skip ci] : {head_subject(pr)[:72]!r}")
    if pr.get("author_login") == BOT_LOGIN:
        return ("bot", "auteur app/github-actions -- push GITHUB_TOKEN sans run")
    return ("unknown",
            f"mergeable_state={ms}, pas de base_ref_changed, sujet sans [skip ci], "
            f"auteur {pr.get('author_login')}")


def remediation_for(cause: str, detail: str) -> str:
    """Texte de remediation pour une cause, valeurs mesurees ajoutees."""
    if cause == "conflict":
        return REMEDIATION_CONFLICT
    if cause == "retarget":
        return REMEDIATION_RETARGET
    if cause == "skip_ci":
        return REMEDIATION_SKIP_CI
    if cause == "bot":
        return REMEDIATION_BOT
    # unknown : le detail nomme les mesures faites (#14477 : "nommer les trois
    # mesures" -- pas de remede au hasard). On y relit les deux valeurs que le
    # texte du remede re-expose ; la forme du detail est garantie par
    # prescribe() et verifiee par les tests.
    ms = next((p.split("=", 1)[1] for p in detail.split(", ") if p.startswith("mergeable_state=")),
              "?")
    author = next((p[len("auteur "):] for p in detail.split(", ") if p.startswith("auteur ")),
                  "?")
    return REMEDIATION_UNKNOWN.format(ms=ms, author=author)


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    """Run a gh command, return parsed JSON (or None if empty). Raise on failure."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def _parse_json_stream(text: str) -> list:
    """Parse consecutive JSON documents into one flat list of rows.

    ``gh api --paginate --jq`` applies the jq program to EACH page and emits
    the outputs back to back -- not one array. Each document here is the jq
    result of one page (a list of row objects).
    """
    dec = json.JSONDecoder()
    rows: list = []
    idx, n = 0, len(text)
    while idx < n:
        while idx < n and text[idx] in " \t\r\n":
            idx += 1
        if idx >= n:
            break
        doc, idx = dec.raw_decode(text, idx)
        rows.extend(doc if isinstance(doc, list) else [doc])
    return rows


def _gh_rows(args: list[str]) -> list:
    """Run a gh command emitting a JSON stream, return flat rows."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return []
    return _parse_json_stream(proc.stdout)


def _gh_lines(args: list[str]) -> list[str]:
    """Run a gh command whose --jq emits bare scalars (gh prints jq string
    results UNQUOTED -- ``2026-09-03T15:06:03Z``, not JSON), one per page."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    return [line for line in proc.stdout.splitlines() if line.strip()]


def list_open_prs(repo: str) -> list[dict]:
    """Open PRs with the fields classify() needs -- REST, not GraphQL.

    The GraphQL rollup 504s on this repository's pool: measured 2026-08-17 in
    pr-gate-stale-sweep.yml (``gh pr list --limit 60 --json statusCheckRollup``
    = HTTP 504), re-measured 2026-09-03 at ``--limit 200`` (504 twice in a
    row). This organ now runs hourly next to the sweep (#14477), i.e. through
    busy hours too, so it collects the way the sweep does -- the same
    population, the same REST pagination, the same stated limit: /check-runs
    returns check runs only, not legacy commit statuses, and every check
    involved here is a check run.

    Check-runs are fetched only for PRs classify() will actually look at
    (base=main, non-draft): classify() rules those two out BEFORE reading the
    rollup, so excluded PRs never pay the per-PR call.
    """
    pulls = _gh_rows([
        "api", f"repos/{repo}/pulls?state=open&per_page=100", "--paginate",
        "--jq", '.[] | {number, draft: .draft, base: .base.ref, '
                'author: .user.login, sha: .head.sha}',
    ])
    out: list[dict] = []
    for p in pulls:
        rollup: list[dict] = []
        if p.get("base") == "main" and not p.get("draft"):
            names = _gh_json([
                "api", f"repos/{repo}/commits/{p['sha']}/check-runs?per_page=100",
                "--jq", "[.check_runs[].name]",
            ]) or []
            rollup = [{"name": n} for n in names]
        out.append({
            "number": p["number"],
            "base_ref_name": p.get("base"),
            "is_draft": bool(p.get("draft")),
            "author_login": p.get("author") or "",
            "statusCheckRollup": rollup,
        })
    return out


def enrich_candidate(repo: str, number: int) -> dict:
    """Measure the CAUSE fields for one candidate PR (gate absent).

    A few REST calls per candidate ONLY -- the pool of gate-absent PRs is
    small (a handful). Each value read here is the value the comment will
    name: never a presumed cause (#14477 acceptance: "le commentaire nomme la
    cause MESUREE, avec la valeur lue").

        pulls/N        -> mergeable_state (REST field; the gh CLI's
                          --json has no equivalent -- `mergeable` is a bool,
                          `mergeStateStatus` conflates BLOCKED with DIRTY)
        pr view        -> sujet du commit de tete (commits[-1].messageHeadline)
        issues/N/events-> dernier `base_ref_changed` (None si jamais)
        runs           -> dernier run `pull_request` du workflow PR gate
                          (None si aucun)
    """
    pull = _gh_json(["api", f"repos/{repo}/pulls/{number}",
                     "--jq", "{ms: .mergeable_state, sha: .head.sha}"]) or {}
    view = _gh_json(["pr", "view", str(number), "--repo", repo,
                     "--json", "commits"]) or {}
    commits = view.get("commits") or []
    head_subject = (commits[-1].get("messageHeadline") or "") if commits else ""
    # /events pages are reverse-chronological: the FIRST emitted document is
    # the most recent selection. jq takes .[0] within each page for the same
    # reason.
    changed_rows = _gh_lines([
        "api", f"repos/{repo}/issues/{number}/events", "--paginate", "--jq",
        "[.[] | select(.event == \"base_ref_changed\")] | .[0].created_at // empty",
    ])
    # Dernier run du WORKFLOW PR gate sur CE SHA -- pas "n'importe quel run
    # pull_request" : #14441 porte un run Always-on guards `edited` a
    # 11:55:50Z, posterieur a son retarget de 11:55:48Z ; seul un run du
    # workflow gate lui-meme, posterieur au retarget, disculpe la cause.
    # /actions/runs defaults to created desc: FIRST document = most recent.
    gate_run_rows = _gh_lines([
        "api", f"repos/{repo}/actions/runs?head_sha={pull.get('sha')}&per_page=100", "--jq",
        "[.workflow_runs[] | select(.name == \"PR gate\")] | sort_by(.created_at) | .[-1].created_at // empty",
    ])
    return {
        "mergeable_state": (pull or {}).get("ms"),
        "head_subject": head_subject,
        "base_changed_at": changed_rows[0] if changed_rows else None,
        "last_pr_run_at": gate_run_rows[0] if gate_run_rows else None,
    }


def ensure_label(repo: str, name: str, color: str, desc: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "label", "create", name, "--repo", repo,
         "--color", color, "--description", desc, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def has_label(pr: dict, name: str) -> bool:
    return any((lab.get("name") == name) for lab in (pr.get("labels") or []))


def apply_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "edit", str(number), "--repo", repo, "--add-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def remove_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "edit", str(number), "--repo", repo, "--remove-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def existing_comment(repo: str, number: int) -> int | None:
    """Return the id of an existing PR-gate-missing comment, or None."""
    comments = _gh_json(["pr", "view", str(number), "--repo", repo,
                         "--json", "comments"]) or {}
    for c in (comments.get("comments") or []):
        if COMMENT_MARKER_START in (c.get("body") or ""):
            return c["id"]
    return None


def _remediate_for(repo: str, number: int, extra: dict, verdict: str,
                   enriched: dict, args: object, counters: dict) -> None:
    """One gate-absent PR: label + comment, both driven by the measured cause.

    ``counters`` aggregates per-cause prints so the sweep log shows how the
    pool actually split (a "1 candidate" that is all ``unknown`` reads
    differently from one that is ``conflict``).
    """
    cause, detail = prescribe({**enriched, **extra})
    counters["cause_" + cause] = counters.get("cause_" + cause, 0) + 1

    label = args.label
    if cause == "conflict":
        label = args.label_conflict
    elif verdict == "bot_missing":
        label = args.label_bot
    remediation = remediation_for(cause, detail)

    if not has_label(enriched, label):
        apply_label(repo, number, label, args.dry_run)
    if not args.dry_run and existing_comment(repo, number) is None:
        post_comment(repo, number,
                     _comment_body(remediation, f"Cause mesuree : {detail}"),
                     args.dry_run)
    if cause == "conflict" and has_label(enriched, args.label):
        # The PR was flagged under the generic label by an earlier pass; the
        # conflict label now carries the accurate, choice-determining cause.
        remove_label(repo, number, args.label, args.dry_run)
    print(f"  #{number:<6} {verdict.upper():<8} cause={cause:<8} {detail}")


def post_comment(repo: str, number: int, body: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def labeled_prs(repo: str, label: str) -> dict[int, bool]:
    """Map PR number -> has-label for all open PRs carrying ``label``.

    Needed so a PR that regains its ``PR gate`` (re-push) gets the label
    retracted idempotently. ``gh pr list`` can filter by label, one query per
    label is enough.
    """
    raw = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open", "--limit", "200",
        "--label", label, "--json", "number,labels",
    ]) or []
    return {pr["number"]: True for pr in raw}


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dry-run", action="store_true", help="log classifications, apply no labels/comments")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--label", default=LABEL_DEFAULT, help=f"regular label name (default: {LABEL_DEFAULT})")
    ap.add_argument("--label-bot", default=LABEL_BOT_DEFAULT, help=f"bot label name (default: {LABEL_BOT_DEFAULT})")
    ap.add_argument("--label-conflict", default=LABEL_CONFLICT_DEFAULT,
                    help=f"conflict label name (default: {LABEL_CONFLICT_DEFAULT})")
    ap.add_argument("--limit", type=int, default=0, help="cap PRs processed (0 = all)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    if not args.dry_run:
        ensure_label(repo, args.label, LABEL_COLOR, LABEL_DESC, args.dry_run)
        ensure_label(repo, args.label_bot, LABEL_BOT_COLOR, LABEL_BOT_DESC, args.dry_run)
        ensure_label(repo, args.label_conflict, LABEL_CONFLICT_COLOR, LABEL_CONFLICT_DESC, args.dry_run)

    prs = list_open_prs(repo)
    if args.limit:
        prs = prs[: args.limit]

    # Map of PRs currently carrying each label (to retract when the gate returns).
    labeled = labeled_prs(repo, args.label)
    labeled_bot = labeled_prs(repo, args.label_bot)
    labeled_conflict = labeled_prs(repo, args.label_conflict)

    counts = {"missing": 0, "bot_missing": 0, "has_gate": 0, "draft": 0, "excluded_base": 0}
    causes = {}
    print(f"[pr-gate-missing] repo={repo} mode={'dry-run' if args.dry_run else 'apply'} "
          f"open_prs={len(prs)} label={args.label}")

    for pr in prs:
        number = pr["number"]
        enriched = {
            "number": number,
            "base_ref_name": pr.get("baseRefName"),
            "is_draft": pr.get("isDraft", False),
            "author_login": (pr.get("author") or {}).get("login", ""),
            "statusCheckRollup": pr.get("statusCheckRollup") or [],
            "labels": (pr.get("labels") or []),
        }
        verdict, why = classify(enriched)
        counts[verdict] = counts.get(verdict, 0) + 1

        if verdict in ("missing", "bot_missing"):
            _remediate_for(repo, number, enrich_candidate(repo, number),
                           verdict, enriched, args, causes)
        elif verdict == "has_gate":
            # Gate back (re-push / conflict resolved): retract labels
            # idempotently. The comment is left as history -- the label
            # retraction IS the resolution signal.
            if number in labeled:
                remove_label(repo, number, args.label, args.dry_run)
                print(f"  #{number:<6} has_gate   {why}  (label retracted)")
            if number in labeled_bot:
                remove_label(repo, number, args.label_bot, args.dry_run)
                print(f"  #{number:<6} has_gate   {why}  (bot label retracted)")
            if number in labeled_conflict:
                remove_label(repo, number, args.label_conflict, args.dry_run)
                print(f"  #{number:<6} has_gate   {why}  (conflict label retracted)")
        elif verdict == "draft":
            pass  # quiet -- the common non-defect case
        else:  # excluded_base
            pass  # quiet -- PRs targeting a feature branch never see PR gate

    print(f"[pr-gate-missing] done: {counts} causes={causes}")
    return 0


def _comment_body(remediation: str, cause_line: str = "") -> str:
    parts = [
        COMMENT_MARKER_START,
        "## PR gate absent du rollup (advisory, #10928)",
        "",
        remediation,
    ]
    if cause_line:
        parts += ["", cause_line]
    parts.append(COMMENT_MARKER_END)
    return "\n".join(parts)


if __name__ == "__main__":
    sys.exit(main())
