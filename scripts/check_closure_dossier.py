#!/usr/bin/env python3
"""check_closure_dossier -- gate de fermeture d'issues (#17956 point 3).

Faire aux issues ce que ``check_adjoint_prevalidation.py`` fait aux PRs : la
fermeture d'une issue exige une lecture firsthand (G.9) que seul ai-01 signe,
et le goulot mesuré le 2026-09-26 est la FERMETURE (531 issues ouvertes,
precisions READY ~42 %). Une lane tierce -- qui n'a pas livre le travail --
pose un dossier de fermeture en commentaire sur l'issue :

    [CLOSURE PREFLIGHT]
    schema: 1
    lane: <machine:workspace>
    issue: <N>
    verdict: CLOSE | KEEP
    acceptance:
      - <critere> -> <PR#/commit/fichier:ligne>
    residue: none | followup #<M> | waiver: <motif date et falsifiable>
    open-prs: 0
    comments-reviewed: <n>
    [/CLOSURE PREFLIGHT]

Ce gate verifie mecaniquement le contrat, puis rend l'un des codes du gate PR :

    0  CLOSE integre   -- dossier intact, chaque controle vert ; ai-01 ferme
    3  KEEP integre    -- dossier intact qui atteste de rester ouvert ; ai-01
                         passe (le KEEP est un verdict, pas un echec)
    1  refuse          -- dossier absent, perime (commentaire non neutre
                         posterieur, PR ouverte referencant l'issue, PR citee
                         non merged, fille fermee), auto-atteste (la lane du
                         dossier est celle du [DELIVERED] / Grain: livrant),
                         ou malforme
    2  injoignable     -- gh a echoue (rate limit, reseau) ; jamais lu comme
                         « pas de dossier »

LA FERMETURE RESTE UN GESTE ai-01 (point 4) : le gate ne ferme rien, il
prepare la lecture G.9 minimale -- le dossier, le delta, la preuve decisive.

Controles (sur l'issue OUVERTE uniquement) :

  1. lane tierce      -- la lane du dossier != lane de tout [DELIVERED] de
                         l'issue et != lane du ``Grain:`` de toute PR merged
                         qui reference l'issue (auto-attestation refusee).
  2. posteriorite     -- aucun commentaire NON NEUTRE (humain ou shared
                         login, hors dossiers et marqueurs de bots) apres le
                         dossier : une reprise de discussion le perime.
  3. PRs citees       -- chaque ``#N`` cite dans l'acceptance est MERGED.
  4. PRs ouvertes     -- aucune PR ouverte ne reference l'issue
                         (``open-prs`` doit valoir le compte live, 0 pour un
                         CLOSE).
  5. fille citee      -- un ``residue: followup #M`` nomme une issue qui
                         existe et est OUVERTE.
  6. lecture complete -- ``comments-reviewed`` egale le nombre de
                         commentaires anterieurs au dossier.

Usage::

    python scripts/check_closure_dossier.py 17284            # une issue
    python scripts/check_closure_dossier.py 17284 --template --lane myia-po-2025:CoursIA-2
    python scripts/check_closure_dossier.py --sweep --limit 50   # label candidate-delivered, oldest-first

Voir aussi : #17956 (dispatch fondateur), check_adjoint_prevalidation.py
(meme grammaire de dossier), verifier_cleanup.py (le crible en amont),
candidate_delivered.py (le label).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from os.path import dirname, abspath
from typing import Any

try:
    from check_adjoint_prevalidation import QUALIFYING_LANES, GRAIN_LANE_RE
except ImportError:  # charge depuis scripts/ en invocation directe
    sys.path.insert(0, dirname(abspath(__file__)))
    from check_adjoint_prevalidation import (  # type: ignore[no-redef]
        QUALIFYING_LANES,
        GRAIN_LANE_RE,
    )

REPO = "jsboige/CoursIA"
LABEL = "candidate-delivered"
SHARED_GITHUB_LOGIN = "jsboige"

START = "[CLOSURE PREFLIGHT]"
END = "[/CLOSURE PREFLIGHT]"

VERDICT_CLOSE = "CLOSE"
VERDICT_KEEP = "KEEP"
CANONICAL_VERDICTS = (VERDICT_CLOSE, VERDICT_KEEP)

EXIT_CLOSE = 0
EXIT_REFUSED = 1
EXIT_UNKNOWN = 2
EXIT_KEEP = 3

REQUIRED_FIELDS = {
    "schema", "lane", "issue", "verdict", "acceptance", "residue",
    "open-prs", "comments-reviewed",
}
INTEGER_FIELDS = {"issue", "open-prs", "comments-reviewed"}

#: ``residue: none`` | ``residue: followup #123`` | ``residue: waiver: ...``
_RESIDUE_NONE_RE = re.compile(r"^none$")
_RESIDUE_FOLLOWUP_RE = re.compile(r"^followup\s+#(\d+)$")
_RESIDUE_WAIVER_RE = re.compile(r"^waiver:\s+\S.+")

#: ``[DELIVERED] lane <machine:workspace> ...`` -- protocole lane-claim.
_DELIVERED_LANE_RE = re.compile(
    r"\[DELIVERED\][^\n]*?\blane\s+([A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+)"
)

#: Un item d'acceptance : ``<critere> -> <preuve>``.
_ACCEPTANCE_ITEM_RE = re.compile(r"^(.+?)\s*->\s*(\S.+)$")

#: Tout ``#N`` dans une preuve d'acceptance (PRs citees).
_EVIDENCE_PR_RE = re.compile(r"#([1-9][0-9]*)")

#: Commentaires neutres pour la posteriorite : blocs de dossier (les deux
#: grammaires) et re-ecritures marker-gardees des bots. Le reste -- humain ou
#: shared login -- est une reprise de discussion qui perime.
_NEUTRAL_PREFIXES = (
    START,
    "[ADJOINT PREFLIGHT]",
    "<!-- PR-PATH-COLLISION:",
    "<!-- variation-genre-signals -->",
    "<!-- gvar2-light-cap -->",
    "<!-- trivial-diff-15740 -->",
)


def gh_json(args: list[str]) -> Any:
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "gh command failed")
    return json.loads(proc.stdout)


@dataclass(frozen=True)
class Dossier:
    fields: dict[str, str]
    acceptance: tuple[str, ...]
    comment_index: int
    author: str
    created_at: str = ""


def parse_dossier(
    body: str,
    comment_index: int,
    author: str,
    created_at: str = "",
) -> tuple[Dossier | None, list[str]]:
    """Parser un commentaire de dossier strictement delimite.

    ``acceptance`` est le seul champ multi-lignes : ses items ``- ...``
    suivent la ligne ``acceptance:``. La prose APRES le marqueur fermant est
    ignoree, jamais refusee (meme arbitrage que le gate PR, #16928).
    """
    lines = body.strip().splitlines()
    if not lines or lines[0].strip() != START:
        return None, []
    errors: list[str] = []
    closing = next(
        (i for i, line in enumerate(lines[1:], 1) if line.strip() == END),
        None,
    )
    if closing is None:
        errors.append("missing closing marker")
        content = lines[1:]
    else:
        content = lines[1:closing]

    fields: dict[str, str] = {}
    acceptance: list[str] = []
    in_acceptance = False
    for raw in content:
        if not raw.strip():
            continue
        if raw.lstrip().startswith("- ") and in_acceptance:
            acceptance.append(raw.strip()[2:].strip())
            continue
        if ":" not in raw:
            errors.append(f"malformed line: {raw.strip()}")
            in_acceptance = False
            continue
        key, value = (part.strip() for part in raw.split(":", 1))
        if key in fields:
            errors.append(f"duplicate field: {key}")
        fields[key] = value
        in_acceptance = key == "acceptance"

    missing = sorted(REQUIRED_FIELDS - fields.keys())
    unknown = sorted(fields.keys() - REQUIRED_FIELDS)
    if missing:
        errors.append("missing fields: " + ", ".join(missing))
    if unknown:
        errors.append("unknown fields: " + ", ".join(unknown))
    return Dossier(fields, tuple(acceptance), comment_index, author, created_at), errors


def _is_neutral_comment(row: dict[str, Any]) -> bool:
    body = (row.get("body") or "").strip()
    login = (row.get("author") or {}).get("login", "")
    if login.endswith("[bot]") or login == "github-actions":
        return True
    return any(body.startswith(p) for p in _NEUTRAL_PREFIXES)


def _merged_referring_prs(repo: str, number: int) -> list[dict[str, Any]]:
    """PRs MERGED referenceant l'issue (timeline cross-referenced), avec body."""
    events = gh_json([
        "api", f"repos/{repo}/issues/{number}/timeline", "--paginate",
    ]) or []
    out: list[dict[str, Any]] = []
    for ev in events:
        if ev.get("event") != "cross-referenced":
            continue
        src = (ev.get("source") or {}).get("issue") or {}
        pr = src.get("pull_request") or {}
        if not pr.get("merged_at"):
            continue
        body = gh_json([
            "pr", "view", str(src["number"]), "--repo", repo,
            "--json", "body", "--jq", ".body",
        ])
        out.append({"number": src["number"], "merged_at": pr["merged_at"],
                    "body": str(body) if body else ""})
    return out


def _open_pr_refs(repo: str, number: int) -> list[int]:
    query = f"is:open is:pr repo:{repo} #{number}"
    out = gh_json([
        "search", "issues", "--json", "number", "--limit", "20", query,
    ]) or []
    return [int(item["number"]) for item in out if item.get("number")]


def load_snapshot(repo: str, number: int) -> dict[str, Any]:
    """Tout ce que le gate lit sur une issue, en un endroit."""
    issue = gh_json([
        "issue", "view", str(number), "--repo", repo,
        "--json", "number,title,state,labels,comments,createdAt",
    ])
    if not isinstance(issue, dict) or "number" not in issue:
        raise RuntimeError(f"issue #{number} introuvable")
    comments = [
        {
            "author": c.get("author") or {},
            "created_at": c.get("createdAt") or "",
            "body": c.get("body") or "",
        }
        for c in (issue.get("comments") or [])
    ]
    return {
        "repo": repo,
        "number": int(issue["number"]),
        "title": issue.get("title") or "",
        "state": issue.get("state") or "",
        "labels": [lab.get("name") or "" for lab in (issue.get("labels") or [])],
        "created_at": issue.get("createdAt") or "",
        "comments": comments,
        "merged_prs": _merged_referring_prs(repo, number),
        "open_prs": _open_pr_refs(repo, number),
    }


def delivering_lanes(snapshot: dict[str, Any]) -> set[str]:
    """Lanes dont le travail est en jeu : [DELIVERED] de l'issue + Grain: des
    PRs merged qui la referencent. Une lane du dossier parmi elles =
    auto-attestation."""
    lanes: set[str] = set()
    for c in snapshot["comments"]:
        lanes.update(_DELIVERED_LANE_RE.findall(c.get("body") or ""))
    for pr in snapshot["merged_prs"]:
        lanes.update(GRAIN_LANE_RE.findall(pr.get("body") or ""))
    return lanes


def _cited_pr_numbers(dossier: Dossier) -> set[int]:
    out: set[int] = set()
    for item in dossier.acceptance:
        m = _ACCEPTANCE_ITEM_RE.match(item)
        if m:
            out.update(int(n) for n in _EVIDENCE_PR_RE.findall(m.group(2)))
    return out


def validate_dossier(dossier: Dossier, snapshot: dict[str, Any]) -> list[str]:
    """Integrite structurelle + controles mecaniques du contrat. Rend la liste
    des defauts ; vide = intact."""
    f = dossier.fields
    errors: list[str] = []

    if f.get("schema") != "1":
        errors.append("schema must be '1'")
    if dossier.author != SHARED_GITHUB_LOGIN:
        errors.append(f"comment author must be {SHARED_GITHUB_LOGIN!r}")
    if snapshot.get("state") != "OPEN":
        errors.append(f"issue state must be OPEN, live={snapshot.get('state')}")

    verdict = f.get("verdict", "")
    if verdict not in CANONICAL_VERDICTS:
        errors.append(
            "verdict must be one of " + ", ".join(map(repr, CANONICAL_VERDICTS))
        )
        return errors  # rien d'autre n'est interpretable

    try:
        issue_n = int(f.get("issue", ""))
        open_prs_claimed = int(f.get("open-prs", ""))
        comments_claimed = int(f.get("comments-reviewed", ""))
    except ValueError:
        errors.append("issue, open-prs and comments-reviewed must be integers")
        return errors
    if issue_n != snapshot["number"]:
        errors.append(f"issue is stale: dossier={issue_n}, live={snapshot['number']}")
    if open_prs_claimed != len(snapshot["open_prs"]):
        errors.append(
            "open-prs is stale: dossier="
            f"{open_prs_claimed}, live={len(snapshot['open_prs'])} "
            f"({snapshot['open_prs']})"
        )
    if comments_claimed != dossier.comment_index:
        errors.append(
            f"comments-reviewed is stale: dossier={comments_claimed}, "
            f"comments before the dossier={dossier.comment_index}"
        )

    lane = f.get("lane", "")
    if lane not in QUALIFYING_LANES:
        errors.append(
            f"lane must be one of the qualifying cluster lanes, got {lane!r}"
        )
    else:
        carriers = delivering_lanes(snapshot)
        if lane in carriers:
            errors.append(
                "self-attestation refused: the dossier lane "
                f"{lane!r} delivered or claimed this issue's work"
            )

    if not dossier.acceptance:
        errors.append("acceptance must carry at least one 'critere -> preuve' item")
    for item in dossier.acceptance:
        if not _ACCEPTANCE_ITEM_RE.match(item):
            errors.append(f"acceptance item lacks '->': {item[:60]!r}")

    residue = f.get("residue", "")
    followup_m = _RESIDUE_FOLLOWUP_RE.match(residue)
    if not (
        _RESIDUE_NONE_RE.match(residue)
        or followup_m
        or _RESIDUE_WAIVER_RE.match(residue)
    ):
        errors.append(
            "residue must be 'none', 'followup #<M>' or 'waiver: <motif daté>'"
        )
    if followup_m:
        child = gh_json([
            "issue", "view", followup_m.group(1), "--repo", snapshot["repo"],
            "--json", "number,state",
        ])
        if not isinstance(child, dict) or "state" not in child:
            errors.append(
                f"residue followup #{followup_m.group(1)} does not exist"
            )
        elif child["state"] != "OPEN":
            errors.append(
                f"residue followup #{followup_m.group(1)} is "
                f"{child['state']} -- a closed child does not keep the parent open"
            )

    # PRs citees dans les preuves : toutes MERGED.
    merged_numbers = {pr["number"] for pr in snapshot["merged_prs"]}
    for n in sorted(_cited_pr_numbers(dossier)):
        if n in merged_numbers:
            continue
        pr = gh_json([
            "pr", "view", str(n), "--repo", snapshot["repo"],
            "--json", "state,mergedAt",
        ])
        if not isinstance(pr, dict) or not pr.get("mergedAt"):
            state = (pr or {}).get("state", "introuvable")
            errors.append(f"cited PR #{n} is not MERGED (state={state})")

    # Posteriorite : aucun commentaire non neutre apres le dossier.
    for c in snapshot["comments"][dossier.comment_index + 1:]:
        if not _is_neutral_comment(c):
            who = (c.get("author") or {}).get("login", "?")
            errors.append(
                f"dossier is stale: non-neutral comment by {who} at "
                f"{c.get('created_at', '?')} postdates it"
            )
    return errors


def evaluate(snapshot: dict[str, Any]) -> tuple[str, list[str], Dossier | None]:
    """(verdict, errors, dossier) -- verdict CLOSE / KEEP / NO-DOSSIER."""
    for index, row in enumerate(snapshot["comments"]):
        body = row.get("body") or ""
        if not body.strip().startswith(START):
            continue
        dossier, errors = parse_dossier(
            body, index,
            (row.get("author") or {}).get("login", ""),
            row.get("created_at", ""),
        )
        if dossier is None:
            continue
        errors.extend(validate_dossier(dossier, snapshot))
        verdict = dossier.fields.get("verdict", "")
        if errors:
            return ("REFUSED", errors, dossier)
        if verdict == VERDICT_CLOSE:
            return (VERDICT_CLOSE, [], dossier)
        return (VERDICT_KEEP, [], dossier)
    return ("NO-DOSSIER", ["no [CLOSURE PREFLIGHT] comment on this issue"], None)


def render_template(snapshot: dict[str, Any], lane: str) -> str:
    """Rend les champs mecaniques ; la lane emetteuse pose verdict, acceptance
    et residue apres lecture firsthand (points 2 et 5 du dispatch)."""
    n_comments = len(snapshot["comments"])
    fields = (
        ("schema", "1"),
        ("lane", lane),
        ("issue", str(snapshot["number"])),
        ("verdict", "REPLACE_WITH_CLOSE_OR_KEEP"),
        ("acceptance", ""),
        ("residue", "REPLACE_WITH_none_OR_followup_#M_OR_waiver:_<motif daté>"),
        ("open-prs", str(len(snapshot["open_prs"]))),
        ("comments-reviewed", str(n_comments)),
    )
    lines = [START, *(f"{key}: {value}" for key, value in fields)]
    lines.append("  - REPLACE_WITH <critère du body> -> <PR#/commit/fichier:ligne>")
    lines.append(END)
    return "\n".join(lines)


def _list_sweep_issues(repo: str, limit: int) -> list[dict[str, Any]]:
    out = gh_json([
        "issue", "list", "--repo", repo, "--state", "open",
        "--label", LABEL, "--json", "number,title,createdAt",
        "--limit", str(limit if limit else 1000),
    ]) or []
    return sorted(out, key=lambda x: x.get("createdAt") or "")


def sweep(repo: str, limit: int, as_json: bool) -> int:
    """Passe oldest-first sur les issues labelisees -- le rapport que consomme
    la passe issues de /coordinate (point 4). Advisory : exit 0, jamais vert."""
    rows: list[dict[str, Any]] = []
    for item in _list_sweep_issues(repo, limit):
        number = int(item["number"])
        try:
            snapshot = load_snapshot(repo, number)
            verdict, errors, dossier = evaluate(snapshot)
        except (RuntimeError, json.JSONDecodeError, OSError) as exc:
            verdict, errors, dossier = "UNKNOWN", [f"UNKNOWN: {exc}"], None
        rc = {
            VERDICT_CLOSE: EXIT_CLOSE,
            VERDICT_KEEP: EXIT_KEEP,
            "NO-DOSSIER": EXIT_REFUSED,
            "REFUSED": EXIT_REFUSED,
        }.get(verdict, EXIT_UNKNOWN)
        rows.append({
            "issue": number, "title": (item.get("title") or "")[:60],
            "verdict": verdict, "rc": rc,
            "lane": (dossier.fields.get("lane") if dossier else None),
            "errors": errors,
        })
        label = {0: "CLOSE", 3: "KEEP", 1: "-", 2: "?"}[rc]
        print(f"  #{number:<6} {label:<6} {item.get('title', '')[:60]}")
        for e in errors[:2]:
            print(f"         {e}")
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    print(f"[closure-dossier] repo={repo} screened={len(rows)} " +
          " ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    if as_json:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("issue", type=int, nargs="?", default=None,
                        help="issue number (omitted with --sweep)")
    parser.add_argument("--template", action="store_true",
                        help="render a dossier template from the live issue")
    parser.add_argument("--lane", default="myia-po-2025:CoursIA-2",
                        choices=sorted(QUALIFYING_LANES),
                        help="lane emitting the dossier, for --template")
    parser.add_argument("--sweep", action="store_true",
                        help="screen every open labeled issue, oldest-first")
    parser.add_argument("--limit", type=int, default=100,
                        help="cap issues screened in --sweep (0 = all)")
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--json", action="store_true",
                        help="machine-readable output")
    args = parser.parse_args(argv)

    if args.sweep:
        return sweep(args.repo, args.limit, args.json)
    if not args.issue:
        parser.error("an issue number is required (or --sweep)")

    try:
        snapshot = load_snapshot(args.repo, args.issue)
        if args.template:
            print(render_template(snapshot, args.lane))
            return EXIT_CLOSE
        verdict, errors, dossier = evaluate(snapshot)
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        print(f"UNKNOWN -- {exc}")
        if args.json:
            print(json.dumps({"issue": args.issue, "verdict": "UNKNOWN",
                              "errors": [str(exc)]}, ensure_ascii=False))
        return EXIT_UNKNOWN

    if args.json:
        print(json.dumps({
            "issue": args.issue,
            "verdict": verdict,
            "lane": (dossier.fields.get("lane") if dossier else None),
            "errors": errors,
        }, ensure_ascii=False, indent=2))
    if verdict == VERDICT_CLOSE:
        print(f"CLOSE -- issue #{args.issue} carries an intact closure dossier "
              f"by {(dossier.fields.get('lane') or '?')}: ai-01 may close.")
        return EXIT_CLOSE
    if verdict == VERDICT_KEEP:
        print(f"KEEP -- issue #{args.issue} carries an intact dossier attesting "
              "it must stay open.")
        return EXIT_KEEP
    print(f"REFUSED -- issue #{args.issue} has no intact closure dossier:")
    for e in errors:
        print(f"  - {e}")
    return EXIT_REFUSED


if __name__ == "__main__":
    sys.exit(main())
