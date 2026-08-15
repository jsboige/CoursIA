#!/usr/bin/env python3
"""Gate pre-merge : aucun nit de review non leve ne doit survivre a un merge.

Pourquoi cet organe existe
--------------------------
Le champ `reviews[].state` est **structurellement aveugle** aux deux canaux de
review qui comptent le plus sur ce depot :

1. Le **user** poste ses nits comme *issue comments* (pas de review formelle) :
   il n'y a donc AUCUN `state` a lire — ni `CHANGES_REQUESTED`, ni meme une
   entree dans `reviews[]`.
2. **Hermes** (bot reviewer) poste ses reserves avec `state: COMMENTED` et le
   verdict en **prefixe de body** (`[Hermes] COMMENT_WITH_CONCERNS`) : lire
   l'etat renvoie `COMMENTED`, qui ne bloque rien.
3. Les **commentaires inline** de review vivent dans `reviewThreads` (GraphQL),
   une 3e surface absente de `gh pr view --json comments,reviews`.

Incident fondateur : PR #10761, mergee 2026-08-14T04:15Z malgre 2 nits user du
2026-08-13T11:07 (~17 h avant) et une review Hermes COMMENT_WITH_CONCERNS
confirmant les 2 nits + 3 points neufs dont « second reviewer obligatoire non
fourni ». `mergeStateStatus: CLEAN`, `reviews[].state: COMMENTED` : les deux
champs qu'un merge-gate lit d'ordinaire etaient verts.

Usage
-----
    python scripts/check_unaddressed_nits.py <PR>          # gate : exit 1 si bloque
    python scripts/check_unaddressed_nits.py <PR> --json   # sortie machine
    python scripts/check_unaddressed_nits.py --audit --limit 400   # audit retro

Un nit est considere **leve** si, apres son horodatage, on trouve au moins un de :
  - un commit pousse sur la branche (le nit a ete traite en code) ;
  - une reponse (comment) sur la PR (le nit a ete discute/refuse explicitement) ;
  - pour un thread inline : `isResolved: true` ou `isOutdated: true`.

Limite honnete de l'heuristique HUMAN
-------------------------------------
Le compte `jsboige` est utilise **a la fois** par le user et par les agents. Le
discriminant retenu est le **CRLF** : un commentaire redige dans l'UI web GitHub
porte `\r\n`, un commentaire poste via `gh` CLI porte `\n`. C'est fiable en
pratique sur ce depot mais ce n'est pas une preuve d'identite : un nit user
poste via `gh` serait manque (faux negatif), un agent collant du CRLF serait
signale a tort (faux positif). Le gate signale, l'humain tranche.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone

REPO = "jsboige/CoursIA"

BOT_LOGINS = {"github-actions", "codecov", "dependabot", "copilot-pull-request-reviewer"}

# Prefixes de tags utilises par les agents du cluster (protocole dashboard/PR).
AGENT_PREFIXES = (
    "[PART-OF-EPIC", "[GRAIN", "[CLAIMED", "[DONE", "[INFO", "[DISPATCH",
    "[ACK", "[RELEASED", "[OVERRIDE", "[MERGED", "[WARN", "[ERROR", "[ASK",
    "[REPLY", "[PROPOSAL", "[BLOCKED", "[ESCALATION",
)

# Marqueurs de reserve d'un reviewer bot (le verdict est dans le body, pas l'etat).
CONCERN_MARKERS = (
    "COMMENT_WITH_CONCERNS", "CHANGES_REQUESTED", "NEEDS_CHANGES", "CONCERNS",
    "SUSPECT_", "STRUCTURAL_ONLY", "avant merge", "avant de merger",
    "il va falloir", "a nuancer", "à nuancer",
)

# Un commentaire qui ANNONCE la levee ou le merge n'est pas un nit — il en est
# la resolution. Sans ce filtre, chaque « CHANGES_REQUESTED levée » est compte
# comme une reserve ouverte (faux positif massif, mesure sur 400 PRs).
LIFT_MARKERS = (
    "levée", "levee", "LGTM", "Mergé", "Merged", "je merge", "Merge.",
    "est adressé", "sont adressés", "sont levées", "est levée",
)


def ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def gh_json(args: list[str]) -> object:
    out = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True
    ).stdout
    return json.loads(out)


def classify(author: str, body: str) -> str | None:
    """'HUMAN' (nit user, UI web) | 'BOT-CONCERN' (reviewer avec reserves) | None."""
    if author in BOT_LOGINS or not body:
        return None
    stripped = body.lstrip()
    if any(m in body for m in LIFT_MARKERS):
        return None  # annonce de levee / de merge : resolution, pas reserve
    if stripped.startswith(AGENT_PREFIXES):
        # Tag de protocole agent : informatif, pas un nit — sauf s'il porte une reserve.
        return "BOT-CONCERN" if any(m in body for m in CONCERN_MARKERS) else None
    if "\r\n" in body:
        return "HUMAN"
    if any(m in body for m in CONCERN_MARKERS):
        return "BOT-CONCERN"
    return None


def review_threads(pr: int) -> list[dict]:
    """Threads inline (3e surface, absente de `gh pr view --json`)."""
    query = """
    query($owner:String!,$repo:String!,$n:Int!){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$n){
          reviewThreads(first:100){nodes{
            isResolved isOutdated path line
            comments(first:1){nodes{author{login} body createdAt}}
          }}
        }
      }
    }"""
    owner, name = REPO.split("/")
    data = gh_json([
        "api", "graphql", "-f", f"query={query}",
        "-F", f"owner={owner}", "-F", f"repo={name}", "-F", f"n={pr}",
    ])
    nodes = data["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]
    out = []
    for t in nodes:
        first = (t.get("comments") or {}).get("nodes") or [{}]
        c = first[0]
        out.append({
            "resolved": bool(t.get("isResolved")),
            "outdated": bool(t.get("isOutdated")),
            "path": t.get("path"),
            "line": t.get("line"),
            "author": (c.get("author") or {}).get("login", "?"),
            "body": c.get("body", ""),
            "createdAt": c.get("createdAt"),
        })
    return out


def analyse(pr_data: dict, threads: list[dict], cutoff: datetime) -> dict:
    """cutoff = mergedAt (audit retro) ou now (gate pre-merge)."""
    commits = [ts(c.get("committedDate")) for c in (pr_data.get("commits") or [])]
    commits = [c for c in commits if c]
    last_commit = max(commits) if commits else None

    comment_times = [ts(c["createdAt"]) for c in (pr_data.get("comments") or [])]
    comment_times = [t for t in comment_times if t]

    signals: list[tuple] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        kind = classify(login, c.get("body", ""))
        if kind:
            signals.append((ts(c["createdAt"]), kind, login, c.get("body", ""), "comment"))
    for r in pr_data.get("reviews") or []:
        login = (r.get("author") or {}).get("login", "")
        body = r.get("body", "")
        kind = classify(login, body)
        if r.get("state") == "CHANGES_REQUESTED":
            kind = "BOT-CONCERN" if kind is None else kind
        if kind:
            signals.append((ts(r.get("submittedAt")), kind, login, body,
                            f"review:{r.get('state')}"))

    blocking = []
    for (when, kind, login, body, src) in signals:
        if when is None or when >= cutoff:
            continue
        # Un commentaire posté APRÈS le merge ne peut pas avoir levé le nit :
        # c'est l'annonce de merge, pas une réponse. Sans cette borne, le gate
        # rate son propre incident fondateur (#10761, où mon commentaire de
        # merge « éteignait » rétroactivement le nit user posté 17 h plus tôt).
        if any(when < t < cutoff for t in comment_times):
            continue  # discute/refuse explicitement apres le nit, avant le merge
        # Un commit poussé après le nit ne le lève PAS à lui seul : sur #10761,
        # le « traitement » était un rebase à 19:41 qui n'adressait aucun des
        # deux nits de 11:07. Le push est reporté comme contexte, pas comme levée
        # — seule une réponse écrite (ou un thread résolu) lève une remarque.
        pushed_after = last_commit is not None and last_commit > when
        blocking.append({
            "kind": kind, "author": login, "src": src,
            "at": when.isoformat(),
            "gap_hours": round((cutoff - when).total_seconds() / 3600.0, 1),
            "code_pushed_after": pushed_after,
            "excerpt": " ".join(body.split())[:280],
        })

    for t in threads:
        if t["resolved"] or t["outdated"]:
            continue
        blocking.append({
            "kind": "INLINE-UNRESOLVED", "author": t["author"], "src": "reviewThread",
            "at": t.get("createdAt") or "?",
            "where": f"{t.get('path')}:{t.get('line')}",
            "excerpt": " ".join((t.get("body") or "").split())[:280],
        })

    return {
        "pr": pr_data.get("number"),
        "title": (pr_data.get("title") or "")[:110],
        "blocking": blocking,
        "blocked": bool(blocking),
    }


FIELDS = "number,title,mergedAt,author,comments,reviews,commits,url,state"

# `commits` porte une connection `authors` par commit : sur un `gh pr list` large,
# GraphQL depasse son plafond de 500 000 noeuds. L'audit retro liste donc SANS
# `commits`, puis ne les recupere que pour les PRs reellement candidates.
LIST_FIELDS = "number,title,mergedAt,url,comments,reviews"


def gate(pr: int, as_json: bool) -> int:
    data = gh_json(["pr", "view", str(pr), "--repo", REPO, "--json", FIELDS])
    merged = ts(data.get("mergedAt"))
    cutoff = merged or datetime.now(timezone.utc)
    result = analyse(data, review_threads(pr), cutoff)
    if as_json:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    elif not result["blocked"]:
        print(f"OK  PR #{pr} — aucun nit non leve.")
    else:
        print(f"BLOCKED  PR #{pr} — {len(result['blocking'])} nit(s) non leve(s) :\n")
        for b in result["blocking"]:
            where = b.get("where", "")
            gap = f" (+{b['gap_hours']}h avant merge)" if "gap_hours" in b else ""
            print(f"  [{b['kind']}] {b['author']} via {b['src']}{where}{gap}")
            print(f"      {b['excerpt']}\n")
        print("Lever chaque nit (commit, reponse explicite, ou issue de suivi nommee)")
        print("avant `gh pr merge`. Cf CLAUDE.md section B.0.")
    return 1 if result["blocked"] else 0


def audit(limit: int, search: str | None = None) -> int:
    cmd = ["pr", "list", "--repo", REPO, "--state", "merged",
           "--limit", str(limit), "--json", LIST_FIELDS]
    if search:
        # Partitionnement de l'historique entre lanes, ex :
        #   --search "merged:2026-07-01..2026-07-15"
        cmd += ["--search", search]
    prs = gh_json(cmd)
    findings = []
    for p in prs:
        merged = ts(p.get("mergedAt"))
        if not merged:
            continue
        # Pre-filtre sans `commits` : si rien ne ressort deja, inutile de payer
        # un appel de plus (les commits ne peuvent que LEVER un nit, jamais en creer).
        if not analyse(p, [], merged)["blocked"]:
            continue
        try:
            p["commits"] = gh_json(
                ["pr", "view", str(p["number"]), "--repo", REPO, "--json", "commits"]
            )["commits"]
        except subprocess.CalledProcessError:
            p["commits"] = []
        # Audit retro : on n'interroge pas les threads inline (1 appel GraphQL/PR).
        res = analyse(p, [], merged)
        if res["blocked"]:
            res["url"] = p.get("url")
            res["merged_at"] = p["mergedAt"]
            findings.append(res)
    findings.sort(key=lambda f: f["pr"], reverse=True)
    print(json.dumps({
        "scanned": len(prs),
        "search": search,
        "oldest_merged": min((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "newest_merged": max((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "flagged": len(findings),
        "findings": findings,
    }, indent=1, ensure_ascii=False))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pr", nargs="?", type=int, help="numero de PR (mode gate)")
    ap.add_argument("--audit", action="store_true", help="audit retro des PRs mergees")
    ap.add_argument("--limit", type=int, default=200, help="taille de l'audit retro")
    ap.add_argument("--search", help="filtre gh (ex: 'merged:2026-07-01..2026-07-15')")
    ap.add_argument("--json", action="store_true", help="sortie machine (mode gate)")
    args = ap.parse_args()
    if args.audit:
        return audit(args.limit, args.search)
    if args.pr is None:
        ap.error("fournir un numero de PR, ou --audit")
    return gate(args.pr, args.json)


if __name__ == "__main__":
    sys.exit(main())
