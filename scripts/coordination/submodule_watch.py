#!/usr/bin/env python3
"""Veille des sous-modules : PRs ouvertes et derive de gitlink, a chaque cycle.

Un sous-module est un depot qu'on fait vivre : son backlog est notre backlog
(``.claude/rules/submodule-maintenance.md``). Les mesures de cette regle vivaient
en prose (boucles shell a recopier) et aucune ne listait les PRs ouvertes dans
les depots de sous-modules. Le cycle coordinateur ne regardait que
``jsboige/CoursIA`` : MetaGeneticSharp#62 et Automata#10, propres et
fusionnables, ont attendu trois jours sans un regard (signalement du 19/10).

Cet organe repond a deux questions, pour chaque depot declare dans ``.gitmodules``
(la liste fait foi, jamais un souvenir) :

1. **Quelles PRs ouvertes attendent ?** Une PR humaine, hors brouillon, ouverte
   depuis plus de ``--max-age-hours`` heures, sans aucun commentaire ni review,
   est ``UNSEEN`` : personne ne l'a regardee. Les PRs de bots (Dependabot) sont
   comptees a part : elles ne rougissent pas l'organe, mais leur nombre et leur
   age s'affichent. Une PR dont le titre commence par ``[HOLD`` ou ``[WIP`` est
   un gel declare (``HOLD``) : comptee et affichee, elle ne rougit pas non plus.
   Les PRs se lisent page par page ; un compte lu different de ``totalCount``
   rend le depot illisible plutot que de taire la queue de la liste.
2. **Le gitlink de CoursIA suit-il sa branche ?** Meme mesure que la Regle 2 :
   ``git ls-tree <ref> <chemin>`` contre ``git ls-remote <url> <branche declaree>``
   (``HEAD`` quand ``.gitmodules`` ne declare pas de branche). Un ``ls-remote``
   muet donne ``INJOIGNABLE``, jamais une egalite.

Sorties : rc 0 = rien d'invisible ; rc 1 = au moins une PR ``UNSEEN`` ou une
``DERIVE`` ; rc 2 = au moins un depot illisible (``UNKNOWN``) et rien de rouge
par ailleurs. Un depot illisible n'est jamais compte comme vide.

Lecture seule. Le jeton s'epingle par commande (Regle 5), jamais par
``gh auth switch`` :

    GH_TOKEN=$(gh auth token -u jsboige) python scripts/coordination/submodule_watch.py
    GH_TOKEN=$(gh auth token -u jsboige) python scripts/coordination/submodule_watch.py --json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MAX_AGE_HOURS = 24.0
MAX_PAGES = 20  # 2 000 PRs ouvertes par depot : au-dela, le depot est declare illisible
# Gel declare dans le titre : la PR est comptee, elle ne rougit pas l'organe.
_HOLD_RE = re.compile(r"^\s*\[(HOLD|WIP)\b", re.IGNORECASE)

_URL_RE = re.compile(r"github\.com[:/]+([^/]+)/([^/]+?)(?:\.git)?/?$")

_PRS_QUERY = """
query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 100, after: $after, orderBy: {field: CREATED_AT, direction: ASC}) {
      totalCount
      pageInfo { hasNextPage endCursor }
      nodes {
        number title isDraft createdAt baseRefName mergeable
        author { __typename login }
        comments { totalCount }
        reviews { totalCount }
        commits(last: 1) { nodes { commit { statusCheckRollup { state } } } }
      }
    }
  }
}
"""

Runner = Callable[[list], "subprocess.CompletedProcess"]


def _run(cmd: list) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=ROOT)


def repo_slug(url: str) -> str | None:
    """``https://github.com/Org/Repo.git`` -> ``Org/Repo`` ; ``None`` hors GitHub."""
    m = _URL_RE.search(url.strip())
    return f"{m.group(1)}/{m.group(2)}" if m else None


def read_submodules(run: Runner = _run) -> list[dict]:
    """Lit ``.gitmodules`` : chemin, url, branche declaree (ou ``None``), slug GitHub."""
    out = run(["git", "config", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.(path|url|branch)$"])
    if out.returncode != 0:
        raise RuntimeError(f".gitmodules illisible : {out.stderr.strip()}")
    subs: dict[str, dict] = {}
    for line in out.stdout.splitlines():
        key, _, value = line.partition(" ")
        name, _, field = key[len("submodule."):].rpartition(".")
        subs.setdefault(name, {"name": name, "path": None, "url": None, "branch": None})[field] = value.strip()
    result = []
    for sub in subs.values():
        sub["slug"] = repo_slug(sub["url"] or "")
        result.append(sub)
    return sorted(result, key=lambda s: s["path"] or "")


def classify_pr(node: dict, now: datetime, max_age_hours: float) -> dict:
    """Ramene une PR GraphQL a une ligne de veille avec son etat."""
    created = datetime.fromisoformat(node["createdAt"].replace("Z", "+00:00"))
    age_h = (now - created).total_seconds() / 3600.0
    author = node.get("author") or {}
    login = author.get("login") or "?"
    is_bot = author.get("__typename") == "Bot" or login.endswith("[bot]")
    comments = (node.get("comments") or {}).get("totalCount", 0)
    reviews = (node.get("reviews") or {}).get("totalCount", 0)
    rollup = None
    commits = ((node.get("commits") or {}).get("nodes") or [])
    if commits:
        rollup = ((commits[-1].get("commit") or {}).get("statusCheckRollup") or {}).get("state")
    if is_bot:
        state = "BOT"
    elif node.get("isDraft"):
        state = "DRAFT"
    elif _HOLD_RE.match(node.get("title") or ""):
        state = "HOLD"
    elif comments == 0 and reviews == 0 and age_h > max_age_hours:
        state = "UNSEEN"
    else:
        state = "OPEN"
    return {
        "number": node["number"],
        "title": node.get("title", ""),
        "author": login,
        "created_at": node["createdAt"],
        "age_hours": round(age_h, 1),
        "base": node.get("baseRefName"),
        "mergeable": node.get("mergeable"),
        "checks": rollup or "NONE",
        "comments": comments,
        "reviews": reviews,
        "state": state,
    }


def fetch_prs(slug: str, run: Runner = _run) -> list[dict]:
    """Toutes les PRs ouvertes, page par page : une PR au-dela de la premiere page
    n'est jamais muette, et un compte lu different de ``totalCount`` rend le depot illisible."""
    owner, name = slug.split("/", 1)
    nodes: list[dict] = []
    after = None
    total = None
    for _ in range(MAX_PAGES):
        cmd = ["gh", "api", "graphql", "-f", f"query={_PRS_QUERY}", "-F", f"owner={owner}", "-F", f"name={name}"]
        if after:
            cmd += ["-f", f"after={after}"]
        out = run(cmd)
        if out.returncode != 0:
            raise RuntimeError(out.stderr.strip() or "gh api graphql a echoue")
        data = json.loads(out.stdout)
        repo = (data.get("data") or {}).get("repository")
        if repo is None:
            raise RuntimeError(f"depot illisible : {data.get('errors')}")
        page = repo["pullRequests"]
        total = page.get("totalCount", total)
        nodes.extend(page["nodes"])
        info = page.get("pageInfo") or {}
        if not info.get("hasNextPage"):
            break
        after = info.get("endCursor")
    else:
        raise RuntimeError(f"plus de {MAX_PAGES} pages de PRs ouvertes : lecture tronquee")
    if total is not None and len(nodes) != total:
        raise RuntimeError(f"lecture incomplete : {len(nodes)} PRs lues pour totalCount={total}")
    return nodes


def gitlink_drift(sub: dict, ref: str, run: Runner = _run) -> dict:
    """Regle 2 : gitlink de ``ref`` contre la tete de la branche declaree."""
    remote_ref = f"refs/heads/{sub['branch']}" if sub.get("branch") else "HEAD"
    tree = run(["git", "ls-tree", ref, sub["path"]])
    local = tree.stdout.split()[2] if tree.returncode == 0 and len(tree.stdout.split()) >= 3 else None
    remote_out = run(["git", "ls-remote", sub["url"], remote_ref])
    remote = remote_out.stdout.split()[0] if remote_out.returncode == 0 and remote_out.stdout.strip() else None
    if local is None or remote is None:
        state = "INJOIGNABLE"
    elif local == remote:
        state = "OK"
    else:
        state = "DERIVE"
    return {"state": state, "remote_ref": remote_ref, "gitlink": local, "remote_head": remote}


def watch(max_age_hours: float, ref: str, now: datetime, run: Runner = _run) -> dict:
    report = {"generated_at": now.isoformat(), "max_age_hours": max_age_hours, "ref": ref, "repos": []}
    for sub in read_submodules(run):
        entry = {"path": sub["path"], "slug": sub["slug"], "branch": sub["branch"]}
        entry["drift"] = gitlink_drift(sub, ref, run)
        if sub["slug"] is None:
            entry["prs_error"] = "url hors GitHub"
            entry["prs"] = None
        else:
            try:
                entry["prs"] = [classify_pr(n, now, max_age_hours) for n in fetch_prs(sub["slug"], run)]
            except (RuntimeError, json.JSONDecodeError, KeyError) as exc:
                entry["prs_error"] = str(exc)[:300]
                entry["prs"] = None
        report["repos"].append(entry)
    return report


def exit_code(report: dict) -> int:
    red = unknown = False
    for repo in report["repos"]:
        if repo["drift"]["state"] == "DERIVE":
            red = True
        if repo["drift"]["state"] == "INJOIGNABLE" or repo.get("prs") is None:
            unknown = True
        if any(pr["state"] == "UNSEEN" for pr in repo.get("prs") or []):
            red = True
    return 1 if red else (2 if unknown else 0)


def render(report: dict) -> str:
    lines = [f"Veille sous-modules ({report['generated_at'][:16]}Z, UNSEEN = humaine, sans commentaire ni review, > {report['max_age_hours']:g} h)"]
    for repo in report["repos"]:
        d = repo["drift"]
        drift = d["state"] if d["state"] != "DERIVE" else f"DERIVE {str(d['gitlink'])[:10]} -> {str(d['remote_head'])[:10]}"
        lines.append(f"\n== {repo['slug']} ({repo['path']}) -- gitlink vs {d['remote_ref']} : {drift}")
        prs = repo.get("prs")
        if prs is None:
            lines.append(f"   UNKNOWN : {repo.get('prs_error')}")
            continue
        humans = [p for p in prs if p["state"] != "BOT"]
        bots = [p for p in prs if p["state"] == "BOT"]
        for p in humans:
            lines.append(
                f"   {p['state']:<6} #{p['number']:<5} {p['age_hours']/24:5.1f} j  base={p['base']:<20} "
                f"checks={p['checks']:<8} c={p['comments']} r={p['reviews']}  {p['title'][:70]}"
            )
        if bots:
            oldest = max(p["age_hours"] for p in bots) / 24
            lines.append(f"   BOT    {len(bots)} PR(s) de bot, la plus ancienne a {oldest:.1f} j : {', '.join('#' + str(p['number']) for p in bots)}")
        if not prs:
            lines.append("   aucune PR ouverte")
    unseen = sum(1 for r in report["repos"] for p in (r.get("prs") or []) if p["state"] == "UNSEEN")
    lines.append(f"\nUNSEEN : {unseen} | rc={exit_code(report)} (0 = rien d'invisible, 1 = a traiter, 2 = depot illisible)")
    return "\n".join(lines)


def main(argv: list | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--max-age-hours", type=float, default=DEFAULT_MAX_AGE_HOURS)
    parser.add_argument("--ref", default="origin/main", help="arbre CoursIA dont on lit les gitlinks")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = watch(args.max_age_hours, args.ref, datetime.now(timezone.utc))
    except RuntimeError as exc:
        print(f"UNKNOWN : {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, ensure_ascii=False, indent=2) if args.json else render(report))
    return exit_code(report)


if __name__ == "__main__":
    sys.exit(main())
