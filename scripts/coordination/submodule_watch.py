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
   **Les checks se lisent par jambe, pas par l'agregat.** ``statusCheckRollup.state``
   est une somme : un rouge d'infrastructure (secret d'application absent, action
   tierce cassee) y rougit **toutes** les PRs du depot, et l'agregat ne permet pas
   de distinguer ce rouge-la d'un rouge propre au diff. Une jambe qui echoue sur
   **toutes** les PRs qui la portent, et portee par **au moins deux** PRs, est
   classee ``INFRA`` : affichee avec sa liste de PRs, elle ne se confond plus avec
   ``FAILURE``. Une jambe rouge sur une seule PR reste ``FAILURE`` — le
   classement est *fail-closed*, il ne masque jamais un rouge propre. Une lecture
   de jambes **tronquee** (plus de 100 contextes, compte lu different de
   ``totalCount``) ne sert jamais a blanchir : elle est ecartee et la PR retombe
   sur son agregat.
2. **Le gitlink de CoursIA suit-il sa branche ?** Meme mesure que la Regle 2 :
   ``git ls-tree <ref> <chemin>`` contre ``git ls-remote <url> <branche declaree>``
   (``HEAD`` quand ``.gitmodules`` ne declare pas de branche). Un ``ls-remote``
   muet donne ``INJOIGNABLE``, jamais une egalite.

Sorties : rc 0 = rien d'invisible ; rc 1 = au moins une PR ``UNSEEN`` ou une
``DERIVE`` ; rc 2 = au moins un depot illisible (``UNKNOWN``) et rien de rouge
par ailleurs. Un depot illisible n'est jamais compte comme vide.

Mode ``--drift-only`` (Regle 2 seule, sans lecture de PRs)
---------------------------------------------------------
La veille ci-dessus suppose un jeton GraphQL et se joue au rythme des cycles de
coordination. Or la derive de gitlink a un proprietaire naturel -- Dependabot --
qui peut silencieusement disparaitre : le 2026-10-29, Dependabot n'a produit
**aucune** PR (tous ecosystemes) depuis le 27/10, alors que le sous-module
Argumentum avait derape de 26 commits. Raison mesuree : le pin de ``main`` a ete
avance a la main de 84 commits (PR #22958, 20:57Z), soit 5 minutes avant que
Dependabot n'auto-cloture sa propre PR (#22823, 21:02Z, « up-to-date now ») :
Dependabot n'avait alors plus de cible a proposer, et son resolution de branche
s'est figee sur une ref du 23/10. Un depot dont l'automatisation est muette a
besoin d'un **autre** regard, et ce regard doit etre quotidien.

``--drift-only`` ne lit que la Regle 2 (``git ls-tree`` + ``git ls-remote``, plus
l'API ``compare`` pour la distance), sans toucher aux PRs : il tourne sans jeton
et sans GraphQL, donc en CI comme en local.

Seuil ``--max-ahead N``
-----------------------
Une derive de **quelques** commits est normale : le sous-module avance tous les
jours et le pin suit au rythme des bumps. Un garde qui rougit sur toute derive
serait rouge en permanence, donc ignore (le piege des gardes sur ``main``). Le
seuil porte sur la **distance** de derive, mesuree par ``ahead_by`` de l'API
``compare`` (nombre de commits dont la branche declaree s'est avancee depuis le
gitlink epingle). rc 1 = au moins un sous-module derive de plus de ``N``
commits (bump en retard, actionnable) ; rc 2 = mesure impossible (depot
injoignable ou ``compare`` muet) : une mesure absente n'est jamais un zero, et
elle ne fait pas rougir une CI sur un incident de reseau.

Le seuil de 10 a ete porte a 40 sur une mesure : Argumentum, la plus active des
cinq, prend **16 commits par jour actif** (100 commits sur 6 jours actifs, 24-29
octobre 2026). A 10, le garde rougissait donc apres **une seule** journee
d'activite amont -- tous les jours pour un cron quotidien, donc jamais lu. La
valeur se lit comme une duree : 40 commits ~ 2,5 jours actifs medians.

Deux consequences pour qui consomme le JSON, et c'est le contrat :

- ``ahead_by`` vaut ``0`` en etat ``OK`` (mesure : pas de derive), ``None`` en
  etat ``DERIVE`` dont la distance n'a pas pu etre mesuree, et ``None`` en etat
  ``INJOIGNABLE``. Un consommateur ne doit **jamais** lire ``ahead_by`` sans lire
  ``state`` : ``0`` signifie « mesure et nulle », pas « je ne sais pas » ;
- ``rc`` est un confort **local**. La CI ne decide pas sur lui : Python rend
  ``1`` aussi bien sur une derive que sur une exception non rattrapee, et un
  artefact vide concluerait alors « bump en retard ». Le workflow lit le JSON,
  qui est la seule source de verite, et traite un artefact absent ou illisible
  comme une panne de mesure -- pas comme une derive.

Lecture seule. Le jeton s'epingle par commande (Regle 5), jamais par
``gh auth switch`` :

    GH_TOKEN=$(gh auth token -u jsboige) python scripts/coordination/submodule_watch.py
    GH_TOKEN=$(gh auth token -u jsboige) python scripts/coordination/submodule_watch.py --json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MAX_AGE_HOURS = 24.0
# Distance de derive au-dela de laquelle le bump est en retard : sous ce seuil,
# la derive est le fonctionnement normal (le pin suit au rythme des bumps).
#
# Pourquoi 40, et pas 10. Mesure du 2026-10-30 sur la branche declaree
# d'Argumentum (la plus active des cinq) : 100 commits sur 6 jours actifs entre
# le 24 et le 29/10, mediane **16 commits par jour actif**. Le seuil est donc une
# **duree deguisee** : a 10, il etait franchi par une seule journee d'activite
# amont, c'est-a-dire presque chaque jour pour un cron quotidien -- exactement le
# rouge permanent qu'on apprend a ignorer. 40 correspond a ~2,5 jours actifs
# medians : le pin peut prendre un jour de retard sans bruit, et un bump
# reellement oublie rougit en trois jours au lieu de trois semaines.
DEFAULT_MAX_AHEAD = 40
MAX_PAGES = 20  # 2 000 PRs ouvertes par depot : au-dela, le depot est declare illisible
# Gel declare dans le titre : la PR est comptee, elle ne rougit pas l'organe.
_HOLD_RE = re.compile(r"^\s*\[(HOLD|WIP)\b", re.IGNORECASE)

_URL_RE = re.compile(r"github\.com[:/]+([^/]+)/([^/]+?)(?:\.git)?/?$")

# Conclusions de ``CheckRun`` qui comptent comme un echec, et etats de ``StatusContext``.
_FAILING_CHECKRUN = {"FAILURE", "TIMED_OUT", "CANCELLED", "ACTION_REQUIRED", "STARTUP_FAILURE"}
_FAILING_STATUS = {"FAILURE", "ERROR"}
# ``EXPECTED`` = statut cree, pas encore traite : plus proche d'attendre que d'etre vert.
_PENDING_STATUS = {"PENDING", "EXPECTED"}

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
        commits(last: 1) { nodes { commit { statusCheckRollup {
          state
          contexts(first: 100) {
            totalCount
            nodes {
              __typename
              ... on CheckRun { name status conclusion }
              ... on StatusContext { context state }
            }
          }
        } } } }
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


def check_rollup(node: dict) -> dict:
    """Le ``statusCheckRollup`` de la tete de la PR, ou ``{}`` s'il n'y en a pas."""
    commits = ((node.get("commits") or {}).get("nodes") or [])
    if not commits:
        return {}
    return (commits[-1].get("commit") or {}).get("statusCheckRollup") or {}


def pr_legs(node: dict) -> dict:
    """Verdict par jambe : ``{nom: FAILURE|PENDING|OK}``.

    Un ``CheckRun`` non termine est ``PENDING`` quoi que dise sa conclusion (elle est
    nulle tant qu'il tourne). Un ``StatusContext`` ``EXPECTED`` (statut cree, pas
    encore traite) est ``PENDING``, pas ``OK`` ; une conclusion ``STALE`` est lue
    ``OK`` sciemment, GitHub l'affichant neutre.

    Les jambes ne sont lues que si l'API les rend **en entier** : un rollup sans
    ``contexts``, ou dont le nombre de noeuds differt de ``totalCount`` (plus de 100
    jambes), rend ``{}`` et l'appelant retombe sur l'agregat. C'est le sens
    fail-closed de la troncature : une jambe rouge situee au-dela du cap et portee
    par une seule PR disparaitrait de la liste, la PR perdrait son ``own_failing``
    et pourrait passer ``INFRA`` sur ses jambes partagees — une lecture partielle
    ne doit donc jamais servir a blanchir."""
    rollup = check_rollup(node)
    contexts = rollup.get("contexts") or {}
    raw = contexts.get("nodes") or []
    total = contexts.get("totalCount")
    if isinstance(total, int) and len(raw) != total:
        return {}
    legs: dict[str, str] = {}
    for ctx in raw:
        if not isinstance(ctx, dict):
            continue
        if ctx.get("__typename") == "StatusContext" or "context" in ctx:
            state = (ctx.get("state") or "").upper()
            if state in _FAILING_STATUS:
                legs[ctx.get("context") or "?"] = "FAILURE"
            elif state in _PENDING_STATUS:
                legs[ctx.get("context") or "?"] = "PENDING"
            else:
                legs[ctx.get("context") or "?"] = "OK"
            continue
        name = ctx.get("name") or "?"
        status = (ctx.get("status") or "").upper()
        conclusion = (ctx.get("conclusion") or "").upper()
        if status and status != "COMPLETED":
            legs[name] = "PENDING"
        elif conclusion in _FAILING_CHECKRUN:
            legs[name] = "FAILURE"
        else:
            legs[name] = "OK"
    return legs


def repo_infra_legs(rows: list[dict]) -> dict:
    """Jambes rouges sur **toutes** les PRs qui les portent, portees par >= 2 PRs.

    Un rouge d'infrastructure frappe le depot entier ; il ne dit rien du diff d'une
    PR. Le seuil de deux porteurs est ce qui rend le classement sur : une jambe
    portee par une seule PR ne peut pas etre declaree infra, donc un rouge propre
    reste un rouge (fail-closed)."""
    carriers: dict[str, list[int]] = {}
    verdicts: dict[str, list[str]] = {}
    for row in rows:
        for name, verdict in (row.get("legs") or {}).items():
            carriers.setdefault(name, []).append(row["number"])
            verdicts.setdefault(name, []).append(verdict)
    return {
        name: sorted(carriers[name])
        for name in carriers
        if len(carriers[name]) >= 2 and all(v == "FAILURE" for v in verdicts[name])
    }


def apply_infra(rows: list[dict], infra: dict) -> list[dict]:
    """Separe le rouge propre a la PR du rouge d'infrastructure, sans jamais masquer le premier."""
    for row in rows:
        legs = row.get("legs") or {}
        own = sorted(n for n, v in legs.items() if v == "FAILURE" and n not in infra)
        shared = sorted(n for n in infra if legs.get(n) == "FAILURE")
        row["own_failing"] = own
        if own:
            row["checks"] = "FAILURE"
        elif shared:
            row["checks"] = "INFRA"
    return rows


def classify_pr(node: dict, now: datetime, max_age_hours: float) -> dict:
    """Ramene une PR GraphQL a une ligne de veille avec son etat."""
    created = datetime.fromisoformat(node["createdAt"].replace("Z", "+00:00"))
    age_h = (now - created).total_seconds() / 3600.0
    author = node.get("author") or {}
    login = author.get("login") or "?"
    is_bot = author.get("__typename") == "Bot" or login.endswith("[bot]")
    comments = (node.get("comments") or {}).get("totalCount", 0)
    reviews = (node.get("reviews") or {}).get("totalCount", 0)
    rollup = check_rollup(node).get("state")
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
        "legs": pr_legs(node),
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


def compare_ahead(slug: str | None, base: str | None, head: str | None, opener=None) -> int | None:
    """Distance de derive : combien de commits la tete a gagne depuis le gitlink.

    L'egalite des SHA ne dit pas *combien* le sous-module a derive : une derive
    de 2 commits et une derive de 26 ne se traitent pas de la meme facon. L'API
    ``compare`` de GitHub repond ``ahead_by`` : le nombre de commits dont la
    tete de branche est en avance sur le gitlink epingle.

    Appel REST stdlib (pas de ``gh``, pas de jeton obligatoire) : les depots de
    sous-modules sont publics, et le mode ``--drift-only`` doit tourner en CI
    sans dependre du binaire ``gh`` ni d'un secret. Un jeton est utilise quand
    il est present dans l'environnement (rate limit plus large).

    Un ``compare`` muet, en erreur, ou une reponse illisible donne ``None`` : une
    mesure absente n'est jamais un zero, et elle ne fait jamais passer une
    derive pour une egalite.
    """
    if not slug or not base or not head:
        return None
    url = f"https://api.github.com/repos/{slug}/compare/{base}...{head}"
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "coursia-submodule-watch",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    open_fn = opener or urlopen
    try:
        with open_fn(Request(url, headers=headers), timeout=30) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except (OSError, ValueError, HTTPError, URLError):
        return None
    value = payload.get("ahead_by") if isinstance(payload, dict) else None
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def gitlink_drift(sub: dict, ref: str, run: Runner = _run, opener=None) -> dict:
    """Regle 2 : gitlink de ``ref`` contre la tete de la branche declaree.

    ``ahead_by`` ne vaut ``0`` que sur une **mesure** (etat ``OK``) : en etat
    ``INJOIGNABLE`` il vaut ``None``, pour qu'un consommateur qui ne lit que ce
    champ ne conclue pas « pas de derive » sur un depot muet.
    """
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
    if state == "DERIVE":
        ahead = compare_ahead(sub.get("slug"), local, remote, opener)
    elif state == "OK":
        ahead = 0
    else:
        ahead = None
    return {
        "state": state,
        "remote_ref": remote_ref,
        "gitlink": local,
        "remote_head": remote,
        "ahead_by": ahead,
    }


def watch(
    max_age_hours: float,
    ref: str,
    now: datetime,
    run: Runner = _run,
    with_prs: bool = True,
    opener=None,
) -> dict:
    report = {"generated_at": now.isoformat(), "max_age_hours": max_age_hours, "ref": ref, "repos": []}
    for sub in read_submodules(run):
        entry = {"path": sub["path"], "slug": sub["slug"], "branch": sub["branch"]}
        entry["drift"] = gitlink_drift(sub, ref, run, opener)
        if not with_prs:
            report["repos"].append(entry)
            continue
        if sub["slug"] is None:
            entry["prs_error"] = "url hors GitHub"
            entry["prs"] = None
        else:
            try:
                rows = [classify_pr(n, now, max_age_hours) for n in fetch_prs(sub["slug"], run)]
                entry["infra"] = repo_infra_legs(rows)
                entry["prs"] = apply_infra(rows, entry["infra"])
            except (RuntimeError, json.JSONDecodeError, KeyError) as exc:
                entry["prs_error"] = str(exc)[:300]
                entry["prs"] = None
        report["repos"].append(entry)
    return report


def drift_exit_code(report: dict, max_ahead: int) -> int:
    """rc du mode ``--drift-only`` : 1 = derive en retard, 2 = mesure impossible.

    Une derive dont la distance n'a pas pu etre mesuree ne fait pas rougir : elle
    est signalee dans la sortie et dans l'artefact, mais un incident de reseau ne
    doit pas transformer une CI de veille en garde permanent rouge. Une derive
    **mesuree** au-dela du seuil, elle, est un bump en retard et vaut rc 1.
    """
    overdue = False
    unknown = False
    for repo in report["repos"]:
        drift = repo["drift"]
        if drift["state"] == "INJOIGNABLE":
            unknown = True
        elif drift["state"] == "DERIVE":
            ahead = drift.get("ahead_by")
            if ahead is None:
                unknown = True
            elif ahead > max_ahead:
                overdue = True
    return 1 if overdue else (2 if unknown else 0)


def render_drift(report: dict, max_ahead: int) -> str:
    lines = [
        f"Derive de gitlink ({report['generated_at'][:16]}Z, ref={report['ref']}, "
        f"bump en retard au-dela de {max_ahead} commits)"
    ]
    for repo in report["repos"]:
        d = repo["drift"]
        if d["state"] == "OK":
            state = "OK"
        elif d["state"] == "INJOIGNABLE":
            state = "INJOIGNABLE (depot muet : jamais une egalite)"
        else:
            ahead = d.get("ahead_by")
            distance = f"{ahead} commits" if ahead is not None else "distance non mesuree"
            state = f"DERIVE {str(d['gitlink'])[:10]} -> {str(d['remote_head'])[:10]} ({distance})"
        lines.append(f"== {repo['slug']} ({repo['path']}) -- vs {d['remote_ref']} : {state}")
    lines.append(f"\nrc={drift_exit_code(report, max_ahead)} (0 = rien, 1 = derive en retard, 2 = mesure impossible)")
    return "\n".join(lines)


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
        infra = repo.get("infra") or {}
        if infra:
            lines.append(
                "   INFRA  jambe(s) rouge(s) sur toutes les PRs du depot, "
                + ", ".join(f"{name} ({len(nums)} PRs)" for name, nums in sorted(infra.items()))
            )
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
    parser.add_argument(
        "--drift-only",
        action="store_true",
        help="Regle 2 seule : aucune lecture de PRs, aucun jeton GraphQL requis",
    )
    parser.add_argument(
        "--max-ahead",
        type=int,
        default=DEFAULT_MAX_AHEAD,
        help="distance de derive (commits) au-dela de laquelle le bump est en retard",
    )
    args = parser.parse_args(argv)
    try:
        report = watch(args.max_age_hours, args.ref, datetime.now(timezone.utc), with_prs=not args.drift_only)
    except RuntimeError as exc:
        print(f"UNKNOWN : {exc}", file=sys.stderr)
        return 2
    if args.drift_only:
        report["max_ahead"] = args.max_ahead
        print(
            json.dumps(report, ensure_ascii=False, indent=2)
            if args.json
            else render_drift(report, args.max_ahead)
        )
        return drift_exit_code(report, args.max_ahead)
    print(json.dumps(report, ensure_ascii=False, indent=2) if args.json else render(report))
    return exit_code(report)


if __name__ == "__main__":
    sys.exit(main())
