#!/usr/bin/env python3
"""Collecte les jambes de check des PRs ouvertes pour les balayeurs de portes.

Produit EXACTEMENT le fichier que leurs selecteurs consomment : une ligne
JSON par PR, avec les cles `number`, `sha`, `fork`, `merge_state`, `checks`
et `workflows`.

Ce que la MESURE a etabli (2026-11-15, pool ouvert de 174 PR) :

  - **les JAMBES se lisent en REST, une lecture par PR, pages comprises**.
    L'endpoint `commits/<sha>/check-runs` rend 100 check-runs par page, les
    plus **RECENTS** d'abord (identifiants decroissants). Mesure
    reproductible (tete de #26598, 123 runs) : page 1 = ids 132 918 765 225
    -> 132 885 793 360 ; page 2 = les 23 restants, tous plus petits
    (132 885 793 284 -> 132 885 792 238). Passer en GraphQL n'est PAS une
    economie : le schema borne le fan-out (une tete de PR porte jusqu'a
    46 suites et 135 runs), de sorte que couvrir le meme contenu en GraphQL
    impose ~1 PR par requete -- autant d'appels, en plus lourd, avec le
    risque de la limite secondaire. Mesure : 25 PR x 20 suites x 20 runs
    echoue ("Resource limits for this query exceeded") ; 5 PR x 64 suites x
    3 runs passe, et rend 29 jambes contre 94 en REST pour la meme PR.
  - **la lecture REST tronque, et c'est un defaut de CORRECTION**. Une tete
    qui porte plus de `per_page` runs exige les pages suivantes. La page 1
    seule donne une vue **INCOMPLETE**, pas une vue perimee : ce sont les
    runs les plus ANCIENS qui manquent, et une jambe peut alors disparaitre
    -- celle d'un nom de check dont TOUS ses runs sont plus anciens que la
    page 1. Mesure du 15/11 (176 PRs ouvertes, pliage par nom, « le plus
    recent gagne ») : 51 PRs portent plus de 100 runs ; pour 43 le verdict
    reste le meme, pour **8 il change** (VERT -> ROUGE : #26729, #26712,
    #26710, #26689, #26645, #26503, #26128, #25262). La pagination est donc
    ici, et elle est le vrai gain de ce changement.
  - **la carte des runs se lit en GraphQL, en bloc**. La clef de pliage du
    selecteur est (workflow_id, name) (#11808) : elle exige le `workflow_id`
    de chaque run, que GraphQL rend par suite -- SANS le fan-out des
    check-runs. Mesure : 18 appels GraphQL / 18 points pour les 174 PR,
    contre 150 appels REST (un par PR portant une jambe `PR gate`).
  - **la conclusion d'un RUN de workflow** (`startup_failure`) n'est exposee
    par AUCUN champ GraphQL : elle reste lue en REST, mais UNIQUEMENT pour
    les PRs dont la jambe `PR gate` est ROUGE -- la seule population dont le
    selecteur la consomme (#21300, `_run_conclusion`). Mesure : 77 PR sur 174.

Le cout du passage est nomme dans le resume (`api-quota:`) : appels REST,
pages lues, appels et points GraphQL.

Usage :

    python3 scripts/ci/fetch_pr_checkruns.py --repo owner/name \
        --prs /tmp/openprs.txt --out /tmp/runs.jsonl [--summary /tmp/s.json]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Callable

# Une lecture REST par PR, en parallele. Le balayeur faisait ses lectures
# SEQUENTIELLEMENT : 174 appels x ~1,4 s = ~4 min mesurees (l'etape 3 du
# balayeur prenait 11 min, contre un plafond de 25 min pour le job).
DEFAULT_WORKERS = 8

# `per_page` de l'endpoint `check-runs` : au-dela, l'endpoint tronque.
REST_PAGE_SIZE = 100

# Plafond de pages lues pour UNE tete. Au-dela, la lecture est INCOMPLETE :
# elle doit etre signalee, jamais absorbée en silence (une tete tronquee
# donne au selecteur une vue incomplete -- exactement le defaut corrige ici).
REST_MAX_PAGES = 50

# Le code HTTP est extrait du message de `gh` (`gh: <texte> (HTTP 403)`),
# jamais devine : une constante mentirait des le premier incident different.
_HTTP_CODE_RE = re.compile(r"HTTP (\d{3})")

# Bornes de la lecture GraphQL de la carte des runs : une page de PR et la
# fenetre de suites. La fenetre couvre les suites de la tete (mesure : 64
# suites au plus, sur 174 PR).
GRAPHQL_PAGE_SIZE = 10
GRAPHQL_SUITES = 64

# Reprises : la limite secondaire de l'API refuse la rafale sans vider le
# budget horaire. Elle se traite par une ATTENTE, jamais par un echec.
DEFAULT_MAX_RETRIES = 3
RETRY_WAIT_SECONDS = 20.0

# Les conclusions rouges du SELECTEUR (`pr-gate-stale-sweep.yml`, bloc
# python du heredoc). La liste est reprise a l'identique : c'est elle qui
# definit la population dont la conclusion de run est consommee.
RED = {"failure", "timed_out", "action_required", "cancelled"}

GRAPHQL_MAP_QUERY = """
query($owner:String!, $repo:String!, $n:Int!, $after:String, $suites:Int!) {
  rateLimit { cost remaining }
  repository(owner:$owner, name:$repo) {
    pullRequests(first:$n, after:$after, states:OPEN, baseRefName:"main",
                 orderBy:{field:UPDATED_AT, direction:DESC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        isDraft
        commits(last:1) {
          nodes {
            commit {
              checkSuites(last:$suites) {
                totalCount
                nodes {
                  workflowRun { databaseId workflow { databaseId name } }
                }
              }
            }
          }
        }
      }
    }
  }
}
"""


class CollectionError(RuntimeError):
    """La collecte n'a pas pu etre menee a bien."""


# --- transports ------------------------------------------------------------

def _is_secondary_limit(message: str) -> bool:
    """La LIMITE SECONDAIRE de l'API (detection d'abus) : elle ne vide pas le
    budget horaire, elle refuse la rafale. Elle se distingue du quota
    primaire par le message et se traite par une ATTENTE, pas par un Echec."""
    text = (message or "").lower()
    return ("rate limit already exceeded" in text
            or "secondary rate limit" in text
            or "abuse detection" in text
            or "please wait a few minutes" in text)


def gh_api(path: str, *, gh: str = "gh", retries: int = DEFAULT_MAX_RETRIES,
           sleep: Callable[[float], None] = time.sleep) -> dict:
    """Un appel REST via `gh api`. Le JSON stdout est la source.

    La limite secondaire se traite par une ATTENTE puis un rejeu : le budget
    horaire reste intact, seule la rafale est refusee.
    """
    last = ""
    for attempt in range(retries + 1):
        proc = subprocess.run([gh, "api", path], capture_output=True, text=True,
                              encoding="utf-8")
        if proc.returncode == 0:
            try:
                return json.loads(proc.stdout or "{}")
            except json.JSONDecodeError:
                raise CollectionError(f"GET {path} : reponse illisible")
        last = (proc.stderr or "").strip()
        if attempt < retries and _is_secondary_limit(last):
            sleep(RETRY_WAIT_SECONDS)
            continue
        break
    raise CollectionError(f"GET {path} : {last[:300]}")


def gh_graphql(query: str, variables: dict, *, gh: str = "gh",
               retries: int = DEFAULT_MAX_RETRIES,
               sleep: Callable[[float], None] = time.sleep) -> dict:
    """Une requete GraphQL via `gh api graphql`.

    `variables` voyage DANS le fichier : melanger `--input` et `-F` produit
    des variables nulles (mesure 2026-11-15).
    """
    payload = {"query": query, "variables": variables}
    handle = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False,
                                         encoding="utf-8")
    last = ""
    try:
        json.dump(payload, handle)
        handle.close()
        for attempt in range(retries + 1):
            proc = subprocess.run(
                [gh, "api", "graphql", "--input", handle.name],
                capture_output=True, text=True, encoding="utf-8")
            if proc.returncode == 0:
                try:
                    out = json.loads(proc.stdout or "{}")
                except json.JSONDecodeError:
                    raise CollectionError("reponse GraphQL illisible")
                if not isinstance(out, dict):
                    raise CollectionError("reponse GraphQL inattendue")
                errors = out.get("errors") or []
                if errors and not out.get("data"):
                    last = str(errors[0].get("message") or "erreur GraphQL")
                    if attempt < retries and _is_secondary_limit(last):
                        sleep(RETRY_WAIT_SECONDS)
                        continue
                    raise CollectionError(last[:300])
                return out
            last = (proc.stderr or "").strip()
            if attempt < retries and _is_secondary_limit(last):
                sleep(RETRY_WAIT_SECONDS)
                continue
            break
    finally:
        try:
            os.unlink(handle.name)
        except OSError:
            pass
    raise CollectionError(f"GraphQL : {last[:300]}")


# --- lecture du listing REST ------------------------------------------------

def parse_prs(path: str | os.PathLike) -> list[dict]:
    """Le listing REST du balayeur : `<numero> <sha> [<fork> [<merge_state>]]`
    par ligne. Les deux balayeurs n'ecrivent pas les memes champs : celui des
    portes ecrit `fork` et `merge_state`, celui d'adjacence n'ecrit que le
    numero et le sha."""
    prs: list[dict] = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            fields = line.split()
            if not fields:
                continue
            try:
                number = int(fields[0])
            except ValueError:
                continue
            prs.append({
                "number": number,
                "sha": fields[1] if len(fields) > 1 else "",
                "fork": (fields[2] if len(fields) > 2 else "false").lower() == "true",
                "merge_state": fields[3] if len(fields) > 3 else "",
            })
    return prs


# --- les jambes : REST, pagination comprise ---------------------------------

def _http_code(message: str) -> str:
    """Le code HTTP porte par le message de `gh`, ou son absence NOMMEE."""
    match = _HTTP_CODE_RE.search(message or "")
    return f"HTTP {match.group(1)}" if match else "aucun code HTTP"


def _flat(message: str, limit: int = 300) -> str:
    """Un message sur une seule ligne, borne (le `detail=` des annotations)."""
    return " ".join((message or "").split())[:limit]


def _unreadable_entry(repo: str, pr: dict, error: str) -> dict:
    """Le detail d'une PR ILLISIBLE : sa SHA, l'endpoint reellement appele,
    le code HTTP extrait du message, et le message lui-meme.

    La SHA est celle de la PR dont la lecture a ECHOUE : le no-op du
    balayeur nomme ainsi le DERNIER echec, pas une PR lue (le pin
    positionnel du workflow, re-pointe sur cette fonction).
    """
    return {
        "sha": pr["sha"],
        "endpoint": f"GET repos/{repo}/commits/{pr['sha']}/check-runs",
        "code": _http_code(error),
        "detail": _flat(error),
    }


def legs_from_rest(check_runs: list[dict]) -> list[dict]:
    """Les jambes d'une PR, au contrat du selecteur.

    REST rend les conclusions en minuscules ("success", "failure") : le
    contrat reste celui de REST, et le selecteur compare aux ensembles
    RED/GREEN inchanges.
    """
    legs: list[dict] = []
    for run in check_runs:
        legs.append({
            "name": run.get("name") or "",
            "status": (run.get("status") or "").lower(),
            "conclusion": (run.get("conclusion") or "").lower(),
            "started_at": run.get("started_at") or "",
            "details_url": run.get("details_url") or "",
            "title": ((run.get("output") or {}).get("title") or ""),
        })
    return legs


def read_legs(repo: str, sha: str, *, rest: Callable[[str], dict] = gh_api,
              page_size: int = REST_PAGE_SIZE,
              max_pages: int = REST_MAX_PAGES) -> tuple[list[dict], int, int, bool]:
    """Les jambes d'une tete de commit, TOUTES les pages lues.

    L'endpoint rend `per_page` runs par page, les plus **RECENTS** d'abord
    (identifiants decroissants) : une tete qui porte plus de `per_page` runs
    exige les pages suivantes, sinon le balayeur lit une vue **INCOMPLETE**
    (les runs les plus anciens manquent) et une jambe peut disparaitre --
    celle d'un nom de check dont tous ses runs sont plus anciens que la
    page 1. Le nombre de pages lues est rendu : il entre dans le quota.

    Le dernier booleen rend la TRONCATURE : au-dela de `max_pages` pages, la
    lecture est incomplete, et une lecture incomplete doit etre signalee
    (une troncature muette rendrait au selecteur une vue incomplete, sans
    trace). Le plafond existait ; ce qui manquait, c'est sa declaration.
    """
    legs: list[dict] = []
    pages = 0
    total = None
    page = 1
    truncated = False
    while True:
        payload = rest(f"repos/{repo}/commits/{sha}/check-runs"
                       f"?per_page={page_size}&page={page}")
        pages += 1
        if total is None:
            raw_total = payload.get("total_count")
            total = raw_total if isinstance(raw_total, int) else None
        runs = payload.get("check_runs") or []
        legs.extend(legs_from_rest(runs))
        # `total_count` arrete la pagination exactement : une tete dont le
        # total est un multiple exact de `per_page` ne coute pas une lecture
        # de plus.
        if total is not None and len(legs) >= total:
            break
        if len(runs) < page_size:
            break
        page += 1
        if page > max_pages:      # garde-fou : jamais plus de 5000 runs par tete
            truncated = True
            break
    return legs, pages, (total if total is not None else len(legs)), truncated


def red_gate_legs(checks: list[dict]) -> bool:
    """Une jambe `PR gate` ROUGE ? (la seule population dont le selecteur
    consomme la conclusion du run de workflow -- `_run_conclusion`)."""
    for check in checks:
        if (check.get("name") or "") == "PR gate" and \
                (check.get("conclusion") or "") in RED:
            return True
    return False


# --- la carte des runs : GraphQL, en bloc -----------------------------------

def read_run_maps(repo: str, *, transport: Callable[[str, dict], dict] = gh_graphql,
                  page_size: int = GRAPHQL_PAGE_SIZE,
                  suites: int = GRAPHQL_SUITES,
                  ) -> tuple[dict[int, dict], dict]:
    """`numero de PR -> {run_id: workflow_id}` pour tout le pool.

    La clef de pliage du selecteur est (workflow_id, name) (#11808) : elle
    exige le `workflow_id` de chaque run. GraphQL le rend par suite, SANS le
    fan-out des check-runs -- c'est ce qui rend la lecture en bloc possible
    (mesure : 18 appels pour 174 PR, contre 150 appels REST).

    Une PR dont la fenetre de suites est trop courte est COMPTEE, pas
    silenciee : son pliage retombe sur le run id (le comportement historique,
    jamais plus permissif).
    """
    owner, _, name = repo.partition("/")
    if not owner or not name:
        raise CollectionError(f"repo illisible: {repo!r}")
    maps: dict[int, dict] = {}
    truncated: list[int] = []
    graphql_errors: list[str] = []
    null_repository_pages = 0
    calls = 0
    points = 0
    after: str | None = None
    while True:
        payload = transport(GRAPHQL_MAP_QUERY, {
            "owner": owner, "repo": name, "n": page_size, "after": after,
            "suites": suites})
        calls += 1
        data = payload.get("data") or {}
        # #26739 -- une reponse qui porte `data` ET `errors` n'echoue pas :
        # elle rend une carte PARTIELLE. La muette faisait croire a une
        # carte complete -- le repli (run_id) ne s'appliquait qu'aux PRs
        # concernees, sans que personne ne le sache.
        for error in payload.get("errors") or []:
            graphql_errors.append(_flat(str((error or {}).get("message")
                                            or error)))
        cost = ((data.get("rateLimit") or {}).get("cost") or 0)
        if isinstance(cost, int):
            points += cost
        repository = data.get("repository")
        if repository is None:
            # Une page `repository: null` rend une carte VIDE : le repli
            # (run_id) s'y applique pour TOUTES les PRs du pool. C'est le
            # meme defaut que la carte fenetree, sans meme la fenetre.
            null_repository_pages += 1
        connection = ((repository or {}).get("pullRequests") or {})
        for node in connection.get("nodes") or []:
            if not node or node.get("isDraft"):
                continue
            number = node.get("number")
            if number is None:
                continue
            mapping: dict[str, int] = {}
            suite_total = None
            for commit_node in ((node.get("commits") or {}).get("nodes") or []):
                commit = commit_node.get("commit") or {}
                suites_connection = commit.get("checkSuites") or {}
                if suite_total is None:
                    raw = suites_connection.get("totalCount")
                    suite_total = raw if isinstance(raw, int) else None
                for suite in suites_connection.get("nodes") or []:
                    run = suite.get("workflowRun") or {}
                    workflow = run.get("workflow") or {}
                    run_id = run.get("databaseId")
                    workflow_id = workflow.get("databaseId")
                    if run_id is not None and workflow_id is not None:
                        mapping[str(run_id)] = workflow_id
            maps[int(number)] = mapping
            if suite_total is not None and suite_total > suites:
                truncated.append(int(number))
        page_info = connection.get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        after = page_info.get("endCursor")
        if not after:
            break
    return maps, {"graphql_calls": calls, "graphql_points": points,
                  "map_truncated": sorted(truncated),
                  "graphql_errors": graphql_errors,
                  "null_repository_pages": null_repository_pages}


def read_run_conclusions(repo: str, sha: str, *,
                         rest: Callable[[str], dict] = gh_api) -> dict:
    """`run_id -> {wf, c}` pour UN sha. Un appel REST.

    La `conclusion` d'un RUN de workflow (`startup_failure`) n'est exposee par
    aucun champ GraphQL : elle reste lue en REST, mais UNIQUEMENT pour les
    PRs dont la jambe `PR gate` est ROUGE (#21300).
    """
    payload = rest(f"repos/{repo}/actions/runs?head_sha={sha}&per_page=100")
    runs = payload.get("workflow_runs") or []
    return {
        str(run.get("id")): {"wf": run.get("workflow_id"),
                             "c": run.get("conclusion") or ""}
        for run in runs if run.get("id") is not None
    }


# --- la collecte ------------------------------------------------------------

def collect(*, repo: str, prs: list[dict],
            workers: int = DEFAULT_WORKERS,
            rest: Callable[[str], dict] = gh_api,
            graphql: Callable[[str, dict], dict] = gh_graphql,
            use_run_map: bool = True,
            use_run_conclusions: bool = True,
            ) -> tuple[list[dict], dict]:
    """Les lignes JSONL et le resume de la collecte."""
    wanted = {pr["number"]: pr for pr in prs}
    legs: dict[int, list[dict]] = {}
    unreadable: dict[int, str] = {}
    unreadable_detail: dict[int, dict] = {}
    truncated_prs: list[int] = []
    pages_read = 0
    rest_calls = 0
    lock = threading.Lock()

    def read_one(pr: dict) -> tuple[int, list[dict], int, str, bool]:
        try:
            pr_legs, pages, _total, truncated = read_legs(repo, pr["sha"],
                                                          rest=rest)
            return pr["number"], pr_legs, pages, "", truncated
        except CollectionError as exc:
            return pr["number"], [], 0, str(exc), False

    if prs:
        with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
            for number, pr_legs, pages, error, truncated in pool.map(read_one, prs):
                with lock:
                    rest_calls += pages
                    pages_read += pages
                if error:
                    unreadable[number] = error[:200]
                    unreadable_detail[number] = _unreadable_entry(
                        repo, wanted[number], error)
                    continue
                if truncated:
                    truncated_prs.append(number)
                legs[number] = pr_legs

    # Le DERNIER echec, dans l'ORDRE DU LISTING : c'est lui que le no-op du
    # balayeur nomme (endpoint + code + detail). Le parcours suit `prs`, pas
    # l'ordre d'arrivee des threads -- deux executions du meme pool peuvent
    # differer, et le no-op doit etre reproductible.
    last_unreadable: dict = {}
    for pr in prs:
        entry = unreadable_detail.get(pr["number"])
        if entry:
            last_unreadable = {"pr": pr["number"], **entry}

    # La carte des runs (clef de pliage) : GraphQL, en bloc.
    run_maps: dict[int, dict] = {}
    graphql_stats = {"graphql_calls": 0, "graphql_points": 0,
                     "map_truncated": [], "graphql_errors": [],
                     "null_repository_pages": 0}
    if use_run_map:
        run_maps, graphql_stats = read_run_maps(repo, transport=graphql)

    # Les conclusions de run : REST, pour les seules PRs a jambe rouge.
    conclusions: dict[int, dict] = {}
    conclusion_failures = 0
    if use_run_conclusions:
        for number, pr_legs in legs.items():
            if not red_gate_legs(pr_legs):
                continue
            sha = wanted[number]["sha"]
            try:
                conclusions[number] = read_run_conclusions(repo, sha, rest=rest)
            except CollectionError:
                conclusion_failures += 1
            with lock:
                rest_calls += 1

    lines: list[dict] = []
    for pr in prs:
        number = pr["number"]
        if number not in legs:
            continue
        workflows: dict[str, dict] = {}
        for run_id, workflow_id in (run_maps.get(number) or {}).items():
            workflows[run_id] = {"wf": workflow_id, "c": ""}
        for run_id, entry in (conclusions.get(number) or {}).items():
            local = workflows.setdefault(run_id, {"wf": entry.get("wf"), "c": ""})
            if entry.get("wf") is not None:
                local["wf"] = entry["wf"]
            if entry.get("c"):
                local["c"] = entry["c"]
        lines.append({
            "number": number,
            "sha": pr["sha"],
            "fork": pr["fork"],
            "merge_state": pr["merge_state"],
            "checks": legs[number],
            "workflows": workflows,
        })

    summary = {
        "prs_listed": len(prs),
        "prs_inspected": len(lines),
        "prs_omitted": len(prs) - len(lines),
        "rest_calls": rest_calls,
        "rest_pages": pages_read,
        "graphql_calls": graphql_stats["graphql_calls"],
        "graphql_points": graphql_stats["graphql_points"],
        "map_truncated": graphql_stats["map_truncated"],
        "run_conclusion_calls": len(conclusions),
        "run_conclusion_failures": conclusion_failures,
        "unreadable": {str(k): v for k, v in unreadable.items()},
        "unreadable_prs": sorted(unreadable),
        # #26739 -- les trois muets du resume, nommes.
        "unreadable_detail": {str(k): v for k, v in unreadable_detail.items()},
        "last_unreadable": last_unreadable,
        "truncated_prs": sorted(truncated_prs),
        "rest_page_cap": REST_MAX_PAGES * REST_PAGE_SIZE,
        "graphql_errors": graphql_stats["graphql_errors"],
        "null_repository_pages": graphql_stats["null_repository_pages"],
    }
    return lines, summary


def write_jsonl(path: str | os.PathLike, lines: list[dict]) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        for line in lines:
            handle.write(json.dumps(line, ensure_ascii=False) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--prs", required=True, help="listing REST")
    parser.add_argument("--out", required=True, help="fichier JSONL produit")
    parser.add_argument("--summary", help="fichier JSON de resume")
    parser.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    parser.add_argument("--no-run-map", action="store_true",
                        help="ne lire AUCUNE carte de runs (GraphQL)")
    parser.add_argument("--no-run-conclusions", action="store_true",
                        help="ne lire AUCUNE conclusion de run en REST")
    parser.add_argument("--annotation-prefix", default="[stale-sweep]",
                        help="prefixe des annotations emises sur stderr")
    parser.add_argument("--json", action="store_true",
                        help="ecrire le resume sur stdout")
    args = parser.parse_args(argv)

    prs = parse_prs(args.prs)
    try:
        lines, summary = collect(
            repo=args.repo, prs=prs, workers=args.workers,
            use_run_map=not args.no_run_map,
            use_run_conclusions=not args.no_run_conclusions)
    except CollectionError as exc:
        print(f"::error::{args.annotation_prefix} NO-OP -- check-runs collection "
              f"failed: {exc}", file=sys.stderr)
        return 1

    write_jsonl(args.out, lines)
    summary["api_quota"] = (
        f"api-quota: {summary['rest_calls']} appel(s) REST "
        f"({summary['rest_pages']} page(s) lue(s)), "
        f"{summary['graphql_calls']} appel(s) GraphQL "
        f"({summary['graphql_points']} point(s))")
    if summary["prs_listed"] and not summary["prs_inspected"]:
        print(f"::error::{args.annotation_prefix} NO-OP -- aucune PR inspectee: "
              "la collecte n'a rien produit (aucun balayage n'a eu lieu)",
              file=sys.stderr)
        return 2
    if summary["run_conclusion_failures"]:
        print(f"::warning::{args.annotation_prefix} run map incomplete: "
              f"{summary['run_conclusion_failures']} lecture(s) REST en echec "
              "(la detection startup_failure est sans verdict sur ces PRs)",
              file=sys.stderr)
    if summary["map_truncated"]:
        print(f"::warning::{args.annotation_prefix} carte des runs fenetree: "
              f"{len(summary['map_truncated'])} PR(s) ont plus de "
              f"{GRAPHQL_SUITES} suites -- leur pliage retombe sur le run id",
              file=sys.stderr)
    # #26739 -- les muets du resume sont NOMMES. Chacun de ces cas rendait
    # une lecture PARTIELLE silencieuse : le selecteur recevait une carte
    # incomplete sans le savoir.
    if summary.get("truncated_prs"):
        print(f"::warning::{args.annotation_prefix} lecture tronquee: "
              f"{','.join('#' + str(n) for n in summary.get('truncated_prs') or [])} "
              f"portent plus de {summary.get('rest_page_cap')} check-runs -- les "
              "pages au-dela du plafond n'ont pas ete lues",
              file=sys.stderr)
    if summary.get("unreadable_prs"):
        print(f"::warning::{args.annotation_prefix} PRs illisibles: "
              f"{','.join('#' + str(n) for n in summary.get('unreadable_prs') or [])} "
              "-- lectures en echec, ces PRs ne sont pas inspectees",
              file=sys.stderr)
    if summary.get("graphql_errors"):
        print(f"::warning::{args.annotation_prefix} erreurs GraphQL "
              f"partielles: {len(summary.get('graphql_errors') or [])} -- reponse "
              f"portant data ET errors: {(summary.get('graphql_errors') or ['aucun'])[0]}",
              file=sys.stderr)
    if summary.get("null_repository_pages"):
        print(f"::warning::{args.annotation_prefix} repository nul sur "
              f"{summary.get('null_repository_pages')} page(s) GraphQL -- la carte "
              "des runs est incomplete pour ces pages",
              file=sys.stderr)
    if args.summary:
        Path(args.summary).write_text(
            json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    if args.json:
        print(json.dumps(summary, ensure_ascii=False))
    else:
        print(f"[check-runs] prs listees={summary['prs_listed']} "
              f"inspectees={summary['prs_inspected']} "
              f"omises={summary['prs_omitted']} -- {summary['api_quota']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
