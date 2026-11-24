"""Lectures groupees de GitHub et de git pour le tapis rapide (#22983).

Modules de la voie legere qui lancent un processus : celui-ci et
`coordination.gh_selection` (selection leger) ; `run(argv, timeout)` est
injecte. Le cache et le verrou sont dans `coordination.gh_cache` (#22630).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import time
from collections.abc import Callable
from datetime import UTC, datetime, timedelta
from pathlib import Path

from coordination.gh_lecture import (  # noqa: F401  -- adresse unique
    Lecture, LectureIncomplete, issue)

Run = Callable[[list[str], int], str]

DEPOT_GH = "jsboige/CoursIA"
#: Le plafond d'UN appel (`gh api`, `git log`) : un appel qui depasse est
#: coupe, pas attendu. A ne pas confondre avec la duree d'un ETAGE : c'est
#: l'echeance partagee qui borne l'etage (#28114, I6).
TIMEOUT_S = 15
#: Le `git fetch` est un aller-retour reseau (mesure du 22/11 : 18 a 20 s) :
#: il a son propre plafond, plus large que celui d'un appel.
FETCH_TIMEOUT_S = 90
#: Un appel qui porte des **CORPS** (la page du pool, la qualification d'un
#: lot) dure plus longtemps qu'un appel de metadonnees : mesure du 23/11 sur
#: ce siege, 3,76 s pour la page du pool (50 issues, corps + 12 commentaires)
#: et 2,05 s pour la qualification d'un lot de 50. Le plafond de 15 s les
#: couperait sur un reseau lent, sans mesure derriere : ils gardent le
#: plafond large, mesure a l'appui.
TIMEOUT_S_CORPS = 90
#: L'echeance UNIQUE d'un tirage de lane, partagee par ses etages.
MUR_TIRAGE_S = 60
# Un 502/504 se resorbe en relisant la meme page en plus petit.
TAILLES_PAGE = (50, 25, 12)
PAGES_PRS_MAX = 20  # au-dela : lecture incomplete plutot que tronquee
FETCH_AGE_MAX_H = 6  # age max de la pointe locale d'origin/main sans fetch
_TRANSITOIRE_RE = re.compile(r"\b50[24]\b|Bad Gateway|Gateway Time-?out", re.IGNORECASE)
_CITATION_RE = re.compile(r"#(\d+)\b")
# Un commit FERME #N s'il le nomme apres un mot de fermeture, ou dans la portee de son
# sujet (`type(zone,#N):`, le tag du grain) ; `See #N` et `Part of #N` ne livrent rien.
_FERME_RE = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s*:?\s+#(\d+)\b",
                       re.IGNORECASE)
_PORTEE_RE = re.compile(r"^[\w.\- ]+\(([^)]*)\)\s*:")
_ISO = "%Y-%m-%dT%H:%M:%SZ"
_PR_TEXTE = ("title", "body", "created_at", "updated_at")
# Requete legere : y ajouter `timelineItems` fait repondre le serveur en 504.
QUERY = """query($owner:String!,$name:String!,$n:Int!,$after:String){
 repository(owner:$owner,name:$name){
  issues(states:OPEN,first:$n,after:$after,orderBy:{field:CREATED_AT,direction:ASC}){
   pageInfo{hasNextPage endCursor}
   nodes{number title body createdAt updatedAt labels(first:20){nodes{name}}
    comments(last:12){totalCount nodes{createdAt author{login} body}}}}}}"""


def run_defaut(argv: list[str], timeout: int) -> str:
    """`subprocess.run` borne ; un code non nul leve `CalledProcessError`."""
    return subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                          timeout=timeout, check=True).stdout


def _timeout(echeance: float | None, plafond: float = TIMEOUT_S,
             horloge=time.monotonic) -> int:
    """Le timeout d'un appel : le plus petit du plafond et du temps restant.

    L'echeance est **monotone et unique** : elle est posee une fois pour tout
    le tirage et partagee par ses etages. Le temps restant est recalcule
    avant chaque appel, donc un etage qui a consomme sa part voit l'etage
    suivant etre coupe plutot qu'attendu (#28114, I6).

    Sans echeance (un appel isole), le plafond de l'appel s'applique seul.
    """
    if echeance is None:
        return int(plafond)
    return max(1, int(min(plafond, echeance - horloge())))


def _appel(run: Run, argv: list[str], lecture: str, page: object,
           timeout: int | None = None) -> str | None:
    """Un appel ; None sur une panne transitoire (502/504, timeout)."""
    try:
        return run(argv, TIMEOUT_S if timeout is None else timeout)
    except subprocess.TimeoutExpired:
        return None
    except subprocess.CalledProcessError as exc:
        cause = f"{' '.join(argv[:3])} rc={exc.returncode} : {str(exc.stderr or '')[:300]}"
        if _TRANSITOIRE_RE.search(cause):
            return None
        raise LectureIncomplete(lecture, page, cause) from exc
    except OSError as exc:
        raise LectureIncomplete(lecture, page, f"commande introuvable : {exc}") from exc


def _page_issues(run: Run, depot: str, after: str | None, page: int) -> dict:
    """Une page d'issues, rejouee a la taille suivante sur panne transitoire."""
    owner, name = depot.split("/")
    for taille in TAILLES_PAGE:
        argv = ["gh", "api", "graphql", "-f", f"query={QUERY}", "-f", f"owner={owner}",
                "-f", f"name={name}", "-F", f"n={taille}"]
        texte = _appel(run, argv + (["-f", f"after={after}"] if after else []), "issues",
                       page, timeout=TIMEOUT_S_CORPS)
        if texte is None:
            continue
        try:
            return json.loads(texte)["data"]["repository"]["issues"]
        except (ValueError, KeyError, TypeError) as exc:
            raise LectureIncomplete("issues", page, f"reponse illisible : {exc}") from exc
    raise LectureIncomplete("issues", page, f"502/504 ou timeout aux tailles {TAILLES_PAGE}")


def lire_issues_ouvertes(run: Run = run_defaut, depot: str = DEPOT_GH) -> list[dict]:
    """Toutes les issues ouvertes (12 derniers commentaires), jamais partielle."""
    issues: list[dict] = []
    after, page = None, 1
    while True:
        data = _page_issues(run, depot, after, page)
        issues.extend(issue(node) for node in data["nodes"])
        if not data["pageInfo"]["hasNextPage"]:
            return issues
        after, page = data["pageInfo"]["endCursor"], page + 1


def lire_prs_ouvertes(run: Run = run_defaut, depot: str = DEPOT_GH,
                      echeance: float | None = None) -> list[dict]:
    """Les PRs ouvertes, REST pagine par 100 (un rejeu sur panne transitoire).

    Cette lecture porte des CORPS (les corps de PR complets : 2 Mo pour 100
    PRs ouvertes) : elle prend donc le plafond `TIMEOUT_S_CORPS`, comme la
    page du pool et la qualification d'un lot. Avec le plafond general
    (`TIMEOUT_S` = 15 s), la lecture etait TOUJOURS incomplete -- mesure du
    24/11 sur ce siege : 41 s pour la page 1 des PRs ouvertes -- et
    l'organe de qualification (`tapis_prise_en_charge`) echouait donc pour
    toutes les lanes avec `lecture prs_ouvertes incomplete`.
    """
    rows: list[dict] = []
    for page in range(1, PAGES_PRS_MAX + 1):
        argv = ["gh", "api", f"repos/{depot}/pulls?state=open&per_page=100&page={page}"]
        texte = _appel(run, argv, "prs_ouvertes", page,
                       timeout=_timeout(echeance, TIMEOUT_S_CORPS)) or _appel(
            run, argv, "prs_ouvertes", page, timeout=_timeout(echeance, TIMEOUT_S_CORPS))
        try:
            chunk = json.loads(texte or "")
            rows.extend({**{k: pr.get(k) or "" for k in _PR_TEXTE}, "number": pr["number"],
                         "draft": bool(pr.get("draft")), "merged_at": pr.get("merged_at"),
                         "head": (pr.get("head") or {}).get("ref") or "",
                         "author": (pr.get("user") or {}).get("login") or ""} for pr in chunk)
        except (ValueError, KeyError, TypeError, AttributeError) as exc:
            cause = f"panne ou reponse illisible : {exc}"
            raise LectureIncomplete("prs_ouvertes", page, cause) from exc
        if len(chunk) < 100:
            return rows
    raise LectureIncomplete("prs_ouvertes", PAGES_PRS_MAX, "plus de pages que le plafond")


def lire_citations_mergees(depot: str | Path, jours: int = 45,
                           run: Run = run_defaut,
                           echeance: float | None = None) -> dict[int, list[dict]]:
    """Par numero cite, les commits `{sha, date, sujet, ferme}` d'`origin/main` sur `jours` jours.
    Un seul `git log`, sans fetch : le body de la PR devient le message du squash."""
    argv = ["git", "-C", str(depot), "log", "origin/main", f"--since={jours}.days",
            "--format=%x1e%H%x1f%ct%x1f%s%x1f%b"]
    try:
        texte = run(argv, _timeout(echeance))
    except (subprocess.SubprocessError, OSError) as exc:
        raise LectureIncomplete("citations_mergees", "git log", str(exc)) from exc
    citations: dict[int, list[dict]] = {}
    for record in texte.split("\x1e"):
        parts = record.strip("\n").split("\x1f", 3)
        if len(parts) < 3 or not parts[1].strip().isdigit():
            continue
        date = datetime.fromtimestamp(int(parts[1]), UTC).strftime(_ISO)
        message = "\n".join(parts[2:])
        portee = _PORTEE_RE.match(parts[2])
        fermes = {int(n) for n in _FERME_RE.findall(message)}
        fermes |= {int(n) for n in _CITATION_RE.findall(portee.group(1))} if portee else set()
        for num in sorted({int(n) for n in _CITATION_RE.findall(message)}):
            citations.setdefault(num, []).append({"sha": parts[0], "date": date,
                                                  "sujet": parts[2], "ferme": num in fermes})
    return citations


def dossier_cache_defaut() -> Path:
    """`%LOCALAPPDATA%/CoursIA/tapis_rapide`, ou `~/.cache/coursia/tapis_rapide`."""
    local = os.environ.get("LOCALAPPDATA")
    return (Path(local) / "CoursIA" if local else Path.home() / ".cache/coursia") / "tapis_rapide"


def _rafraichir_origin_main(run: Run, depot: str | Path,
                            echeance: float | None = None) -> str | None:
    """`git fetch origin main` si la pointe locale d'origin/main a plus de
    `FETCH_AGE_MAX_H` h ou est illisible : une panne se NOMME, ne leve pas."""
    try:
        argv = ["git", "-C", str(depot), "log", "-1", "--format=%ct", "origin/main"]
        tip = datetime.fromtimestamp(int(run(argv, TIMEOUT_S).strip()), UTC)
        if datetime.now(UTC) - tip <= timedelta(hours=FETCH_AGE_MAX_H):
            return None
    except (ValueError, subprocess.SubprocessError, OSError):
        pass  # pointe illisible : le fetch se tente quand meme
    try:
        run(["git", "-C", str(depot), "fetch", "-q", "origin", "main"],
            _timeout(echeance, FETCH_TIMEOUT_S))
        return None
    except (subprocess.SubprocessError, OSError) as exc:
        return f"fetch origin/main impossible ({str(exc)[:100]}), pointe locale gardee"


def lire_tout(depot: str | Path, cache_s: int = 300, run: Run = run_defaut, jours: int = 45,
              dossier_cache: Path | None = None) -> Lecture:
    """Les trois lectures, ou le cache local de moins de `cache_s` s (0 : sans cache).

    **Une seule lecture reseau par machine et par instant** (#22630) : le cache est
    relu apres le verrou partage -- si une autre lane a rafraichi pendant l'attente,
    cette passe ne consomme aucun credit gh. Le verrou n'est jamais bloquant.
    """
    from coordination import gh_cache

    chemin = (dossier_cache or dossier_cache_defaut()) / f"lecture-{jours}j.json"

    def _depuis_cache(brut: dict) -> Lecture:
        brut["citations"] = {int(k): v for k, v in brut["citations"].items()}
        return Lecture(**{**brut, "depuis_cache": True})

    def _reseau() -> Lecture:
        return _lire_reseau(depot, cache_s, run, jours)

    return gh_cache.lire_unique(chemin, cache_s, _reseau, _depuis_cache)


def _lire_reseau(depot: str | Path, cache_s: int, run: Run, jours: int) -> Lecture:
    """Les trois lectures reseau."""
    appels = [0]

    def compte(argv: list[str], timeout: int) -> str:
        appels[0] += 1
        return run(argv, timeout)

    debut = time.monotonic()
    fetch_note = _rafraichir_origin_main(compte, depot)  # AVANT les citations
    lecture = Lecture(issues=lire_issues_ouvertes(compte), prs=lire_prs_ouvertes(compte),
                      citations=lire_citations_mergees(depot, jours, compte),
                      lu_a=datetime.now(UTC).strftime(_ISO), fetch_note=fetch_note)
    lecture.appels, lecture.secondes = appels[0], round(time.monotonic() - debut, 1)
    return lecture


def charger_depuis(dossier: str | Path, depot: str | Path | None = None, jours: int = 45,
                   run: Run = run_defaut) -> Lecture:
    """Rejoue `issues.json` et `prs_ouvertes.json` d'un dossier deja lu ; avec
    `depot`, les citations se lisent en plus sur son `origin/main` local."""
    base, debut = Path(dossier), time.monotonic()
    try:
        issues, prs = (json.loads((base / nom).read_text(encoding="utf-8"))
                       for nom in ("issues.json", "prs_ouvertes.json"))
        meta = base / "meta.json"
        lu_a = json.loads(meta.read_text(encoding="utf-8")).get("fetched_at", "") \
            if meta.exists() else ""
    except (OSError, ValueError, AttributeError) as exc:
        raise LectureIncomplete("dossier", str(base), str(exc)) from exc
    lecture = Lecture(issues=issues, prs=prs, lu_a=str(lu_a))
    if depot is not None:
        lecture.citations, lecture.appels = lire_citations_mergees(depot, jours, run), 1
    lecture.secondes = round(time.monotonic() - debut, 1)
    return lecture
