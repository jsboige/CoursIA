"""Lectures groupees de GitHub et de git pour le tapis rapide (#22983).

Seul module de la voie legere qui lance un processus ; `run(argv, timeout)` est
injecte, les tests en passent un faux. Le nombre d'appels ne depend pas des candidats.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
import time
from collections.abc import Callable
from dataclasses import asdict, dataclass, field
from datetime import UTC, datetime, timedelta
from pathlib import Path

Run = Callable[[list[str], int], str]

DEPOT_GH = "jsboige/CoursIA"
TIMEOUT_S = 90
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


class LectureIncomplete(RuntimeError):
    """Une lecture n'a pas abouti : rien ne doit etre servi."""

    def __init__(self, lecture: str, page: object, cause: str) -> None:
        super().__init__(f"lecture {lecture} incomplete (page {page}) : {cause}")
        self.lecture, self.page, self.cause = lecture, page, cause


@dataclass
class Lecture:
    """Les trois lectures d'un tirage, et ce qu'elles ont coute."""

    issues: list[dict]
    prs: list[dict]
    citations: dict[int, list[dict]] = field(default_factory=dict)
    lu_a: str = ""
    appels: int = 0
    secondes: float = 0.0
    depuis_cache: bool = False
    fetch_note: str | None = None  # fetch d'origin/main tente et echoue (sinon None)

    @property
    def origin_main_le(self) -> str | None:
        """Dernier commit de la fenetre : chaque commit de squash cite sa PR."""
        return max((c["date"] for cs in self.citations.values() for c in cs), default=None)


def run_defaut(argv: list[str], timeout: int) -> str:
    """`subprocess.run` borne ; un code non nul leve `CalledProcessError`."""
    return subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                          timeout=timeout, check=True).stdout


def _appel(run: Run, argv: list[str], lecture: str, page: object) -> str | None:
    """Un appel ; None sur une panne transitoire (502/504, timeout)."""
    try:
        return run(argv, TIMEOUT_S)
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
        texte = _appel(run, argv + (["-f", f"after={after}"] if after else []), "issues", page)
        if texte is None:
            continue
        try:
            return json.loads(texte)["data"]["repository"]["issues"]
        except (ValueError, KeyError, TypeError) as exc:
            raise LectureIncomplete("issues", page, f"reponse illisible : {exc}") from exc
    raise LectureIncomplete("issues", page, f"502/504 ou timeout aux tailles {TAILLES_PAGE}")


def _issue(node: dict) -> dict:
    """Une issue GraphQL a plat, aux champs de `issues.json`."""
    com = node.get("comments") or {}
    return {"number": node["number"], "title": node.get("title") or "",
            "body": node.get("body") or "", "created_at": node.get("createdAt") or "",
            "updated_at": node.get("updatedAt") or "",
            "labels": [lab["name"] for lab in (node.get("labels") or {}).get("nodes") or []],
            "comments_total": com.get("totalCount") or 0,
            "comments": [{"created_at": c.get("createdAt") or "",
                          "author": (c.get("author") or {}).get("login") or "",
                          "body": (c.get("body") or "")[:600]} for c in com.get("nodes") or []]}


def lire_issues_ouvertes(run: Run = run_defaut, depot: str = DEPOT_GH) -> list[dict]:
    """Toutes les issues ouvertes (12 derniers commentaires), jamais une liste partielle."""
    issues: list[dict] = []
    after, page = None, 1
    while True:
        data = _page_issues(run, depot, after, page)
        issues.extend(_issue(node) for node in data["nodes"])
        if not data["pageInfo"]["hasNextPage"]:
            return issues
        after, page = data["pageInfo"]["endCursor"], page + 1


def lire_prs_ouvertes(run: Run = run_defaut, depot: str = DEPOT_GH) -> list[dict]:
    """Les PRs ouvertes, REST pagine par 100 (un rejeu sur panne transitoire)."""
    rows: list[dict] = []
    for page in range(1, PAGES_PRS_MAX + 1):
        argv = ["gh", "api", f"repos/{depot}/pulls?state=open&per_page=100&page={page}"]
        texte = _appel(run, argv, "prs_ouvertes", page) or _appel(run, argv, "prs_ouvertes", page)
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
                           run: Run = run_defaut) -> dict[int, list[dict]]:
    """Par numero cite, les commits `{sha, date, sujet, ferme}` d'`origin/main` sur `jours` jours.

    Un seul `git log`, sans fetch : le body de la PR devient le message du squash."""
    argv = ["git", "-C", str(depot), "log", "origin/main", f"--since={jours}.days",
            "--format=%x1e%H%x1f%ct%x1f%s%x1f%b"]
    try:
        texte = run(argv, TIMEOUT_S)
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


def _rafraichir_origin_main(run: Run, depot: str | Path) -> str | None:
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
        run(["git", "-C", str(depot), "fetch", "-q", "origin", "main"], TIMEOUT_S)
        return None
    except (subprocess.SubprocessError, OSError) as exc:
        return f"fetch origin/main impossible ({str(exc)[:100]}), pointe locale gardee"


def lire_tout(depot: str | Path, cache_s: int = 300, run: Run = run_defaut, jours: int = 45,
              dossier_cache: Path | None = None) -> Lecture:
    """Les trois lectures, ou le cache local de moins de `cache_s` s (0 : sans cache).

    Un cache illisible se relit sur le reseau ; sans verrou, le dernier ecrivain gagne."""
    chemin = (dossier_cache or dossier_cache_defaut()) / f"lecture-{jours}j.json"
    if cache_s > 0:
        try:
            brut = json.loads(chemin.read_text(encoding="utf-8"))
            if time.time() - float(brut.pop("_epoch")) < cache_s:
                brut["citations"] = {int(k): v for k, v in brut["citations"].items()}
                return Lecture(**{**brut, "depuis_cache": True})
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            pass  # cache absent ou illisible : relu sur le reseau
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
    if cache_s > 0:
        try:
            chemin.parent.mkdir(parents=True, exist_ok=True)
            fd, tmp = tempfile.mkstemp(dir=chemin.parent, suffix=".tmp")
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                json.dump({**asdict(lecture), "_epoch": time.time()}, fh, ensure_ascii=False)
            os.replace(tmp, chemin)
        except OSError:
            pass  # un cache non ecrit ne change pas le tirage
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
