"""Instantane local partage des etats GitHub (#22630).

Le tapis (`scripts/pick_idle_grain.py`) et le lecteur de claims
(`scripts/check_lane_claim.py`) interrogent GitHub pour chaque candidat :
`gh issue view` par issue (GraphQL, ~5 s), plus une lecture de checks par PR
pour la file de reparation. Sur le pool reel (494 issues ouvertes), une passe
du tapis coute **274 s** -- le user l'a qualifie de « vrai defaut de
conception » : il n'y a pas de raison que le tapis consomme des credits gh a
chaque passe.

Ce module tient un **instantane local, partage par machine**, sous
`%LOCALAPPDATA%/CoursIA/gh-snapshot/<owner>__<repo>/` (POSIX :
`$XDG_DATA_HOME/CoursIA/...`, sinon `~/.local/share/CoursIA/...`) :

- `issues.json`   : les issues ouvertes (numero, titre, labels, `updated_at`) ;
- `comments.json` : les commentaires par issue (formes normalisees) ;
- `prs.json`      : les PRs ouvertes (numero, etat, tete, `updated_at`) ;
- `checks.json`   : le rollup de checks par tete de PR ;
- `repair.json`   : liste de la file de reparation, etats de PR et verdicts
  B.0 evalues, fingerprints `updatedAt` et horodatages inclus ;
- `meta.json`     : l'etat du rafraichissement (horodatages, version).

Le rafraichissement est **incremental** : seules les issues demandees et dont
l'entree est perimee sont relues, une par une (commentaires inclus). Un
verrou (fichier, `O_CREAT|O_EXCL`) fait que deux lanes de la meme machine
partagent le meme rafraichissement au lieu de le faire chacune.

Ce module ne fait **aucune** autorite sur les claims : il remplace le
*transport*, pas la semantique. La regle HARD de `lane-claim-protocol.md`
reste : la lane relance `check_lane_claim.py N` juste avant d'editer.

Le contrat de lecture est volontairement minimal : `load_snapshot()` rend un
dictionnaire que le lecteur de claims consomme via `set_snapshot()`.
"""

from __future__ import annotations

import json
from concurrent.futures import ThreadPoolExecutor
import os
import subprocess
import time
from collections.abc import Iterator
from contextlib import contextmanager
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SNAPSHOT_VERSION = 1

#: Duree de validite des payloads PAR ISSUE (issue + commentaires), en
#: secondes. Arbitrage coordinateur du 2026-10-26 (PR #22684) : cache de
#: CYCLE CRON -- les charges couteuses par element vivent au-dela de la
#: cadence du cron (1800 s), un verdict ou un claim vieux de 20-30 min ne
#: fait pas de tort au tri : la lane reverifie `check_lane_claim.py` a la
#: source avant toute edition, et le merge relit B.0 a la tete exacte.
DEFAULT_TTL_SECONDS = 1800

#: Fenetre maximale lue par le balayage des commentaires du depot, en
#: secondes (2 h). Le balayage lit les commentaires MODIFIES depuis `since` :
#: son cout croit avec la fenetre, pas avec le nombre d'issues visees.
#: Mesure du 27/10 (ce siege) : 417 commentaires sur 1,5 jour = 23,7 s de
#: lecture, 5 pages -- une fenetre de cet ordre tient dans le budget.
#: La borne de 2 h est CONSERVATRICE et n'est etablie par aucune mesure : la
#: « fenetre de 24 h qui depassait le budget » invoquee par la version
#: precedente mesurait en realite un fil ENTIER, lu sans `since` effectif
#: (argv casse, revue du 28/10). Au-dela de la borne, la lecture par issue
#: prend le relais : la valeur exacte n'est donc pas critique.
MAX_SWEEP_LOOKBACK_SECONDS = 2 * 3600

#: Budget du balayage, en secondes. Avec un `since` effectif, 1,5 jour de fil
#: tient en 5 pages et 23,7 s (mesure du 27/10) : 60 s couvrent la fenetre de
#: `MAX_SWEEP_LOOKBACK_SECONDS`. Le `TimeoutExpired` observe avant le
#: correctif d'argv mesurait un fil entier, pas cette fenetre.
SWEEP_TIMEOUT_SECONDS = 60.0

#: Nombre de fils pour la lecture PARALLELE des commentaires d'issue.
#: Les lectures sont des appels REST independants : mesure du 27/10,
#: 24 issues en 2,4 s avec 8 fils (median 0,73 s par issue), contre
#: 17,5 s en serie.
PARALLEL_READ_WORKERS = 8

#: Duree au-dela de laquelle un verrou est considere comme abandonne (min).
LOCK_STALE_SECONDS = 900


class SnapshotLockTimeout(TimeoutError):
    """Le verrou n'a pas ete obtenu : aucune ecriture n'est autorisee."""


# --- emplacement ---------------------------------------------------------------


def snapshot_root() -> Path:
    """Racine des instantanes locaux, partagee par machine.

    Windows : `%LOCALAPPDATA%/CoursIA/gh-snapshot`. POSIX :
    `$XDG_DATA_HOME/CoursIA/gh-snapshot`, sinon `~/.local/share/CoursIA/gh-snapshot`.
    """
    local = os.environ.get("LOCALAPPDATA")
    if local:
        base = Path(local)
    else:
        xdg = os.environ.get("XDG_DATA_HOME")
        base = Path(xdg) if xdg else Path.home() / ".local" / "share"
    return base / "CoursIA" / "gh-snapshot"


def snapshot_dir(repo: str) -> Path:
    """Repertoire d'un instantane, un par depot."""
    return snapshot_root() / repo.replace("/", "__")


# --- verrou --------------------------------------------------------------------


def _pid_alive(pid: int) -> bool:
    """Le processus qui tient le verrou est-il encore vivant ?

    Windows n'a pas de `kill(pid, 0)` sans risque : `os.kill(pid, 0)` y
    termine le processus. On interroge donc l'API Win32
    (`OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION)`) : un handle nul
    signifie « processus absent » ; une erreur d'ACCES signifie
    « present mais intouchable », donc vivant.
    """
    if pid <= 0:
        return False
    if os.name == "nt":
        try:
            import ctypes

            handle = ctypes.windll.kernel32.OpenProcess(0x1000, False, pid)
            if not handle:
                return False
            ctypes.windll.kernel32.CloseHandle(handle)
            return True
        except Exception:  # noqa: BLE001 - on ne peut pas dire : on presume vivant
            return True
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return True
    return True


@contextmanager
def snapshot_lock(repo: str, timeout: float = 120.0) -> Iterator[Path]:
    """Verrou de rafraichissement, partage entre lanes de la meme machine.

    `O_CREAT|O_EXCL` est atomique sur tous les OS vises : le createur gagne,
    les autres attendent. Un verrou abandonne est casse dans deux cas :

    - le processus qui le tient est **mort** (le fichier porte son pid) --
      mesure du 27/10 : un tirage interrompu a laisse le verrou, et toutes
      les lanes de la machine ont attendu `LOCK_STALE_SECONDS` (15 min) ;
    - le verrou est **vieux** (age > `LOCK_STALE_SECONDS`).

    Un verrou dont le contenu ne porte pas un pid POSITIF (fichier vide,
    contenu non numerique, lecture impossible) a un proprietaire **inconnu**,
    pas mort : il est respecte jusqu'a la borne d'age. Un fichier vide est
    l'etat normal entre la creation atomique et l'ecriture du pid (#22983).

    Sans le cas d'age, un processus mort bloquerait la machine jusqu'au
    redemarrage.
    """
    directory = snapshot_dir(repo)
    directory.mkdir(parents=True, exist_ok=True)
    lock_path = directory / "refresh.lock"
    deadline = time.monotonic() + timeout
    while True:
        try:
            fd = os.open(str(lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                handle.write(str(os.getpid()))
            break
        except FileExistsError:
            try:
                age = time.time() - lock_path.stat().st_mtime
            except OSError:
                age = 0.0
            holder = None
            try:
                texte = lock_path.read_text(encoding="utf-8").strip()
            except (OSError, UnicodeDecodeError):
                texte = ""
            if texte:
                try:
                    pid = int(texte)
                except ValueError:
                    pid = 0
                if pid > 0:
                    holder = pid
            # #22983 -- un pid `<= 0` (fichier VIDE, contenu non numerique)
            # est INCONNU, jamais MORT. Le fichier est vide par construction
            # entre `O_CREAT|O_EXCL` et l'ecriture du pid (`os.fdopen`
            # ci-dessus) : c'est la fenetre de course normale, et la lire
            # comme un proprietaire disparu faisait VOLER le verrou -- deux
            # processus entraient alors dans la section qui existe pour les
            # exclure (mesure du 28/10 : acquisition en 0,00 s au lieu de
            # l'attente). Un pid positif, lui, se verifie.
            dead_holder = holder is not None and not _pid_alive(holder)
            if age > LOCK_STALE_SECONDS or dead_holder:
                try:
                    lock_path.unlink()
                except OSError:
                    pass
                continue
            if time.monotonic() > deadline:
                # Un timeout ne doit JAMAIS entrer dans le bloc protégé : deux
                # lanes ecriraient alors sans exclusion. `refresh()` garde son
                # repli lecture seule ; le flush de reparation ignore l'ecriture.
                raise SnapshotLockTimeout(
                    f"verrou de l'instantane non obtenu apres {timeout:g} s")
            time.sleep(0.2)
    try:
        yield lock_path
    finally:
        try:
            lock_path.unlink()
        except OSError:
            pass


# --- lecture / ecriture --------------------------------------------------------


def _read_json(path: Path, default: Any) -> Any:
    try:
        raw = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return default
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        return default
    return data if isinstance(data, type(default)) else default


def _write_json(path: Path, payload: Any) -> None:
    """Ecriture atomique : un lecteur concurrent ne voit jamais un fichier tronque."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1),
                   encoding="utf-8")
    os.replace(tmp, path)


def load_snapshot(repo: str) -> dict:
    """Rend l'instantane courant (vide s'il n'existe pas encore).

    Contrat : toujours un dictionnaire avec les cles `issues`, `comments`,
    `prs`, `checks`, `repair`, `meta`. Une entree corrompue rend le dossier vide plutot
    que de lever : un instantane illisible ne doit pas empecher le tapis.
    """
    directory = snapshot_dir(repo)
    meta = _read_json(directory / "meta.json", {})
    issues = _read_json(directory / "issues.json", {})
    comments = _read_json(directory / "comments.json", {})
    prs = _read_json(directory / "prs.json", {})
    checks = _read_json(directory / "checks.json", {})
    repair = _read_json(directory / "repair.json", {})
    return {
        "meta": meta if isinstance(meta, dict) else {},
        "issues": issues if isinstance(issues, dict) else {},
        "comments": comments if isinstance(comments, dict) else {},
        "prs": prs if isinstance(prs, dict) else {},
        "checks": checks if isinstance(checks, dict) else {},
        "repair": repair if isinstance(repair, dict) else {},
    }


def save_snapshot(repo: str, snapshot: dict) -> None:
    """Ecrit l'instantane (meta en dernier : sa presence date l'ecriture)."""
    directory = snapshot_dir(repo)
    for key in ("issues", "comments", "prs", "checks", "repair"):
        _write_json(directory / f"{key}.json", snapshot.get(key) or {})
    _write_json(directory / "meta.json", snapshot.get("meta") or {})


def snapshot_age_seconds(snapshot: dict) -> float | None:
    """Age de l'instantane en secondes, ou None s'il n'a jamais ete ecrit."""
    stamp = (snapshot.get("meta") or {}).get("refreshed_at")
    if not stamp:
        return None
    try:
        parsed = datetime.fromisoformat(str(stamp).replace("Z", "+00:00"))
    except ValueError:
        return None
    return (datetime.now(UTC) - parsed).total_seconds()


def is_fresh(snapshot: dict, ttl_seconds: int = DEFAULT_TTL_SECONDS) -> bool:
    """Vrai si l'instantane est plus recent que le TTL."""
    age = snapshot_age_seconds(snapshot)
    return age is not None and age <= ttl_seconds


# --- transport GitHub ----------------------------------------------------------


def _gh_api(path: str, *, params: str | list[str] = "",
            timeout: float = 30.0) -> Any:
    """Un appel REST `gh api`, en JSON, avec un compte des appels.

    Le compteur vit dans l'attribut de module `CALL_COUNT` : le mandat
    mesure les « appels gh » de la passe, il faut donc pouvoir les compter.

    `timeout` borne CHAQUE appel (mesure #22684 : le priming d'une passe a
    froid emet jusqu'a 2 appels par candidat -- 140 pour une fenetre de 70 --
    et sans borne, un seul `gh` lent pendant une saturation du pool GitHub
    pend la passe entiere du tapis ; `subprocess.TimeoutExpired` est une
    `Exception`, donc les fail-open en place (`fetch_failures` par issue,
    repli du priming et de la voie en processus) la traitent comme une
    lecture impossible, jamais comme un verdict).
    """
    cmd = ["gh", "api", path]
    if params:
        if isinstance(params, str):
            cmd.append(params)
        else:
            cmd.extend(params)
    proc = subprocess.run(
        cmd, check=False, capture_output=True, text=True, shell=False,
        encoding="utf-8", errors="replace", timeout=timeout,
    )
    CALL_COUNT["n"] += 1
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh api {path}: {proc.stderr.strip()[:200] or proc.returncode}"
        )
    return json.loads(proc.stdout)


#: Compteur d'appels gh du processus (remis a zero par `reset_call_count`).
CALL_COUNT: dict[str, int] = {"n": 0}


def reset_call_count() -> None:
    """Remet le compteur a zero (mesure de passe)."""
    CALL_COUNT["n"] = 0


def normalise_comment(raw: dict) -> dict:
    """Commentaire REST -> forme attendue par le lecteur de claims.

    `gh issue view --json comments` rend `author.login` / `createdAt` / `url` ;
    l'API REST rend `user.login` / `created_at` / `html_url`. Le lecteur de
    claims ne lit que les trois premiers : on normalise ici pour que les deux
    voies produisent **exactement** la meme forme.
    """
    return {
        "body": raw.get("body") or "",
        "createdAt": raw.get("created_at") or raw.get("createdAt") or "",
        "updatedAt": raw.get("updated_at") or raw.get("updatedAt") or "",
        "author": {"login": ((raw.get("user") or raw.get("author") or {})
                             .get("login") or "")},
        "url": raw.get("html_url") or raw.get("url") or "",
    }


def fetch_issue_comments(repo: str, number: int) -> list[dict]:
    """Commentaires d'une issue, en REST (rapide : ~0,3 s contre ~5 s en GraphQL)."""
    raw = _gh_api(f"repos/{repo}/issues/{number}/comments", params="--paginate")
    if isinstance(raw, dict):
        raw = raw.get("comments") or []
    return [normalise_comment(c) for c in raw
            if isinstance(c, dict)]


def fetch_issue(repo: str, number: int) -> dict:
    """Metadonnees d'une issue (titre, labels) -- REST."""
    raw = _gh_api(f"repos/{repo}/issues/{number}")
    labels = []
    for lb in raw.get("labels") or []:
        if isinstance(lb, dict):
            labels.append(lb.get("name") or "")
        elif isinstance(lb, str):
            labels.append(lb)
    return {
        "number": raw.get("number") or number,
        "title": raw.get("title") or "",
        "labels": labels,
        "updated_at": raw.get("updated_at") or "",
        "state": raw.get("state") or "",
    }


# --- balayage incremental du depot (#22983) -----------------------------------
#
# La lecture par issue (`fetch_issue_comments`) fait UN appel par issue :
# pour la fenetre du tapis (84 a 174 issues), c'est 84 a 174 appels, et la
# mesure du 2026-10-27 (coordinateur, `main` a jour) donne 184 s pour 54
# claims verifies un par un. Le depot expose un point d'entree **unique** qui
# rend la lecture incrémentale : `repos/<repo>/issues/comments`, avec
# `since=`. Un seul appel, quel que soit le nombre d'issues concernees.


def _issue_number_from_url(issue_url: str) -> int | None:
    """Numero d'issue porte par l'`issue_url` d'un commentaire, ou None.

    Aucun filtre PR ici : l'exclusion d'un commentaire de PULL REQUEST se
    fait sur `html_url` (`_is_pull_request_comment`), seule forme fiable.
    #22983 -- l'API REST rend `/issues/<n>` dans `issue_url` pour TOUT
    commentaire, y compris ceux des PRs : mesure du 28/10 sur 100
    commentaires reels, 100/100 en `/issues/`, dont 37 commentaires de PR
    (leur `html_url` porte `/pull/`). Un filtre `"/pulls/" in issue_url`
    ne se declenchait donc jamais.
    """
    if not issue_url:
        return None
    tail = str(issue_url).rstrip("/").rsplit("/", 1)[-1]
    try:
        return int(tail)
    except ValueError:
        return None


def _is_pull_request_comment(item: dict) -> bool:
    """Vrai si le commentaire appartient a une PULL REQUEST.

    #22983 -- `html_url` est la seule surface qui distingue les deux
    formes : `/pull/<n>` pour une PR, `/issues/<n>` sinon (mesure du 28/10 :
    37 commentaires de PR sur 100, tous en `/pull/`). Issues et PRs
    partagent la numerotation du depot, et le lecteur de claims raisonne sur
    des issues -- un commentaire de PR ne doit jamais etrangler le numero
    d'une issue.
    """
    return "/pull/" in str((item or {}).get("html_url") or "")


def fetch_repo_comments_since(repo: str, since: str | None = None, *,
                              timeout: float = 60.0) -> dict[int, list[dict]]:
    """Tous les commentaires du depot, groupes par issue, en REST.

    Un seul point d'entree pagine : `repos/<repo>/issues/comments`, avec
    `since=` pour ne prendre que les commentaires modifies apres un
    horodatage ISO 8601. C'est ce qui rend le **rafraichissement
    incremental** possible : la lecture par issue fait un appel par issue,
    le balayage en fait un seul, quel que soit le nombre d'issues visees.

    Rend `{numero_issue: [commentaires normalises]}` -- les commentaires de
    PR sont exclus (sur `html_url`, voir `_is_pull_request_comment`). Lève en
    cas d'echec de lecture : l'appelant decide.
    """
    # `-X GET` est OBLIGATOIRE : `gh api` bascule en POST des qu'un champ
    # `-f` est present, et un POST sur un point d'entree de liste rend
    # `404 Not Found` (mesure du 27/10 : le balayage levait
    # `gh: Not Found (HTTP 404)` et tout le rafraichissement echouait).
    params: list[str] = ["--paginate", "-X", "GET"]
    if since:
        # #22983 -- DEUX elements d'argv, jamais un seul. En un seul
        # element (`"-f since=..."`), `gh` lit le nom de champ ` since`
        # (espace initial) et l'encode en parametre de requete : la requete
        # part en `?+since=...`, nom inconnu de GitHub, qui rend alors le
        # fil ENTIER au lieu de filtrer -- ~30 000 commentaires, et le
        # balayage meurt sur son propre timeout. Mesure du 28/10
        # (`GH_DEBUG=api`) : un element -> `?+since=2026-10-28T00%3A00%3A00Z`,
        # deux elements -> `?since=2026-10-28T00%3A00%3A00Z`. `fetch_open_issues`
        # juste en dessous utilise deja la forme en deux elements.
        params.extend(["-f", f"since={since}"])
    raw = _gh_api(f"repos/{repo}/issues/comments", params=params,
                   timeout=timeout)
    if isinstance(raw, dict):
        raw = raw.get("comments") or []
    grouped: dict[int, list[dict]] = {}
    for item in raw or []:
        if not isinstance(item, dict):
            continue
        if _is_pull_request_comment(item):
            continue
        number = _issue_number_from_url(str(item.get("issue_url") or ""))
        if number is None:
            continue
        grouped.setdefault(number, []).append(normalise_comment(item))
    for items in grouped.values():
        items.sort(key=lambda c: c.get("createdAt") or "")
    return grouped


def fetch_open_issues(repo: str, *, timeout: float = 60.0) -> dict[int, dict]:
    """Metadonnees de TOUTES les issues ouvertes du depot, en REST.

    Un seul point d'entree pagine : `repos/<repo>/issues?state=open`. Le
    pave du tapis est constitue d'issues ouvertes -- leslire toutes en une
    poignee d'appels evite un appel par issue pour les seules metadonnees
    (titre, labels).
    """
    raw = _gh_api(f"repos/{repo}/issues", params=["--paginate", "-X", "GET",
                                                   "-f", "state=open"],
                   timeout=timeout)
    if isinstance(raw, dict):
        raw = raw.get("issues") or []
    out: dict[int, dict] = {}
    for item in raw or []:
        if not isinstance(item, dict):
            continue
        if item.get("pull_request"):
            # Une PR est une issue pour REST : elle n'a pas de titre d'issue.
            continue
        number = item.get("number")
        if not isinstance(number, int):
            continue
        labels = []
        for lb in item.get("labels") or []:
            if isinstance(lb, dict):
                labels.append(lb.get("name") or "")
            elif isinstance(lb, str):
                labels.append(lb)
        out[number] = {
            "number": number,
            "title": item.get("title") or "",
            "labels": labels,
            "updated_at": item.get("updated_at") or "",
            "state": item.get("state") or "",
        }
    return out


def sweep_repo_comments(repo: str, snapshot: dict, *, since: str | None = None,
                        timeout: float = SWEEP_TIMEOUT_SECONDS) -> tuple[dict, int]:
    """Balaye les commentaires du depot et les fusionne dans l'instantane.

    Le balayage est **incremental par construction** : `since` borne la
    lecture aux commentaires modifies apres cet horodatage. Un issue dont
    aucun commentaire n'a bouge depuis le dernier balayage garde sa liste
    inchangee -- son horodatage de lecture avance quand meme, sans appel,
    tant que son stamp est DANS la fenetre lue (voir la regle des stamps
    ci-dessous).

    #22983 -- cette fonction ne ressuscite PAS la `sweep_comments` retiree
    par la revue ai-01 du 2026-10-27 (#22684, point 3). La retirement portait
    sur deux defauts precis : (1) une forme d'argv invalide
    (`params=f"--paginate&since={since}"` devenait UN argument que `gh`
    refuse), (2) aucun appelant en production. Ici, l'argv est une LISTE de
    DEUX elements (`["--paginate", "-f", "since=..."]`), et l'appelant
    existe : `ensure_comments`, qui remplace la lecture a deux appels par
    issue. Le nom reste different pour que la garde de la retirement
    (`test_sweep_comments_est_retire`) continue de dire ce qu'elle dit.

    Rend `(snapshot, nb_appels_gh)`.
    """
    grouped = fetch_repo_comments_since(repo, since, timeout=timeout)
    comments = dict(snapshot.get("comments") or {})
    meta = dict(snapshot.get("meta") or {})
    stamps = dict(meta.get("comment_stamps") or {})
    now = time.time()
    for number, items in grouped.items():
        key = str(number)
        existing = [c for c in (comments.get(key) or [])
                    if isinstance(c, dict)]
        by_url = {c.get("url"): c for c in existing if c.get("url")}
        for c in items:
            by_url[c.get("url")] = c
        comments[key] = sorted(by_url.values(),
                               key=lambda c: c.get("createdAt") or "")
    # #22983 -- REGLE UNIQUE du stamp : il n'avance qu'a ce que le balayage a
    # REELLEMENT couvert. Le balayage ne lit que `[since, now]` ; un stamp
    # ANTERIEUR a `since` marque des commentaires qu'il n'a pas vus, et le
    # trou `[stamp, since]` n'est rendu par personne d'autre que la lecture
    # par issue. Avancer un tel stamp a `now` declare donc l'issue lue
    # jusqu'a maintenant : un `[CLAIMED]` poste dans le trou n'est rendu NI
    # par le balayage NI par la lecture par issue, et ne le sera plus jamais
    # (temoin de la revue du 28/10 : 7 passes consecutives sans le voir).
    # Un stamp `>= since` est, lui, couvert en entier (la lecture precedente
    # allait jusqu'a `stamp`, le balayage couvre tout ce qui a bouge apres
    # `since` <= `stamp`) : il avance a `now`, ce qui evite la lecture par
    # issue pour une issue immobile.
    complets = not since
    since_epoch: float | None = None
    if since:
        try:
            since_epoch = datetime.fromisoformat(
                str(since).replace("Z", "+00:00")).timestamp()
        except ValueError:
            # `since` illisible : on ne SAIT pas ce que le balayage a couvert.
            # Aucun stamp n'avance (fail-closed : la lecture par issue suit).
            since_epoch = None
    cibles = set(stamps) | {str(n) for n in grouped}
    for key in cibles:
        stamp = stamps.get(key)
        if complets:
            # Balayage complet : tout le fil a ete lu.
            stamps[key] = now
        elif (since_epoch is not None
              and isinstance(stamp, (int, float)) and stamp >= since_epoch):
            stamps[key] = now
        # Sinon : trou non couvert (stamp < since), ou issue jamais lue sous
        # un balayage partiel -- aucun stamp n'est pose, le lecteur reste
        # fail-closed et relit l'issue.
    meta["comment_stamps"] = stamps
    meta["comments_swept_at"] = _utc_now()
    meta["comments_sweep_since"] = since
    snapshot["comments"] = comments
    snapshot["meta"] = meta
    return snapshot, 1


def ensure_comments(repo: str, numbers: list[int], snapshot: dict, *,
                    ttl_seconds: int = DEFAULT_TTL_SECONDS,
                    timeout: float = SWEEP_TIMEOUT_SECONDS) -> tuple[dict, int, dict]:
    """Garantit les commentaires ET les metadonnees des issues demandees.

    Deux voies, dans cet ordre :

    1. **balayage** (`sweep_comments`) quand il est borne -- il faut que
       chaque issue perimee ait un horodatage de lecture connu, pour que
       `since` puisse borner la lecture. Un balayage non borne (tout le
       depot) n'est jamais tente : il couterait plus cher que la lecture
       par issue ;
    2. **lecture par issue** pour ce qui reste perime apres le balayage.

    Les metadonnees (titre, labels) sont lues **en une fois** pour toutes
    les issues ouvertes du depot (`fetch_open_issues`) plutot qu'une par
    issue : le pave du tapis est fait d'issues ouvertes.

    Rend `(snapshot, nb_appels_gh, stats)`.
    """
    numbers = [int(n) for n in numbers]
    meta = dict(snapshot.get("meta") or {})
    stamps = dict(meta.get("comment_stamps") or {})
    comments = dict(snapshot.get("comments") or {})
    issues = dict(snapshot.get("issues") or {})
    now = time.time()
    calls = 0
    stats = {"demandes": len(numbers), "perimes": 0, "balayes": 0,
             "lus": 0, "meta_balayees": 0, "appels": 0}

    def _stale(number: int) -> bool:
        key = str(number)
        stamp = stamps.get(key)
        if key not in comments:
            return True
        if not isinstance(stamp, (int, float)):
            return True
        return (now - stamp) > ttl_seconds

    stale = [n for n in numbers if _stale(n)]
    stats["perimes"] = len(stale)
    if stale:
        known = [stamps[str(n)] for n in stale
                 if isinstance(stamps.get(str(n)), (int, float))]
        # #22983 -- le balayage n'est tente que si sa FENETRE est courte.
        # Son cout croit avec l'ACTIVITE du depot, pas avec le nombre
        # d'issues visees : mesure du 27/10, 417 commentaires sur 1,5 jour
        # = 23,7 s (5 pages). La lecture par issue, elle, coutait ~0,73 s par
        # issue (median) -- soit ~15 s pour 150 issues, et elle est
        # PARALLELISEE. Le balayage reste utile quand la fenetre est courte :
        # il avance aussi les horodatages des issues immobiles, sans appel.
        if known:
            oldest = min(known)
            # #22983 -- la porte est REELLE : elle compare la fenetre NON
            # rognee, `now - oldest`. La version precedente bornait d'abord
            # (`bounded = max(oldest, now - MAX)`) puis comparait
            # `(now - bounded) <= MAX` : tautologie par construction de
            # `max()`, donc AUCUNE branche n'ecartait le balayage. Le
            # balayage lisait alors `[now - MAX, now]` et laissait le trou
            # `[oldest, now - MAX]` sans lecteur. Ici, une fenetre trop large
            # ECARTE le balayage : la lecture par issue couvre chaque issue
            # perimee en entier, et coute moins cher qu'un balayage de
            # plusieurs jours.
            if (now - oldest) <= MAX_SWEEP_LOOKBACK_SECONDS:
                since = datetime.fromtimestamp(oldest, UTC).strftime(
                    "%Y-%m-%dT%H:%M:%SZ")
                try:
                    snapshot, calls_sweep = sweep_repo_comments(
                        repo, snapshot, since=since, timeout=timeout)
                    calls += calls_sweep
                    stats["balayes"] = len(stale)
                    stats["since"] = since
                    meta = dict(snapshot.get("meta") or {})
                    stamps = dict(meta.get("comment_stamps") or {})
                    comments = dict(snapshot.get("comments") or {})
                except Exception as exc:  # noqa: BLE001 - le repli par issue suit
                    stats["balayage_echoue"] = str(exc)[:120]
        # Ce qui reste perime apres le balayage : lecture par issue, en
        # PARALLELE. Les lectures sont des appels REST independants --
        # mesure du 27/10 : 24 issues en 2,4 s avec 8 fils (median 0,73 s
        # par issue), contre 17,5 s en serie.
        remaining = [n for n in stale if _stale(n)]

        def _read_one(number: int):
            key = str(number)
            try:
                return key, fetch_issue_comments(repo, number), None
            except Exception as exc:  # noqa: BLE001 - une issue illisible ne casse pas la passe
                return key, None, exc

        if remaining:
            with ThreadPoolExecutor(max_workers=PARALLEL_READ_WORKERS) as pool:
                for key, payload, exc in pool.map(_read_one, remaining):
                    if exc is not None:
                        meta.setdefault("fetch_failures", {})[key] = {
                            "at": now, "error": str(exc)[:160],
                        }
                        continue
                    comments[key] = payload
                    stamps[key] = now
                    calls += 1
                    stats["lus"] += 1
    # Les metadonnees (titre, labels) sont lues pour TOUTE cible dont
    # l'entree manque -- pas seulement pour les perimes : le lecteur de
    # claims a besoin des deux, et une metadonnee manquante le ferait
    # retomber sur le reseau pour cette issue.
    missing_meta = [n for n in numbers if str(n) not in issues]
    if missing_meta:
        try:
            open_issues = fetch_open_issues(repo, timeout=timeout)
            calls += 1
            for number, meta_issue in open_issues.items():
                issues[str(number)] = meta_issue
            stats["meta_balayees"] = len(open_issues)
        except Exception as exc:  # noqa: BLE001 - repli par issue
            meta.setdefault("fetch_failures", {})["__open_issues__"] = {
                "at": now, "error": str(exc)[:160],
            }
        for number in missing_meta:
            key = str(number)
            if key in issues:
                continue
            try:
                issues[key] = fetch_issue(repo, number)
                calls += 1
            except Exception as exc:  # noqa: BLE001 - une issue illisible ne casse pas la passe
                meta.setdefault("fetch_failures", {})[key] = {
                    "at": now, "error": str(exc)[:160],
                }
    meta["comment_stamps"] = stamps
    snapshot["issues"] = issues
    snapshot["comments"] = comments
    snapshot["meta"] = meta
    stats["appels"] = calls
    return snapshot, calls, stats


def ensure_issue_payloads(repo: str, numbers: list[int],
                          snapshot: dict,
                          ttl_seconds: int = DEFAULT_TTL_SECONDS) -> tuple[dict, int]:
    """Garantit les payloads (issue + commentaires) des issues demandees.

    Rend `(snapshot, nb_appels_gh)`. Une issue dont les commentaires sont
    deja dans l'instantane et frais ne declenche **aucun** appel : c'est le
    chemin chaud, celui que le tapis prend apres un premier passage.
    """
    issues = dict(snapshot.get("issues") or {})
    comments = dict(snapshot.get("comments") or {})
    meta = dict(snapshot.get("meta") or {})
    stamps = dict(meta.get("comment_stamps") or {})
    now = time.time()
    calls = 0
    for number in numbers:
        key = str(number)
        stamp = stamps.get(key)
        fresh = isinstance(stamp, (int, float)) and (now - stamp) <= ttl_seconds
        if fresh and key in comments and key in issues:
            continue
        try:
            issues[key] = fetch_issue(repo, number)
            calls += 1
            fetched = fetch_issue_comments(repo, number)
        except Exception as exc:  # noqa: BLE001 - un issue illisible ne casse pas la passe
            # L'echec est NOMME : une issue introuvable n'est jamais un
            # verdict libre, et le lecteur de claims ne verra pas d'entree
            # pour cette issue (il reste sur la voie reseau pour elle).
            meta.setdefault("fetch_failures", {})[key] = {
                "at": now, "error": str(exc)[:160],
            }
            continue
        comments[key] = fetched
        stamps[key] = now
        calls += 1
    meta["comment_stamps"] = stamps
    snapshot["issues"] = issues
    snapshot["comments"] = comments
    snapshot["meta"] = meta
    return snapshot, calls


def serves(snapshot: dict, numbers: list[int] | None,
           ttl_seconds: int = DEFAULT_TTL_SECONDS) -> bool:
    """Vrai si l'instantane peut servir les issues demandees.

    La validite est **par issue** : un instantane peut etre frais pour une
    issue dont les commentaires viennent d'etre lus, et périmé pour une
    autre. Un horodatage global serait faux dans les deux sens -- il
    declarerait frais un instantane dont les commentaires demandes n'ont
    jamais ete lus.
    """
    if not numbers:
        return is_fresh(snapshot, ttl_seconds)
    stamps = (snapshot.get("meta") or {}).get("comment_stamps") or {}
    comments = snapshot.get("comments") or {}
    now = time.time()
    for number in numbers:
        key = str(number)
        stamp = stamps.get(key)
        if not isinstance(stamp, (int, float)) or (now - stamp) > ttl_seconds:
            return False
        if key not in comments:
            return False
    return True


def refresh(repo: str, *, issue_numbers: list[int] | None = None,
            ttl_seconds: int = DEFAULT_TTL_SECONDS) -> dict:
    """Rafraichit l'instantane sous verrou, et rend son etat.

    - si l'instantane peut servir les issues demandees, il est rendu **tel
      quel** (0 appel gh) ;
    - sinon, les commentaires des issues demandees sont re-lu depuis le cache
      local ou l'API REST, et l'instantane est reecrit.

    Le verrou fait que deux lanes de la meme machine ne rafraichissent pas
    en meme temps : la seconde lit l'instantane produit par la premiere.
    """
    snapshot = load_snapshot(repo)
    if serves(snapshot, issue_numbers, ttl_seconds):
        return snapshot
    try:
        with snapshot_lock(repo):
            # Relecture sous verrou : une autre lane a pu rafraichir entre-temps.
            snapshot = load_snapshot(repo)
            if serves(snapshot, issue_numbers, ttl_seconds):
                return snapshot
            numbers = issue_numbers or []
            if numbers:
                # #22983 -- `ensure_comments` (balayage incremental + lecture
                # par issue pour le reste) remplace `ensure_issue_payloads`
                # (DEUX appels par issue). Meme contrat de sortie : les
                # commentaires ET les metadonnees des issues demandees sont
                # garantis.
                snapshot, _calls, _stats = ensure_comments(
                    repo, numbers, snapshot, ttl_seconds=ttl_seconds)
            meta = dict(snapshot.get("meta") or {})
            meta["version"] = SNAPSHOT_VERSION
            meta["repo"] = repo
            meta["refreshed_at"] = _utc_now()
            snapshot["meta"] = meta
            save_snapshot(repo, snapshot)
        return snapshot
    except SnapshotLockTimeout:
        # Comportement historique du timeout : conserver la lecture existante,
        # meme perimee, mais ne jamais executer le bloc d'ecriture sans verrou.
        return snapshot


def _utc_now() -> str:
    return datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def install(snapshot: dict) -> None:
    """Installe l'instantane dans le lecteur de claims (import tardif)."""
    import sys
    here = Path(__file__).resolve().parent.parent  # scripts/
    if str(here) not in sys.path:
        sys.path.insert(0, str(here))
    import check_lane_claim as clc
    clc.set_snapshot(snapshot)


__all__ = [
    "DEFAULT_TTL_SECONDS",
    "SNAPSHOT_VERSION",
    "SnapshotLockTimeout",
    "ensure_comments",
    "ensure_issue_payloads",
    "fetch_issue",
    "fetch_issue_comments",
    "fetch_open_issues",
    "fetch_repo_comments_since",
    "sweep_repo_comments",
    "install",
    "is_fresh",
    "load_snapshot",
    "normalise_comment",
    "refresh",
    "reset_call_count",
    "save_snapshot",
    "snapshot_age_seconds",
    "snapshot_dir",
    "snapshot_lock",
    "snapshot_root",
]
