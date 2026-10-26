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

Le rafraichissement est **incremental** : les commentaires sont lus par
`issues/comments?since=`, les issues et les PRs par leur `updated_at`. Un
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
import os
import subprocess
import time
from collections.abc import Iterator
from contextlib import contextmanager
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SNAPSHOT_VERSION = 1

#: Duree de validite d'un instantane (secondes). Le mandat : « un instantane
#: de quelques minutes suffit pour trier et proposer ».
DEFAULT_TTL_SECONDS = 600

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


@contextmanager
def snapshot_lock(repo: str, timeout: float = 120.0) -> Iterator[Path]:
    """Verrou de rafraichissement, partage entre lanes de la meme machine.

    `O_CREAT|O_EXCL` est atomique sur tous les OS vises : le createur gagne,
    les autres attendent. Un verrou abandonne (age > `LOCK_STALE_SECONDS`) est
    casse -- sans quoi un processus mort bloquerait la machine jusqu'au
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
            if age > LOCK_STALE_SECONDS:
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


def _gh_api(path: str, *, params: str = "", timeout: float = 30.0) -> Any:
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
        cmd.append(params)
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


def sweep_comments(repo: str, since: str) -> dict[int, list[dict]]:
    """Balayage incremental des commentaires du depot (`issues/comments?since=`).

    Rend `{numero: [commentaires normalises]}` -- uniquement les commentaires
    **crees ou modifies** depuis `since` (horodatage ISO). C'est la voie
    "rafraichissement periodique" : elle ne re-telecharge pas l'historique.
    """
    raw = _gh_api(f"repos/{repo}/issues/comments", params=f"--paginate&since={since}")
    if isinstance(raw, dict):
        raw = raw.get("comments") or []
    out: dict[int, list[dict]] = {}
    for comment in raw:
        if not isinstance(comment, dict):
            continue
        url = comment.get("issue_url") or ""
        number = None
        if url:
            tail = url.rstrip("/").rsplit("/", 1)[-1]
            if tail.isdigit():
                number = int(tail)
        if number is None:
            continue
        out.setdefault(number, []).append(normalise_comment(comment))
    return out


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
                snapshot, _ = ensure_issue_payloads(
                    repo, numbers, snapshot, ttl_seconds)
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
    "ensure_issue_payloads",
    "fetch_issue",
    "fetch_issue_comments",
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
    "sweep_comments",
]
