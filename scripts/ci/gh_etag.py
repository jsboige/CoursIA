#!/usr/bin/env python3
"""Lectures REST GitHub conditionnelles (ETag), persistees et partagees par machine.

Pourquoi cet organe existe
--------------------------
Le protocole existe deja dans `pr_gate.py::_gh_api` (#26260, T-I) : renvoyer
l'`Etag` d'une reponse en `If-None-Match` fait repondre le serveur `304` quand
le chemin n'a pas change, et un 304 ne consomme **aucun quota** (mesure
#26260 : `remaining` inchange avant/apres). Mais ce cache est **memoire de
processus** : il ne protege que les polls d'un meme run. B.0
(`check_unaddressed_nits.py`), `check_run_state.py` et les cycles des lanes
relisent les MEMES chemins (`repos/.../issues/N`, `commits/<sha>`,
`pulls/N`...) a chaque cycle, chaque cycle etant un processus neuf : le gain
potentiel -- plusieurs lanes et organes par machine, puis le cycle suivant --
reste non collecte.

Ce module persiste l'association (chemin -> etag, corps) dans un fichier
machine-partage (`%LOCALAPPDATA%/CoursIA/gh_etag/cache.json`), selon la
discipline de `coordination/gh_cache_fichier.py` (#22630) : ecriture atomique
(mkstemp + os.replace), un cache absent/corrompu n'est JAMAIS bloquant.

Invariants (B.0 est un organe de merge : un etat perime ne doit jamais
produire un faux vert)
-------------------------------------------------------------
1. Le corps servi est TOUJOURS soit un `200` frais, soit un `304` -- et un
   304 est une **preuve serveur** que le chemin est INCHANGE depuis le corps
   cache. Aucun corps n'est jamais servi sans que le serveur ait repondu :
   il n'y a donc pas d'age maximal a borner, la fraicheur est certifiee a
   chaque lecture, pas supposee.
2. Un echec non-304 (rc non nul, 5xx, rate-limit, corps non-JSON) est une
   ERREUR (`subprocess.CalledProcessError` / `json.JSONDecodeError`, memes
   surfaces que l'appel `gh api` non conditionnel), jamais une reutilisation
   silencieuse du corps cache.
3. Le statut HTTP est lu dans le bloc d'en-tetes AVANT le returncode :
   `gh api -i` sort en rc=1 sur un 304 (mesure #26260), ce qui n'est pas un
   echec.
4. Un cache illisible, un dossier impossible a creer, une ecriture ratee :
   lecture directe non conditionnelle -- le cache degrade coute un 200, il
   ne change jamais le verdict.

Périmètre : REST seul (`api repos/...` sans `--paginate` ni autre drapeau).
GraphQL n'a pas d'ETag ; `--paginate` suit ses pages en interne et ne permet
pas d'injecter un `If-None-Match` par page -- ces lectures restent
inconditionnelles.

Usage :
    from gh_etag import conditional_get
    body, served_by_304 = conditional_get("repos/jsboige/CoursIA/issues/42")

Desactivation / redirection (tests, debug) :
    COURSIA_GH_ETAG=0            # desactive toute lecture/écriture du cache
    COURSIA_GH_ETAG_DIR=<dir>    # dossier de cache explicite
"""
from __future__ import annotations

import copy
import json
import os
import subprocess
import tempfile
from pathlib import Path

#: Plafond d'entrees : borne la taille du fichier (une entree = un chemin).
#: Au-dela, la plus ancienne insertion part (les dictionnaires Python gardent
#: l'ordre d'insertion). Une entree evictee ne coute qu'un 200 a la prochaine
#: lecture -- jamais un verdict. L'eviction est FIFO A LA PREMIERE insertion :
#: une re-inscription (nouvel etag du meme chemin) NE DEPLACE PAS l'entree --
#: un chemin chaud revalide souvent peut donc partir avant un chemin froid
#: recent. Choisi (CR #26631, non bloquant) : pour un cache de revalidation,
#: une eviction ne coute qu'un 200, jamais un verdict.
MAX_ENTRIES = 200

#: Plafond par entree : `git/blobs/<sha>` rend le contenu ENTIER en base64 --
#: sans borne, quelques blobs suffiraient a faire du fichier de cache le
#: plus gros objet de la machine. Un corps trop gros n'est PAS stocke : sa
#: lecture reste non conditionnelle (un 200 de plus), jamais un verdict.
BODY_MAX_BYTES = 200_000

#: Borne d'appel, alignee sur GH_CALL_TIMEOUT_S de B.0 (#19643).
TIMEOUT_S = 90.0

#: Compteurs de passe (mesurabilite #17315 / #26260 point 1).
CALLS = 0
HITS_304 = 0

_DISABLE = ("0", "off", "false", "no")


def cache_dir(environ: dict | None = None) -> Path | None:
    """Dossier du cache, ou None si desactive / sans base locale.

    `COURSIA_GH_ETAG` a 0/off desactive ; `COURSIA_GH_ETAG_DIR` designe un
    dossier explicite (tests) ; sinon `%LOCALAPPDATA%` (repli `APPDATA`)
    puis `CoursIA/gh_etag`, voisin du cache du tapis rapide (#22630).
    """
    env = os.environ if environ is None else environ
    if str(env.get("COURSIA_GH_ETAG", "1")).strip().lower() in _DISABLE:
        return None
    explicit = env.get("COURSIA_GH_ETAG_DIR")
    if explicit:
        return Path(explicit)
    base = env.get("LOCALAPPDATA") or env.get("APPDATA")
    if not base:
        return None
    return Path(base) / "CoursIA" / "gh_etag"


def _cache_path(environ: dict | None = None) -> Path | None:
    dossier = cache_dir(environ)
    return dossier / "cache.json" if dossier else None


#: Store memoire : chemin -> (etag, corps). Charge une fois par processus.
_store: dict[str, tuple[str, object]] | None = None


def _load_store() -> dict[str, tuple[str, object]]:
    """Le store persiste, ou {} s'il est absent/illisible (jamais fatal)."""
    global _store
    if _store is not None:
        return _store
    store: dict[str, tuple[str, object]] = {}
    chemin = _cache_path()
    if chemin is not None:
        try:
            brut = json.loads(chemin.read_text(encoding="utf-8"))
            if isinstance(brut, dict):
                for path, entry in brut.items():
                    if (isinstance(path, str) and isinstance(entry, list)
                            and len(entry) == 2
                            and isinstance(entry[0], str)):
                        store[path] = (entry[0], entry[1])
        except (OSError, ValueError):
            pass  # cache absent ou corrompu : lecture directe, jamais un verdict
    _store = store
    return store


def _save_store(store: dict[str, tuple[str, object]]) -> None:
    """Ecriture atomique (mkstemp + os.replace, discipline #22630).

    Un echec d'ecriture est ignore : le cache ne bloque jamais l'organe.
    """
    chemin = _cache_path()
    if chemin is None:
        return
    try:
        chemin.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=chemin.parent, suffix=".tmp")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(store, fh, ensure_ascii=False)
        os.replace(tmp, chemin)
    except (OSError, TypeError, ValueError):
        pass


def _http_status(header_block: str) -> int:
    """Code de statut d'un bloc d'en-tetes `gh api -i` (ligne 1)."""
    parts = header_block.splitlines()[0].split() if header_block else []
    try:
        return int(parts[1]) if len(parts) >= 2 else 0
    except ValueError:
        return 0


def _etag_of(header_block: str) -> str | None:
    for line in header_block.splitlines():
        if line.lower().startswith("etag:"):
            return line.split(":", 1)[1].strip()
    return None


def etag_applicable(args: list[str]) -> str | None:
    """Chemin REST conditionnable d'un argv `gh`, ou None.

    Seule la forme `["api", "repos/...", ...]` SANS AUCUN drapeau est
    conditionnable : `--paginate` suit ses pages en interne (pas de
    `If-None-Match` par page injectable via la CLI), `--jq` transforme le
    corps, `graphql` n'a pas d'ETag. Conservateur par construction : tout
    argv douteux reste sur le chemin non conditionnel d'origine.

    #26631 (CR coordinateur) : sans dossier de cache (`cache_dir()` None --
    desactive, ou machine sans LOCALAPPDATA/APPDATA comme un runner Linux),
    rend None AUSSI : l'appelant reste alors sur son chemin d'origine OCTET
    POUR OCTET. Un faux `subprocess.run` de test sert le stdout sans bloc
    d'en-tetes de `gh api -i` ; le chemin conditionnel y lirait un corps
    vide (incident : test_gh_json_porte_une_borne_par_appel, run 43651006619).
    Sans cache, il n'y a de toute facon rien a revalider : le conditionnel
    ne doit jamais changer la forme de l'appel.
    """
    if cache_dir() is None:
        return None
    if len(args) < 2 or args[0] != "api":
        return None
    path = args[1]
    if not isinstance(path, str) or not path.startswith("repos/"):
        return None
    if any(str(a).startswith("-") for a in args[2:]):
        return None
    return path


def conditional_get(path: str, timeout: float = TIMEOUT_S) -> tuple[object, bool]:
    """GET conditionnel d'un chemin REST ; rend (corps JSON, servi_par_304).

    Echecs (memes surfaces que l'appel non conditionnel) :
    - rc non nul SANS 304 : `subprocess.CalledProcessError` ;
    - 200 au corps non-JSON : `json.JSONDecodeError` ;
    - `gh` absent : `FileNotFoundError` ; borne depassee : `TimeoutExpired`.
    Un 304 sans corps en cache (store perdant) est une erreur BRUYANTE : le
    serveur certifie un etat que nous ne pouvons plus produire.
    """
    global CALLS, HITS_304
    CALLS += 1

    store = _load_store()
    entry = store.get(path)
    etag = entry[0] if entry else None

    cmd = ["gh", "api", "-i"]
    if etag:
        cmd += ["-H", f"If-None-Match: {etag}"]
    cmd.append(path)
    completed = subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=False, timeout=timeout,
    )

    # Statut lu AVANT le rc : `gh api -i` sort en rc=1 sur un 304 (mesure
    # #26260) -- ce n'est pas un echec.
    header_block, _, body_text = completed.stdout.partition("\n\n")
    status = _http_status(header_block)

    if status == 304:
        if entry is None:
            raise subprocess.CalledProcessError(
                completed.returncode, cmd,
                stderr=f"gh api {path} : 304 sans corps en cache (store perdant)"
                " -- lecture impossible, jamais un corps fabrique",
            )
        HITS_304 += 1
        # Deepcopy : le store ne doit pas partager un objet avec un appelant
        # qui le mute (memes precautions que pr_gate #26260, remarque CR).
        return copy.deepcopy(entry[1]), True

    if completed.returncode != 0:
        # Tout autre echec reste un echec : JAMAIS une reuse du corps cache.
        raise subprocess.CalledProcessError(
            completed.returncode, cmd,
            output=completed.stdout, stderr=completed.stderr,
        )

    body = json.loads(body_text)  # non-JSON = JSONDecodeError, comme avant
    new_etag = _etag_of(header_block)
    if new_etag and len(body_text) <= BODY_MAX_BYTES:
        store[path] = (new_etag, copy.deepcopy(body))
        while len(store) > MAX_ENTRIES:
            store.pop(next(iter(store)))
        _save_store(store)
    return body, False


def reset_for_tests() -> None:
    """Remet a zero l'etat de processus (store memoire et compteurs)."""
    global _store, CALLS, HITS_304
    _store = None
    CALLS = 0
    HITS_304 = 0
