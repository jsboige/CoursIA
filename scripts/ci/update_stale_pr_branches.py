#!/usr/bin/env python3
"""Met a jour les branches de PR EN RETARD sur leur base, sans jamais forcer.

Pourquoi cet organe existe (#16149)
-----------------------------------
`gh pr update-branch` est le SEUL remede a un rouge perime : un check evalue
contre une base gelee anterieure au fix du garde sur `main` ne peut pas etre
repare par `gh run rerun`, qui rejoue cette meme base gelee et rend le meme
rouge (cf `scripts/check_stale_guard_reds.py`, qui localise ce rouge mais ne
le repare pas). Le 2026-09-14, la passe manuelle du coordinateur a reussi sur
`ok=15 ko=0` -- seize PRs du stock. C'est cette passe manuelle que l'organe
automatise, avec les gardes que la main appliquait implicitement.

Sur le plancher DWELL, l'organe ne dit RIEN, et c'est deliberé (#16149).
`update-branch` cree un commit de fusion qui rafraichit la date de committer ;
avant le fix, cela re-armait les 120 min que le geste sert a franchir -- 2 h de
taxe par reparation. **#16149 est ferme dans `scripts/ci/merge_dwell.py`** : le
plancher se mesure desormais sur le dernier commit qui modifie le COTE PR, et
une fusion de base dont l'arbre est IDENTIQUE a l'auto-merge de ses deux
parents (`git merge-tree --write-tree`, fail-closed si la preuve est
inatteignable) est exemptee. Un `update-branch` nominal ne re-arme donc plus
rien.

Consequence pour cet organe : il n'a aucun cout DWELL a declarer, et il n'en
declare aucun -- un champ `dwell_floor_reset` serait faux dans le cas nominal.
La seule chose qu'il puisse en dire est negative et non mesurable de son cote :
l'exemption est fail-closed, donc un `update-branch` dont la PREUVE echoue
re-arme bel et bien le plancher. Cette preuve se calcule sur l'arbre Git, pas
sur l'objet PR -- l'organe ne l'a pas et n'invente pas de verdict a sa place.
Le plancher se lit dans `merge_dwell.py`.

Contrat
-------
Entree : des NUMEROS DE PR explicites, repetables (`--pr 123 --pr 456`).
Jamais un pool : l'organe n'enumere rien, ne liste rien, ne decouvre rien. Un
organe qui enumererait le pool se ferait appeler comme un balayage et
appliquerait un geste destructeur a une population qu'il n'a pas lue.

Defaut = DRY-RUN. `--apply` est requis pour ecrire. Jamais de force-push, jamais
de rebase, jamais de `--rebase`, jamais de repli.

Pour chaque PR, neuf conditions doivent tenir ENSEMBLE pour que
`gh pr update-branch <N>` soit appele :

  1. `state == OPEN`            -- une PR fermee/mergee n'a pas de branche a rafraichir ;
  2. pas un fork                -- `isCrossRepository` : l'ecriture n'est pas de notre cote ;
  3. pas un brouillon           -- un draft n'est pas en file de merge ;
  4. base ET tete inchangees depuis la mesure -- la base est FIGEE par son SHA
     (pas par son nom : une base empilee avance), le compare du deficit porte
     sur `base_sha...head_sha`, et les DEUX SHA sont relus apres le compare,
     immediatement avant l'appel d'ecriture. Une tete ou une base qui bouge
     sous nos pieds pendant ou apres la mesure est un REFUSE, pas un
     « on reessaie » ;
  5. `mergeable != CONFLICTING` -- un conflit n'a jamais de repli ici ;
  6. `mergeable == MERGEABLE`   -- un `UNKNOWN` de `mergeable` OU de
     `mergeStateStatus` est un SKIP nomme, reessayable : GitHub n'a pas fini
     de calculer, et decider sans son verdict n'est pas decider ;
  7. deficit de commits REEL `behind_by > 0` mesure par l'API de comparaison --
     voir la section suivante, c'est le point le plus fragile de tout l'organe ;
  8. RESERVATION du registre des mises a jour en vol obtenue sous verrou
     inter-processus AVANT l'appel distant (voir plus bas) : sans reservation,
     pas d'ecriture ;
  9. plafond `--max-updates` (defaut 3) non epuise.

Pourquoi le retard NE se lit PAS dans `mergeStateStatus` (mesure du 2026-09-17)
-------------------------------------------------------------------------------
Le reflexe naturel est de garder l'organe sur `mergeStateStatus == BEHIND`.

**Mesure du 2026-09-17** (`gh pr list --state open --limit 200`, plafond
touche : 200 lignes rendues sur 208 PR ouvertes au total, total lu par
`search/issues`). Repartition des 200 lignes lues :
`BLOCKED: 54, CLEAN: 128, DIRTY: 9, UNSTABLE: 9` -- **`BEHIND: 0`**.

Un gate sur `BEHIND` aurait donc rendu l'organe structurellement inerte : jamais
un seul appel, et un rapport vert disant « rien a faire », indiscernable de
« rien a faire » sur un pool qui ne l'est pas.

La verite est ailleurs. Mesuree sur un echantillon de ce meme pool par
`GET /repos/{owner}/{repo}/compare/{base}...{head}` :

    #16552  BLOCKED    behind_by=2
    #16548  BLOCKED    behind_by=11
    #16546  CLEAN      behind_by=11     <- CLEAN et 11 commits de retard
    #16528  UNSTABLE   behind_by=20
    #16325  UNSTABLE   behind_by=118
    #16219  DIRTY      behind_by=175

`mergeStateStatus` ne rapporte `BEHIND` que sous certaines configurations de
protection de branche ; partout ailleurs il rapporte `CLEAN` ou `BLOCKED` sur
une branche qui a un retard reel. L'organe lit donc `behind_by` -- le deficit
exact, contre la base DECLAREE -- et n'utilise `mergeStateStatus` que pour les
deux etats qui n'ont pas d'ambiguite : `DIRTY` (conflit, REFUSE) et son
affichage dans le resultat. `behind_by` etant mesure contre `baseRefName`, le
cas empile est couvert sans code special.

Le gate de non-inertie vit dans les tests
(`test_clean_and_behind_is_updated_from_the_compare_api`) : la PR y est `CLEAN`
ET en retard de 11 commits -- exactement la ligne #16546. Rebrancher l'organe
sur `mergeStateStatus` fait rougir ce test, il ne peut pas redevenir muet en
silence.

Un `behind_by` illisible (API injoignable) rend un SKIP `BEHIND_UNKNOWN` :
fail-closed, nomme, reessayable -- jamais un « probablement en retard ».

Ce que l'organe ne fait PAS et ne fera pas
------------------------------------------
- Il ne passe JAMAIS `--rebase` : un rebase reecrit les commits d'auteur, ce que
  la discipline de lane reserve a l'auteur de la PR.
- Il ne « repare » jamais un conflit, une protection refusee ou une tete qui a
  bouge : ces trois-la sortent en REFUSE structure et remontent a un humain.
- Il ne se replie sur aucun autre geste. Un repli force-push sur une branche de
  PR a lane unique est autorise par la regle, mais ce n'est pas a un automate
  d'update-branch de le decider : le geste est different et son autorisation
  appartient a l'auteur.

PRs empilees (stacked)
----------------------
`gh pr update-branch <N>` fusionne la base DECLAREE de la PR (`baseRefName` de
l'API) dans sa branche -- il n'y a pas de flag `--base`. Une PR empilee est donc
mise a jour contre sa base d'empilement SANS que l'appelant ait a la nommer, et
une erreur ici (update contre `main` au lieu de la base empilee) est impossible
par construction : l'organe ne fournit jamais de base et n'appelle pas git. Il
REPORTE la base et sa nature (`base_kind: main|stacked`, `base_source:
pr.baseRefName`) pour que la lecture distingue les deux cas.

Fraicheur du verdict apres application
--------------------------------------
Un `update-branch` reecrit la tete : les checks, les reviews et le dossier
`[ADJOINT PREFLIGHT]` ont ete rendus contre la tete PRECEDENTE. Chaque resultat
applique porte donc `freshness: STALE`, `refresh_required: true` et
`invalidated: [checks, reviews, dossier]` -- ce n'est pas une decoration : le
gate d'entree en review (`scripts/check_adjoint_prevalidation.py`) lie le
dossier au SHA exact, donc un dossier non rafraichi est REFUSE a la lecture
suivante.

Mise a jour « deja en vol »
---------------------------
L'API ne porte pas de champ « mise a jour en cours » parmi les champs lus ici.
L'organe tient donc son PROPRE registre local (`<state-dir>/in-flight.json`,
defaut sous le repertoire temporaire, reglable par `--state-dir`). Ce registre
est une RESERVATION, pas un journal : l'entree est acquise sous un verrou
inter-processus (`flock` sur POSIX, `msvcrt.locking` sur Windows) AVANT
l'appel `gh pr update-branch`, par read-merge-write sous verrou. Deux
processus qui partagent le meme state-dir ne peuvent donc pas muter la meme
PR : le premier reserve, le second lit la reservation sous le meme verrou et
sort en SKIP `UPDATE_IN_FLIGHT`.

Sur ECHEC de l'appel distant, la reservation est liberee sous verrou (seule
NOTRE cle est retiree : les enregistrements des autres PR survivent). Sur
SUCCES, la reservation DEVIENT l'enregistrement en vol : une PR dont la tete
est encore celle enregistree et dont l'enregistrement est plus jeune que
`--in-flight-ttl` (defaut 900 s) reste bloquee -- un second appel pendant
qu'une mise a jour est en vol rendrait un echec opaque. Un enregistrement
perime, ou dont la tete a change (donc la mise a jour a atterri), est ignore.

Fail-closed sur le registre lui-meme (review 5240194972) : un registre PRESENT
mais illisible ou corrompu n'est JAMAIS lu comme vide -- c'est un REFUSE
`LEDGER_CORRUPT`, parce qu'un registre improvise desarmerait la garde au
moment precis ou deux processus pourraient se marcher dessus. Un state-dir
inouvrirable est un REFUSE `LEDGER_UNWRITABLE` : sans garde, pas d'ecriture.
Les ecritures du registre sont atomiques (replace) et passent par un fichier
temporaire UNIQUE par ecrivain (`mkstemp`) : le tmp a nom fixe d'une version
anterieure etait une collision entre ecrivains.

Usage
-----
    python scripts/ci/update_stale_pr_branches.py --pr 16546 --pr 16548
    python scripts/ci/update_stale_pr_branches.py --pr 16546 --pr 16548 --apply
    python scripts/ci/update_stale_pr_branches.py --pr 16546 --apply --max-updates 1

Sortie : JSON sur stdout, toujours (les deux modes), forme stable.
Codes de sortie :
  0  -- aucune PR refusee (mises a jour appliquees et/ou SKIP benins) ;
  1  -- au moins une PR en REFUSE (conflit, fork, tete/base qui a bouge,
        protection refusee, echec de l'appel) : un humain doit regarder ;
  2  -- erreur d'appelant (arguments).
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.parse
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:  # POSIX
    import fcntl
except ImportError:  # Windows : le verrou du registre bascule sur msvcrt
    fcntl = None
if os.name == "nt":
    import msvcrt

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_MAX_UPDATES = 3
DEFAULT_IN_FLIGHT_TTL = 900
MAIN_BRANCHES = {"main", "master"}

#: Champs `gh pr view` lus. `mergeable` porte le conflit ; `isCrossRepository`
#: porte le fork ; `baseRefName` est la base DECLAREE de la PR -- la seule
#: contre laquelle `gh pr update-branch` fusionne, et celle que l'organe
#: reporte. `mergeStateStatus` est lu pour l'affichage et pour `DIRTY`
#: seulement : le RETARD ne s'y lit pas (mesure 2026-09-17, 0 `BEHIND` sur les
#: 200 lignes ouvertes lues alors que le pool en porte jusqu'a 175 commits --
#: voir le docstring du module).
PR_FIELDS = (
    "number,state,isDraft,isCrossRepository,baseRefName,headRefName,"
    "headRefOid,mergeable,mergeStateStatus,url"
)

ACTION_UPDATE = "UPDATE"
ACTION_SKIP = "SKIP"
ACTION_REFUSE = "REFUSE"

#: Ce qu'un `update-branch` perime pour la lecture suivante.
UPDATED_INVALIDATES = ["checks", "reviews", "dossier"]


class GhError(RuntimeError):
    """Un appel `gh` a echoue, ou a rendu une charge inexploitable."""


def run_gh(args: list[str]) -> str:
    """Execute `gh`. Point de couture unique : les tests remplacent ce nom."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        raise GhError(detail or f"gh {' '.join(args[:3])} exited {proc.returncode}")
    return proc.stdout


def read_pr(pr: int, repo: str) -> dict[str, Any]:
    """Lit l'etat LIVE d'une PR : etat, base, tete, mergeabilite."""
    raw = run_gh(["pr", "view", str(pr), "--repo", repo, "--json", PR_FIELDS])
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise GhError(f"gh pr view #{pr} did not return an object")
    return data


def encode_path_segment(value: str) -> str:
    """Encode un segment de chemin d'API GitHub (review 5240194972).

    `gh api` recoit l'URL telle quelle : un `#` non encode y devient un
    fragment (l'endpoint reel change silencieusement) et un caractere Unicode
    passe au petit bonheur de la couche transport. Chaque segment interpole
    dans un chemin est donc encode integralement.
    """
    return urllib.parse.quote(str(value), safe="")


def read_branch_sha(repo: str, ref: str) -> str:
    """SHA immuable porte par une branche du depot, a l'instant de l'appel.

    La base DECLAREE d'une PR empilee est une branche qui AVANCE : son nom ne
    prouve rien. Seul le SHA lu au moment de la mesure fige la decision --
    c'est contre ce commit-la que le deficit est mesure puis re-verifie avant
    l'ecriture (review 5240194972, finding 1).
    """
    raw = run_gh(["api", f"repos/{repo}/git/ref/heads/{encode_path_segment(ref)}"])
    data = json.loads(raw)
    sha = None
    if isinstance(data, dict):
        obj = data.get("object")
        if isinstance(obj, dict):
            sha = obj.get("sha")
    if not isinstance(sha, str) or not sha:
        raise GhError(f"ref heads/{ref} de {repo} n'a pas rendu de SHA")
    return sha


def base_kind(base: str | None) -> str:
    """`main` pour la base d'integration, `stacked` pour toute autre base."""
    return "main" if (base or "") in MAIN_BRANCHES else "stacked"


def read_behind(repo: str, base: str, head: str) -> int:
    """Nombre de commits de `base` absents de `head` -- le retard exact.

    `base` et `head` sont des SHA immuables en production, mais la fonction
    reste ref-generic : les segments sont encodes (review 5240194972), car un
    `#` cru dans un chemin d'API devient un fragment d'URL et rend un deficit
    illisible -- `BEHIND_UNKNOWN` -- sans qu'aucune erreur ne le dise. C'est la
    seule lecture de retard de l'organe : `mergeStateStatus` ne rapporte pas
    `BEHIND` sur ce depot (mesure du module).
    """
    raw = run_gh(
        [
            "api",
            f"repos/{repo}/compare/{encode_path_segment(base)}...{encode_path_segment(head)}",
        ]
    )
    data = json.loads(raw)
    if not isinstance(data, dict) or not isinstance(data.get("behind_by"), int):
        raise GhError(f"compare {base}...{head} did not return an integer behind_by")
    return data["behind_by"]


def attach_behind(snapshot: dict[str, Any], repo: str) -> dict[str, Any]:
    """Epingle les SHA de base et de tete, puis mesure le retard SUR CES SHA.

    Appele SEULEMENT apres les gardes de metadonnees : une PR fermee, un fork,
    un brouillon ou un conflit se decide sans savoir de combien de commits la
    branche est en retard, et l'appel n'est pas gratuit.

    La base DECLAREE (`baseRefName`) est un nom mutable : sur une PR empilee,
    la branche parent peut avancer PENDANT l'appel de comparaison, et un
    compare par nom lirait un retard calcule contre un commit DIFFERENT de
    celui que `gh pr update-branch` fusionnera. Le compare porte donc sur
    `base_sha...head_sha` (review 5240194972, finding 1), et ces SHA pinnes
    sont re-verifies par `recheck_pinned_refs` juste avant l'ecriture.

    Le retard est rendu `None` (avec `behind_error`) quand l'API ne repond pas :
    c'est une donnee manquante NOMMEE, que `classify` traite en SKIP fail-closed
    -- jamais en « probablement en retard ».
    """
    base_ref = snapshot.get("baseRefName")
    head_ref = snapshot.get("headRefName")
    head_sha = snapshot.get("headRefOid")
    try:
        base_sha = read_branch_sha(repo, base_ref) if base_ref else None
        snapshot["base_sha"] = base_sha
        snapshot["head_sha"] = head_sha
        snapshot["behind_by"] = (
            read_behind(repo, base_sha, head_sha) if base_sha and head_sha else None
        )
        snapshot["behind_error"] = None
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        snapshot["behind_by"] = None
        snapshot["behind_error"] = f"{type(exc).__name__}: {exc}"
    return snapshot


# --------------------------------------------------------------------------
# Registre des mises a jour en vol
# --------------------------------------------------------------------------


class LedgerError(RuntimeError):
    """Registre en vol illisible ou corrompu : la garde refuse, elle n'improvise pas."""


def ledger_path(state_dir: Path) -> Path:
    return Path(state_dir) / "in-flight.json"


def ledger_lock_path(path: Path) -> Path:
    """Le verrou vit a cote du registre et n'est JAMAIS remplace : le detenteur
    du verrou doit tenir le meme fichier ouvert jusqu'a sa liberation."""
    return path.with_name(path.name + ".lock")


@contextmanager
def ledger_lock(path: Path):
    """Verrou inter-processus exclusif autour du registre en vol.

    `flock` sur POSIX, `msvcrt.locking` sur Windows -- deux verrous du systeme
    de fichiers : deux PROCESSUS distincts partageant le meme state-dir se
    bloquent reellement (review 5240194972, finding 2), pas seulement deux
    fils du meme processus. Le fichier de verrou est ouvert en ajout, jamais
    remplace, et la region verrouillee est le premier octet.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = open(path, "a+b")
    acquired = False
    try:
        handle.seek(0)
        if fcntl is not None:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        else:
            # LK_LOCK : bloquant, 10 tentatives espacees d'une seconde.
            msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK, 1)
        acquired = True
        yield handle
    finally:
        if acquired:
            handle.seek(0)
            try:
                if fcntl is not None:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
                else:
                    msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            except OSError:
                pass  # la fermeture du handle libere le verrou de toute facon
        handle.close()


#: Un `previous_head` est un SHA Git : hexadecimal SHA-1 (40) ou SHA-256 (64),
#: les deux formats que l'API GitHub rend pour une ref de branche -- accepter
#: les deux n'est pas de la complaisance, c'est la compatibilite avec un depot
#: migre en SHA-256 (testee).
RECORD_SHA_RE = re.compile(r"^[0-9a-f]{40}$|^[0-9a-f]{64}$")


def valid_ledger_record(record: Any) -> bool:
    """Schema structurel MINIMAL d'un enregistrement du registre en vol.

    Un enregistrement ecrit par `try_reserve_update` porte TOUJOURS
    `previous_head` (SHA hex 40 ou 64, jamais None -- la reservation n'a lieu
    qu'apres un compare reussi, donc sur une tete epinglee) et `started_at`
    (numerique FINI, pas booleen -- un bool est un int en Python, et `True`
    n'est pas un instant). Tout enregistrement qui ne respecte pas ce schema
    n'a pas pu etre ecrit par cet organe : corruption structurelle, pas une
    version future.

    Les champs SUPPLEMENTAIRES sont acceptes (review 5240575597) : une version
    future de l'organe peut en ajouter, et rejeter l'inconnu casserait la
    compatibilite sans gain de surete -- les champs requis restent valides.
    C'est la SEULE tolerance de compatibilite, et elle est testee.
    """
    if not isinstance(record, dict):
        return False
    head = record.get("previous_head")
    if not isinstance(head, str) or not RECORD_SHA_RE.fullmatch(head):
        return False
    started = record.get("started_at")
    if isinstance(started, bool) or not isinstance(started, (int, float)):
        return False
    return math.isfinite(started)


def read_ledger(path: Path) -> dict[str, dict[str, Any]]:
    """Lecture stricte : ABSENT = registre vide ; PRESENT mais illisible ou
    malforme = `LedgerError`.

    Fail-closed (review 5240194972, finding 2) : lire un registre corrompu
    comme vide desarmerait la garde UPDATE_IN_FLIGHT au moment precis ou deux
    processus pourraient se marcher dessus. Le refus est explicite, il
    n'improvise pas un registre neuf.

    La validation est STRUCTURELLE, cle par cle (review 5240575597, F2
    residuel) : valider l'objet racine laissait passer un enregistrement
    scalaire ou liste -- ecrase ou conserve en silence, pendant qu'une mutation
    restait autorisee. Chaque enregistrement doit respecter le schema minimal
    `valid_ledger_record` ; UNE entree qui echoue refuse TOUT le registre,
    avant toute reecriture. Les seuls appelants mutation sont sous verrou
    (`try_reserve_update`, `release_reservation`) : la validation est rendue
    sous le meme verrou que la lecture.
    """
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except (OSError, ValueError, UnicodeError) as exc:
        raise LedgerError(f"registre {path.name} illisible ou corrompu : {exc}") from exc
    if not isinstance(data, dict):
        raise LedgerError(f"registre {path.name} corrompu : pas un objet JSON")
    for record_key, record in data.items():
        if not valid_ledger_record(record):
            raise LedgerError(
                f"registre {path.name} corrompu : l'enregistrement {record_key!r} ne "
                "respecte pas le schema ({previous_head: SHA hex, started_at: numerique fini})"
            )
    return data


def write_ledger(path: Path, data: dict[str, dict[str, Any]]) -> None:
    """Ecriture atomique via un temporaire UNIQUE par ecrivain.

    Le temporaire a nom fixe d'une version anterieure (`in-flight.json.tmp`)
    etait une collision : deux ecrivains preparaient le meme chemin et le
    `replace` du dernier ecrasait la preparation de l'avant-dernier. `mkstemp`
    donne un nom unique ; le verrou ordonne, le nom unique evite la collision.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(dir=path.parent, prefix=path.name + ".", suffix=".tmp")
    tmp = Path(tmp_name)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True))
        tmp.replace(path)
    except BaseException:
        tmp.unlink(missing_ok=True)
        raise


def ledger_key(repo: str, pr: int) -> str:
    return f"{repo}#{pr}"


def record_in_flight(record: dict[str, Any], *, head: str | None, now: float, ttl: int) -> bool:
    """Un enregistrement du registre bloque-t-il encore la tete donnee ?

    Fenetre `--in-flight-ttl` non perimee ET meme tete : la mise a jour
    enregistree est toujours en vol. Une tete differente (l'ancienne mise a
    jour a atterri) ou un enregistrement perime ne bloquent pas.

    Pas de try/except ici : l'appelant (`try_reserve_update`) n'atteint cette
    fonction qu'avec un enregistrement VALIDE par `valid_ledger_record` -- un
    `started_at` non numerique y serait un defaut de wiring a faire rougir,
    pas une corruption a silencer (review 5240575597).
    """
    started_at = float(record["started_at"])
    return (now - started_at) < ttl and record.get("previous_head") == head


def try_reserve_update(
    path: Path,
    key: str,
    *,
    reservation: dict[str, Any],
    now: float,
    ttl: int,
) -> tuple[bool, dict[str, dict[str, Any]]]:
    """Reserve la mise a jour SOUS VERROU, AVANT tout appel distant.

    Rend `(reserve, registre)` : `reserve=False` signifie qu'une mise a jour
    est deja en vol sur cette tete (le registre la dit sous verrou). Tout le
    read-merge-write vit sous le verrou : deux processus qui arrivent en meme
    temps se serialisent, le premier ecrit sa reservation, le second la LIT --
    il ne peut plus l'ecraser (review 5240194972, finding 2). Le registre
    corrompu leve `LedgerError` : fail-closed, jamais un registre improvise.
    """
    with ledger_lock(ledger_lock_path(path)):
        ledger = read_ledger(path)
        record = ledger.get(key)
        if isinstance(record, dict) and record_in_flight(
            record, head=reservation.get("previous_head"), now=now, ttl=ttl
        ):
            return False, ledger
        merged = dict(ledger)
        merged[key] = dict(reservation)
        write_ledger(path, merged)
        return True, merged


def release_reservation(path: Path, key: str, reservation: dict[str, Any]) -> None:
    """Libere la reservation d'une mise a jour qui n'a PAS eu lieu.

    Relit le registre sous verrou et ne retire NOTRE cle que s'il porte
    ENCORE exactement notre reservation : un enregistrement ecrit entre-temps
    par un autre processus -- pour cette PR ou une autre -- survit.
    """
    with ledger_lock(ledger_lock_path(path)):
        ledger = read_ledger(path)
        if ledger.get(key) == reservation:
            merged = dict(ledger)
            del merged[key]
            write_ledger(path, merged)


def release_quietly(path: Path, key: str, reservation: dict[str, Any]) -> list[str]:
    """Libere la reservation sans laisser son echec masquer le verdict principal.

    Une reservation non liberee n'est pas un danger : elle maintient la garde
    UPDATE_IN_FLIGHT jusqu'a l'expiration du TTL, donc fail-closed. C'est
    signale en warning, pas leve en exception.
    """
    try:
        release_reservation(path, key, reservation)
    except (LedgerError, OSError) as exc:
        return [
            f"reservation non liberee ({exc}) : la garde UPDATE_IN_FLIGHT "
            "tiendra jusqu'a l'expiration du TTL"
        ]
    return []


# --------------------------------------------------------------------------
# Decision (pure)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Verdict:
    action: str
    code: str
    reason: str


def classify_metadata(
    snapshot: dict[str, Any],
    *,
    measured: dict[str, Any] | None,
) -> Verdict | None:
    """Gardes decidables sur les SEULES metadonnees. `None` = continuer.

    Separees de `classify` pour que l'appel de comparaison (le seul cout
    variable de l'organe) ne soit paye que par les PR qui passent tout ceci :
    une PR fermee, un fork, un brouillon, un conflit ou un `mergeable=UNKNOWN`
    se tranchent sans savoir de combien de commits la branche est en retard.

    `measured` est la mesure de reference (premiere lecture) ; `None` pour la
    premiere passe. Quand elle est fournie, toute derive de base ou de tete
    entre les deux lectures est un REFUSE -- c'est la garde TOCTOU.
    """
    if snapshot.get("state") != "OPEN":
        return Verdict(
            ACTION_SKIP,
            "NOT_OPEN",
            f"state={snapshot.get('state')} : seules les PR OPEN portent une branche a rafraichir",
        )
    if snapshot.get("isCrossRepository"):
        return Verdict(
            ACTION_REFUSE,
            "FORK",
            "isCrossRepository=true : la branche appartient a un fork, "
            "`gh pr update-branch` n'y ecrit pas",
        )
    if snapshot.get("isDraft"):
        return Verdict(
            ACTION_SKIP,
            "DRAFT",
            "brouillon : la mise a jour se fera quand la PR sera presentee",
        )

    if measured is not None:
        before_base = measured.get("baseRefName")
        after_base = snapshot.get("baseRefName")
        if before_base != after_base:
            return Verdict(
                ACTION_REFUSE,
                "BASE_CHANGED",
                f"base changee entre mesure et application : {before_base} -> {after_base}",
            )
        before_head = measured.get("headRefOid")
        after_head = snapshot.get("headRefOid")
        if before_head != after_head:
            return Verdict(
                ACTION_REFUSE,
                "HEAD_CHANGED",
                f"tete changee entre mesure et application : {before_head} -> {after_head}",
            )

    mergeable = snapshot.get("mergeable")
    if mergeable == "CONFLICTING":
        return Verdict(
            ACTION_REFUSE,
            "CONFLICTING",
            "mergeable=CONFLICTING : conflit avec la base ; "
            "aucun repli force-push/rebase n'est applique ici",
        )
    if mergeable != "MERGEABLE":
        return Verdict(
            ACTION_SKIP,
            "MERGEABLE_UNKNOWN",
            f"mergeable={mergeable} : GitHub calcule encore ; reessayer plus tard",
        )

    # `DIRTY` est un conflit franc, redondant avec `mergeable` mais sans cout.
    # Tout autre `mergeStateStatus` est IGNORE : il ne porte pas le retard sur
    # ce depot (0 `BEHIND` sur les 200 lignes ouvertes lues, mesure du module).
    if snapshot.get("mergeStateStatus") == "DIRTY":
        return Verdict(
            ACTION_REFUSE,
            "CONFLICTING",
            "mergeStateStatus=DIRTY : conflit avec la base ; "
            "aucun repli force-push/rebase n'est applique ici",
        )
    # Fail-closed sur l'indetermination (review 5240194972, finding 3) :
    # `mergeable=MERGEABLE` avec `mergeStateStatus=UNKNOWN` signifie que GitHub
    # n'a pas fini de calculer l'etat de fusion -- un `MERGEABLE` rendu avant
    # la fin du calcul n'est pas un verdict. SKIP nomme, reessayable, avant
    # tout appel de comparaison.
    if snapshot.get("mergeStateStatus") == "UNKNOWN":
        return Verdict(
            ACTION_SKIP,
            "MERGE_STATE_UNKNOWN",
            "mergeStateStatus=UNKNOWN bien que mergeable=MERGEABLE : GitHub "
            "n'a pas fini de calculer l'etat de fusion ; fail-closed, reessayer",
        )
    return None


def classify(
    snapshot: dict[str, Any],
    *,
    measured: dict[str, Any] | None,
    applied: int,
    max_updates: int,
) -> Verdict:
    """Rend la decision COMPLETE pour une mesure de PR. Fonction pure.

    Enchaine les gardes de metadonnees (`classify_metadata`) puis celles qui
    supposent la mesure du retard : le deficit lui-meme et le plafond.

    La garde UPDATE_IN_FLIGHT ne vit PAS ici : elle n'est pas decidable sur une
    photo en memoire, elle doit etre ATOMIQUE avec l'ecriture -- c'est la
    reservation `try_reserve_update` qui la porte, sous verrou, juste avant
    l'appel distant (review 5240194972, finding 2).
    """
    gate = classify_metadata(snapshot, measured=measured)
    if gate is not None:
        return gate

    behind_by = snapshot.get("behind_by")
    if behind_by is None:
        return Verdict(
            ACTION_SKIP,
            "BEHIND_UNKNOWN",
            f"retard illisible ({snapshot.get('behind_error') or 'behind_by absent'}) : "
            "fail-closed, reessayer plus tard",
        )
    if behind_by <= 0:
        return Verdict(
            ACTION_SKIP,
            "UP_TO_DATE",
            f"behind_by={behind_by} : la branche n'est pas en retard sur sa base ; "
            "un update serait un no-op",
        )

    if max_updates and applied >= max_updates:
        return Verdict(ACTION_SKIP, "CAP_REACHED", cap_reason(max_updates))

    return Verdict(
        ACTION_UPDATE,
        "OK",
        f"branche en retard de {behind_by} commit(s) sur sa base, sans conflit",
    )


# --------------------------------------------------------------------------
# Resultat
# --------------------------------------------------------------------------


def build_result(
    pr: int,
    snapshot: dict[str, Any],
    verdict: Verdict,
    *,
    updated: bool,
    warnings: list[str] | None = None,
) -> dict[str, Any]:
    base = snapshot.get("baseRefName")
    stale = bool(updated)
    return {
        "pr": pr,
        "action": verdict.action,
        "code": verdict.code,
        "reason": verdict.reason,
        "base": base,
        "base_kind": base_kind(base),
        "stacked": base_kind(base) == "stacked",
        "base_source": "pr.baseRefName",
        "rebase": False,
        # La tete N'EST PAS re-lue apres l'appel : `gh pr update-branch` rend la
        # main a son client avant que GitHub reecrive la reference, donc une
        # relecture immediate peut rendre l'ANCIENNE valeur -- une precision
        # fausse. L'organe nomme donc ce qu'il a reellement observe au moment de
        # la decision, et laisse la nouvelle tete au lecteur.
        "previous_head": snapshot.get("headRefOid"),
        "head_ref": snapshot.get("headRefName"),
        "mergeable": snapshot.get("mergeable"),
        "merge_state_status": snapshot.get("mergeStateStatus"),
        "behind_by": snapshot.get("behind_by"),
        "url": snapshot.get("url"),
        "updated": updated,
        "freshness": "STALE" if stale else None,
        "refresh_required": stale,
        "invalidated": list(UPDATED_INVALIDATES) if stale else [],
        "warnings": list(warnings or []),
    }


def blank_result(pr: int) -> dict[str, Any]:
    """Squelette commun : une PR dont AUCUNE surface n'a ete lue."""
    return {
        "pr": pr,
        "action": ACTION_SKIP,
        "code": "",
        "reason": "",
        "base": None,
        "base_kind": None,
        "stacked": False,
        "base_source": "pr.baseRefName",
        "rebase": False,
        "previous_head": None,
        "head_ref": None,
        "mergeable": None,
        "merge_state_status": None,
        "behind_by": None,
        "url": None,
        "updated": False,
        "freshness": None,
        "refresh_required": False,
        "invalidated": [],
        "warnings": [],
    }


def error_result(
    pr: int,
    exc: BaseException,
    *,
    warnings: list[str] | None = None,
) -> dict[str, Any]:
    return {
        **blank_result(pr),
        "action": ACTION_REFUSE,
        "code": "ERROR",
        "reason": f"{type(exc).__name__}: {exc}",
        "warnings": list(warnings or []),
    }


def cap_reached_result(pr: int, max_updates: int) -> dict[str, Any]:
    """Resultat du plafond, rendu SANS aucune lecture reseau.

    Une fois `--max-updates` epuise, l'etat des PR restantes ne peut plus
    changer la decision : les lire serait payer deux lectures et un appel de
    comparaison pour un verdict deja connu.
    """
    return {
        **blank_result(pr),
        "code": "CAP_REACHED",
        "reason": cap_reason(max_updates),
    }


def cap_reason(max_updates: int) -> str:
    return f"plafond --max-updates {max_updates} atteint : PR suivante au prochain appel"


# --------------------------------------------------------------------------
# Traitement d'une PR
# --------------------------------------------------------------------------


def recheck_pinned_refs(
    repo: str,
    live: dict[str, Any],
    pinned: dict[str, Any],
) -> Verdict | None:
    """Relit les DEUX SHA pinnes APRES le compare, juste avant l'ecriture.

    C'est la seconde moitie de la garde TOCTOU (review 5240194972, finding 1) :
    l'appel de comparaison laisse lui-meme une fenetre ouverte -- la base ou
    la tete peuvent bouger PENDANT ce compare. Ecrire apres coup reviendrait a
    fusionner des commits que personne n'a decides : la derive est un REFUSE.

    Rend `None` si rien n'a bouge. Leve `GhError`/`OSError` si la relecture
    elle-meme echoue -- l'appelant tranche en REFUSE structure.
    """
    base_ref = live.get("baseRefName")
    head_ref = live.get("headRefName")
    base_sha = pinned.get("base_sha")
    head_sha = pinned.get("head_sha")
    base_now = read_branch_sha(repo, base_ref)
    head_now = read_branch_sha(repo, head_ref)
    if base_now != base_sha:
        return Verdict(
            ACTION_REFUSE,
            "BASE_CHANGED",
            f"sha de la base {base_ref} change entre le compare et l'ecriture : "
            f"{base_sha} -> {base_now}",
        )
    if head_now != head_sha:
        return Verdict(
            ACTION_REFUSE,
            "HEAD_CHANGED",
            f"sha de la tete {head_ref} change entre le compare et l'ecriture : "
            f"{head_sha} -> {head_now}",
        )
    return None


def process_one(
    pr: int,
    *,
    repo: str,
    apply: bool,
    ledger_file: Path,
    key: str,
    now: float,
    in_flight_ttl: int,
    applied: int,
    max_updates: int,
) -> dict[str, Any]:
    """Mesure, epingle, re-mesure, reserve, puis applique si -- et seulement
    si -- tout tient.

    L'ordre des lectures est un choix de cout : les gardes de metadonnees
    tranchent d'abord (un appel), la relecture TOCTOU vient ensuite, et le
    deficit de commits -- le seul appel de comparaison -- n'est paye que par
    les PR qui ont deja passe tout le reste. La sequence FINALE, elle, est un
    choix de surete (review 5240194972) :

      1. la base et la tete sont EPINGLEES par SHA, et le compare porte sur
         ces SHA -- pas sur le nom mutable de la base ;
      2. la RESERVATION du registre en vol est acquise sous verrou AVANT
         l'appel distant : c'est elle qui arrete un second processus, pas un
         enregistrement ecrit apres coup ;
      3. les SHA epingles sont RELUS immediatement avant l'ecriture -- la
         relecture est la derniere chose avant `gh pr update-branch`, pour que
         la fenetre TOCTOU residuelle soit minimale ;
      4. sur echec (distant ou de garde), la reservation est liberee sans
         toucher aux enregistrements des autres PR.
    """
    try:
        measured = read_pr(pr, repo)
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        return error_result(pr, exc)

    early = classify_metadata(measured, measured=None)
    if early is not None:
        return build_result(pr, measured, early, updated=False)

    # Garde TOCTOU noms + tete : la base et la tete doivent etre celles qu'on
    # vient de mesurer. Un update-branch lance sur une tete qui a bouge
    # reecrit une branche que quelqu'un d'autre vient de pousser.
    try:
        live = read_pr(pr, repo)
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        return error_result(pr, exc)

    early = classify_metadata(live, measured=measured)
    if early is not None:
        return build_result(pr, live, early, updated=False)

    pinned = attach_behind(live, repo)
    verdict = classify(pinned, measured=measured, applied=applied, max_updates=max_updates)
    if verdict.action != ACTION_UPDATE:
        return build_result(pr, pinned, verdict, updated=False)

    if not apply:
        return build_result(pr, pinned, verdict, updated=False)

    # Reservation AVANT toute mutation distante : sans reservation, pas
    # d'ecriture. Fail-closed sur le registre : corrompu ou inouvrirable =
    # REFUSE explicite, jamais un registre improvise.
    reservation = {"previous_head": pinned.get("head_sha"), "started_at": now}
    try:
        reserved, _merged = try_reserve_update(
            ledger_file,
            key,
            reservation=reservation,
            now=now,
            ttl=in_flight_ttl,
        )
    except LedgerError as exc:
        return build_result(
            pr,
            pinned,
            Verdict(
                ACTION_REFUSE,
                "LEDGER_CORRUPT",
                f"registre des mises a jour en vol corrompu : {exc} ; "
                "la garde UPDATE_IN_FLIGHT refuse plutot que d'improviser",
            ),
            updated=False,
        )
    except OSError as exc:
        return build_result(
            pr,
            pinned,
            Verdict(
                ACTION_REFUSE,
                "LEDGER_UNWRITABLE",
                f"reservation impossible ({exc}) : sans garde en vol, pas d'ecriture",
            ),
            updated=False,
        )
    if not reserved:
        return build_result(
            pr,
            pinned,
            Verdict(
                ACTION_SKIP,
                "UPDATE_IN_FLIGHT",
                "une mise a jour est deja reservee sur cette tete (registre sous "
                "verrou) : attendre son atterrissage",
            ),
            updated=False,
        )

    # Relecture des SHA epingles : la DERNIERE chose avant l'ecriture.
    try:
        drift = recheck_pinned_refs(repo, live, pinned)
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        return error_result(pr, exc, warnings=release_quietly(ledger_file, key, reservation))
    if drift is not None:
        return build_result(
            pr,
            pinned,
            drift,
            updated=False,
            warnings=release_quietly(ledger_file, key, reservation),
        )

    try:
        run_gh(["pr", "update-branch", str(pr), "--repo", repo])
    except (GhError, OSError) as exc:
        return build_result(
            pr,
            pinned,
            Verdict(ACTION_REFUSE, "UPDATE_FAILED", f"`gh pr update-branch` a echoue : {exc}"),
            updated=False,
            warnings=release_quietly(ledger_file, key, reservation),
        )

    # Succes : la reservation DEVIENT l'enregistrement en vol -- elle etait
    # deja en place avant l'appel, il n'y a rien a re-ecrire.
    return build_result(pr, pinned, verdict, updated=True)


# --------------------------------------------------------------------------
# Entree
# --------------------------------------------------------------------------


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--pr",
        type=int,
        action="append",
        required=True,
        help="numero de PR a considerer (repetable) -- jamais un pool",
    )
    parser.add_argument("--repo", default=DEFAULT_REPO, help="depot cible")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="appliquer les mises a jour (defaut : dry-run, aucune ecriture)",
    )
    parser.add_argument(
        "--max-updates",
        type=int,
        default=DEFAULT_MAX_UPDATES,
        help="plafond de mises a jour par appel "
        f"(defaut {DEFAULT_MAX_UPDATES} ; 0 = sans plafond)",
    )
    parser.add_argument(
        "--in-flight-ttl",
        type=int,
        default=DEFAULT_IN_FLIGHT_TTL,
        help=f"fenetre pendant laquelle une mise a jour estimee en vol bloque un 2e appel "
        f"(defaut {DEFAULT_IN_FLIGHT_TTL} s)",
    )
    parser.add_argument(
        "--state-dir",
        default=None,
        help="repertoire du registre des mises a jour en vol (defaut : temporaire)",
    )
    args = parser.parse_args(argv)
    # `--max-updates 0` desactive le plafond ; une valeur NEGATIVE n'a pas de
    # sens et se lirait comme « plafond depasse des le premier appel » -- un
    # refus silencieux de tout travail. De meme un TTL nul ou negatif rendrait
    # la garde UPDATE_IN_FLIGHT inoperante : on refuse les deux, bruyamment.
    if args.max_updates < 0:
        parser.error(f"--max-updates ne peut pas etre negatif (recu {args.max_updates})")
    if args.in_flight_ttl <= 0:
        parser.error(f"--in-flight-ttl doit etre > 0 (recu {args.in_flight_ttl})")
    return args


def dedupe(prs: list[int]) -> list[int]:
    """Conserve l'ordre, retire les doublons : une PR n'est jamais traitee 2 fois."""
    seen: set[int] = set()
    out: list[int] = []
    for pr in prs:
        if pr not in seen:
            seen.add(pr)
            out.append(pr)
    return out


def default_state_dir() -> Path:
    return Path(tempfile.gettempdir()) / "coursia-update-branch"


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    path = ledger_path(state_dir)

    now = time.time()
    applied = 0
    results: list[dict[str, Any]] = []
    for pr in dedupe(args.pr):
        # Plafond epuise : la decision est deja prise, donc on ne paie AUCUNE
        # lecture pour les PR restantes (voir `cap_reached_result`).
        if args.max_updates and applied >= args.max_updates:
            results.append(cap_reached_result(pr, args.max_updates))
            continue
        result = process_one(
            pr,
            repo=args.repo,
            apply=args.apply,
            ledger_file=path,
            key=ledger_key(args.repo, pr),
            now=now,
            in_flight_ttl=args.in_flight_ttl,
            applied=applied,
            max_updates=args.max_updates,
        )
        if result["updated"]:
            applied += 1
        results.append(result)

    payload = {
        "repo": args.repo,
        "mode": "apply" if args.apply else "dry-run",
        "max_updates": args.max_updates,
        "updates_applied": applied,
        "results": results,
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 1 if any(r["action"] == ACTION_REFUSE for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
