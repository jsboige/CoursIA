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
  4. base ET tete inchangees depuis la mesure -- relecture apres la mesure et
     avant l'appel d'ecriture. La fenetre n'est pas nulle : l'appel de
     comparaison du deficit s'intercale entre la relecture et l'ecriture, et
     c'est elle qui reste ouverte. Une tete qui bouge sous nos pieds est un
     REFUSE, pas un « on reessaie » ;
  5. `mergeable != CONFLICTING` -- un conflit n'a jamais de repli ici ;
  6. `mergeable == MERGEABLE`   -- `UNKNOWN` est un SKIP nomme, reessayable ;
  7. deficit de commits REEL `behind_by > 0` mesure par l'API de comparaison --
     voir la section suivante, c'est le point le plus fragile de tout l'organe ;
  8. aucune mise a jour deja en vol pour cette PR (registre local, voir plus bas) ;
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
defaut sous le repertoire temporaire, reglable par `--state-dir`) : a chaque
application reussie il enregistre `{previous_head, started_at}`. Une PR dont la
tete est encore celle enregistree et dont l'enregistrement est plus jeune que
`--in-flight-ttl` (defaut 900 s) sort en SKIP `UPDATE_IN_FLIGHT` -- un second
appel pendant qu'une mise a jour est en vol rendrait un echec opaque. Un
enregistrement perime, ou dont la tete a change (donc la mise a jour a atterri),
est ignore. L'ecriture du registre est atomique (tmp + replace).

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
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

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


def base_kind(base: str | None) -> str:
    """`main` pour la base d'integration, `stacked` pour toute autre base."""
    return "main" if (base or "") in MAIN_BRANCHES else "stacked"


def read_behind(repo: str, base: str, head: str) -> int:
    """Nombre de commits de `base` absents de `head` -- le retard exact.

    Mesure contre la base DECLAREE (`baseRefName`), donc le cas d'une PR
    empilee est couvert sans branche de code dediee. C'est la seule lecture de
    retard de l'organe : `mergeStateStatus` ne rapporte pas `BEHIND` sur ce
    depot (mesure du module).
    """
    raw = run_gh(["api", f"repos/{repo}/compare/{base}...{head}"])
    data = json.loads(raw)
    if not isinstance(data, dict) or not isinstance(data.get("behind_by"), int):
        raise GhError(f"compare {base}...{head} did not return an integer behind_by")
    return data["behind_by"]


def attach_behind(snapshot: dict[str, Any], repo: str) -> dict[str, Any]:
    """Ajoute le retard exact a une mesure de PR (appel de comparaison).

    Appele SEULEMENT apres les gardes de metadonnees : une PR fermee, un fork,
    un brouillon ou un conflit se decide sans savoir de combien de commits la
    branche est en retard, et l'appel n'est pas gratuit.

    Le retard est rendu `None` (avec `behind_error`) quand l'API ne repond pas :
    c'est une donnee manquante NOMMEE, que `classify` traite en SKIP fail-closed
    -- jamais en « probablement en retard ».
    """
    base = snapshot.get("baseRefName")
    head = snapshot.get("headRefOid")
    try:
        snapshot["behind_by"] = read_behind(repo, base, head) if base and head else None
        snapshot["behind_error"] = None
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        snapshot["behind_by"] = None
        snapshot["behind_error"] = f"{type(exc).__name__}: {exc}"
    return snapshot


# --------------------------------------------------------------------------
# Registre des mises a jour en vol
# --------------------------------------------------------------------------


def ledger_path(state_dir: Path) -> Path:
    return Path(state_dir) / "in-flight.json"


def read_ledger(path: Path) -> dict[str, dict[str, Any]]:
    """Registre absent, illisible ou malforme = registre vide, jamais une erreur."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError, UnicodeError):
        return {}
    return data if isinstance(data, dict) else {}


def write_ledger(path: Path, data: dict[str, dict[str, Any]]) -> None:
    """Ecriture atomique : un lecteur concurrent voit l'ancien ou le nouveau."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(
        json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    tmp.replace(path)


def ledger_key(repo: str, pr: int) -> str:
    return f"{repo}#{pr}"


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
    return None


def classify(
    snapshot: dict[str, Any],
    *,
    measured: dict[str, Any] | None,
    ledger: dict[str, dict[str, Any]],
    key: str,
    now: float,
    in_flight_ttl: int,
    applied: int,
    max_updates: int,
) -> Verdict:
    """Rend la decision COMPLETE pour une mesure de PR. Fonction pure.

    Enchaine les gardes de metadonnees (`classify_metadata`) puis celles qui
    supposent la mesure du retard : le deficit lui-meme, le registre des mises
    a jour en vol, et le plafond.
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

    record = ledger.get(key)
    if isinstance(record, dict):
        try:
            started_at = float(record.get("started_at", 0))
        except (TypeError, ValueError):
            started_at = 0.0
        in_window = now - started_at < in_flight_ttl
        same_head = record.get("previous_head") == snapshot.get("headRefOid")
        if in_window and same_head:
            return Verdict(
                ACTION_SKIP,
                "UPDATE_IN_FLIGHT",
                "une mise a jour recente est enregistree sur cette tete : "
                "attendre son atterrissage",
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


def error_result(pr: int, exc: BaseException) -> dict[str, Any]:
    return {
        **blank_result(pr),
        "action": ACTION_REFUSE,
        "code": "ERROR",
        "reason": f"{type(exc).__name__}: {exc}",
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


def process_one(
    pr: int,
    *,
    repo: str,
    apply: bool,
    ledger: dict[str, dict[str, Any]],
    ledger_file: Path,
    key: str,
    now: float,
    in_flight_ttl: int,
    applied: int,
    max_updates: int,
) -> dict[str, Any]:
    """Mesure, re-mesure, puis applique si -- et seulement si -- tout tient.

    L'ordre des lectures est un choix de cout : les gardes de metadonnees
    tranchent d'abord (un appel), la relecture TOCTOU vient ensuite, et le
    deficit de commits -- le seul appel de comparaison -- n'est paye que par
    les PR qui ont deja passe tout le reste.
    """
    try:
        measured = read_pr(pr, repo)
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        return error_result(pr, exc)

    early = classify_metadata(measured, measured=None)
    if early is not None:
        return build_result(pr, measured, early, updated=False)

    # Garde TOCTOU : la base et la tete doivent etre celles qu'on vient de
    # mesurer. Un update-branch lance sur une tete qui a bouge reecrit une
    # branche que quelqu'un d'autre vient de pousser.
    try:
        live = read_pr(pr, repo)
    except (GhError, ValueError, OSError, UnicodeError) as exc:
        return error_result(pr, exc)

    early = classify_metadata(live, measured=measured)
    if early is not None:
        return build_result(pr, live, early, updated=False)

    verdict = classify(
        attach_behind(live, repo),
        measured=measured,
        ledger=ledger,
        key=key,
        now=now,
        in_flight_ttl=in_flight_ttl,
        applied=applied,
        max_updates=max_updates,
    )
    if verdict.action != ACTION_UPDATE:
        return build_result(pr, live, verdict, updated=False)

    if not apply:
        return build_result(pr, live, verdict, updated=False)

    try:
        run_gh(["pr", "update-branch", str(pr), "--repo", repo])
    except (GhError, OSError) as exc:
        return build_result(
            pr,
            live,
            Verdict(ACTION_REFUSE, "UPDATE_FAILED", f"`gh pr update-branch` a echoue : {exc}"),
            updated=False,
        )

    # Le registre est ecrit APRES le succes : c'est un enregistrement de ce qui a
    # eu lieu, jamais une reservation. Un echec d'ecriture degrade la garde
    # UPDATE_IN_FLIGHT -- il est signale, il n'annule pas la mise a jour.
    warnings: list[str] = []
    try:
        ledger[key] = {"previous_head": live.get("headRefOid"), "started_at": now}
        write_ledger(ledger_file, ledger)
    except (OSError, TypeError, ValueError) as exc:
        warnings.append(f"registre non ecrit ({exc}) : la garde UPDATE_IN_FLIGHT est degradee")

    return build_result(pr, live, verdict, updated=True, warnings=warnings)


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
    ledger = read_ledger(path)

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
            ledger=ledger,
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
