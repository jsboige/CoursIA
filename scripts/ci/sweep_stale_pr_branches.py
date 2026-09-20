#!/usr/bin/env python3
"""Pilote de balayage : trouve les PRs en retard sur leur base, delegue la mise a jour.

Pourquoi ce pilote existe (#16915)
----------------------------------
Mandat user du 2026-09-19 : « j'ai l'impression que le CI n'aide pas avec des
MAJ de rebase successives qui sont mandatees et coutent enormement de temps a
tout le monde : il faut qu'elles soient automatiques pour la plupart ».

L'organe `scripts/ci/update_stale_pr_branches.py` sait mettre a jour une PR
NOMMEE (`--pr`, repetable) sous neuf gardes eprouvees (TOCTOU par SHA pinne,
registre en vol sous verrou, plafond, jamais de force-push, jamais `--rebase`)
-- mais il est invoque par RIEN et n'a pas de mode decouverte : `--pr` est un
argument requis, par contrat (« Jamais un pool : l'organe n'enumere rien »).

Ce pilote est la piece manquante, et elle ne fait QUE ca :

  1. ENUMERE les PRs ouvertes (un appel REST pagine, champs legers) ;
  2. PREFILTRE par metadonnees peu couteuses (brouillon, fork, non
     mergeable) -- une selection, pas une decision ;
  3. MESURE le retard des survivantes (meme lecture `behind_by` de
     l'API de comparaison que l'organe) ;
  4. DELEEGUE les candidates a l'organe par sous-processus, `--pr` par
     `--pr`, et relaie sa sortie JSON telle quelle.

Le pilote n'ecrit JAMAIS. Il ne fusionne rien, ne pousse rien, n'appelle pas
git. Seul l'organe ecrit, et seulement sous ses propres gardes.

Ce que le pilote n'est PAS
--------------------------
- Il n'est pas un decisionnaire : sa mesure de retard est une HEURISTIQUE DE
  SELECTION. L'organe re-epingle les SHA et re-mesure lui-meme avant toute
  ecriture (gardes TOCTOU de la review 5240194972) : le pilote n'est jamais
  cru pour la decision d'ecriture, et n'a pas besoin de l'etre.
- Il ne reimplemente aucune garde : conflit, base empilee, registre en vol,
  plafond, tout vit dans l'organe. Une garde dupliquee ici deriverait en
  silence (la lecon de la copie `is_advisory` de pr-gate-stale-sweep.yml,
  verrouillee par test AST -- ici il n'y a PAS de copie du tout).
- Il ne survend pas son gisement : mesure du 2026-09-19 sur 213 PRs ouvertes,
  ~12 DIRTY mises a part, la population reellement rattrapable est celle des
  CLEAN/BLOCKED/UNSTABLE portant un `behind_by > 0`. La valeur n'est pas le
  nombre de PRs debloquees, c'est la SUPPRESSION des allers-retours : un
  commentaire, une session de worker dediee et un dossier exact-head remplaces
  par un run.

Selection : les plus anciennes d'abord
--------------------------------------
REST `/pulls` rend les PRs par creation decroissante (plus recentes en tete),
et le pilote passe a l'organe AU PLUS `--max-updates` candidates. Servir les
plus recentes d'abord serait a l'envers : une PR jeune emet encore des
evenements `synchronize` et possede d'autres voies de rattrapage, une PR
quiete et agée n'en a aucune -- c'est exactement la lecon mesuree de
pr-gate-stale-sweep.yml (run 33169455408 : cap 8 servi aux 8 plus recentes,
les 5 agées restées BLOCKED 4 a 7 h). Les candidates sont donc triees par
numero croissant avant decoupe.

Plancher DWELL : le contrat que ce balayage presuppose
------------------------------------------------------
Un `update-branch` reecrit la tete ; avant #16149 il re-armait les 120 min de
plancher que le geste sert a franchir. `scripts/ci/merge_dwell.py` mesure
desormais sur `last_authoritative_committed_at`, qui EXEMPTE les fusions de
rafraichissement de base PROUVEES content-free (deux parents, second ancetre
de la base, arbre identique a l'auto-merge). Le pilote presuppose ce contrat
et le VERROUILLE par un test de non-regression dans SA suite
(test_update_branch_shape_does_not_rearm_dwell) : si merge_dwell regresse,
la suite du pilote rougit en meme temps que celle du gate -- le balayage
automatique ne peut pas reintroduire silencieusement la taxe de 2 h.

Sortie JSON, toujours (les deux modes) : population enumeree, exclusions
nommees, candidates mesurees, et la charge de l'organe relayee INTEGRALEMENT
(chaque resultat porte action, base_kind, freshness, invalidated -- cf
l'acceptance #16915).

Codes de sortie :
  0 -- balayage sain (candidates ou non ; mises a jour appliquees et/ou
        SKIP benins de l'organe) ;
  1 -- l'organe a rendu au moins un REFUSE (conflit, tete/base qui a bouge,
        echec d'appel) : un humain doit regarder -- relaye tel quel, jamais
        etoufe ;
  2 -- erreur d'appelant ou d'enumeration (arguments, listing illisible).
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

# L'organe vit dans le meme repertoire : import direct, aucune copie. En
# execution script, `scripts/ci` n'est pas sur sys.path sinon.
_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from update_stale_pr_branches import (  # noqa: E402
    DEFAULT_MAX_UPDATES,
    DEFAULT_REPO,
    base_kind,
    read_behind,
    read_branch_sha,
    run_gh,
)

#: Chemin de l'organe delegue, unique invocable d'ecriture.
ORGAN_PATH = _HERE / "update_stale_pr_branches.py"

#: Champs d'enumeration (GraphQL via `gh pr list --json`). Mesure du
#: 2026-09-20 : l'API REST `/pulls` rend `mergeable: null` sur 211 des 214
#: PRs ouvertes (calcul paresseux non rafraichi a l'echelle du pool), tandis
#: que GraphQL calcule a la lecture et rend MERGEABLE/CONFLICTING/UNKNOWN --
#: enumerer par REST rendait le prefiltre structurellement inert (0 candidate
#: sur un pool porteuses). `mergeable: UNKNOWN` (calcul en cours) est EXCLU
#: nomme, jamais devine : il revient au balayage suivant, exactement comme le
#: SKIP nomme de l'organe.
LIST_FIELDS = (
    "number,isDraft,isCrossRepository,baseRefName,headRefOid,mergeable,url"
)

#: Population ouverte mesuree le 2026-09-19 : 213 PRs. La borne d'enumeration
#: garde une marge ; au-dela, la queue (les plus ANCIENNES, dernieres dans
#: l'ordre de `gh pr list`, plus recentes en tete) attend le balayage
#: suivant -- dit, jamais cache.
DEFAULT_LIST_LIMIT = 400


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", default=DEFAULT_REPO, help="depot cible")
    parser.add_argument(
        "--list-limit",
        type=int,
        default=DEFAULT_LIST_LIMIT,
        help=f"borne de lignes enumerees (defaut {DEFAULT_LIST_LIMIT} ; "
        "au-dela, la queue attend le balayage suivant)",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="transmettre --apply a l'organe (defaut : dry-run, aucune "
        "ecriture -- ni chez le pilote, ni chez l'organe)",
    )
    parser.add_argument(
        "--max-updates",
        type=int,
        default=DEFAULT_MAX_UPDATES,
        help="plafond de mises a jour par balayage, transmis a l'organe ET "
        "borne la selection (defaut 3 ; 0 = sans plafond -- deconseille : "
        "chaque mise a jour perime un dossier exact-head)",
    )
    parser.add_argument(
        "--state-dir",
        default=None,
        help="repertoire du registre en vol de l'organe (transmis tel quel)",
    )
    args = parser.parse_args(argv)
    if args.list_limit <= 0:
        parser.error(f"--list-limit doit etre > 0 (recu {args.list_limit})")
    if args.max_updates < 0:
        parser.error(f"--max-updates ne peut pas etre negatif (recu {args.max_updates})")
    return args


def list_open_prs(repo: str, limit: int) -> list[dict[str, Any]]:
    """Enumere les PRs ouvertes en champs legers, plus recentes en tete.

    Une ligne mal formee est ecartee silencieusement mais COMPTEE par
    l'ecart enumere/lu ; un echec de l'appel lui-meme remonte en GhError
    (exit 2). Les noms internes (draft/fork/base/head) sont normalises ici,
    une seule fois.
    """
    raw = run_gh(
        [
            "pr",
            "list",
            "--repo",
            repo,
            "--state",
            "open",
            "--limit",
            str(limit),
            "--json",
            LIST_FIELDS,
        ]
    )
    data = json.loads(raw)
    if not isinstance(data, list):
        raise RuntimeError("`gh pr list --json` n'a pas rendu une liste")
    rows: list[dict[str, Any]] = []
    for item in data:
        if not isinstance(item, dict) or not isinstance(item.get("number"), int):
            continue
        rows.append(
            {
                "number": item["number"],
                "draft": bool(item.get("isDraft")),
                "fork": bool(item.get("isCrossRepository")),
                "base": item.get("baseRefName"),
                "head_ref": item.get("headRefOid"),
                "head": item.get("headRefOid"),
                "mergeable": item.get("mergeable"),
                "url": item.get("url"),
            }
        )
    return rows


def metadata_exclusion(row: dict[str, Any]) -> str | None:
    """Raison d'exclusion peu couteuse, ou None si la ligne passe.

    Brouillon, fork et non-mergeable se lisent DEJA dans la ligne
    d'enumeration GraphQL (calcul de mergeabilite frais a la lecture) : les
    ecarter ici evite de payer, pour chaque desesperee, un appel de ref et un
    appel de comparaison que l'organe rendrait de toute facon en
    REFUSE/SKIP. Ce n'est qu'une selection -- l'organe re-verifie chaque
    garde sur ses propres lectures avant d'ecrire.
    """
    if row.get("draft"):
        return "draft"
    if row.get("fork"):
        return "fork"
    if row.get("mergeable") != "MERGEABLE":
        # CONFLICTING (conflit reel) ou UNKNOWN (calcul en cours) : exclu
        # maintenant, re-mesure au balayage suivant.
        return "not_mergeable"
    return None


def measure_behind(repo: str, row: dict[str, Any]) -> int | None:
    """Retard de la PR contre sa base DECLAREE, ou None si illisible.

    Reutilise les lecteurs de l'organe (aucune reimplementation). Par NOM pour
    la base : c'est une lecture de SELECTION, pas une decision -- une base
    empilee qui avance entre ici et l'invocation de l'organe est re-epinnee
    par l'organe lui-meme (review 5240194972, finding 1).
    """
    base_ref = row.get("base")
    head_sha = row.get("head")
    if not base_ref or not head_sha:
        return None
    try:
        base_sha = read_branch_sha(repo, base_ref)
        behind = read_behind(repo, base_sha, head_sha)
    except (RuntimeError, ValueError, OSError, UnicodeError):
        # GhError derive de RuntimeError : retard inconnu, fail-closed -- la
        # ligne revient au balayage suivant, jamais devinee.
        return None
    return behind if isinstance(behind, int) else None


def run_organ(
    repo: str,
    prs: list[int],
    *,
    apply: bool,
    max_updates: int,
    state_dir: str | None,
) -> tuple[int, dict[str, Any] | None, str]:
    """Invoque l'organe en sous-processus et relaie (exit, JSON, stdout brut).

    Couture unique des tests : ils remplacent ce nom, jamais subprocess.
    """
    argv = [sys.executable, str(ORGAN_PATH)]
    for pr in prs:
        argv += ["--pr", str(pr)]
    argv += ["--repo", repo]
    if apply:
        argv += ["--apply"]
    argv += ["--max-updates", str(max_updates)]
    if state_dir:
        argv += ["--state-dir", state_dir]
    proc = subprocess.run(
        argv, capture_output=True, text=True, encoding="utf-8", errors="replace"
    )
    payload: dict[str, Any] | None = None
    try:
        parsed = json.loads(proc.stdout)
        if isinstance(parsed, dict):
            payload = parsed
    except ValueError:
        payload = None
    return proc.returncode, payload, proc.stdout


def _pilot_row(
    row: dict[str, Any], behind: int | None, *, selected: bool, deferred: bool
) -> dict[str, Any]:
    """Ligne de resultat pilote, meme contrat de champs que l'organe.

    `action`/`base_kind` toujours presents ; `freshness`/`invalidated` nuls --
    le pilote n'ecrit rien, donc ne perime rien : seules les lignes de
    l'organe (relayees integralement) portent `freshness: STALE`.
    """
    pr = row.get("number")
    return {
        "pr": pr,
        "action": "SELECTED" if selected else ("DEFERRED" if deferred else "NOT_SELECTED"),
        "code": "",
        "reason": (
            "candidate passe a l'organe (decision finale = l'organe)"
            if selected
            else "candidate au-dela du plafond : au prochain balayage"
            if deferred
            else "retard nul ou illisible : rien a deleguer"
        ),
        "base": row.get("base"),
        "base_kind": base_kind(row.get("base")),
        "behind_by": behind,
        "url": row.get("url"),
        "updated": False,
        "freshness": None,
        "invalidated": [],
    }


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    try:
        rows = list_open_prs(args.repo, args.list_limit)
    except RuntimeError as exc:
        print(
            json.dumps(
                {
                    "repo": args.repo,
                    "mode": "apply" if args.apply else "dry-run",
                    "error": f"enumeration illisible : {exc}",
                },
                indent=2,
                ensure_ascii=False,
            )
        )
        return 2

    excluded = {"draft": 0, "fork": 0, "not_mergeable": 0}
    measured: list[tuple[dict[str, Any], int | None]] = []
    up_to_date = 0
    behind_unknown = 0
    for row in rows:
        reason = metadata_exclusion(row)
        if reason:
            excluded[reason] += 1
            continue
        behind = measure_behind(args.repo, row)
        if behind is None:
            behind_unknown += 1
            measured.append((row, None))
        elif behind > 0:
            measured.append((row, behind))
        else:
            up_to_date += 1
            measured.append((row, 0))

    candidates = sorted(
        ((row, b) for row, b in measured if (b or 0) > 0), key=lambda rb: rb[0]["number"]
    )
    cap = args.max_updates if args.max_updates > 0 else len(candidates)
    selected = candidates[:cap]
    deferred = candidates[cap:]

    organ_exit: int | None = None
    organ_payload: dict[str, Any] | None = None
    organ_stdout = ""
    if selected:
        organ_exit, organ_payload, organ_stdout = run_organ(
            args.repo,
            [row["number"] for row, _ in selected],
            apply=args.apply,
            max_updates=args.max_updates,
            state_dir=args.state_dir,
        )

    organ_results = (organ_payload or {}).get("results") or []
    pilot_results = [
        _pilot_row(row, b, selected=False, deferred=False)
        for row, b in measured
        if (b or 0) <= 0
    ] + [
        _pilot_row(row, b, selected=False, deferred=True) for row, b in deferred
    ]

    payload = {
        "repo": args.repo,
        "mode": "apply" if args.apply else "dry-run",
        "max_updates": args.max_updates,
        "list_limit": args.list_limit,
        "enumerated": len(rows),
        "excluded": {**excluded, "up_to_date": up_to_date, "behind_unknown": behind_unknown},
        "candidates": len(candidates),
        "selected": [row["number"] for row, _ in selected],
        "deferred": [row["number"] for row, _ in deferred],
        "organ_invoked": bool(selected),
        "organ_exit": organ_exit,
        "organ": organ_payload,
        "results": list(organ_results) + pilot_results,
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    if organ_exit is not None and organ_stdout and organ_payload is None:
        # L'organe a parle mais pas en JSON : le dire plutot que maquiller un
        # relais vide en balayage sain.
        print("[sweep] sortie organe non-JSON (extrait) :", organ_stdout[:400], file=sys.stderr)
    if organ_exit is None:
        return 0
    return organ_exit


if __name__ == "__main__":
    sys.exit(main())
