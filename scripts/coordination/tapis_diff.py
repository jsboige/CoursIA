#!/usr/bin/env python3
"""La PREUVE de livraison par le DIFF : un marqueur DESIGNE une PR a verifier.

Un marqueur de fil (`[DELIVERED] ... PR #N -- paths: ...`) n'est **pas** une
preuve de livraison : il **designe** la PR a verifier. La preuve, c'est le
**diff** de cette PR, demontre couvrant le **perimetre** declare par la clause
`paths:` (revue du 19/11, revue 5967171401).

Trois verdicts -- `couvre` (le diff couvre le perimetre, l'attribution est
connue et couverte, la PR est integree), `tranche` (diff partiel, ou
attribution inconnue ou globale) et `a_verifier` (preuve absente, perimetre
non declare, etat inconnu, PR fermee sans fusion). Les deux derniers
laissent l'issue **dans la rotation** : une tranche livree ne livre pas
l'issue.

**fail-CLOSED vers l'exclusion** : une preuve absente ne vaut jamais
exclusion ; elle vaut le maintien dans la rotation.

**Une livraison complete exige DEUX choses** (revue du 19/11, DM
`night-27242-unknown-scope-stays-in-rotation`) : un perimetre
**independant du marqueur de livraison** (l'attribution portee par
l'issue) et **l'etat de la PR**. Le diff seul n'atteste qu'une tranche ;
une PR **fermee sans fusion** n'atteste rien.

Le **perimetre** lui-meme -- ce qu'un glob certifie, la separation entre
visite, attribution et livraison complete -- vit dans
`coordination.tapis_perimetre` ; la **preuve** (le diff ET l'etat de la
PR) vit dans `coordination.tapis_preuve`. Les deux sont extraits de ce
module pour tenir le plafond de lignes (19/11).

Aucune lecture n'est reecrite : la clause `paths:`, la PR designee et le
matcher de chemins sont ceux de `scripts/check_lane_claim.py`, l'organe qui
fait autorite sur les claims.

Usage :
    python scripts/coordination/tapis_diff.py --marqueur "[DELIVERED] ..." \
        [--diff a.py,b.py] [--attribution c.py] [--etat OPEN]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_lane_claim
from coordination.tapis_marqueurs import evenements
from coordination.tapis_perimetre import attribution, couvert_par, couverture
from coordination.tapis_preuve import Preuve, comme_preuve, preuve_gh

#: Les trois verdicts de la preuve par le diff.
COUVRE = "couvre"
TRANCHE = "tranche"
A_VERIFIER = "a_verifier"

NOTE_INFO = ("[INFO] candidate-delivered : une route vers l'urne de cloture, "
             "pas une preuve -- c'est le diff de la PR qui decide")


def perimetre(ligne: str) -> list[str]:
    """La clause `paths:` du marqueur -- le perimetre DECLARE de la livraison."""
    return check_lane_claim._extract_paths_clause(ligne) or []


def pr_designee(ligne: str) -> int | None:
    """La PR designee par le marqueur (`[DELIVERED] ... PR #N`)."""
    return check_lane_claim._extract_delivered_pr_ref(ligne)


def verdict(ligne: str, preuve, attribution: list[str] | None = None) -> tuple[str, str]:
    """(verdict, detail) -- sans preuve, l'issue reste dans la rotation.

    `preuve` porte les fichiers modifies de la PR **et l'etat de la PR**
    (`Preuve`) ; une liste de fichiers seule est une preuve **incomplete**
    (etat inconnu), fail-CLOSED.

    `attribution` est le perimetre porte par l'issue : la livraison doit le
    couvrir. Inconnu (`None`) ou global (`[]`), le diff n'atteste qu'une
    **tranche** : l'issue reste dans la rotation.
    """
    pr = pr_designee(ligne)
    per = perimetre(ligne)
    if pr is None:
        return A_VERIFIER, "marqueur sans PR designee : rien a verifier"
    if not per:
        return A_VERIFIER, f"PR #{pr} : perimetre non declare (pas de clause `paths:`)"
    if preuve is None:
        return A_VERIFIER, f"PR #{pr} : diff absent ou illisible"
    p = comme_preuve(preuve)
    if not p.etat_known:
        return A_VERIFIER, (f"PR #{pr} : etat de la PR inconnu -- une preuve sans "
                            "etat ne certifie pas l'integration, l'issue reste "
                            "dans la rotation")
    if not p.integree:
        return A_VERIFIER, (f"PR #{pr} : fermee sans fusion -- la livraison n'a pas "
                            "eu lieu, l'issue reste dans la rotation")
    couverts, partiels, manquants = couverture(list(p.fichiers), per)
    if manquants:
        return TRANCHE, f"PR #{pr} : diff partiel -- manque {', '.join(manquants)}"
    if partiels:
        return TRANCHE, (f"PR #{pr} : perimetre declare en glob ({', '.join(partiels)}) "
                        "-- un glob ne certifie pas la completude : la preuve reste "
                        "une preuve de tranche, l'issue reste dans la rotation")
    if attribution is None:
        return TRANCHE, (f"PR #{pr} : attribution inconnue (l'issue ne porte aucun "
                         "marqueur d'attribution) -- le diff atteste une tranche, "
                         "pas une livraison complete : l'issue reste dans la rotation")
    if not attribution:
        return TRANCHE, (f"PR #{pr} : attribution globale (marqueur sans clause "
                         "`paths:`) -- le diff atteste une tranche, l'issue reste "
                         "dans la rotation")
    etroits = [a for a in attribution if not couvert_par(a, per)]
    if etroits:
        return TRANCHE, (f"PR #{pr} : livraison complete mais perimetre plus etroit "
                         f"que l'issue -- manque {', '.join(etroits)}")
    return COUVRE, f"PR #{pr} : le diff couvre le perimetre ({len(couverts)})"


def _dernier_delivered(evts) -> object | None:
    livres = [e for e in evts if e.marque == "DELIVERED"]
    return livres[-1] if livres else None


def decider(e, comments: list[dict], code: str | None, preuve) -> str | None:
    """L'ecart LIVREE, decide par le DIFF de la PR designee.

    Le code d'un autre ecart (GEL, RECLAMEE...) n'est pas touche : seul
    LIVREE releve de la preuve. Un marqueur de livraison **designe** une PR ;
    l'ecart n'est pose que si le diff couvre le perimetre declare, et il est
    retire sinon -- l'issue reste alors dans la rotation.
    """
    if code not in (None, "LIVREE"):
        return code
    evts = evenements(comments)
    ev = _dernier_delivered(evts)
    if ev is None:
        if code == "LIVREE":
            e.ecart, e.motif = None, ""
            e.notes.append(NOTE_INFO)
        return None
    ligne = f"[{ev.marque}] {ev.reste}"
    num, per = pr_designee(ligne), perimetre(ligne)
    if not per:
        if code == "LIVREE":
            e.ecart, e.motif = None, ""
            e.notes.append(f"PR #{num} : perimetre non declare -- "
                           "l'issue reste dans la rotation")
        return None
    etat, detail = verdict(ligne, preuve(num) if num else None, attribution(evts))
    if etat == COUVRE:
        e.motif = detail
        return "LIVREE"
    if code == "LIVREE":
        e.ecart, e.motif = None, ""
    e.notes.append(f"{detail} -- l'issue reste dans la rotation")
    return None


def appliquer(etats, lec, preuve) -> None:
    """Applique la preuve par le diff aux etats d'une tranche.

    `lec` porte les issues lues (fenetre) ; `preuve` est l'appelable qui rend
    les fichiers modifies d'une PR, ou None si la lecture echoue. Sans
    `preuve`, rien n'est change : le classement reste sur le marqueur.
    """
    if preuve is None:
        return
    issues = {it["number"]: it for it in lec.issues}
    for e in etats:
        it = issues.get(e.numero) or {}
        e.ecart = decider(e, it.get("comments") or [], e.ecart, preuve)


def main(argv: list[str] | None = None) -> int:
    """Verifie un marqueur contre un diff : la preuve, en ligne de commande."""
    p = argparse.ArgumentParser(description="Verifie la couverture du diff d'une PR.")
    p.add_argument("--marqueur", required=True, help="la ligne du marqueur")
    p.add_argument("--diff", default="", help="fichiers modifies, separes par des virgules")
    p.add_argument("--attribution", default="",
                   help="perimetre attribue a l'issue (marqueurs d'attribution), "
                        "separe par des virgules")
    p.add_argument("--etat", default="", choices=("", "OPEN", "CLOSED", "MERGED"),
                   help="etat de la PR ; vide = inconnu (preuve incomplete)")
    p.add_argument("--fusionne", action="store_true",
                   help="la PR a ete fusionnee")
    args = p.parse_args(argv)
    diff = [f for f in args.diff.split(",") if f]
    attr = [f.strip() for f in args.attribution.split(",") if f.strip()] or None
    preuve = Preuve(tuple(diff), args.etat, args.fusionne) if diff else None
    code, detail = verdict(args.marqueur, preuve, attr)
    print(f"{code} : {detail}")
    return 0 if code == COUVRE else 1


if __name__ == "__main__":
    sys.exit(main())
