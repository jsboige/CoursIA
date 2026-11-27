#!/usr/bin/env python3
"""La voie LEGERE du tirage : la rotation universelle, seule.

Ce module est la **bascule** du tirage par defaut (#27225, suite de #27223) : le
tirage separe deux temps qui etaient confondus :

- la **rotation universelle** (`coordination.tapis_universel`) classe TOUTES
  les issues ouvertes sur leurs **metadonnees seules** et tourne la tete de
  niveau. Elle n'ecarte rien : chaque classe a son creneau de lecture
  (19/11), et chaque grain servi porte son **etat** et l'**action** ;
- la **qualification** (`coordination.tapis_qualification`) ne porte que sur
  le grain pris en charge : son corps, son **fil complet**, et la re-decision
  des neuf regles d'ecart, AVANT l'action.

Les neuf regles ne sont pas decidables sur des metadonnees : les decider pour
TOUT le pool coutait 22 s ; sur la **fenetre servie**, 1 a 2 appels par grain.

**La qualification precede le service** (dispatch `c0030` du coordinateur,
24/11) : la lane ne recoit que des grains **confirmes** sur leur FIL COMPLET.
La fenetre servie, sa qualification et le rapport vivent dans
`coordination.tapis_leger_fenetre` (extraction, comme `tapis_leger_texte`).

Mesures (pool de 441 issues, 18/11) : le **leger** rend 24 grains en
**17,9 s** ; le **lourd** (corps + 12 commentaires) en rend 11 en 33,5 s.

Le **mur global** (`--budget-s`, 60 s) leve `LectureIncomplete` (code 3) au depassement -- jamais une liste a moitie.
"""
from __future__ import annotations

import time
from datetime import UTC, datetime
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection, tapis_borne, tapis_equilibre
from coordination import (tapis_age, tapis_ancre, tapis_labels, tapis_origami,
                          tapis_public, tapis_rapide, tapis_repli,
                          tapis_rotation)
from coordination import tapis_leger_fenetre as lq
from coordination import tapis_service, tapis_universel
# L'import de l'occupation est sur **sa propre ligne** : la PR d'age (#28022)
# modifie la ligne d'import voisine, et deux ancres distinctes fusionnent sans
# conflit (les deux PRs restent donc mergeables dans n'importe quel ordre).
from coordination import tapis_occupation
from coordination import tapis_leger_rapport
from coordination.tapis_marqueurs import _iso, lane_de_pr

#: Re-export du RAPPORT : l'appelant de `main` (`scripts/coordination/
#: tapis_repli.py`) appelle `tapis_leger._rapport(...)`, et l'extraction du
#: 22/11 l'avait retire du module -- l'appelant echouait alors sur l'arbre
#: fusionne (`AttributeError: module 'coordination.tapis_leger' has no
#: attribute '_rapport'`, run 45326540394). Le symbole reste donc resolvable
#: par le module, et l'appel interne passe par le meme point de resolution.
_rapport = tapis_leger_rapport.rapport

#: Le classement propose ce multiple de grains : la qualification ecarte
#: quelques-uns au moment de l'action, et la file doit rester pleine.
CANDIDATS_MULT = 3


def _ordre(etats_: list, lane: str, maintenant: datetime,
          graine: str) -> tuple[list, list]:
    """L'ordre de TOUTES les issues ouvertes : les grains d'abord, les
    conteneurs ensuite (un conteneur ne passe jamais devant un grain).

    L'ordre est **fair** (`rotation=False`) : le decalage de tete par lane
    est applique a la FENETRE, pas au pool -- sinon la fenetre ne peut pas
    etre un bloc contigu du pool classe (`tapis_rotation.bloc`).
    """
    grains_ = [e for e in etats_ if not e.conteneur]
    conteneurs = [e for e in etats_ if e.conteneur]
    return (tapis_universel.rotation_universelle(
                grains_, lane, maintenant, len(grains_), graine, rotation=False),
            tapis_universel.rotation_universelle(
                conteneurs, lane, maintenant, len(conteneurs), graine,
                rotation=False))

def classer(lane: str, maintenant: datetime, jours: int, graine: str, depot,
            run=gh_bulk.run_defaut,
            budget_s: float = gh_selection.MUR_GLOBAL_S,
            echeance: float | None = None) -> dict:
    """Le POOL classe : l'ordre fair des grains, et les conteneurs.

    C'est la lecture de metadonnees du tirage leger, SANS la fenetre : la
    prise en charge s'en sert pour les VAGUES (ouvrir la vague suivante
    quand la fenetre ne donne aucun grain servable).
    """
    debut = time.monotonic()
    # UNE echeance monotone pour les trois etages (#28114, I6) : le temps
    # restant borne chaque appel, donc l'etage suivant est COUPE, pas attendu.
    echeance = echeance if echeance is not None else debut + gh_bulk.MUR_TIRAGE_S
    metas, duree = gh_selection.lire_metadonnees_issues(run, budget_s=budget_s,
                                                         echeance=echeance)
    t1 = time.monotonic()
    citations = gh_bulk.lire_citations_mergees(depot, jours, run, echeance=echeance)
    t2 = time.monotonic()
    prs = gh_bulk.lire_prs_ouvertes(run, echeance=echeance)
    t3 = time.monotonic()
    etats_ = tapis_universel.etats_leger(metas, citations, maintenant)
    # L'OCCUPATION se decide sur les metadonnees seules (labels + PRs
    # ouvertes) : l'urne de cloture et la PR qui tient l'issue sortent de la
    # tete -- avant la rotation, sans un appel reseau de plus. Les exclus
    # sont affiches (jamais de grain perdu en silence).
    occupation = tapis_occupation.marques(metas, prs, lane)
    grains_, conteneurs = _ordre(etats_, lane, maintenant, graine)
    grains_, conteneurs, exclus = tapis_occupation.retirer(
        grains_, conteneurs, occupation, lane)
    # Les lanes qui **gerent** l'urne ne perdent aucun grain : elles n'ont
    # donc aucune exclusion a afficher. Elles recoivent une section
    # **courte** : ce qui est a l'urne, ce qui est occupe -- l'information
    # qui leur manque pour arbitrer.
    resume = (tapis_occupation.resume(occupation)
              if tapis_occupation.privilege(lane) else [])
    return {"metas": metas, "citations": citations, "prs": prs, "etats": etats_,
            "grains": grains_, "conteneurs": conteneurs,
            "occupation": {"marques": occupation, "exclus": exclus,
                           "resume": resume},
            "phases": {"selection_s": duree, "citations_s": round(t2 - t1, 1),
                       "prs_s": round(t3 - t2, 1)},
            "secondes": round(time.monotonic() - debut, 1)}


def tirage(lane: str, grains: int, maintenant: datetime, jours: int, graine: str,
           depot, run=gh_bulk.run_defaut,
           budget_s: float = gh_selection.MUR_GLOBAL_S,
           echeance: float | None = None) -> tuple[dict, int]:
    """Le tirage leger complet : le rapport et le code de sortie.

    Sortie 3 : la lecture de selection est incomplete (rien n'est servi) --
    jamais une liste a moitie. Une lecture incomplete du POOL n'est pas
    equivalente : la selection paginee est complete ou elle echoue.

    I2 (#28114) : le REPLI CHRONOLOGIQUE (`tapis_repli`) rend la main -- hors
    reseau, ou quand les filtres vident la file. Le cache local fait foi, et
    le pool est servi dans l'ordre de creation.
    """
    debut = time.monotonic()
    # UNE echeance monotone pour TOUTE la commande (I6 de #28114) : la
    # selection, la qualification et le repli se partagent le MEME budget.
    # Avant, chaque etage repartait d'une horloge neuve (60 s la selection,
    # 60 s la qualification) : une selection de 25 s suivie de 40 s de
    # qualification depassait le contrat de la commande entiere.
    # Le tirage garde SON budget, plafonne par l'echeance de la commande.
    echeance = (tapis_borne.part(echeance, budget_s) if echeance is not None
                else debut + budget_s)
    try:
        classe = classer(lane, maintenant, jours, graine, depot, run, budget_s,
                          echeance=echeance)
    except gh_bulk.LectureIncomplete:
        return tapis_repli.replir(lane, grains, maintenant, jours, graine,
                                   depot, echeance=echeance)
    ancres = tapis_ancre.lire(lane)
    # SELECTION PAR AGE (mandat du 22/11) : les issues ANCIENNES d'abord ; les
    # CONTENEURS passent avec : leurs racines labellisees `consolidation`.
    ages, exclus, reinit = tapis_age.tour(classe["grains"], ancres, maintenant,
                                          classe["conteneurs"])
    # Le LOT PUBLIC est le chemin public isole (`tapis_public.lot_public`) :
    # les TESTS le portent tel quel, et l'entrelacement des classes (un
    # creneau de lecture chacune, 19/11) y vit avec la selection par age.
    file, fenetre = tapis_public.lot_public(
        lane, classe["grains"], classe["conteneurs"], grains,
        max(grains * CANDIDATS_MULT, grains), maintenant, ancres=ancres,
        ages_g=ages, exclus_g=exclus, reboucle=False, reinit=reinit)
    secondes = time.monotonic() - debut
    phases = classe["phases"]
    # `tapis_origami.mesurer` est TOTAL : il rend un etat d'echec, jamais une
    # exception -- le garde de l'appelant ne doublait que le garde interne.
    _, origami = tapis_origami.mesurer(
        gh_bulk.Lecture(issues=[], prs=classe["prs"],
                        citations=classe["citations"],
                        lu_a=_iso(maintenant), secondes=round(secondes, 1),
                        appels=0), reseau=True)
    # La fin du tirage -- cap de livraisons, QUALIFICATION de la fenetre servie,
    # puis le rapport -- vit dans `tapis_leger_fenetre`.
    return lq.servir(classe=classe, file=file, fenetre=fenetre, origami=origami,
                     lane=lane, grains=grains, maintenant=maintenant, jours=jours,
                     graine=graine, depot=depot, run=run, phases=phases,
                     secondes=secondes, budget_s=budget_s, echeance=echeance)


# La sortie texte de la voie leger vit dans tapis_leger_texte (extraction
# pour tenir le plafond de lignes de ce module) ; l'alias garde les
# appelants intacts (tapis_voie_leger, tests).
from coordination.tapis_leger_texte import texte  # noqa: E402,F401


def main(argv: list[str] | None = None, run=gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    """Point d'entree du tirage leger (`tapis_leger.py --lane ...`)."""
    import argparse
    import json
    from pathlib import Path

    p = argparse.ArgumentParser(
        description="Tapis leger : rotation universelle sur metadonnees seules.")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8)
    p.add_argument("--json", action="store_true")
    p.add_argument("--jours", type=int, default=45)
    p.add_argument("--graine", default=None)
    p.add_argument("--budget-s", type=float, default=gh_selection.MUR_GLOBAL_S)
    args = p.parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    maintenant = maintenant or datetime.now(UTC)
    graine = args.graine or tapis_rapide.graine_defaut(args.lane, maintenant)
    try:
        r, code = tirage(args.lane, args.grains, maintenant, args.jours, graine,
                         depot, run, args.budget_s)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        return 3
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else texte(r)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return code


if __name__ == "__main__":
    sys.exit(main())
