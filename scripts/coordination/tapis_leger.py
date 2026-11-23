#!/usr/bin/env python3
"""La voie LEGERE du tirage : la rotation universelle, seule.

Ce module est la **bascule** du tirage par defaut (#27225, suite de #27223) : le
tirage separe deux temps qui etaient confondus :

- la **rotation universelle** (`coordination.tapis_universel`) classe TOUTES
  les issues ouvertes sur leurs **metadonnees seules** et tourne la tete de
  niveau. Elle n'ecarte rien : un conteneur ne passe jamais devant un grain
  (#26926), et chaque grain servi porte son **etat** et l'**action** ;
- la **qualification** (`coordination.tapis_qualification`) ne porte que sur
  le grain pris en charge : son corps, son **fil complet**, et la re-decision
  des neuf regles d'ecart, AVANT l'action.

Les neuf regles ne sont pas decidables sur des metadonnees : les decider pour
TOUT le pool coutait 22 s ; a l'action, 1 a 2 appels par grain pris en charge.

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
from coordination import gh_bulk, gh_selection, tapis_equilibre
from coordination import tapis_age, tapis_ancre, tapis_origami, tapis_rapide, tapis_rotation
from coordination import tapis_service, tapis_universel
# L'import de l'occupation est sur **sa propre ligne** : la PR d'age (#28022)
# modifie la ligne d'import voisine, et deux ancres distinctes fusionnent sans
# conflit (les deux PRs restent donc mergeables dans n'importe quel ordre).
from coordination import tapis_occupation
from coordination import tapis_leger_rapport
from coordination.tapis_marqueurs import _iso, lane_de_pr

#: Le classement propose ce multiple de grains : la qualification ecarte
#: quelques-uns au moment de l'action, et la file doit rester pleine.
CANDIDATS_MULT = 3


def _ordre(etats_: list, lane: str, maintenant: datetime,
          graine: str) -> tuple[list, list]:
    """L'ordre de TOUTES les issues ouvertes : les grains d'abord, les
    conteneurs ensuite (un conteneur ne passe jamais devant un grain).

    L'ordre est **fair** (`rotation=False`) : le decalage de tete par lane
    est applique a la FENETTRE, pas au pool -- sinon la fenetre ne peut pas
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
            budget_s: float = gh_selection.MUR_GLOBAL_S) -> dict:
    """Le POOL classe : l'ordre fair des grains, et les conteneurs.

    C'est la lecture de metadonnees du tirage leger, SANS la fenetre : la
    prise en charge s'en sert pour les VAGUES (ouvrir la vague suivante
    quand la fenetre ne donne aucun grain servable).
    """
    debut = time.monotonic()
    metas, duree = gh_selection.lire_metadonnees_issues(run, budget_s=budget_s)
    t1 = time.monotonic()
    citations = gh_bulk.lire_citations_mergees(depot, jours, run)
    t2 = time.monotonic()
    prs = gh_bulk.lire_prs_ouvertes(run)
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
           budget_s: float = gh_selection.MUR_GLOBAL_S) -> tuple[dict, int]:
    """Le tirage leger complet : le rapport et le code de sortie.

    Sortie 3 : la lecture de selection est incomplete (rien n'est servi) --
    jamais une liste a moitie. Une lecture incomplete du POOL n'est pas
    equivalente : la selection paginee est complete ou elle echoue.
    """
    debut = time.monotonic()
    classe = classer(lane, maintenant, jours, graine, depot, run, budget_s)
    ancres = tapis_ancre.lire(lane)
    # SELECTION PAR AGE (mandat du 22/11) : les issues ANCIENNES d'abord.
    # La rotation par numero servait les recentes (mesure du 22/11 : 0 issue
    # anterieure au 01/11 dans les 60 premiers grains d'un pool de 455).
    # Les CONTENEURS passent avec : leurs racines labellisees `consolidation`
    # font de leurs membres des consolidations (revue ai-01 du 22/11).
    ages, exclus, reinit = tapis_age.tour(classe["grains"], ancres, maintenant,
                                          classe["conteneurs"])
    file, fenetre = tapis_rotation.bloc(classe["grains"], classe["conteneurs"],
                                         grains, max(grains * CANDIDATS_MULT, grains),
                                         lane, maintenant, ancres=ancres,
                                         ages_g=ages, exclus_g=exclus)
    tapis_ancre.proposer(lane, "grains", fenetre["primaires"]["grains"],
                          fenetre["reprises"]["grains"],
                          reboucle=False, reinit=reinit)
    tapis_ancre.proposer(lane, "conteneurs",
                          fenetre["primaires"]["conteneurs"],
                          fenetre["reprises"]["conteneurs"])
    secondes = time.monotonic() - debut
    phases = classe["phases"]
    # `tapis_origami.mesurer` est TOTAL : il rend un etat d'echec, jamais une
    # exception -- le garde de l'appelant ne doublait que le garde interne.
    _, origami = tapis_origami.mesurer(
        gh_bulk.Lecture(issues=[], prs=classe["prs"],
                        citations=classe["citations"],
                        lu_a=_iso(maintenant), secondes=round(secondes, 1),
                        appels=0), reseau=True)
    # Cap de livraisons EPIC (#21067) : le garde arbitre (charge en vol,
    # item K=2 / famille K=4) vivait dans le seul pick_idle_grain, retire du
    # tirage depuis #26926 -- rebranche sur la voie reelle, fail-OPEN.
    from coordination import tapis_cap_livraisons
    file, temoins_cap, cap_mesure = tapis_cap_livraisons.passer(
        file, classe["grains"] + classe["conteneurs"], lane, maintenant,
        classe["prs"], run=run)
    rapport = tapis_leger_rapport.rapport(
        lane, graine, maintenant, classe["metas"], phases["selection_s"],
        secondes, budget_s, classe["etats"], file, classe["prs"], origami,
        phases, fenetre, classe.get("occupation"))
    rapport["cap_livraisons"] = {"mesure": cap_mesure, "ecartes": temoins_cap,
                                 "fenetre_j": tapis_cap_livraisons.FENETRE_J}
    return rapport, 0


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
