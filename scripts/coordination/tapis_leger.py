#!/usr/bin/env python3
"""La voie LEGERE du tirage : la rotation universelle, seule.

Ce module est la **bascule** du tirage par defaut (#27225, suite de #27223).

Le tirage separe deux temps qui etaient confondus :

- la **rotation universelle** (`coordination.tapis_universel`) classe TOUTES
  les issues ouvertes sur leurs **metadonnees seules** et tourne la tete de
  niveau. Elle n'ecarte rien : un conteneur ne passe jamais devant un grain
  (#26926), et chaque grain servi porte son **etat** et l'**action** a faire ;
- la **qualification** (`coordination.tapis_qualification`) ne porte que sur
  le grain que la lane engage a **prendre** : son corps, son **fil complet**,
  et la re-decision des neuf regles d'ecart. Elle s'execute AVANT l'action,
  sur un grain a la fois.

Pourquoi la qualification n'est plus dans le tirage : les neuf regles ne sont
pas decidables sur des metadonnees (un gel, une livraison, un claim se lisent
dans le corps ou le fil). Les decider pour TOUT le pool coutait 22 s de
lecture -- plus cher que le chemin lourd lui-meme (21,9 s pour 441 issues).
Decider au moment de l'action coute 1 a 2 appels par grain pris en charge.

Mesures (pool de 441 issues, 18/11, meme machine, meme lane) :

| Chemin | Lecture | Duree | Ce qu'il sert |
|---|---|---|---|
| lourd | corps + 12 commentaires de tout le pool (5,2 Mo) | 33,5 s | 11 grains, exclusions appliquees |
| **leger** | **metadonnees seules** (8,6 s a chaud, 15,4 s a froid) + citations (1,6 s) + PRs (4,7 s) | **17,9 s** | une file de 24, exclusions a decider a l'action |

Le **mur global** (`--budget-s`, 60 s par defaut) couvre la lecture de
selection ; son depassement leve `LectureIncomplete` et l'appelant le dit
(code de sortie 3) -- jamais une liste a moitie.
"""
from __future__ import annotations

import time
from datetime import UTC, datetime
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection, tapis_equilibre
from coordination import tapis_fenetre, tapis_origami, tapis_rapide
from coordination import tapis_service, tapis_universel
from coordination.tapis_marqueurs import _age, _iso, lane_de_pr

#: Le classement propose ce multiple de grains : la qualification ecarte
#: quelques-uns au moment de l'action, et la file doit rester pleine.
CANDIDATS_MULT = 3


def _ordre(etats_: list, lane: str, maintenant: datetime,
          graine: str) -> tuple[list, list]:
    """L'ordre de TOUTES les issues ouvertes : les grains d'abord, les
    conteneurs ensuite (un conteneur ne passe jamais devant un grain).

    L'ordre est **fair** (`rotation=False`) : le decalage de tete par lane
    est applique a la FENETTRE, pas au pool -- sinon la fenetre ne peut pas
    etre un bloc contigu du pool classe (`tapis_fenetre.bloc`).
    """
    grains_ = [e for e in etats_ if not e.conteneur]
    conteneurs = [e for e in etats_ if e.conteneur]
    return (tapis_universel.rotation_universelle(
        grains_, lane, maintenant, len(grains_), graine, rotation=False),
            tapis_universel.rotation_universelle(
                conteneurs, lane, maintenant, len(conteneurs), graine,
                rotation=False))

def _rapport(lane: str, graine: str, maintenant: datetime, metas: list[dict],
             duree: float, secondes: float, budget_s: float, etats_: list,
             file: list, prs: list[dict], origami: dict,
             phases: dict | None = None, fenetre: dict | None = None) -> dict:
    """Le rapport du tirage leger : l'etat de chaque grain et l'action a faire."""
    vos = sorted((pr for pr in prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    rapport = tapis_universel.rapport(etats_=etats_, file=file,
                                      lane=lane, maintenant=maintenant,
                                      lecture={})
    rapport.update({
        "graine": graine, "voie": "leger", "pool": len(metas),
        "fenetre": fenetre or {},
        "lecture": {"issues": len(metas), "secondes": round(secondes, 1),
                    "selection_s": duree, "budget_s": budget_s,
                    "phases": phases or {}, "budget_epuise": False},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)} for pr in vos],
        "qualification": {
            "organe": "scripts/coordination/tapis_prise_en_charge.py",
            "vagues": "scripts/coordination/tapis_vagues.py : la file se remplit",
            "quand": "avant l'action, sur le grain pris en charge",
            "ecarts": "les neuf regles se decident sur le fil complet",
        },
        "origami_parking": origami,
    })
    return rapport


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
    grains_, conteneurs = _ordre(etats_, lane, maintenant, graine)
    return {"metas": metas, "citations": citations, "prs": prs, "etats": etats_,
            "grains": grains_, "conteneurs": conteneurs,
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
    file, fenetre = tapis_fenetre.bloc(classe["grains"], classe["conteneurs"],
                                       grains, max(grains * CANDIDATS_MULT, grains),
                                       lane, maintenant)
    secondes = time.monotonic() - debut
    phases = classe["phases"]
    try:
        _, origami = tapis_origami.mesurer(
            gh_bulk.Lecture(issues=[], prs=classe["prs"], citations=classe["citations"],
                            lu_a=_iso(maintenant), secondes=round(secondes, 1),
                            appels=0), reseau=True)
    except Exception:  # noqa: BLE001 - un garde ne doit pas casser le tirage
        origami = {"measured": False, "reason": "mesure Origami en echec"}
    rapport = _rapport(lane, graine, maintenant, classe["metas"],
                       phases["selection_s"], secondes, budget_s, classe["etats"],
                       file, classe["prs"], origami, phases, fenetre)
    return rapport, 0


def texte(r: dict) -> str:
    """La sortie courte de la voie leger : l'etat de chaque grain et l'action.

    Elle dit ce que le chemin lourd dit, et une chose de plus : **ou** se
    qualifie un grain, et **quand** (avant l'action).
    """
    lu = r["lecture"]
    lignes = [f"Tapis leger -- lane {r['lane']} -- {r['maintenant']} "
              f"-- source : GitHub + origin/main local (rotation universelle)"]
    lignes.append(f"{lu['issues']} issues ouvertes ; rotation sur metadonnees seules "
                  f"(selection {lu['selection_s']} s, citations {lu['phases'].get('citations_s')} s, "
                  f"PRs {lu['phases'].get('prs_s')} s, budget {lu['budget_s']} s) ; "
                  f"file de {len(r['grains'])} grain(s)")
    fen = r.get("fenetre") or {}
    if fen.get("blocs", 1) > 1:
        lignes.append(f"Fenetre : bloc {fen['bloc']}/{fen['blocs']} du pool classe "
                      f"(taille {fen['taille']}) -- la fenetre avance d'un bloc par "
                      f"tranche de 4 h : le pool entier est couvert en "
                      f"{fen['blocs']} tranches.")
    lignes.append(f"\nVos PRs ouvertes ({len(r['vos_prs'])}) -- traitez d'abord leurs nits :")
    lignes += [f"  #{p['numero']}  {p['age_j']} j  {p['titre'][:90]}"
               for p in r["vos_prs"]]
    lignes.append("\nGrains -- qualifier avant action, puis servir :")
    for g in r["grains"]:
        lignes.append(f"  #{g['numero']}  {g['titre'][:80]}")
        lignes.append(f"      {g['action']}")
    q = r["qualification"]
    lignes.append(f"\nQualification : {q['organe']} -- {q['quand']} ; {q['ecarts']}.")
    return "\n".join(lignes)


def main(argv: list[str] | None = None, run=gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    """Point d'entree du tirage leger (`tapis_leger.py --lane ...`)."""
    import argparse
    import json
    import sys
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
    import sys

    sys.exit(main())
