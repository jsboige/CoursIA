#!/usr/bin/env python3
"""La rotation UNIVERSELLE du tapis : toutes les issues, donnees legeres.

Le tirage actuel (`coordination/tapis_rapide.py`) classe le pool entier, mais
applique **neuf regles d'ecart avant la rotation** et lit le **corps, les
commentaires et les PRs** de chaque issue ouverte. Pour classer 439 issues
afin d'en servir quelques-unes, ce sont deux lectures qui ne servent a rien.

Ce module fait la rotation **sur les metadonnees seules** :

- la lecture est **legere** (`coordination.gh_selection`) : numero, titre,
  date, labels -- et le signal du **travail reel** (les commits de
  `origin/main` qui citent l'issue). Une apparition dans une liste n'est pas
  une visite ;
- la rotation porte sur **toutes** les issues ouvertes : les verifications
  (claim, gel, contenu livre) se font **a la prise en charge**, par le lecteur
  existant, sur le grain servi ; seules les exclusions en **donnees** (un
  label d'exclusion pose sur l'issue) sont ecartees des la lecture ;
- chaque grain servi porte son **etat et l'action a faire**, jamais une
  exclusion silencieuse.

La bascule du tirage par defaut est la tranche suivante : elle suppose que la
prise en charge qualifie le grain (le lecteur lourd cible), ce qui est un
changement de protocole autant que de code.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import UTC, datetime
from pathlib import Path

from coordination import gh_bulk, gh_selection, tapis_citations, tapis_equilibre, tapis_labels, tapis_rapide
from coordination.tapis_rapide import Etat, graine_defaut, ordonner
# Le rapport a son propre fichier (extraction pour tenir le plafond de lignes
# de ce module, comme `tapis_leger_texte` pour `tapis_leger`) ; l'alias garde
# les appelants intacts (`tapis_universel.rapport`, tests).
from coordination.tapis_universel_rapport import rapport


def _parent_de_titre(titre: str) -> int | None:
    """La racine d'EPIC portee par le TITRE (le corps n'est pas lu ici).

    Mêmes motifs que le tirage complet : `[EPIC] ... #12345` et `[#12345] ...`.
    """
    for motif in (r"^\s*\[\s*epic\b[^\]]{0,40}?#(\d+)", r"^\s*\[#(\d+)\b"):
        import re
        m = re.match(motif, titre or "", re.IGNORECASE)
        if m:
            return int(m.group(1))
    return None


def etats_leger(metas: list[dict], citations: dict[int, list[dict]],
                maintenant: datetime,
                citations_ouvertes: dict[int, list[dict]] | None = None) -> list[Etat]:
    """Un etat par issue **servable**, sur les metadonnees seules.

    Les visites comptent le **travail reel** : les commits qui citent l'issue,
    et les PRs **ouvertes** qui la citent (le travail en cours compte aussi).
    Les marqueurs de visite vivent dans les commentaires -- ils sont lus a la
    prise en charge, pas au classement.

    Les exclusions en **donnees** (I5) se decident ICI, sur les labels de
    l'issue : un label d'exclusion (`tapis_labels.ecart_label`) ecarte le
    grain, comme le fait deja le tirage complet (`tapis_rapide._decider`).
    C'est le point de passage commun de la voie legere, des VAGUES et du
    REPLI chronologique : les trois lisent cette fonction, donc les trois
    ecarteront un grain en pause. Le rapport les PUBLIE
    (`tapis_labels.ecartees`) : une exclusion n'est jamais silencieuse."""
    etats = []
    for it in metas:
        n = int(it["number"])
        labels = list(it.get("labels") or [])
        # L'URNE (`candidate-delivered`) ne se decide PAS ici : elle a deux
        # portes -- l'organe d'OCCUPATION (`tapis_occupation`), qui sait qu'une
        # lane gerante (coordinateur, adjoint, secretaire) ne perd aucun grain
        # et recoit l'urne en **resume**, et la regle LABEL du tirage complet.
        # Ecarter l'urne ici supprimerait ce second porteur de la decision, et
        # le retirage (voie legere) perdrait le grain sans publier son motif.
        # Les AUTRES labels d'exclusion (la pause) s'appliquent ici, comme
        # avant : les VAGUES et le REPLI lisent cette fonction.
        autres = [lab for lab in labels
                  if lab.strip().lower() != tapis_labels.LABEL_LIVRE]
        if tapis_labels.ecart_label(autres):
            continue  # exclusion en donnees : le grain n'est pas servable
        titre = it.get("title") or ""
        parent = _parent_de_titre(titre)
        e = Etat(n, titre, labels, it.get("created_at") or "",
                 parent, parent or n, tapis_rapide._conteneur_de(titre, labels),
                 any(lab.strip().lower() == "consolidation" for lab in labels))
        cites = citations.get(n, []) + (citations_ouvertes or {}).get(n, [])
        e.derniere_visite, e.visites_total, e.visites = tapis_equilibre.compter(
            [], cites, maintenant)
        etats.append(e)
    return etats


def rotation_universelle(etats_: list[Etat], lane: str, maintenant: datetime,
                          grains: int, graine: str | None = None,
                          rotation: bool = True) -> list[Etat]:
    """La rotation de TOUTES les issues ouvertes, sans ecarter.

    L'ordre est celui de `tapis_equilibre` : niveau croissant (visites du
    tour moins les priorites legeres), puis le decalage de tete par lane.

    `rotation=False` rend l'ordre **fair** (le decalage de tete par lane
    n'est pas applique) : la voie legere s'en sert, parce que sa FENETRE
    doit pouvoir etre un bloc contigu du pool classe."""
    return ordonner(etats_, lane, maintenant, grains, graine, rotation=rotation)


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Tapis universel : rotation de toutes les issues, lecture legere.")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8)
    p.add_argument("--json", action="store_true")
    p.add_argument("--jours", type=int, default=45, help="fenetre des commits cites")
    p.add_argument("--budget-s", type=float, default=gh_selection.MUR_GLOBAL_S,
                   help="budget global de la lecture de selection")
    return p


def main(argv: list[str] | None = None, run: gh_bulk.Run = gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    args = _parser().parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    maintenant = maintenant or datetime.now(UTC)
    try:
        metas, duree = gh_selection.lire_metadonnees_issues(
            run, budget_s=args.budget_s)
        citations = gh_bulk.lire_citations_mergees(depot, args.jours, run)
        prs = gh_bulk.lire_prs_ouvertes(run)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        return 3
    etats_ = etats_leger(metas, citations, maintenant,
                          tapis_citations.des_prs_ouvertes(prs))
    file = rotation_universelle(etats_, args.lane, maintenant, args.grains,
                                graine_defaut(args.lane, maintenant))
    r = rapport(etats_, file, args.lane, maintenant,
                {"issues": len(metas), "secondes": duree, "budget_s": args.budget_s},
                ecartees=tapis_labels.ecartees(metas))
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else "\n".join(
        f"#{g['numero']} {g['titre'][:70]} -- {g['action']}" for g in r["grains"])
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
