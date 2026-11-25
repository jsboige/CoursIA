#!/usr/bin/env python3
"""La PREUVE de travail : ce qui prouve une livraison, et ce qui ne la prouve pas.

Dans la REQUALIFICATION d'un grain pris en charge, la decision se lit sur le
**fil** : un GRAIN (un marqueur nominatif qui nomme une lane) prouve une
prise en charge ; un `[DELIVERED]` ne prouve PAS une livraison : il DESIGNE la PR a verifier. La preuve, c'est le diff de cette PR couvrant le perimetre declare (`coordination.tapis_diff`).

Trois signaux ne prouvent **rien** de la livraison (revue du 19/11, #27242) :

- la **citation** d'un commit ou d'une PR : une activite *autour* de l'issue ;
- le **label** `candidate-delivered` : une ROUTE vers l'urne de cloture du
  coordinateur et de l'adjoint, pas un verdict de livraison ;
- une PR **ouverte** qui cite l'issue : une couverture en cours, pas un fait.

Les deux derniers restent **visibles** : ils deviennent des NOTES que la lane
lit avant d'agir. Une lane qui rencontre une issue dans l'urne verifie la
preuve sur l'artefact, puis rend la main (#15069) -- elle n'herite d'aucune
exclusion que personne n'a prouvee.

**L'urne, elle, n'est pas un grain neuf** (TASK c0021 du coordinateur,
22/11) : elle est reservee au coordinateur et a l'adjoint (#15069). Pour une
lane worker, le label n'est plus retire du chemin de la decision : l'ecart
`LABEL` des neuf regles retire le grain. Les lanes qui **gerent** l'urne
gardent la note et le grain.
"""
from __future__ import annotations

import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_occupation, tapis_rapide

#: Le label d'urne : il route l'issue, il ne la livre pas. Il est lu dans
#: `tapis_labels` (la TABLE des labels, #28114) -- source unique ; le meme
#: libelle y porte le nom `LABEL_URNE` dans `tapis_occupation`.
from coordination.tapis_labels import LABEL_LIVRE


#: La note d'urne et la fonction qui la pose vivent dans `tapis_occupation` :
#: l'urne est une occupation, et ce module a un plafond de lignes.
NOTE_URNE = tapis_occupation.NOTE_URNE
urne_en_note = tapis_occupation.urne_en_note


def note_couverture(numero: int, lane: str,
                    prs_par_issue: dict[int, list[dict]]) -> str | None:
    """Une PR qui cite l'issue : une couverture, pas une preuve de livraison.

    La meme phrase que le verdict `COUVERTE`, mais **note** : elle informe la
    lane au lieu de lui retirer le grain.
    """
    return tapis_rapide._couverte(numero, lane, prs_par_issue)


def etats_de_tranche(lec, notes_urne: dict[int, str],
                     prs_par_issue: dict[int, list[dict]], lane: str,
                     maintenant: datetime, jours: int,
                     issues: dict[int, dict] | None = None) -> list:
    """Les etats d'une tranche, notes d'urne et de couverture comprises.

    Les notes s'ajoutent aux ecarts : un signal qui ne prouve pas la
    livraison informe la lane, il ne lui retire pas le grain.

    **L'OCCUPATION, elle, retire le grain** (TASK c0021, 22/11) : l'urne est
    reservee au coordinateur et a l'adjoint (#15069), et la PR qui tient
    l'issue l'occupe pour une autre lane. Les deux marques sont lues sur les
    memes metadonnees que le tirage (labels + PRs ouvertes).
    """
    etats = tapis_rapide.etats(lec, lane, maintenant, jours)
    for e in etats:
        if note := notes_urne.get(e.numero):
            e.notes.append(note)
        if note := note_couverture(e.numero, lane, prs_par_issue):
            e.notes.append(note)
    if issues is not None:
        occupation = tapis_occupation.marques_issues(issues, prs_par_issue, lane)
        tapis_occupation.exclure(etats, occupation, lane)
    return etats
