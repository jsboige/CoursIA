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
"""
from __future__ import annotations

import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_rapide

#: Le label d'urne : il route l'issue, il ne la livre pas.
from coordination.tapis_labels import LABEL_LIVRE

NOTE_URNE = ("label candidate-delivered : urne de cloture (coordinateur, adjoint) "
              "-- signal, pas preuve : verifie l'artefact, puis rends la main")


def urne_en_note(issues: dict[int, dict]) -> dict[int, str]:
    """Retire le label d'urne du chemin de la decision ; rend sa note.

    Le label ne prouve pas la livraison : il ne doit donc pas ecarter le grain
    dans la requalification. Il reste dit -- en note, sur le grain servi.
    """
    notes: dict[int, str] = {}
    for n, it in issues.items():
        labs = [str(l) for l in (it.get("labels") or [])]
        reste = [l for l in labs if l.strip().lower() != LABEL_LIVRE]
        if len(reste) != len(labs):
            it["labels"] = reste
            notes[n] = NOTE_URNE
    return notes


def note_couverture(numero: int, lane: str,
                    prs_par_issue: dict[int, list[dict]]) -> str | None:
    """Une PR qui cite l'issue : une couverture, pas une preuve de livraison.

    La meme phrase que le verdict `COUVERTE`, mais **note** : elle informe la
    lane au lieu de lui retirer le grain.
    """
    return tapis_rapide._couverte(numero, lane, prs_par_issue)


def etats_de_tranche(lec, notes_urne: dict[int, str],
                     prs_par_issue: dict[int, list[dict]], lane: str,
                     maintenant: datetime, jours: int) -> list:
    """Les etats d'une tranche, notes d'urne et de couverture comprises.

    Les notes s'ajoutent aux ecarts : un signal qui ne prouve pas la
    livraison informe la lane, il ne lui retire pas le grain.
    """
    etats = tapis_rapide.etats(lec, lane, maintenant, jours)
    for e in etats:
        if note := notes_urne.get(e.numero):
            e.notes.append(note)
        if note := note_couverture(e.numero, lane, prs_par_issue):
            e.notes.append(note)
    return etats
