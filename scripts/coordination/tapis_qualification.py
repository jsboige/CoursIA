#!/usr/bin/env python3
"""La QUALIFICATION d'un grain PRIS EN CHARGE : le corps, le fil complet, sa decision.

C'est le temps d'**action** du tapis : le tirage propose un ordre sur toutes les
issues ouvertes (rotation universelle, metadonnees seules, `coordination.tapis_leger`),
et la lane qualifie le grain qu'elle engage a prendre, avant de le reclamer.

La qualification lit :

- le **corps** de l'issue (une lecture ciblee, une requete par lot) ;
- son **fil complet**, par l'organe REST `gh_snapshot` (pagination complete) --
  jamais la fenetre des 12 derniers commentaires de la lecture groupee, qui peut
  cacher le marqueur qui ecarte un grain (constat de #27179) ;
- et rejoue les **neuf regles d'ecart** de `tapis_rapide.etats` : la voie legere
  ne redecide pas, elle alimente la meme decision.

**La requalification ne confond pas la trace et le travail** (revue du 19/11,
#27242) : elle decide sur le **fil**. Une citation de commit, une PR ouverte
qui cite l'issue, un label `candidate-delivered` : trois signaux qui
n'ont ete **prouves** par personne et qui ne peuvent donc pas retirer un grain
de la file. Ils restent dit, en notes (`coordination.tapis_preuves`), et la
lecture ne relit plus les citations de `origin/main`.

**Un marqueur n'est pas une preuve** (revue du 19/11, `5967171401`) : un
`[DELIVERED]` DESIGNE la PR a verifier. La preuve, c'est le **diff** de cette
PR couvrant le perimetre declare (`coordination.tapis_diff`) ; un diff absent
ou partiel laisse l'issue dans la rotation. Le correctif s'applique au temps
d'action, quand `preuve` est fourni : le classement reste sur le marqueur, la
bascule reste a arbitrer.

**fail-CLOSED.** Une decision qui n'a pas pu etre prise REFUSE le grain : le
grain porte son code de refus (`FIL_ILLISIBLE`, `MUR_EPUISE`, `ECHEANCE`) et
son motif, il n'est pas servi. Un grain non qualifie ne s'engage pas.

**Chaque numero demande recoit un verdict** (`coordination.tapis_lot`) : lu,
illisible, ou absent de la reponse -- aucun ne disparait sans motif.

Ce que rend `qualifier` :

- `servis` : les grains servables, dans l'ordre donne ;
- `ecartees` : `{numero: {code, motif, fenetre_suffit}}` -- les exclusions
  **affichees**, jamais retirees en silence ; un code de lecture y figure
  aussi : le grain est REFUSE, pas decide ;
- `echecs` : les numeros illisibles (corps ou fil) ;
- `arrete` : le mur global a ete atteint ;
- `appels` : le nombre d'appels de la qualification ;
- `chrono` : `{secondes, premier_servable_s}` -- le temps jusqu'au **premier
  grain servable**, distinct de la latence du classement (celle du tirage,
  dans son propre rapport).

Usage (prise en charge d'un grain) :

    python scripts/coordination/tapis_qualification.py --issue 17397

Usage (prise en charge d'une file, le premier servable gagne) :

    python scripts/coordination/tapis_qualification.py --issues 17397 27241 17545
"""
from __future__ import annotations

import sys
import time
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_diff, tapis_fenetre, tapis_lot, tapis_occupation
from coordination import tapis_preuves
from coordination import tapis_fil_complet, tapis_rapide, tapis_verdict

#: Candidats par lot de lecture (une requete GraphQL pour le lot).
LOT = 50

#: Les codes de REFUS ne sont pas des verdicts TERMINAUX : le grain n'a pas
#: ete decide, il n'a pas etre lu. L'ancre de rotation ne passe pas un
#: numero dont la lecture a echoue (peer, 19/11) : la coverage ne sacrifie
#: pas la qualite.
CODES_NON_TERMINAUX = tuple(tapis_fil_complet.CODES_REFUS) + (tapis_lot.ABSENT,)


def qualifier(candidats: list[int], lane: str, maintenant: datetime, jours: int,
              prs: list[dict], run,
              echeance: float | None = None, lot: int = LOT,
              horloge=time.monotonic, debut: float | None = None, preuve=None
              ) -> tuple[list, dict, list[int], bool, int, dict]:
    """Qualifie les candidats PRIS EN CHARGE, dans l'ordre donne.

    Rend `(servis, ecartees, echecs, arrete, appels, chrono)`. `preuve` rend
    le diff d'une PR : sans lui, LIVREE reste pose sur le marqueur.
    """
    issues: dict[int, dict] = {}
    confirmes: dict[int, object] = {}
    ecartees: dict[int, dict] = {}
    echecs: list[int] = []
    exclus: set[int] = set()
    notes_urne: dict[int, str] = {}
    prs_par_issue = tapis_rapide._prs_par_issue(prs)
    arrete = False
    appels = 0
    premier: float | None = None
    i = 0
    while i < len(candidats):
        if echeance is not None and horloge() > echeance:
            arrete = True
            break
        tranche = candidats[i:i + lot]
        i += lot
        appels += tapis_lot.fenetre(tranche, run, issues, echecs, ecartees)
        notes_urne.update(tapis_preuves.urne_en_note(issues, lane))
        lec = tapis_lot.lec(list(issues.values()), maintenant, appels)
        etats = tapis_preuves.etats_de_tranche(lec, notes_urne, prs_par_issue,
                                               lane, maintenant, jours, issues)
        tapis_diff.appliquer(etats, lec, preuve)
        for e in etats:
            if e.ecart and e.numero not in ecartees:
                ecartees[e.numero] = {"numero": e.numero, "code": e.ecart,
                                      "motif": e.motif,
                                      "fenetre_suffit": tapis_fenetre.suffit(
                                          issues.get(e.numero))}
        retenus = [e for e in etats if e.ecart is None and e.numero not in exclus
                   and e.numero not in confirmes]
        if not retenus:
            continue
        conf, rejet, rates, n = tapis_fil_complet.confirmer(
            retenus, lec, lane, maintenant, jours, echeance, horloge, preuve=preuve)
        appels += n
        echecs.extend(rates)
        for e in conf:
            tapis_fenetre.noter(e, issues.get(e.numero))
            confirmes[e.numero] = e
            if premier is None and debut is not None:
                premier = horloge() - debut
        for r in rejet:
            exclus.add(r["numero"])
            ecartees[r["numero"]] = {**r, "fenetre_suffit": False}
    servis = [confirmes[n] for n in candidats if n in confirmes]
    chrono = {"secondes": round(horloge() - debut, 1) if debut is not None else None,
              "premier_servable_s": round(premier, 1) if premier is not None else None}
    tapis_verdict.avancer(lane, confirmes, ecartees)
    return servis, ecartees, echecs, arrete, appels, chrono
