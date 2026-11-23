#!/usr/bin/env python3
"""Les exclusions en DONNEES : les labels qui ecartent un grain (#28114).

L'invariant I5 du contrat du picker : « les exclusions dures sont des
**donnees**, pas de la memoire ». Un label pose sur l'issue voyage avec elle
et se voit dans GitHub ; il ecarte le grain la ou le grain se decide -- au
tirage (`tapis_rapide._decider`) comme au claim
(`tapis_qualification_fil.qualification_grain`).

Ce module n'est qu'une TABLE : la DECISION reste dans l'organe de regles, qui
donne le code (`LABEL`) et le motif.

Deux labels, deux sens :

- `candidate-delivered` : l'urne de cloture (coordinateur, adjoint) ;
- `pause` : une pause posee une fois ecarte le grain -- sans regex de titre
  ni souvenir d'agent (les pauses du 22/11 etaient filtreees a la main).
"""
from __future__ import annotations

#: Le label de l'urne de cloture : le grain livre appartient au coordinateur.
LABEL_LIVRE = "candidate-delivered"

#: Le label de pause : la pause est une donnee, pas un souvenir.
LABEL_PAUSE = "pause"

#: label canonique (sans casse) -> motif de l'ecart.
MOTIFS: dict[str, str] = {
    LABEL_LIVRE: "label candidate-delivered : urne de cloture (coordinateur, adjoint)",
    LABEL_PAUSE: "label pause : pause posee en donnees",
}


def ecart_label(labels: list[str]) -> str | None:
    """Le motif d'ecart porte par un label d'exclusion, ou None.

    Les labels se comparent **sans casse** et sans espaces autour : le nom
    GitHub est libre, `Pause` et `pause` sont le meme label.
    """
    poses = {lab.strip().lower() for lab in labels}
    for label, motif in MOTIFS.items():
        if label in poses:
            return motif
    return None


def ecartees(metas: list[dict]) -> list[dict]:
    """Les issues ecartees par un label d'exclusion, avec leur motif.

    Le rapport **publie** l'exclusion : elle n'est jamais silencieuse. Les
    metadonnees suffisent -- le label voyage avec l'issue.
    """
    out: list[dict] = []
    for it in metas:
        motif = ecart_label([str(lab) for lab in (it.get("labels") or [])])
        if motif:
            out.append({"numero": int(it["number"]), "motif": motif})
    return out
