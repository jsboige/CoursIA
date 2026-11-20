#!/usr/bin/env python3
"""L'AVANCE du curseur, BORNEE au lot (revue du peer, 19/11).

Le curseur n'avance que sur les numeros que le LOT a reellement pris en
charge. Une qualification **nominative** d'un numero qui n'appartient pas a
la tranche ne deplace plus l'ancre des primaires pendantes : le curseur
annoncait alors une couverture que personne n'avait mesuree (revue du
19/11, point b).

Trois etats pour un numero de la tranche :

- **pris en charge et decide** : le curseur passe ;
- **pris en charge, non decide** (lecture impossible, budget epuise) : le
  numero est PARKE, sous SON code, et le curseur passe ;
- **propose, non pris en charge** : rien n'a ete decide sur lui. Il reste
  en attente ; il n'est parke QUE si le curseur finit par le sauter -- sinon
  il serait perdu pour la rotation.

La REPRISE ne porte pas le curseur : une primaire etrangere deja parquee
ne fait pas avancer une tranche que le lot ne touche pas (revue du 19/11).
"""
from __future__ import annotations

from coordination import tapis_non_tente


def avancer(cible: list[int], ancre: int | None, couvert: set[int] | None,
            att: dict, inc: dict) -> int | None:
    """Fait avancer le curseur sur la tranche, borne au lot.

    `cible` : les numeros de la tranche, dans l'ordre. `couvert` : le lot
    reellement pris en charge (None : avance non bornee, voie heritage).
    `att` : les numeros servis. `inc` : les numeros parcs (modifie sur place).
    """
    sautes: list[int] = []
    for n in cible:
        if ancre is not None and n <= ancre:
            continue
        if couvert is not None and n not in couvert:
            # Ni decide, ni refuse : le numero sera saute par le curseur.
            sautes.append(n)
            continue
        # Le curseur passe par-dessus n : les numeros sautes sont parkes,
        # sinon ils seraient perdus pour la rotation.
        for s in sautes:
            if s not in inc:
                tapis_non_tente.parquer_non_tente(inc, s)
        sautes = []
        if n in inc:
            ancre = n
            continue
        if not att.get(n):
            tapis_non_tente.parquer_non_tente(inc, n)
        ancre = n
    return ancre
