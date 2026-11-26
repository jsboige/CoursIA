#!/usr/bin/env python3
"""La FORME positive d'un echec d'OUTIL : quand un code d'echec est-il le
MOTIF COURANT du rendu ?

Review du coordinateur (25/11, #28440) : `est_echec_outil()` lisait un code
d'echec **n'importe ou** dans le commentaire. Une forme ordinaire sur deux
lignes suffisait :

    [RELEASED] lane X -- GPU partage indisponible
    Essai du 22/11 : verify-reject

Aucun jeton de la deuxieme ligne n'est un marqueur du passe, et la premiere
ligne ne porte aucun code : le rendu etait donc lu comme un echec d'OUTIL,
et le grain etait **degele pour les autres lanes** alors que le motif
courant etait une **barriere reelle** (le GPU partage indisponible).

La portee locale -- un echec d'outil ne gele que la lane qui l'a subi --
est donc reservee aux formes **positivement identifiees** :

- le format **explicite** : `motif: <code>` ;
- la forme **Rust mesuree** (22/11) : un code suivi de sa fournee et de sa
  date, `(1) verify-reject (fournee w3p, 22/11)`.

Toute autre mention d'un code est un rappel : le motif courant n'est pas
identifie, et le gel reste **global** (fail-CLOSED) -- le comportement
d'avant. La regle **ne depend pas** d'un vocabulaire de barrieres : une
barriere reelle n'a pas besoin d'etre reconnue, il suffit que le code ne
soit pas le motif courant.
"""
from __future__ import annotations

import re

#: Le format explicite : le code est **nomme** comme motif du rendu.
_MOTIF_EXPLICITE_RE = re.compile(r"\bmotif\s*:\s*([\w-]+)")

#: La forme Rust mesuree : le code est suivi de sa fournee et de sa date
#: (`22/11`), comme dans les rendus de production du 22/11.
_FORME_RUST_RE = re.compile(r"([\w-]+)\s*\([^()]*\d{1,2}/\d{1,2}[^()]*\)")


def codes_identifies(corps: str) -> set[str]:
    """Les codes d'echec **positivement identifies** comme motif courant.

    Le corps est lu en minuscules : les codes du vocabulaire sont ASCII.
    """
    texte = (corps or "").lower()
    trouves = {m.group(1) for m in _MOTIF_EXPLICITE_RE.finditer(texte)}
    trouves |= {m.group(1) for m in _FORME_RUST_RE.finditer(texte)}
    return trouves
