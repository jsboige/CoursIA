#!/usr/bin/env python3
"""Le grain NON TENTE : propose, jamais qualifie -- le TROISIEME etat.

Trois etats se distinguer pour un numero propose par le tirage :

- un **verdict TERMINAL** (confirme, ou ecarte par une regle de contenu) :
  le curseur passe, le numero est acquitte ;
- un **refus de lecture** (`FIL_ILLISIBLE`, `MUR_EPUISE`, `ECHEANCE`,
  `ABSENT`) : rien n'a ete decide non plus, mais la lecture a echoue --
  le numero est parque dans la file de reprise, et le curseur passe ;
- un grain **NON TENTE** : propose, et jamais qualifie -- la qualification
  s'est arretee avant lui (budget, echeance, fin de vague). Rien n'a ete
  decide sur lui, et il ne se confond avec aucun des deux etats ci-dessus :
  il porte SON code.

**Pourquoi il ne doit pas figer le curseur** (mesure du 19/11, peer
`ai-01:CoursIA`) : pool 1..6, taille 2, ancre 2. La tranche [3, 4] est
proposee, seul 4 est qualifie ; 3 n'a pas ete tente. Le curseur qui s'arrete
au premier numero non decide RE-PROPOSE la meme tranche au cycle suivant --
quatre cycles de suite -- et **5 et 6 ne sont jamais proposes** : la
couverture du pool s'arrete. Le curseur passe donc par-dessus le grain non
tente, qui est parque comme un illisible et **revient au service par la file
de reprise** : aucun numero n'est perdu, et le pool continue d'etre couvert.

La file de reprise elle-meme (et sa borne de latence) vit dans
`coordination.tapis_retry` ; l'arithmetique de la selection dans
`coordination.tapis_tranche`.
"""
from __future__ import annotations

from coordination.tapis_retry import parquer

#: Le grain PROPOSE mais jamais qualifie (ni confirme, ni refuse) : rien
#: n'a ete decide sur lui, la qualification s'est arretee avant. Ce n'est
#: NI un verdict terminal, NI un fil illisible : il porte SON code.
NON_TENTE = "NON_TENTE"


def parquer_non_tente(inc: dict, n: int) -> dict:
    """PARQUE un grain propose mais non qualifie, sous SON code.

    Il ne **fige** pas le curseur (voir le module) : il est rendu au service
    par la file de reprise, comme un refus de lecture -- sous un code qui
    le distingue.
    """
    return parquer(inc, n, {"code": NON_TENTE,
                            "motif": "grain propose mais non qualifie : "
                                     "aucune decision n'a ete prise"})
