"""Self-sorting arrays a regles plus riches : reparation bidirectionnelle et
affinite "kin" (agregation par algotype).

Suite directe de ``self_sorting`` (modele minimal vue-cellule). Le notebook
ICT-2 a montre honnetement que les regles uni-directionnelles de base
reproduisent la robustesse et le delai de gratification du papier de
Zhang, Goldstein & Levin (2025), mais **pas** l'agregation positive par
"kin" (algotype) : elles produisent au contraire des *impasses* aux
frontieres ``insertion | bubble``. ICT-2 renvoie explicitement le jeu de
regles plus riche a **ICT-4** -- c'est ce module.

Deux ingredients ajoutes au modele minimal
-------------------------------------------
1. **Reparation bidirectionnelle** (``bidirectional=True``).
   Une cellule garde la "personnalite" de son algotype (sa direction de
   regard *primaire* : ``bubble`` -> droite, ``insertion`` -> gauche), mais
   lorsque cette direction primaire ne propose aucun mouvement, elle jette
   un coup d'oeil a son *autre* voisin et corrige une inversion qui s'y
   trouve. C'est exactement l'indice de l'Exercice 3 d'ICT-2. Consequence :
   toute inversion adjacente devient corrigeable par l'une de ses deux
   extremites, donc l'impasse chimerique disparait et le tri converge
   toujours -- sans pour autant creer d'agregation.

2. **Affinite "kin"** (``kin_affinity=True``).
   Un second elan, *neutre pour l'ordre*. Quand une cellule n'a aucun
   mouvement de tri a faire, elle peut echanger sa place avec un voisin de
   **valeur egale** (donc interchangeable pour l'objectif de tri : deux
   cellules de meme valeur sont des "destins equivalents") si cet echange
   **augmente** le nombre de paires adjacentes de meme algotype. L'ordre des
   valeurs est strictement preserve (on n'echange que des egaux) ; ce qui
   bouge, c'est l'organisation *secondaire* par algotype.

Idee centrale d'ICT-4
---------------------
L'agregation par algotype n'est encodee comme objectif nulle part. Elle
**emerge** dans les *degres de liberte* laisses par l'ordre primaire : la ou
plusieurs cellules partagent une valeur, l'ordre ne les contraint pas, et la
preference locale pour le semblable peut s'y exprimer. Une seconde couche
d'organisation causale s'installe dans le jeu que la premiere lui laisse --
un motif que la serie ICT retrouve a l'echelle macro (emergence causale).

Terminaison
-----------
Les mouvements de tri font **decroitre strictement** le nombre d'inversions
(borne par 0) ; les mouvements "kin" preservent les inversions et font
**croitre strictement** le nombre de paires de meme algotype (borne par
n-1). Le couple (inversions, -kin_adjacency) decroit lexicographiquement :
le systeme atteint toujours un point fixe.

Stdlib uniquement (comme tout le package ``ict``).
"""

from __future__ import annotations

import random
from typing import Optional

from .self_sorting import Cell, Probe, ALGOTYPES


class KinSortingArray:
    """Tableau auto-trie a regles enrichies (reparation + affinite kin).

    Parametres
    ----------
    values        : valeurs (cle de tri ; l'ordre cible est croissant).
    algotypes     : regle locale primaire de chaque cellule ("bubble"/"insertion").
    frozen        : cellules defectueuses (passagers, mode passif uniquement ici).
    seed          : graine du planificateur asynchrone (reproductibilite).
    bidirectional : active la reparation par coup d'oeil au second voisin.
    kin_affinity  : active l'elan secondaire d'agregation par algotype.
    kin_sign      : +1 = attraction (se regrouper avec le semblable, defaut) ;
                    -1 = repulsion (s'eloigner du semblable -> segregation a la
                    Schelling, agregation negative). Sans effet si kin_affinity
                    est False.
    """

    def __init__(
        self,
        values: list,
        algotypes: Optional[list] = None,
        frozen: Optional[list] = None,
        seed: int = 0,
        bidirectional: bool = True,
        kin_affinity: bool = True,
        kin_sign: int = 1,
    ) -> None:
        n = len(values)
        if algotypes is None:
            algotypes = ["bubble"] * n
        if frozen is None:
            frozen = [False] * n
        if not (len(algotypes) == len(frozen) == n):
            raise ValueError("values, algotypes et frozen doivent avoir la meme longueur")
        if any(a not in ALGOTYPES for a in algotypes):
            raise ValueError(f"algotypes doit etre parmi {ALGOTYPES}")

        if kin_sign not in (1, -1):
            raise ValueError("kin_sign doit etre +1 (attraction) ou -1 (repulsion)")
        self.bidirectional = bidirectional
        self.kin_affinity = kin_affinity
        self.kin_sign = kin_sign
        self.cells = [
            Cell(value=values[i], algotype=algotypes[i], frozen=frozen[i], cid=i)
            for i in range(n)
        ]
        self.rng = random.Random(seed)
        self.steps = 0
        self.probe = Probe()
        self.probe.snapshot(self.cells)

    # ------------------------------------------------------------------ etat
    @property
    def values(self) -> list:
        return [c.value for c in self.cells]

    @property
    def algotypes(self) -> list:
        return [c.algotype for c in self.cells]

    def _swap(self, i: int, j: int) -> None:
        self.cells[i], self.cells[j] = self.cells[j], self.cells[i]
        self.probe.swaps += 1

    # ----------------------------------------------------------- mouvements de tri
    def _sort_target(self, i: int) -> Optional[int]:
        """Position du voisin que la cellule i echangerait pour reduire une
        inversion. Direction *primaire* selon l'algotype ; si la reparation
        bidirectionnelle est active, repli sur l'autre voisin. None sinon."""
        c = self.cells[i]
        if c.frozen:
            return None
        n = len(self.cells)
        if c.algotype == "bubble":
            # primaire : regarde a droite (les grandes valeurs migrent a droite)
            if i + 1 < n and c.value > self.cells[i + 1].value:
                return i + 1
            # reparation : coup d'oeil a gauche
            if self.bidirectional and i - 1 >= 0 and c.value < self.cells[i - 1].value:
                return i - 1
        else:  # insertion : regarde a gauche
            if i - 1 >= 0 and c.value < self.cells[i - 1].value:
                return i - 1
            if self.bidirectional and i + 1 < n and c.value > self.cells[i + 1].value:
                return i + 1
        return None

    # --------------------------------------------------------- mouvements "kin"
    @staticmethod
    def _kin_adjacency(algotypes: list) -> int:
        """Nombre de paires adjacentes de meme algotype (potentiel d'agregation)."""
        return sum(1 for k in range(len(algotypes) - 1) if algotypes[k] == algotypes[k + 1])

    def _kin_target(self, i: int) -> Optional[int]:
        """Position d'un voisin de *valeur egale* avec qui un echange augmente
        strictement l'agregation par algotype. Echange neutre pour l'ordre
        (valeurs identiques). None s'il n'y en a pas."""
        if not self.kin_affinity:
            return None
        c = self.cells[i]
        if c.frozen:
            return None
        algos = self.algotypes
        base = self._kin_adjacency(algos)
        for j in (i - 1, i + 1):
            if 0 <= j < len(self.cells) and not self.cells[j].frozen and self.cells[j].value == c.value:
                trial = algos[:]
                trial[i], trial[j] = trial[j], trial[i]
                # attraction (kin_sign=+1) : on accepte si l'agregation augmente ;
                # repulsion (kin_sign=-1) : si elle diminue (segregation).
                if self.kin_sign * (self._kin_adjacency(trial) - base) > 0:
                    return j
        return None

    # ------------------------------------------------------------------ activite
    def _has_sort_move(self) -> bool:
        return any(self._sort_target(i) is not None for i in range(len(self.cells)))

    def _has_kin_move(self) -> bool:
        return self.kin_affinity and any(
            self._kin_target(i) is not None for i in range(len(self.cells))
        )

    def has_move(self) -> bool:
        """Le systeme est-il encore actif (un mouvement de tri OU de kin) ?"""
        return self._has_sort_move() or self._has_kin_move()

    # ------------------------------------------------------------------ dynamique
    def step(self) -> bool:
        """Active une cellule non gelee au hasard. Priorite au tri ; a defaut,
        un mouvement d'affinite kin. Retourne True si un echange a eu lieu."""
        movable = [i for i, c in enumerate(self.cells) if not c.frozen]
        if not movable:
            return False
        i = self.rng.choice(movable)
        self.probe.comparisons += 1
        acted = False
        j = self._sort_target(i)
        if j is not None:
            self._swap(i, j)
            acted = True
        else:
            k = self._kin_target(i)
            if k is not None:
                self._swap(i, k)
                acted = True
        self.steps += 1
        self.probe.snapshot(self.cells)
        return acted

    def run(self, max_steps: int = 40000, record: bool = True) -> "KinSortingArray":
        """Active des cellules jusqu'au point fixe (ni tri ni kin) ou max_steps."""
        if record:
            while self.steps < max_steps and self.has_move():
                self.step()
        else:
            while self.steps < max_steps and self.has_move():
                movable = [i for i, c in enumerate(self.cells) if not c.frozen]
                if not movable:
                    break
                i = self.rng.choice(movable)
                j = self._sort_target(i)
                if j is not None:
                    self._swap(i, j)
                else:
                    k = self._kin_target(i)
                    if k is not None:
                        self._swap(i, k)
                self.steps += 1
            self.probe.snapshot(self.cells)
        return self
