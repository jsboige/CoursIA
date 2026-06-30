"""Self-sorting arrays : le tri comme morphogenese minimale (cell-eye-view).

Reimplementation pedagogique inspiree de :

    Taining Zhang, Adam Goldstein, Michael Levin,
    "Classical sorting algorithms as a model of morphogenesis: self-sorting
    arrays reveal unexpected competencies in a minimal model of basal
    intelligence", Adaptive Behavior, 2025 (arXiv:2401.05375).

Idee directrice
---------------
Au lieu d'un controleur global qui trie un tableau, **chaque element devient
une cellule autonome** qui applique localement la regle de son *algotype*.
L'ordre global n'est plus impose d'en haut : il *emerge* des decisions locales.
Le tri devient alors une **trajectoire** dans un espace de configurations
(morphospace), exactement l'objet d'etude de la serie ICT (#4588).

Regles locales (vue-cellule)
----------------------------
- ``bubble``    : la cellule regarde sa voisine de DROITE ; si elle est plus
                  grande qu'elle, elle glisse a droite (les grandes valeurs
                  migrent vers la fin).
- ``insertion`` : la cellule regarde sa voisine de GAUCHE ; si elle est plus
                  petite qu'elle, elle glisse a gauche (les petites valeurs
                  migrent vers le debut).

Les deux pulsions sont coherentes avec le meme ordre croissant global : un
tableau melangeant les deux algotypes (tableau *chimerique*) converge donc
aussi, ce qui permet d'etudier l'agregation par algotype.

Cellules defectueuses (frozen) et robustesse
--------------------------------------------
Une cellule ``frozen`` n'initie jamais d'action. Deux regimes existent
(``frozen_mode``) :

- ``"passive"`` (defaut, fidele au papier) : la cellule cassee n'agit pas mais
  reste un *passager* — une voisine saine peut la deplacer. Le systeme atteint
  alors un ordre eleve malgre les cellules cassees : c'est la robustesse
  emergente observee par Zhang, Goldstein & Levin.
- ``"obstacle"`` : la cellule gelee est en plus *infranchissable* ; elle agit
  comme un mur. Les cellules saines trient seulement a l'interieur des
  segments delimites par les murs (variante d'etude, plus fragile).

Le planificateur (scheduler) est asynchrone et seedable : a chaque pas, une
cellule non gelee est activee au hasard. La version notebook privilegie le
determinisme experimental (reproductibilite par seed) a la fidelite multi-thread.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Optional

ALGOTYPES = ("bubble", "insertion")


@dataclass
class Cell:
    """Un element autonome du tableau.

    value     : la cle de tri (objectif global = ordre croissant des valeurs).
    algotype  : la regle locale suivie ("bubble" ou "insertion").
    frozen    : cellule defectueuse, n'agit pas et n'est pas traversable.
    cid       : identite stable, pour suivre le voyage de la cellule meme
                lorsqu'elle change de position.
    """

    value: int
    algotype: str = "bubble"
    frozen: bool = False
    cid: int = -1


@dataclass
class Probe:
    """Enregistre la trajectoire complete du systeme, pas a pas."""

    values: list = field(default_factory=list)       # snapshot des valeurs
    algotypes: list = field(default_factory=list)     # snapshot des algotypes
    positions: list = field(default_factory=list)     # cid -> position (par pas)
    swaps: int = 0
    comparisons: int = 0

    def snapshot(self, cells: list) -> None:
        self.values.append([c.value for c in cells])
        self.algotypes.append([c.algotype for c in cells])
        self.positions.append({c.cid: i for i, c in enumerate(cells)})

    def __len__(self) -> int:
        return len(self.values)


class SelfSortingArray:
    """Un tableau dont les elements se trient eux-memes (vue-cellule)."""

    def __init__(
        self,
        values: list,
        algotypes: Optional[list] = None,
        frozen: Optional[list] = None,
        seed: int = 0,
        frozen_mode: str = "passive",
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
        if frozen_mode not in ("passive", "obstacle"):
            raise ValueError("frozen_mode doit etre 'passive' ou 'obstacle'")
        self.frozen_mode = frozen_mode

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

    def _neighbor_blocked(self, j: int) -> bool:
        """Le voisin j empeche-t-il l'echange ? (uniquement en mode obstacle)."""
        return self.frozen_mode == "obstacle" and self.cells[j].frozen

    def _target_neighbor(self, i: int) -> Optional[int]:
        """Position du voisin que la cellule i tenterait d'echanger, si la regle
        locale s'applique (valeur dans le mauvais ordre et voisin non bloquant).
        Retourne None sinon. L'echange se fait toujours entre i et le voisin."""
        c = self.cells[i]
        if c.frozen:
            return None
        if c.algotype == "bubble":
            j = i + 1
            if j < len(self.cells) and not self._neighbor_blocked(j) and c.value > self.cells[j].value:
                return j
        else:  # insertion : regarde a gauche
            j = i - 1
            if j >= 0 and not self._neighbor_blocked(j) and c.value < self.cells[j].value:
                return j
        return None

    def has_move(self) -> bool:
        """Le systeme est-il encore actif (au moins une cellule peut agir) ?"""
        return any(self._target_neighbor(i) is not None for i in range(len(self.cells)))

    # ------------------------------------------------------------------ dynamique
    def step(self) -> bool:
        """Active une cellule non gelee au hasard ; elle applique sa regle.

        Retourne True si un swap a eu lieu, False sinon (cellule activee sans
        mouvement valide -- un "pas a vide", fidele a une activation basale qui
        n'aboutit pas toujours).
        """
        movable = [i for i, c in enumerate(self.cells) if not c.frozen]
        if not movable:
            return False
        i = self.rng.choice(movable)
        self.probe.comparisons += 1
        j = self._target_neighbor(i)
        acted = False
        if j is not None:
            self._swap(i, j)
            acted = True
        self.steps += 1
        self.probe.snapshot(self.cells)
        return acted

    def run(self, max_steps: int = 20000, record: bool = True) -> "SelfSortingArray":
        """Active des cellules jusqu'au point fixe (plus aucun mouvement) ou max_steps.

        Si ``record`` est False, on ne snapshote que l'etat final (utile pour
        les balayages ou seul l'etat terminal compte).
        """
        if record:
            while self.steps < max_steps and self.has_move():
                self.step()
        else:
            while self.steps < max_steps and self.has_move():
                movable = [i for i, c in enumerate(self.cells) if not c.frozen]
                if not movable:
                    break
                i = self.rng.choice(movable)
                j = self._target_neighbor(i)
                if j is not None:
                    self._swap(i, j)
                self.steps += 1
            self.probe.snapshot(self.cells)
        return self

    def perturb(self, n_swaps: int = 3) -> None:
        """Applique une perturbation exogene (lesion) : n_swaps echanges aleatoires
        entre cellules non gelees. Sert a etudier l'auto-reparation."""
        movable = [i for i, c in enumerate(self.cells) if not c.frozen]
        for _ in range(n_swaps):
            if len(movable) < 2:
                break
            a, b = self.rng.sample(movable, 2)
            self._swap(a, b)
        self.probe.snapshot(self.cells)
