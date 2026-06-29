"""Package `ict` — Integrated Causal Trajectories.

Couche experimentale legere posee a cote de PyPhi pour la serie ICT
(cf. Epic #4588). Ce module ne depend que de la bibliotheque standard :
les simulations, trajectoires et metriques fonctionnent sans PyPhi, qui
n'est sollicite que pour les calculs IIT stricts sur de petits systemes.

Premier jalon livre : le modele de morphogenese minimale par tri auto-organise
(self-sorting arrays), d'apres Zhang, Goldstein & Levin,
"Classical sorting algorithms as a model of morphogenesis", Adaptive Behavior
2025 (arXiv:2401.05375).
"""

from .self_sorting import Cell, Probe, SelfSortingArray, ALGOTYPES
from . import sorting_metrics
from . import trajectories
from . import causal_emergence
from . import tpm_estimation
from . import scale_free

__all__ = [
    "Cell", "Probe", "SelfSortingArray", "ALGOTYPES",
    "sorting_metrics", "trajectories", "causal_emergence", "tpm_estimation",
    "scale_free",
]
