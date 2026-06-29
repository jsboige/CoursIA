"""Package `ict` — Integrated Causal Trajectories.

Couche experimentale legere posee a cote de PyPhi pour la serie ICT
(cf. Epic #4588). Hors numpy/matplotlib, le package ne depend de rien :
simulations, trajectoires et metriques fonctionnent sans PyPhi, qui n'est
sollicite que pour les calculs IIT stricts sur de petits systemes.

Strate 1 (tri = morphogenese minimale) : modele de tri auto-organise
(self-sorting arrays), d'apres Zhang, Goldstein & Levin, "Classical sorting
algorithms as a model of morphogenesis", Adaptive Behavior 2025
(arXiv:2401.05375), pont vers la causal emergence (Hoel ; Jansma & Hoel 2025).

Strate 2 (morphogenese dynamique) : paysages d'attracteurs et signaux
precurseurs sur un vrai modele a bifurcation pli (``bistable`` + ``early_warning``,
notebook ICT-8 ; May 1977 ; Scheffer et al. 2009), puis **agence morphologique** :
reparation de forme apres ablation par reaction-diffusion (``reaction_diffusion``
+ ``agency``, notebook ICT-9 ; Gray & Scott 1983 ; Pearson 1993 ; Mordvintsev
et al. 2020 ; Levin).
"""

from .self_sorting import Cell, Probe, SelfSortingArray, ALGOTYPES
from .kin_sorting import KinSortingArray
from .bistable import GrazingModel
from .reaction_diffusion import GrayScott
from . import sorting_metrics
from . import trajectories
from . import causal_emergence
from . import tpm_estimation
from . import scale_free
from . import early_warning
from . import bistable
from . import reaction_diffusion
from . import agency

__all__ = [
    "Cell", "Probe", "SelfSortingArray", "KinSortingArray", "ALGOTYPES",
    "GrazingModel", "GrayScott",
    "sorting_metrics", "trajectories", "causal_emergence", "tpm_estimation",
    "scale_free", "early_warning", "bistable", "reaction_diffusion", "agency",
]
