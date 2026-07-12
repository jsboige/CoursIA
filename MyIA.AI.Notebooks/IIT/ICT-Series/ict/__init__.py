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

Strate 3 (agentivite et valence) : morphodynamique strategique et signature
de valence (``strategic_morphodynamics``, ``valence``, ``multiscale_agency``,
``catastrophe``, notebooks ICT-11..13 ; Axelrod 1984 ; Thom 1972).

Strate 4 (energie libre) : le principe d'energie libre comme lecture unifiee
de l'agentivite morphologique (``free_energy``, notebook ICT-14 ; Friston).

Strate 5 (theorie fondatrice cross-substrat) : compression et longueur de
description minimale (``compression``, ``mdl``, ``epsilon_machine`` ;
Crutchfield ; Hoel), dynamique de features en panel (``feature_dynamics``,
notebook ICT-20) et synthese (``synthesis``). La fleche du temps /
reversibilisation (ICT-18) y outille retrospectivement la signature
thermodynamique de l'agentivite.

Strate 5 (capstone jumeau anthropique) : la **fronce de Thom** comme
micro-analogue du desalignement emergent (``persona_cusp``, notebook
ICT-23 ; Epic #4588 / #5104). Le substrat est un agent dont l'identite
(p) est un parametre d'ordre, pilote par la recompense (b) et la charge
semantique (a = -transgression * charge). L'inoculation `charge -> 0`
aplatit la fronce et supprime la bistabilite : c'est la prediction P0
d'#5104 (Anthropic arXiv:2511.18397, OpenAI arXiv:2506.19823).
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
from . import multiscale_agency
from . import catastrophe
from . import valence
from . import strategic_morphodynamics
from . import free_energy
from . import compression
from . import mdl
from . import epsilon_machine
from . import feature_dynamics
from . import time_arrow
from . import synthesis
from . import persona_cusp
from . import stake
from . import workspace

__all__ = [
    "Cell", "Probe", "SelfSortingArray", "KinSortingArray", "ALGOTYPES",
    "GrazingModel", "GrayScott",
    "sorting_metrics", "trajectories", "causal_emergence", "tpm_estimation",
    "scale_free", "early_warning", "bistable", "reaction_diffusion", "agency",
    "multiscale_agency", "catastrophe", "valence", "strategic_morphodynamics",
    "free_energy", "compression", "mdl", "epsilon_machine", "feature_dynamics",
    "time_arrow", "synthesis", "persona_cusp", "stake", "workspace",
]
