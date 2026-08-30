"""Tranche 3/3 — adaptateurs cross-engine runtime EVPI/EVSI (issue #13569).

Ce package branche la *meme* description de probleme de decision sur deux
moteurs bayesiens natifs du depot et expose leurs sorties sous un contrat
JSON unique, pour comparaison croisee.

Deux moteurs :

- **Infer.NET** (C#/.NET via ``Microsoft.ML.Probabilistic``)
  Cf. ``DecInfer/DecInfer-6-Value-Information.ipynb`` pour le calculateur
  natif ; l'adaptateur ``adapter_infernet.py`` extrait ce calculateur et le
  sert sur le contrat JSON sans le reimplementer en Python.

- **PyMC** (Python)
  Cf. ``PyMC/DecPyMC-5-Value-Information.ipynb`` pour le calculateur natif ;
  l'adaptateur ``adapter_pymc.py`` appelle ``pymc.sample`` sur le meme
  ``DecisionProblem``.

Le contrat commun est ``VoiContract`` : ``DecisionProblem`` + matrice de
vraisemblance ``L[etat, outcome]`` + cout fixe d'observation. La sortie est
un ``VoiResult`` avec ``eu_no_info``, ``best_no_info``, ``evpi``, ``evsi``,
``evsi_net``, ``observe``. Le runner ``compare.py`` execute les deux
adaptateurs sur le meme contrat et ecrit le tableau d'accord/desaccord.

**Reference** : interface canonique ``MyIA.AI.Notebooks/IIT/ICT-Series/ict/voi.py``
(PR #13652, tranche 1/3) — la meme signature ``animat_decision_summary``
sert ici de specification executable.

**Ne pas modifier** : ``DecInfer-6``, ``DecPyMC-5``, ``DecPyMC-11`` ni
``#13664`` (contrainte d'acceptance de la tranche 3/3).
"""

from .contract import VoiContract, VoiResult, animat_decision_summary_contract
from . import adapter_pymc
from . import adapter_infernet
from . import compare

__all__ = [
    "VoiContract",
    "VoiResult",
    "animat_decision_summary_contract",
    "adapter_pymc",
    "adapter_infernet",
    "compare",
]
