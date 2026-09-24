"""tv -- package réutilisable issu de TV-00b (Attention Variants from scratch).

Ce package extrait les briques canoniques du notebook TV-00b en modules Python
importables, sans dépendance sur le reste du notebook. Trois classes principales :

- :class:`VariantAttn` : attention unifiée MHA / MQA / GQA / SWA (leviers : n_kv_heads, window, banded).
- :class:`Bloc`        : bloc pré-norm résiduel (LN -> attn -> résiduel, LN -> MLP -> résiduel).
- :class:`PetitLM`     : transformer minimal (embedding + N blocs + LayerNorm + tête linéaire).

Helpers publics : :func:`build_kv_heads`, :func:`attn_masked`, :func:`attn_banded`,
:func:`causal_window_mask`.

Origine
-------

Issue **#17540** (Russell & Norvig arc B, raisonnement internalisé). Vérification
organ-first c.807 : TV-00b contient bien ces classes (cellules 12, 26). Avant
l'extraction, les classes n'étaient **pas** importables : elles vivaient dans les
cellules du notebook. Le grain d'exécution est cette extraction.

Témoin négatif
--------------

Le témoin négatif du grain #17540 (Huang 2026) est l'entraînement avec vs sans
supervision de chaîne de pensée (CoT) sur une tâche synthétique multi-sauts.
L'extraction du modèle canonique n'est pas le témoin négatif elle-même ; elle
rend le témoin **faisable** dans un grain ultérieur, et c'est précisément le
geste attendu par l'organ-first (question 3 : exporter / refactorer dans la
série source).

Voir aussi
----------

- TV-00b : ``Attention-Variants-from-scratch.ipynb`` (origine).
- TV-03  : ``TV-03-Internalisation-CoT.ipynb`` (à venir — grain d'exécution).
- Issue  : **#17540**.
"""
from __future__ import annotations

from .model import (
    VariantAttn,
    Bloc,
    PetitLM,
    build_kv_heads,
    attn_masked,
    attn_banded,
    causal_window_mask,
)
from .task import (
    Vocab,
    Lot,
    lot_single_hop,
    lot_multi_hop,
    evaluer_single_hop,
    evaluer_multi_hop,
    entrainer,
    entrainer_multi_seed,
)

__all__ = [
    "VariantAttn",
    "Bloc",
    "PetitLM",
    "build_kv_heads",
    "attn_masked",
    "attn_banded",
    "causal_window_mask",
    "Vocab",
    "Lot",
    "lot_single_hop",
    "lot_multi_hop",
    "evaluer_single_hop",
    "evaluer_multi_hop",
    "entrainer",
    "entrainer_multi_seed",
]
