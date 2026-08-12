"""Verificateurs RLVR de la serie PostTraining (corpus issue #10289).

Modules de recompense verifiable (RLVR) alimentant l'entraînement GRPO de
PT-11/PT-12. Chaque verificateur expose une fonction de recompense binaire
calculee par un solveur mecanique (pas de reward model appris) — c'est la
definition meme de RLVR.

Tier-2 (Lean) : :mod:`lean_rlvr_verifier` — recompense une preuve Lean par
elaboration + oracle d'axiomes, avec detection de reward hacking (sorry,
sorryAx transitif, native_decide, axiomes interdits).
"""

from .lean_rlvr_verifier import LeanRLVRVerifier, RLVRResult

__all__ = ["LeanRLVRVerifier", "RLVRResult"]
