"""Chargement et curation GPU-free des traces J-Lens d'ICT-24 (strate 5, #5681 Track S).

Miroir de :mod:`ict.sae_traces` pour le **tete-a-tete SAE <-> J-space** motive par
l'article *Global Workspace in Claude* (Anthropic, 2025) : l'article identifie le
workspace global d'un grand modele par le **jacobien des logits** (le "J-space"),
tandis que nos traces SAE (pipeline #5101, :mod:`ict.sae_traces`) operationalisent
la meme question via les **features SAE**. Les deux lectures, longtemps paralleles,
ne sont presque jamais confrontees **sur le meme substrat avec le meme appareil**.
Qwen3.5-9B-Base est le SEUL modele pour lequel les DEUX appareils sont publies
(SAE officiel Qwen-Scope + lens Jacobian-Lens ``jlens`` d'Anthropic) : le
tete-a-tete y est donc reproductible, et c'est le substrat de la piste Track S de
#5681.

Ce module outille le notebook **ICT-24 -- WorkspaceIgnition** (Epic #4588) pour
cette piste : faire tourner la batterie d'emergence (:mod:`ict.workspace`,
:mod:`ict.synthesis`) SUR LES TRACES J-LENS (et non plus seulement SAE), afin de
mesurer falsifiablement si le workspace global se co-localise avec les pics de
complexite integree creditee -- la gate de co-location cross-methode de #5681.

Pourquoi un module mince (pas une reinvention)
----------------------------------------------
Le schema ``.npz`` est **identique** a celui de :mod:`ict.sae_traces` (directive
#5681) : cles ``<set>__<idx>__{topk_ids,topk_vals,tokens}`` + ``__meta__`` (JSON,
mêmes champs ``d_sae`` / ``k`` / ``layer`` / ``variant``). Les fonctions
d'aval (:func:`densify`, :func:`mean_activation_by_set`,
:func:`differential_features`, :func:`acts_topk_panels`,
:func:`binarize_quantile`, :func:`states_from_panel`) operent sur ce schema commun
sans rien savoir de la provenance (SAE ou J-lens) : elles sont donc **reexportees
telles quelles** depuis :mod:`ict.sae_traces` (DRY -- un meme appareil sur les deux
familles, invariant methodologique de la serie ICT). L'apport specifique de ce
module est double :

* :func:`load_traces` -- garde-fou **anti-melange** : valide que la trace portee
  est bien un lens jacobien (``meta["lens"] == "jacobian"``), pour qu'une trace SAE
  ne puisse pas etre chargee par megarde comme trace J-lens dans le notebook
  tete-a-tete (et reciproquement via :mod:`ict.sae_traces`).
* documentation honnete de la **divergence semantique** ci-dessous.

Divergence semantique honnete vs SAE (garde-fou a reporter dans le notebook)
---------------------------------------------------------------------------
Pour le **SAE top-k officiel Qwen-Scope**, une feature hors top-50 vaut
**exactement zero** : le SAE top-k force la troncature, donc :func:`densify`
materialise une representation **exacte** (cf. :mod:`ict.sae_traces`).

Pour **J-Lens** (directions singulieres principales de la matrice jacobienne des
logits par token), ne garder que le top-k des directions par score est une
**troncature de rang-k** : les directions negligees ont un coefficient petit mais
**NON nul** en realite. :func:`densify` materialise donc une **approximation
rang-k** de la projection J-space, pas une exactitude absolue comme pour le SAE.

La batterie d'emergence tourne a l'identique (meme appareil, c'est l'objectif),
MAIS le verdict doit etre rapporte avec cette nuance : la co-localisation
SAE <-> J se mesure entre deux representations de natures differentes (l'une
exacte par construction, l'autre approximee par troncature). Ce n'est pas un
defaut -- c'est la meilleure approximation disponible d'un J-space qu'aucun
top-k n'epuise -- c'est une limite honnete a inscrire dans le notebook (garde-fou
#1 de :mod:`ict.workspace` : ne pas vendre comme equivalentes les deux lectures).

Numpy uniquement : AUCUN import torch ici (le GPU reste confine au script
d'extraction ``scripts/extract_jlens_traces.py``, piste GPU2 de #5681).

References
----------
* Anthropic, *Global Workspace in Claude* (anthropic.com/research/global-workspace,
  2025) -- substrat motivationnel ; J-space = jacobien des logits.
* :mod:`ict.sae_traces` -- l'adaptateur parallele (features SAE), dont les
  fonctions d'aval sont reexportees ici.
* :mod:`ict.workspace` -- la batterie d'emergence consommatrice, agnostique a la
  provenance des traces (consomme des ``acts[T, K]`` et des ``states``).
* #5681 -- piste Track S (tete-a-tete 9B-Base) et Track P (4B-instruct persona).
"""

from __future__ import annotations

from pathlib import Path

from .sae_traces import (
    densify,
    mean_activation_by_set,
    differential_features,
    acts_topk_panels,
    binarize_quantile,
    states_from_panel,
)
from .sae_traces import load_traces as _sae_load_traces

__all__ = [
    "load_traces",
    "densify",
    "mean_activation_by_set",
    "differential_features",
    "acts_topk_panels",
    "binarize_quantile",
    "states_from_panel",
]


# --------------------------------------------------------------------------- #
# Chargement (garde-fou anti-melange SAE <-> J-Lens, tete-a-tete #5681)
# --------------------------------------------------------------------------- #
def load_traces(path: str | Path) -> dict:
    """Recharge un ``.npz`` de traces **J-Lens** (meme schema que :mod:`ict.sae_traces`).

    Garde-fou anti-melange : valide la nature de la trace via ``meta["lens"]``.

    * ``meta["lens"] == "sae"`` -> **refuse** (c'est une trace SAE : utiliser
      :func:`ict.sae_traces.load_traces`). Evite de charger une trace SAE comme
      trace J-lens dans le notebook tete-a-tete #5681.
    * ``meta["lens"] == "jacobian"`` -> **accepte** (trace J-Lens nominale).
    * ``meta["lens"]`` absent -> **accepte** (retro-compatibilite avec un extracteur
      qui n'ecrit pas encore le champ). L'extracteur GPU2
      (``scripts/extract_jlens_traces.py``) DOIT ecrire ``"lens": "jacobian"``
      pour la tracabilite du tete-a-tete.

    Retourne ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
    "tokens"}}}`` -- meme structure que :func:`ict.sae_traces.load_traces` (les
    fonctions d'aval ``densify`` / ``differential_features`` / ... sont
    reexportees telles quelles depuis :mod:`ict.sae_traces`).
    """
    traces = _sae_load_traces(path)
    lens = traces.get("meta", {}).get("lens")
    if lens == "sae":
        raise ValueError(
            f"trace {path} porte meta['lens']='sae' : c'est une trace SAE, pas "
            f"J-Lens. Utiliser ict.sae_traces.load_traces pour les traces SAE "
            f"(garde-fou anti-melange du tete-a-tete #5681 Track S)."
        )
    return traces
