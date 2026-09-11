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

Pour **J-Lens** (IDs du vocabulaire du modele + logits signes captures
token par token), ne garder que le top-k par score est une **troncature
de rang-k** sur la projection : les identifiants et logits negliges
existent dans le buffer original mais **ne sont pas observes** dans la
trace exportee. :func:`densify` materialise donc une **vue partielle**
du J-space (un top-k d'identifiants vocabulaire + leurs logits signes),
pas une exactitude absolue comme pour le SAE -- les identifiants hors
top-k sont **non observes** (cf. :func:`ict.trace_contract.topk_semantics`
qui code cette asymetrie comme ``TOPK_UNOBSERVED`` vs ``TOPK_EXACT_ZERO``
pour SAE).

La batterie d'emergence tourne a l'identique (meme appareil, c'est l'objectif),
MAIS le verdict doit etre rapporte avec cette nuance : la co-localisation
SAE <-> J se mesure entre deux representations de natures differentes (l'une
exacte par construction, l'autre partielle par troncature d'identifiants).
Ce n'est pas un defaut -- c'est la meilleure approximation disponible d'un
J-space qu'aucun top-k n'epuise -- c'est une limite honnete a inscrire dans
le notebook (garde-fou #1 de :mod:`ict.workspace` : ne pas vendre comme
equivalentes les deux lectures).

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
# Binding local ``_sae_load_npz_unchecked`` : :func:`load_traces` lit le
# .npz via :func:`ict.sae_traces._load_npz_unchecked` (meme schema, memes
# loaders numpy-only + garde BOS-inf, SANS enforce) puis applique la
# discrimination J-Lens via le contrat v1. Le nom ``_sae_load_npz_unchecked``
# est explicite : c'est la fonction ``_load_npz_unchecked`` **telle qu'elle
# est vue par jlens_traces**, pas un appel direct (qui ferait perdre le
# monkeypatching des tests : un monkeypatch sur
# ``ict.sae_traces._load_npz_unchecked`` prend effet via le binding importe,
# cf. :mod:`ict.tests.test_jlens_traces`, helper ``_fake_load_factory``).
from .sae_traces import _load_npz_unchecked as _sae_load_npz_unchecked

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
def load_traces(path: str | Path, *, strict: bool = False) -> dict:
    """Recharge un ``.npz`` de traces **J-Lens** (meme schema que :mod:`ict.sae_traces`).

    Validation du **contrat de trace v1** (:mod:`ict.trace_contract`) :
    appelle :func:`ict.trace_contract.validate_manifest` puis
    :func:`ict.trace_contract.enforce_instrument` avec ``expected="jlens"``.
    Toute trace ``meta['instrument'] == 'sae'`` (ou un manifeste qui declare
    un autre instrument du contrat) est REFUSEE avec un diagnostic
    actionnable -- c'est l'acceptance #1 anti-melange du ticket #15476.

    Le contrat v1 introduit le champ ``meta['instrument']`` (canonique) en
    plus du champ legacy ``meta['lens']``. Les deux sont lus en
    retro-compatibilite : un manifeste sans ``instrument`` mais avec
    ``lens='jacobian'`` est accepte comme J-Lens ; un manifeste avec
    ``instrument='jlens'`` est accepte directement.

    Le parametre ``strict`` (defaut ``False``) suit la meme convention que
    :func:`ict.sae_traces.load_traces` : ``False`` accepte les traces
    historiques, ``True`` exige un manifeste v1 complet.

    Retourne ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
    "tokens"}}}`` -- meme structure que :func:`ict.sae_traces.load_traces` (les
    fonctions d'aval ``densify`` / ``differential_features`` / ... sont
    reexportees telles quelles depuis :mod:`ict.sae_traces`).
    """
    # Delegation via le binding local ``_sae_load_npz_unchecked`` (import
    # explicite ligne 91, ``as _sae_load_npz_unchecked``) : un monkeypatch
    # sur ``ict.jlens_traces._sae_load_npz_unchecked`` prend effet ; les
    # tests :mod:`ict.tests.test_jlens_traces` (post-c.1050) monkeypatchent
    # ``ict.sae_traces._load_npz_unchecked`` directement. Voir
    # :mod:`ict.tests.test_jlens_traces._fake_load_factory`.
    #
    # Note technique : le chargeur J-Lens ne delegue PAS a
    # ``ict.sae_traces.load_traces`` (qui enforce ``instrument=='sae'`` et
    # refuserait systematiquement une trace J-Lens legacy ``lens='jacobian'``).
    # Il utilise :func:`ict.sae_traces._load_npz_unchecked` (parsing
    # structurel + garde BOS-inf SANS enforce) puis applique sa propre
    # validation/enforcement avec ``expected='jlens'``.
    raw_meta, prompts = _sae_load_npz_unchecked(path)
    traces = {"meta": raw_meta, "prompts": prompts}
    # Contrat v1 : validation + anti-melange (acceptance #1).
    # Import local pour eviter tout cycle d'import (trace_contract ne depend
    # de rien du package, sae_traces trace_contract ne depend pas de sae_traces).
    from .trace_contract import validate_manifest, enforce_instrument
    traces["meta"] = validate_manifest(traces["meta"], strict=strict, expected="jlens")
    enforce_instrument(traces["meta"], "jlens")
    return traces
