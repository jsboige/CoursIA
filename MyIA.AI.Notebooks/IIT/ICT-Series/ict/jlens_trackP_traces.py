"""Chargement et curation GPU-free des traces J-Lens Track P (ICT-24, strate 5, #5681).

Miroir de :mod:`ict.jlens_traces` (Track S) pour la **piste persona** de #5681.
Track S confrontait SAE <-> J-lens sur le MÊME substrat (Qwen3.5-9B-Base, prompts de
structure) pour mesurer la co-location cross-appareil. Track P pose une question
orthogonale : le **workspace global se réorganise-t-il selon le persona** elicité ?
Des conditionnements persona contrastés (prudent ↔ enthousiaste, formel ↔ casual,
contrarien) produisent-ils des ignitions / candidates-workspace DISTINCTES au même
layer ? C'est la lecture "persona" du *Global Workspace in Claude* (Anthropic, 2026).

Substrat (G.1 — voir :mod:`extract_jlens_trackP_traces`)
--------------------------------------------------------
La matrice #5681 listait Track P comme "4B-instruct, J-lens via Subtext". Vérifié
firsthand (po-2025 2026-07-11, ``list_repo_files`` HF) : **ni** ``Qwen3.5-4B-Instruct``
**ni** de source de lens "Subtext" ne sont publiés. Le substrate réel exécutable est
``Qwen3.5-4B`` (base) + persona par **prompts de conditionnement** — l'effet persona
est isolé du post-training (paradigme workspace-on-persona d'Anthropic). Le détail
de ce discrepancy est porté par ``meta["substrate_g1_note"]`` dans les fixtures.

Pourquoi un module mince (pas une reinvention)
----------------------------------------------
Le schéma ``.npz`` est **identique** à celui de :mod:`ict.sae_traces` (directive
#5681) : cles ``<set>__<idx>__{topk_ids,topk_vals,tokens}`` + ``__meta__`` (JSON,
mêmes champs ``d_sae`` / ``k`` / ``layer`` / ``variant``). Les fonctions d'aval
(:func:`densify`, :func:`mean_activation_by_set`, :func:`differential_features`,
:func:`acts_topk_panels`, :func:`binarize_quantile`, :func:`states_from_panel`)
operent sur ce schema commun sans rien savoir de la provenance : elles sont donc
**reexportees telles quelles** depuis :mod:`ict.sae_traces` (DRY). L'apport
specifique de ce module est le garde-fou anti-mélange ci-dessous.

Garde-fou anti-mélange (apport spécifique)
------------------------------------------
:func:`load_traces` valide la nature de la trace pour empêcher une erreur de
catégorie dans le notebook persona :

* ``meta["lens"] == "sae"`` -> **refuse** (c'est une trace SAE).
* ``meta["track"]`` commence par ``"S"`` -> **refuse** : c'est une fixture Track S
  (Qwen3.5-9B-Base, structure), pas Track P. Les deux tracks sont des **modèles
  distincts** (9B vs 4B) sur des questions orthogonales (structure vs persona) :
  charger une fixture 9B dans un notebook persona 4B n'a pas de sens, même si le
  schéma .npz est compatible. C'est l'anti-mélange propre à Track P (Track S a le
  sien dans :mod:`ict.jlens_traces`, anti SAE).
* ``meta["track"]`` commence par ``"P"`` ou est absent -> **accepte** (fixture
  Track P nominale, ou rétro-compatibilité avec un extracteur qui n'écrit pas le
  champ). L'extracteur GPU2 (:mod:`extract_jlens_trackP_traces`) DOIT écrire
  ``"track": "P ..."`` pour la traçabilité.

Numpy uniquement : AUCUN import torch ici (le GPU reste confiné au script
d'extraction, piste GPU2 de #5681).

References
----------
* Anthropic, *Global Workspace in Claude* (transformer-circuits.pub, 2026).
* :mod:`ict.jlens_traces` -- l'adaptateur parallèle Track S (structure, 9B-Base),
  dont les fonctions d'aval sont reexportees ici aussi (DRY via :mod:`ict.sae_traces`).
* :mod:`extract_jlens_trackP_traces` -- le runner GPU2 (couche #1) + note G.1 substrate.
* :mod:`ict.workspace` -- la batterie d'émergence consommatrice, agnostique à la
  provenance des traces (consomme des ``acts[T, K]`` et des ``states``).
* #5681 -- piste Track S (tête-à-tête 9B-Base) et Track P (persona 4B).
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
# Chargement (garde-fou anti-mélange Track S/SAE <-> Track P, #5681)
# --------------------------------------------------------------------------- #
def load_traces(path: str | Path, *, strict: bool = False) -> dict:
    """Recharge un ``.npz`` de traces **J-Lens Track P** (persona, 4B).

    Garde-fou anti-mélange : valide la nature de la trace via ``meta["lens"]`` et
    ``meta["track"]``.

    * ``meta["lens"] == "sae"`` -> **refuse** (c'est une trace SAE : utiliser
      :func:`ict.sae_traces.load_traces`).
    * ``meta["track"]`` commence par ``"S"`` -> **refuse** : c'est une fixture
      Track S (modèle 9B-Base, question de structure), pas Track P (modèle 4B,
      persona). Les deux tracks sont des substrats NON comparables directement
      (modèles distincts). Évite de charger une fixture Track S comme trace
      Track P dans le notebook persona #5681.
    * ``meta["track"]`` commence par ``"P"`` ou est absent -> **accepte** (fixture
      Track P nominale, ou rétro-compatibilité).

    Validation du **contrat de trace v1** (:mod:`ict.trace_contract`, #15476),
    même discipline que :func:`ict.jlens_traces.load_traces` : ce chargeur ne
    délègue PAS à :func:`ict.sae_traces.load_traces` (qui enforce
    ``instrument == 'sae'`` et refuserait systématiquement une trace Track P
    legacy ``lens='jacobian'``). Il lit le ``.npz`` via
    :func:`ict.sae_traces._load_npz_unchecked`, applique ses gardes Track P,
    puis le contrat avec ``expected='jlens'`` (legacy ``lens='jacobian'``
    accepté en rétro-compatibilité). Un manifeste sans ``instrument`` NI
    ``lens`` est stampé ``instrument='jlens'`` par cet adaptateur
    (rétro-compat documentée par
    ``tests/test_jlens_trackP_traces.py::test_load_traces_accepts_missing_track_and_lens``).
    Le paramètre ``strict`` (défaut ``False``) suit la même convention que
    :func:`ict.sae_traces.load_traces`.

    Retourne ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
    "tokens"}}}`` -- même structure que :func:`ict.sae_traces.load_traces`.
    """
    raw_meta, prompts = _sae_load_npz_unchecked(path)
    # Gardes Track P posées AVANT l'enforce contrat : les tests #5681 matchent
    # les ValueError historiques ("sae" / "Track S").
    if raw_meta.get("lens") == "sae":
        raise ValueError(
            f"trace {path} porte meta['lens']='sae' : c'est une trace SAE, pas "
            f"J-Lens Track P. Utiliser ict.sae_traces.load_traces (garde-fou "
            f"anti-mélange du tete-a-tete #5681 Track P)."
        )
    track = raw_meta.get("track", "")
    if isinstance(track, str) and track.startswith("S"):
        raise ValueError(
            f"trace {path} porte meta['track']={track!r} : c'est une fixture "
            f"Track S (Qwen3.5-9B-Base, structure), pas Track P (persona 4B). "
            f"Modèles distincts = substrats non comparables directement "
            f"(garde-fou anti-mélange Track S/Track P #5681)."
        )
    # Rétro-compat : manifeste sans discriminant -> cet adaptateur (consommateur
    # J-Lens Track P) déclare 'jlens' avant la validation du contrat.
    if raw_meta.get("instrument") is None and raw_meta.get("lens") is None:
        raw_meta["instrument"] = "jlens"
    from .trace_contract import validate_manifest, enforce_instrument
    meta = validate_manifest(raw_meta, strict=strict, expected="jlens")
    enforce_instrument(meta, "jlens")
    return {"meta": meta, "prompts": prompts}
