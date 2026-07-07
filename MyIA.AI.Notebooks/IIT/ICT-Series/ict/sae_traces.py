"""Chargement et curation GPU-free des traces SAE d'ICT-21 (strate 5, #5101).

Outille le notebook **ICT-21 -- SAETrajectoires** et tout l'aval S4 (#5102
LLMSubstrat, #5635 WorkspaceIgnition) : le pipeline GPU
(:mod:`scripts.extract_sae_traces`) stocke pour chaque token la representation
**sparse exhaustive** du SAE top-k officiel Qwen-Scope (indices + valeurs du
top-50). Toute activation hors top-50 vaut **exactement zero** par construction
du SAE top-k : la densification ici est donc *exacte*, pas une approximation.

Ce module est un **adaptateur mince** (precedent :mod:`ict.feature_dynamics`) :

* :func:`load_traces` -- recharge un ``.npz`` d'extraction (sans pickle) en
  structure par (jeu de prompts, index de prompt) ;
* :func:`densify` -- materialise [T, F] dense pour un sous-ensemble de
  features, depuis le sparse (ids, vals) ;
* :func:`mean_activation_by_set` -- vecteur d'activation moyenne [d_sae] par
  jeu de prompts, accumule depuis le sparse ;
* :func:`differential_features` -- selection top-K des features qui
  *discriminent les regimes* (variance inter-jeux de l'activation moyenne) :
  c'est le ``acts_topk`` (K~64) du schema amende de #5101 ;
* :func:`binarize_quantile` / :func:`states_from_panel` -- panel binarise
  (~10 features) -> codes d'etats discrets consommables par
  :func:`ict.synthesis.emergence_gain` (meme discipline de creditation que
  S1-S3, aucune complaisance nouvelle).

Numpy uniquement : AUCUN import torch ici (regle d'architecture de la serie,
le GPU est confine au script d'extraction).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

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
# Chargement
# --------------------------------------------------------------------------- #
def load_traces(path: str | Path) -> dict:
    """Recharge un ``.npz`` produit par ``scripts/extract_sae_traces.py``.

    Retourne ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
    "tokens"}}}`` avec ``ids`` [T, k] int32, ``vals`` [T, k] float32 (depuis
    float16), ``tokens`` [T] str. Aucun ``allow_pickle`` requis.
    """
    data = np.load(Path(path), allow_pickle=False)
    meta = json.loads(str(data["__meta__"]))
    prompts: dict[tuple[str, int], dict] = {}
    for key in data.files:
        if key == "__meta__":
            continue
        set_name, idx, field = key.rsplit("__", 2)
        entry = prompts.setdefault((set_name, int(idx)), {})
        if field == "topk_ids":
            entry["ids"] = data[key].astype(np.int32)
        elif field == "topk_vals":
            entry["vals"] = data[key].astype(np.float32)
        elif field == "tokens":
            entry["tokens"] = data[key]
    for (set_name, idx), entry in prompts.items():
        missing = {"ids", "vals"} - set(entry)
        if missing:
            raise ValueError(f"trace {set_name}__{idx} incomplete : manque {missing}")
    return {"meta": meta, "prompts": prompts}


# --------------------------------------------------------------------------- #
# Densification exacte depuis le sparse top-k
# --------------------------------------------------------------------------- #
def densify(ids: np.ndarray, vals: np.ndarray, feature_ids: np.ndarray) -> np.ndarray:
    """Materialise [T, F] dense pour ``feature_ids``, exact par construction.

    Une feature absente du top-50 d'un token a une activation exactement nulle
    (SAE top-k) : aucun biais de troncature.
    """
    feature_ids = np.asarray(feature_ids, dtype=np.int64)
    T = ids.shape[0]
    dense = np.zeros((T, feature_ids.size), dtype=np.float32)
    # position de chaque id du top-k dans feature_ids (ou -1)
    order = np.argsort(feature_ids)
    sorted_feats = feature_ids[order]
    pos = np.searchsorted(sorted_feats, ids)
    pos = np.clip(pos, 0, sorted_feats.size - 1)
    hit = sorted_feats[pos] == ids                       # [T, k] bool
    rows = np.broadcast_to(np.arange(T)[:, None], ids.shape)
    dense[rows[hit], order[pos[hit]]] = vals[hit]
    return dense


def mean_activation_by_set(traces: dict) -> dict[str, np.ndarray]:
    """Activation moyenne [d_sae] par jeu de prompts, accumulee du sparse."""
    d_sae = int(traces["meta"]["d_sae"])
    sums: dict[str, np.ndarray] = {}
    counts: dict[str, int] = {}
    for (set_name, _), entry in traces["prompts"].items():
        acc = sums.setdefault(set_name, np.zeros(d_sae, dtype=np.float64))
        np.add.at(acc, entry["ids"].ravel(), entry["vals"].ravel().astype(np.float64))
        counts[set_name] = counts.get(set_name, 0) + entry["ids"].shape[0]
    return {s: (acc / counts[s]).astype(np.float32) for s, acc in sums.items()}


def differential_features(traces: dict, k: int = 64) -> np.ndarray:
    """Top-``k`` features par variance inter-jeux de l'activation moyenne.

    C'est la selection ``acts_topk`` du schema amende de #5101 : les features
    qui *discriminent les regimes* (code vs prose vs dialogue...), pas les plus
    actives en absolu (qui seraient dominees par la ponctuation/le formatage).
    """
    means = mean_activation_by_set(traces)
    stack = np.stack(list(means.values()))               # [n_sets, d_sae]
    score = stack.var(axis=0)
    return np.argsort(score)[::-1][:k].astype(np.int64)


def acts_topk_panels(traces: dict, feature_ids: np.ndarray) -> dict[tuple[str, int], np.ndarray]:
    """Panels denses [T, K] float32 par prompt pour ``feature_ids`` (schema amende)."""
    return {key: densify(e["ids"], e["vals"], feature_ids)
            for key, e in traces["prompts"].items()}


# --------------------------------------------------------------------------- #
# Panel binarise -> etats discrets (consommable par ict.synthesis)
# --------------------------------------------------------------------------- #
def binarize_quantile(dense: np.ndarray, q: float = 0.5) -> np.ndarray:
    """Binarise [T, F] par seuil au quantile ``q`` des valeurs POSITIVES de
    chaque feature (les zeros structurels du top-k n'ecrasent pas le seuil).

    Une feature jamais active sur la fenetre reste toute a False.
    """
    if not 0.0 <= q < 1.0:
        raise ValueError(f"quantile q={q} hors [0, 1)")
    T, F = dense.shape
    bits = np.zeros((T, F), dtype=bool)
    for j in range(F):
        col = dense[:, j]
        pos = col[col > 0]
        if pos.size == 0:
            continue
        bits[:, j] = col > np.quantile(pos, q)
    return bits


def states_from_panel(bits: np.ndarray) -> np.ndarray:
    """Encode chaque ligne binaire en un code d'etat entier (bit-packing).

    Limite volontaire a 20 features (2^20 etats) : au-dela, l'estimation de
    TPM d':func:`ict.synthesis.emergence_gain` n'aurait de toute facon plus
    aucun support statistique sur quelques milliers de tokens.
    """
    T, F = bits.shape
    if F > 20:
        raise ValueError(f"panel a {F} features : bit-packing limite a 20 "
                         "(explosion d'etats vs support statistique)")
    weights = (1 << np.arange(F)).astype(np.int64)
    return bits.astype(np.int64) @ weights
