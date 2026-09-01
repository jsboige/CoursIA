"""Fidelite de reconstruction des SAE Qwen-Scope par taille (Livrable 1, #8236).

Outille le notebook de calibration **ICT-21b-SAECalibration** (Phase 0 de #8236) :
avant toute comparaison cross-echelle de forme/dynamique, il faut etablir ce que
chaque SAE reconstruit effectivement du residual stream a sa profondeur appariee.
Ce module porte les mesures, toutes GPU-free :

* :func:`reconstruction_mse` -- erreur quadratique moyenne par element entre
  residual original et reconstruction decodee du SAE ;
* :func:`fraction_variance_unexplained` -- FVU corpus (||H-R||^2 / Var(H)),
  la metrique standard de la litterature SAE : 0 = reconstruction parfaite,
  1 = aussi mauvais que de predire la moyenne du corpus ;
* :func:`l0_measured` -- L0 mesure depuis les codes sparse stockes (indices +
  valeurs du top-k) : doit coincider avec le ``k`` de la release officielle
  (garde :func:`assert_l0_release_consistent`) ;
* :func:`dead_features` -- features jamais (ou quasi jamais) actives sur le
  corpus : borne la largeur *effective* du dictionnaire ;
* :func:`fidelity_report` -- agrege tout en un dict serialisable, consomme par
  le notebook et par ``scripts/extract_sae_fidelity.py``.

Conventions d'encodage = demo officielle Qwen-Scope, cf
:mod:`scripts.extract_sae_traces` : ``acts = topk(relu(hidden @ W_enc.T + b_enc),
k)`` et ``recon = acts @ W_dec`` (le b_dec du checkpoint n'est PAS soustrait --
la demo l'applique au decode ; les deux sont stockes dans la trace pour que le
notebook puisse trancher, la metrique ici prend la reconstruction telle que le
pipeline la produit).

Numpy uniquement : AUCUN import torch ici (regle d'architecture de la serie,
le GPU est confine au script d'extraction).
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "reconstruction_mse",
    "fraction_variance_unexplained",
    "l0_measured",
    "assert_l0_release_consistent",
    "dead_features",
    "fidelity_report",
]


# --------------------------------------------------------------------------- #
# Metriques de reconstruction
# --------------------------------------------------------------------------- #
def reconstruction_mse(hidden: np.ndarray, recon: np.ndarray) -> float:
    """Erreur quadratique moyenne par element entre residual et reconstruction.

    ``hidden`` et ``recon`` : [T, d_model] (T tokens, meme ordre). Le residual
    d'origine est pris AVANT application du b_dec du SAE (convention demo
    Qwen-Scope), ce qui est la grandeur que le decodeur doit reproduire.
    """
    hidden = np.asarray(hidden, dtype=np.float64)
    recon = np.asarray(recon, dtype=np.float64)
    if hidden.shape != recon.shape or hidden.ndim != 2:
        raise ValueError(f"formes incompatibles: {hidden.shape} vs {recon.shape}")
    return float(np.mean((hidden - recon) ** 2))


def fraction_variance_unexplained(hidden: np.ndarray, recon: np.ndarray) -> float:
    """FVU corpus : ||H - R||_F^2 / ||H - mean(H)||_F^2.

    0.0 = reconstruction parfaite ; 1.0 = reconstruire la moyenne du corpus
    (le pire utile) ; > 1.0 = pire que la moyenne. La variance est prise sur
    l'axe des tokens, en flottant 64 bits pour stabiliser le ratio sur des
    norms de residual tres grandes (1e2 typique en bf16 converti).
    """
    hidden = np.asarray(hidden, dtype=np.float64)
    recon = np.asarray(recon, dtype=np.float64)
    if hidden.shape != recon.shape or hidden.ndim != 2:
        raise ValueError(f"formes incompatibles: {hidden.shape} vs {recon.shape}")
    denom = float(np.sum((hidden - hidden.mean(axis=0)) ** 2))
    if denom == 0.0:
        raise ValueError("corpus degenere : variance nulle (un seul token ?)")
    return float(np.sum((hidden - recon) ** 2) / denom)


# --------------------------------------------------------------------------- #
# Metriques du code sparse
# --------------------------------------------------------------------------- #
def l0_measured(vals: np.ndarray, atol: float = 1e-9) -> float:
    """L0 moyen mesure : nombre moyen d'activations non nulles par token.

    ``vals`` : [T, k] valeurs du top-k stockees par le pipeline. Pour un SAE
    top-k officiel, relu() peut annuler des valeurs selectionnees : le L0
    mesure est donc <= k, et l'ecart est une information (features mortes en
    position selectionnee), pas une erreur de mesure.
    """
    vals = np.asarray(vals, dtype=np.float64)
    if vals.ndim != 2:
        raise ValueError(f"attendu [T, k], recu {vals.shape}")
    return float(np.mean(np.count_nonzero(np.abs(vals) > atol, axis=1)))


def assert_l0_release_consistent(l0: float, k_release: int, tol: float = 0.05) -> None:
    """Refuse un L0 mesure qui s'ecarte de la release officielle du SAE.

    Une release ``L0_50`` encode en top-k=50 : le L0 mesure doit tomber a
    +/- ``tol`` (fraction) de k. Un ecart plus grand signifie qu'on mesure
    la mauvaise release (confusion L0_50/L0_100) ou un pipeline modifie --
    dans les deux cas la comparaison cross-echelle serait invalide.
    """
    if abs(l0 - k_release) > tol * k_release:
        raise AssertionError(
            f"L0 mesure {l0:.1f} incoherent avec la release k={k_release} "
            f"(tolerance {tol:.0%}) : mauvaise release confondue ?"
        )


def dead_features(
    counts: np.ndarray, n_tokens: int, activation_threshold: float = 0.01
) -> np.ndarray:
    """Indices des features actives sur < ``activation_threshold`` du corpus.

    ``counts`` : [d_sae] nombre de tokens ou chaque feature est active (non
    nulle apres relu), accumule depuis le sparse par
    :func:`ict.sae_traces.mean_activation_by_set` ou par le script d'extraction.
    Retourne les indices tries croissant.
    """
    counts = np.asarray(counts)
    if counts.ndim != 1 or n_tokens <= 0:
        raise ValueError(f"attendu vecteur [d_sae] et n_tokens > 0, recu {counts.shape}/{n_tokens}")
    return np.flatnonzero(counts < activation_threshold * n_tokens)


# --------------------------------------------------------------------------- #
# Rapport agrege
# --------------------------------------------------------------------------- #
def fidelity_report(
    hidden: np.ndarray,
    recon: np.ndarray,
    vals: np.ndarray,
    counts: np.ndarray,
    *,
    k_release: int,
    label: str,
) -> dict:
    """Agregue les metriques Phase 0 pour une taille, en un dict serialisable.

    ``label`` identifie la ligne du tableau cross-echelle du notebook (ex.
    ``"1.7B-Qwen3 / W32K (14/28)"``). Leve :exc:`AssertionError` via
    :func:`assert_l0_release_consistent` si le L0 mesure contredit la release
    declaree -- le rapport ne se construit pas sur une mesure incoherente.
    """
    l0 = l0_measured(vals)
    assert_l0_release_consistent(l0, k_release)
    dead = dead_features(counts, n_tokens=hidden.shape[0])
    return {
        "label": label,
        "n_tokens": int(hidden.shape[0]),
        "d_model": int(hidden.shape[1]),
        "k_release": int(k_release),
        "l0_measured": round(l0, 2),
        "reconstruction_mse": round(reconstruction_mse(hidden, recon), 6),
        "fvu": round(fraction_variance_unexplained(hidden, recon), 4),
        "n_dead_features": int(dead.size),
        "dead_fraction": round(float(dead.size) / float(counts.size), 4),
    }
