"""Signaux precurseurs (*early-warning signals*, EWS) de transitions critiques.

Outille le notebook **ICT-8**. Quand un systeme dynamique approche d'une
bifurcation pli (*fold* / noeud-col), la valeur propre dominante de son
equilibre tend vers zero : le systeme **recupere de plus en plus lentement**
de ses perturbations. Ce *ralentissement critique* (Wissel 1984 ; Scheffer et
al., *Early-warning signals for critical transitions*, Nature 2009 ; Dakos et
al. 2012) laisse deux empreintes statistiques mesurables **avant** la bascule :

* la **variance** des fluctuations augmente (le systeme s'ecarte plus loin et
  plus longtemps de l'equilibre) ;
* l'**autocorrelation de retard 1** (AR1) augmente (les ecarts persistent d'un
  pas a l'autre — la "memoire" s'allonge).

Le piege central -- et la lecon anti-complaisance d'ICT-8
---------------------------------------------------------
Mesurer naivement ces indicateurs **fabrique ou masque** le signal :

1. **Sur-echantillonnage.** Si l'intervalle d'echantillonnage est tres petit
   devant le temps de relaxation, l'AR1 est ecrasee pres de 1 *partout* et n'a
   aucune marge pour monter. Il faut **amincir** la serie (``thin``) a une
   cadence comparable au temps de relaxation.
2. **Tendance non-stationnaire.** Le glissement deterministe de l'equilibre est
   une tendance qu'il faut **retirer** (``detrend``) avant de mesurer la
   *variance des fluctuations* — sinon on mesure la derive, pas le bruit.

Ce module fournit donc, dans l'ordre : ``thin`` -> ``detrend`` -> indicateurs
roulants (``rolling_variance``, ``rolling_lag1_autocorr``) -> test de tendance
(``kendall_tau``), agreges par ``ews_summary``. Numpy uniquement (pas de scipy),
comme le reste du package leger ``ict``.
"""

from __future__ import annotations

import math
from typing import Optional

import numpy as np
from numpy.lib.stride_tricks import sliding_window_view


# --------------------------------------------------------------------------- #
# Pretraitement : amincissement et detrendage
# --------------------------------------------------------------------------- #
def thin(x, factor: int) -> np.ndarray:
    """Sous-echantillonne la serie d'un facteur ``factor`` (un point sur N).

    Indispensable quand le pas d'integration est tres fin devant le temps de
    relaxation : sans cela l'AR1 sature pres de 1 et le signal disparait.
    """
    if factor < 1:
        raise ValueError("factor doit etre >= 1")
    return np.asarray(x, dtype=float)[::factor]


def _gaussian_kernel(sigma: float, truncate: float = 4.0) -> np.ndarray:
    radius = int(truncate * sigma + 0.5)
    t = np.arange(-radius, radius + 1, dtype=float)
    k = np.exp(-(t ** 2) / (2.0 * sigma ** 2))
    return k / k.sum()


def gaussian_smooth(x, sigma: float) -> np.ndarray:
    """Lissage gaussien (estimation de la tendance lente). Bords par reflexion."""
    x = np.asarray(x, dtype=float)
    if sigma <= 0:
        return x.copy()
    k = _gaussian_kernel(sigma)
    pad = len(k) // 2
    xp = np.pad(x, pad, mode="reflect")
    return np.convolve(xp, k, mode="valid")


def detrend(x, sigma: float) -> np.ndarray:
    """Retire la tendance lente : residus = serie - lissage gaussien(sigma)."""
    x = np.asarray(x, dtype=float)
    return x - gaussian_smooth(x, sigma)


# --------------------------------------------------------------------------- #
# Indicateurs
# --------------------------------------------------------------------------- #
def lag1_autocorr(x) -> float:
    """Autocorrelation de retard 1 (scalaire) d'une serie."""
    x = np.asarray(x, dtype=float)
    a, b = x[:-1], x[1:]
    am, bm = a.mean(), b.mean()
    den = math.sqrt(((a - am) ** 2).sum() * ((b - bm) ** 2).sum())
    if den == 0.0:
        return float("nan")
    return float(((a - am) * (b - bm)).sum() / den)


def rolling_variance(x, window: int) -> np.ndarray:
    """Variance sur fenetre glissante de largeur ``window``."""
    x = np.asarray(x, dtype=float)
    if window < 2 or window > len(x):
        raise ValueError("window doit verifier 2 <= window <= len(x)")
    return sliding_window_view(x, window).var(axis=1)


def rolling_lag1_autocorr(x, window: int) -> np.ndarray:
    """AR1 sur fenetre glissante de largeur ``window``."""
    x = np.asarray(x, dtype=float)
    if window < 3 or window > len(x):
        raise ValueError("window doit verifier 3 <= window <= len(x)")
    w = sliding_window_view(x, window)
    a, b = w[:, :-1], w[:, 1:]
    am = a.mean(axis=1, keepdims=True)
    bm = b.mean(axis=1, keepdims=True)
    num = ((a - am) * (b - bm)).sum(axis=1)
    den = np.sqrt(((a - am) ** 2).sum(axis=1) * ((b - bm) ** 2).sum(axis=1))
    out = np.full(num.shape, np.nan)
    nz = den > 0
    out[nz] = num[nz] / den[nz]
    return out


# --------------------------------------------------------------------------- #
# Test de tendance : tau de Kendall (+ p-value par approximation normale)
# --------------------------------------------------------------------------- #
def kendall_tau(x, y):
    """tau-a de Kendall entre ``x`` et ``y`` et sa p-value (approx. normale).

    tau ~ +1 : ``y`` croit de facon monotone avec ``x`` ; tau ~ -1 : decroit.
    Numpy pur, O(n^2) -- adapte aux series d'indicateurs (dizaines a centaines
    de points). Les egalites sont comptees comme non-concordantes (tau-a).
    """
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    n = len(x)
    if n < 3:
        return float("nan"), float("nan")
    c = d = 0
    for i in range(n - 1):
        sx = np.sign(x[i + 1:] - x[i])
        sy = np.sign(y[i + 1:] - y[i])
        prod = sx * sy
        c += int(np.sum(prod > 0))
        d += int(np.sum(prod < 0))
    tau = (c - d) / (0.5 * n * (n - 1))
    z = 3.0 * tau * math.sqrt(n * (n - 1)) / math.sqrt(2.0 * (2 * n + 5))
    p = math.erfc(abs(z) / math.sqrt(2.0))
    return float(tau), float(p)


# --------------------------------------------------------------------------- #
# Recuperation apres perturbation (ralentissement critique direct)
# --------------------------------------------------------------------------- #
def recovery_time(trajectory, baseline: float, tol: float) -> Optional[int]:
    """Premier indice ou ``|x - baseline| <= tol`` (retour a l'equilibre).

    Renvoie ``None`` si le systeme ne revient jamais dans la tolerance — utile
    pour mesurer l'allongement du temps de recuperation pres du pli.
    """
    traj = np.asarray(trajectory, dtype=float)
    within = np.abs(traj - baseline) <= tol
    idx = np.argmax(within)
    if not within[idx]:
        return None
    return int(idx)


# --------------------------------------------------------------------------- #
# Agregat haut niveau
# --------------------------------------------------------------------------- #
def ews_summary(x, window: int, thin_factor: int = 1, detrend_sigma: float = 0.0):
    """Chaine complete : thin -> detrend -> indicateurs roulants -> tendance.

    Renvoie un dict : series ``variance`` / ``ar1`` (sur fenetres glissantes),
    leur ``index`` (centre de fenetre dans la serie amincie), et les tendances
    ``tau_var`` / ``tau_ar1`` (+ p-values). Des tendances positives et
    significatives signent le ralentissement critique.
    """
    s = thin(x, thin_factor)
    if detrend_sigma > 0:
        s = detrend(s, detrend_sigma)
    var = rolling_variance(s, window)
    ar1 = rolling_lag1_autocorr(s, window)
    half = window // 2
    index = np.arange(len(var)) + half
    tau_var, p_var = kendall_tau(index, var)
    tau_ar1, p_ar1 = kendall_tau(index, ar1)
    return {
        "variance": var,
        "ar1": ar1,
        "index": index,
        "tau_var": tau_var,
        "p_var": p_var,
        "tau_ar1": tau_ar1,
        "p_ar1": p_ar1,
    }
