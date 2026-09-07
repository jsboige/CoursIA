"""Diagnostic du biais de frontiere kappa_c (case 3 iceberg, #8182) : artefact de mesure ou residu structurel ?

La case « p_hat auto-referent » de la matrice de dissociations
(``docs/ict/dissociations-matrix.md``) a rendu ``TESTE (CONFIRMED)`` avec
``kappa_c`` observe a 0.080 pour une prediction lineaire ``KAPPA_C_PREDICTED
= (1 - a) / a_hat ~= 0.053`` (biais +0.027, 5/5 graines, PR #9567). La note
de la matrice laisse ouverte la question : ce biais est-il **structurel**
(la boucle fermee cause une derive que la theorie lineaire ne capture pas)
ou un **artefact de calibration de la procedure de mesure** ?

Ce module pre-enregistre la reponse AVANT le re-run :

Prediction pre-enregistree
-------------------------
Le critere utilise par la case n'est PAS la frontiere asymptotique
``|g(kappa)| = 1`` mais un critere FINI : ratio ``R_T / R_0 >= 5`` apres
``T = 200`` pas, evalue sur une grille de maille Irreguliere
(..., 0.05, 0.06, 0.08, ...). Deux frontieres theoriques pre-enregistrees :

1. **Frontiere deterministe finie** : sans bruit, ``R_T / R_0 = g(kappa)^T``
   exactement (chaque trajectoire croit du meme facteur), avec
   ``g(kappa) = a + kappa * a_hat``. Le critere fini est franchi quand
   ``g^T = 5``, soit ``g* = 5^(1/T)`` et::

       KAPPA_STAR_FINITE = (5^(1/200) - 0.95) / 0.95 ~= 0.06113

2. **Frontiere bruitee finie** : avec bruit additif ``sigma = 0.05`` et
   ``R_0^2 = E[x_0^2] = 1/3`` (x_0 ~ U(-1, 1)), ``E[R_T^2]`` cumule la
   croissance deterministe et la variance du bruit accumulee::

       E[R_T^2] = g^(2T) R_0^2 + sigma^2 (g^(2T) - 1) / (g^2 - 1)

   Le critere fini ``E[R_T^2] = 25 R_0^2`` definit ``KAPPA_STAR_NOISY``,
   resolu numeriquement (~= 0.060, voir constante calculee au chargement).

Grille fine et bande de verdict
-------------------------------
La grille fine est **uniforme** sur ``[0.050, 0.080]`` (pas 0.002), donc
volontairement plus large que la bande de verdict des deux cotes : les
points sous 0.058 et au-dela de 0.064 servent de **sentinelles**. Une
grille confinee a la bande rendrait le test tautologique -- un decalage
structurel a 0.07 y serait lu « dans la bande ». La tolerance de la bande
est **une maille fine entiere** (pas la demi-maille) : l'estimateur
« premier point de grille au-dessus du seuil » peut overshooter le vrai
franchissement d'une maille complete par construction, la demi-maille
sous-couvrirait cette quantification.

Verdicts (trois issues, pre-enregistrees) :

- ``ARTEFACT_DE_MESURE`` : la frontiere mesuree sur grille FINE tombe dans
  la bande ``[KAPPA_STAR_NOISY - maille, KAPPA_STAR_FINITE + maille]``
  (maille = pas de la grille fine) sur >= 4/5 graines -- le biais +0.027
  est alors integre par le critere fini (frontiere finie + arrondi a la
  maille de la grille d'origine : 0.06 < kappa* < 0.08 -> premiere maille
  franchissable 0.08), PAS par la boucle.
- ``STRUCTURAL_RESIDUE`` : la frontiere fine reste hors de la bande sur
  >= 2 graines -- il existe un decalage que ni la frontiere finie ni le
  bruit n'expliquent.
- ``INCONCLUSIF_INSTRUMENT`` : un controle echoue (delieur ``kappa = 0``
  non borne, ou fausse divergence a ``kappa = 0.03`` sous frontiere) --
  l'instrument ne permet pas de trancher.

Null adversarial : la facon la plus directe de tuer la prediction
``ARTEFACT_DE_MESURE`` est que la frontiere fine tombe sur une sentinelle
(sous 0.058 ou au-dela de 0.064) -- si le +0.027 etait structurel, la
frontiere fine resterait autour de 0.07-0.08, hors bande, et la note
« biais structurel ? » de la matrice gagnerait un support numerique.

Substrat : numpy uniquement, CPU-only. Reutilise ``ict.phat_self_reference``
(grille, simulateur, seuils -- aucun code duplique) : le re-run se fait sur
le MEME instrument que la case d'origine, seuls changent la grille (fine)
et le critere de lecture.
"""

from __future__ import annotations

from typing import Dict, Sequence, Tuple

import numpy as np

from ict.phat_self_reference import (
    HORIZON_T,
    KAPPA_C_PREDICTED,
    RATIO_DIVERGENT,
    EnvironmentParams,
    stability_scan,
)


# --------------------------------------------------------------------------- #
#  Frontieres pre-enregistrees (formules fermee + resolution numerique)         #
# --------------------------------------------------------------------------- #

# Frontiere deterministe finie : g*^T = RATIO_DIVERGENT avec g = a + kappa a_hat.
_PARAMS = EnvironmentParams()  # a = a_hat = 0.95, sigma = 0.05, b = 0


def kappa_star_finite(
    ratio: float = RATIO_DIVERGENT,
    horizon: int = HORIZON_T,
    params: EnvironmentParams = _PARAMS,
) -> float:
    """Frontiere du critere fini deterministe : ``g(kappa)^T = ratio``."""
    g_star = ratio ** (1.0 / horizon)
    return (g_star - params.a) / params.a_hat


def kappa_star_noisy(
    ratio: float = RATIO_DIVERGENT,
    horizon: int = HORIZON_T,
    params: EnvironmentParams = _PARAMS,
    r0_sq: float = 1.0 / 3.0,
) -> float:
    """Frontiere du critere fini bruite (bissection, precision 1e-9).

    Resout ``E[R_T^2] = ratio^2 * R_0^2`` avec, pour ``g != 1`` :

        E[R_T^2] = g^(2T) R_0^2 + sigma^2 (g^(2T) - 1) / (g^2 - 1)

    (les deux termes viennent de la recursion lineaire ``x_{t+1} = g x_t +
    epsilon`` : la variance du terme initial croit comme ``g^(2T)``, celle
    du bruit accumule comme une serie geometrique). ``x_0 ~ U(-1, 1)``
    donne ``R_0^2 = 1/3``.
    """
    target = (ratio ** 2) * r0_sq

    def expected_r_t_sq(kappa: float) -> float:
        g = params.a + kappa * params.a_hat
        g2t = g ** (2 * horizon)
        if abs(g * g - 1.0) < 1e-12:
            var_noise = params.sigma ** 2 * horizon  # limite g -> 1
        else:
            var_noise = params.sigma ** 2 * (g2t - 1.0) / (g * g - 1.0)
        return g2t * r0_sq + var_noise

    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if expected_r_t_sq(mid) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


# Constantes pre-enregistrees au chargement (reproductibles, affichees par
# ``run_full_protocol`` et verrouillees par les tests).
KAPPA_STAR_FINITE: float = kappa_star_finite()   # ~ 0.06113
KAPPA_STAR_NOISY: float = kappa_star_noisy()     # ~ 0.0602

# Grille fine UNIFORME [0.050, 0.080], pas 0.002 — volontairement plus
# large que la bande de verdict : les points hors bande (sous 0.058,
# au-dela de 0.064) sont les sentinelles du null adversarial. Confiner la
# grille a la bande rendrait le test tautologique.
FINE_STEP: float = 0.002
FINE_GRID: Tuple[float, ...] = tuple(
    round(x, 4) for x in np.arange(0.050, 0.080 + 1e-9, FINE_STEP)
)

# Points de controle (hors bande) : delieur causal + regime stable sous
# frontiere (une fausse divergence a 0.03 dirait que le bruit fabrique des
# franchissements n'importe ou -> instrument non concluant).
CONTROL_KAPPA_DELIEUR: float = 0.0
CONTROL_KAPPA_STABLE: float = 0.03

# Grille d'origine de la case (re-jouee pour P1 : la premiere maille
# au-dessus des frontieres pre-enregistrees doit etre 0.08).
ORIGINAL_GRID: Tuple[float, ...] = (
    0.0, 0.02, 0.04, 0.05, 0.06, 0.08, 0.10, 0.15, 0.20, 0.30, 0.50, 1.00,
)

SEEDS: Tuple[int, ...] = (0, 1, 7, 42, 99)


# --------------------------------------------------------------------------- #
#  Mesure : frontiere observee sur une grille donnee                            #
# --------------------------------------------------------------------------- #


def observed_boundary(scan: Dict[str, np.ndarray]) -> np.ndarray:
    """Premier kappa de la grille ou le ratio median franchit RATIO_DIVERGENT.

    Renvoie un tableau (une valeur par graine) ; si aucune maille ne
    franchit, la valeur est la derniere maille de la grille (convention de
    ``estimate_stability_boundary`` du module d'origine).
    """
    kappa_grid = scan["kappa_grid"]
    ratio_median = scan["ratio_median"]
    n_seeds = ratio_median.shape[0]
    out = np.empty(n_seeds, dtype=np.float64)
    for i in range(n_seeds):
        above = np.where(ratio_median[i] >= RATIO_DIVERGENT)[0]
        out[i] = float(kappa_grid[above[0]]) if len(above) else float(kappa_grid[-1])
    return out


# --------------------------------------------------------------------------- #
#  Verdict : trois issues pre-enregistrees                                      #
# --------------------------------------------------------------------------- #


def diagnose(
    scan_original: Dict[str, np.ndarray],
    scan_fine: Dict[str, np.ndarray],
    scan_control: Dict[str, np.ndarray],
) -> Dict[str, object]:
    """Compose le verdict pre-enregistre a partir des trois scans.

    ``scan_original`` : grille d'origine (P1 -- coherences avec
    l'observation historique 0.080). ``scan_fine`` : grille fine (P2, le
    test qui tranche). ``scan_control`` : delieur + regime stable
    (controles d'instrument).
    """
    # Tolerance = UNE maille fine entiere (pas la demi-maille) : l'estimateur
    # « premier point de grille au-dessus du seuil » peut overshooter le vrai
    # franchissement d'une maille complete par construction.
    tol = FINE_STEP
    band_lo = KAPPA_STAR_NOISY - tol
    band_hi = KAPPA_STAR_FINITE + tol

    boundary_original = observed_boundary(scan_original)
    boundary_fine = observed_boundary(scan_fine)

    n_seeds = len(boundary_fine)
    n_in_band = int(np.sum((boundary_fine >= band_lo) & (boundary_fine <= band_hi)))

    # Controles d'instrument.
    kg = scan_control["kappa_grid"]
    rm = scan_control["ratio_median"]
    delieur_ratios = rm[:, int(np.where(np.isclose(kg, CONTROL_KAPPA_DELIEUR))[0][0])]
    delieur_stable = bool(np.all(delieur_ratios < RATIO_DIVERGENT))
    stable_ratios = rm[:, int(np.where(np.isclose(kg, CONTROL_KAPPA_STABLE))[0][0])]
    no_false_positive = bool(np.all(stable_ratios < RATIO_DIVERGENT))

    if not (delieur_stable and no_false_positive):
        verdict = "INCONCLUSIF_INSTRUMENT"
        detail = (
            f"controles echoues : delieur_stable={delieur_stable} "
            f"(max {float(np.max(delieur_ratios)):.2f}), "
            f"no_false_positive@0.03={no_false_positive} "
            f"(max {float(np.max(stable_ratios)):.2f})"
        )
    elif n_in_band >= max(1, n_seeds - 1):
        verdict = "ARTEFACT_DE_MESURE"
        detail = (
            f"frontiere fine {n_in_band}/{n_seeds} graines dans la bande "
            f"[{band_lo:.4f}, {band_hi:.4f}] (median "
            f"{float(np.median(boundary_fine)):.4f}) ; grille d'origine : "
            f"premiere maille au-dessus de kappa* = "
            f"{float(np.min([k for k in ORIGINAL_GRID if k >= KAPPA_STAR_NOISY])):.2f}"
            f" -> le biais +0.027 est integre par critere fini + maille."
        )
    else:
        verdict = "STRUCTURAL_RESIDUE"
        detail = (
            f"frontiere fine hors bande sur {n_seeds - n_in_band}/{n_seeds} "
            f"graines (median {float(np.median(boundary_fine)):.4f}, bande "
            f"[{band_lo:.4f}, {band_hi:.4f}]) : decalage ni fini ni bruit."
        )

    return {
        "verdict": verdict,
        "verdict_detail": detail,
        "kappa_star_finite": KAPPA_STAR_FINITE,
        "kappa_star_noisy": KAPPA_STAR_NOISY,
        "kappa_c_theory_asymptotic": KAPPA_C_PREDICTED,
        "band": [band_lo, band_hi],
        "boundary_original_per_seed": boundary_original.tolist(),
        "boundary_fine_per_seed": boundary_fine.tolist(),
        "n_in_band": n_in_band,
        "delieur_stable": delieur_stable,
        "no_false_positive_stable": no_false_positive,
    }


# --------------------------------------------------------------------------- #
#  Protocole complet                                                            #
# --------------------------------------------------------------------------- #


def run_full_protocol(
    seeds: Sequence[int] = SEEDS,
) -> Dict[str, object]:
    """Execute les trois scans (original, fin, controles) et rend le verdict.

    Appel unique du notebook ; tous les seuils et frontieres sont
    pre-enregistres au module (tests verrouillent leur valeur).
    """
    control_grid = np.unique(
        np.array([CONTROL_KAPPA_DELIEUR, CONTROL_KAPPA_STABLE], dtype=float)
    )

    scan_original = stability_scan(kappa_grid=ORIGINAL_GRID, seeds=seeds)
    scan_fine = stability_scan(kappa_grid=FINE_GRID, seeds=seeds)
    scan_control = stability_scan(kappa_grid=control_grid, seeds=seeds)

    verdict = diagnose(scan_original, scan_fine, scan_control)

    return {
        "frontieres_pre_enregistrees": {
            "kappa_star_finite": KAPPA_STAR_FINITE,
            "kappa_star_noisy": KAPPA_STAR_NOISY,
            "kappa_c_asymptotique": KAPPA_C_PREDICTED,
        },
        "fine_grid": list(FINE_GRID),
        "verdict": verdict,
        "ratio_median_fine": scan_fine["ratio_median"].tolist(),
        "ratio_median_original": scan_original["ratio_median"].tolist(),
        "ratio_median_control": scan_control["ratio_median"].tolist(),
        "seeds": list(seeds),
    }


if __name__ == "__main__":
    import json
    from pathlib import Path

    out = run_full_protocol()
    dest = Path(__file__).resolve().parent / "results" / "phat_causal_unlink_results.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(
        json.dumps(out, indent=2, ensure_ascii=False, default=float) + "\n",
        encoding="utf-8",
    )
    v = out["verdict"]
    print(f"KAPPA_STAR_FINITE = {KAPPA_STAR_FINITE:.6f}")
    print(f"KAPPA_STAR_NOISY  = {KAPPA_STAR_NOISY:.6f}")
    print(f"verdict           = {v['verdict']}")
    print(f"detail            = {v['verdict_detail']}")
    print(f"results           = {dest}")
