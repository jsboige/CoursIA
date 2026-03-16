"""
Exercice : Portfolio avec Contraintes de Risque (VaR / CVaR)
============================================================
Traduction Python du notebook Infer-15-Decision-Utility-Money (C#/Infer.NET).

Actifs :
  - Obligataire  : rendement moyen 3 %,  écart-type 2 %
  - Actions      : rendement moyen 8 %,  écart-type 15 %
  - Immobilier   : rendement moyen 5 %,  écart-type 8 %

Hypothèses :
  - Rendements indépendants et gaussiens (comme dans le notebook original)
  - La combinaison linéaire de gaussiennes est une gaussienne :
        mu_p   = w1*mu1 + w2*mu2 + w3*mu3
        sigma_p = sqrt(w1²*s1² + w2²*s2² + w3²*s3²)
  - Niveau de confiance : 95 %  (z = 1.645)
  - VaR  = -(mu_p - z * sigma_p)          [perte en % si positif]
  - CVaR = -(mu_p - sigma_p * phi(z) / (1 - 0.95))
             phi = densité normale standard en z

TODOs couverts :
  1. Modélisation gaussienne de chaque actif
  2. Définition des poids (plusieurs allocations)
  3. Calcul de la distribution du portefeuille
  4. Calcul VaR et CVaR à 95 %
  5. Optimisation : maximiser le rendement sous contrainte CVaR < 5 %
  6. Bonus : grille complète d'allocations + meilleure trouvée

Dépendances standard : numpy, scipy
"""
from __future__ import annotations

import numpy as np
from scipy.stats import norm
from scipy.optimize import minimize
import itertools

# ──────────────────────────────────────────────────────────────────────────────
# TODO 1 : Paramètres des actifs (analogue aux Variable.GaussianFromMeanAndVariance)
# ──────────────────────────────────────────────────────────────────────────────

ASSETS = {
    "Obligataire": {"mu": 0.03, "sigma": 0.02},
    "Actions":     {"mu": 0.08, "sigma": 0.15},
    "Immobilier":  {"mu": 0.05, "sigma": 0.08},
}

CONFIDENCE = 0.95          # Seuil de confiance VaR / CVaR
Z = norm.ppf(CONFIDENCE)   # ≈ 1.6449
PHI_Z = norm.pdf(Z)        # φ(z) ≈ 0.1031
CVAR_CONSTRAINT = 0.05     # Contrainte : CVaR < 5 %


# ──────────────────────────────────────────────────────────────────────────────
# TODO 3 : Distribution du portefeuille (Gaussienne analytique)
# ──────────────────────────────────────────────────────────────────────────────

def portfolio_distribution(weights: np.ndarray) -> tuple[float, float]:
    """
    Calcule mu_p et sigma_p du portefeuille sous hypothèse d'indépendance.

    mu_p    = Σ wᵢ · μᵢ
    sigma_p = √(Σ wᵢ² · σᵢ²)
    """
    mus    = np.array([a["mu"]    for a in ASSETS.values()])
    sigmas = np.array([a["sigma"] for a in ASSETS.values()])
    mu_p    = float(weights @ mus)
    sigma_p = float(np.sqrt((weights**2) @ (sigmas**2)))
    return mu_p, sigma_p


# ──────────────────────────────────────────────────────────────────────────────
# TODO 4 : Calcul VaR et CVaR à 95 %
# ──────────────────────────────────────────────────────────────────────────────

def compute_var(mu_p: float, sigma_p: float) -> float:
    """VaR₉₅ = -(μ - z·σ)  — exprimée en perte (positif = perte)."""
    return -(mu_p - Z * sigma_p)


def compute_cvar(mu_p: float, sigma_p: float) -> float:
    """CVaR₉₅ = -(μ - σ · φ(z) / (1 - α))."""
    return -(mu_p - sigma_p * PHI_Z / (1 - CONFIDENCE))


def analyse_portfolio(weights: np.ndarray, label: str = "") -> dict:
    """Calcule toutes les métriques pour un vecteur de poids."""
    w = np.array(weights, dtype=float)
    assert abs(w.sum() - 1.0) < 1e-6, "Les poids doivent sommer à 1"
    mu_p, sigma_p = portfolio_distribution(w)
    var   = compute_var(mu_p, sigma_p)
    cvar  = compute_cvar(mu_p, sigma_p)
    return {
        "label":   label,
        "w_oblig": w[0],
        "w_act":   w[1],
        "w_immo":  w[2],
        "mu_p":    mu_p,
        "sigma_p": sigma_p,
        "VaR_95":  var,
        "CVaR_95": cvar,
        "ok":      cvar < CVAR_CONSTRAINT,
    }


# ──────────────────────────────────────────────────────────────────────────────
# TODO 6 : Affichage formaté
# ──────────────────────────────────────────────────────────────────────────────

HEADER = (
    f"{'Portefeuille':<28} | {'Oblig':>6} {'Act':>6} {'Immo':>6} "
    f"| {'μ_p':>7} {'σ_p':>7} | {'VaR95':>7} {'CVaR95':>7} | {'CVaR<5%':>7}"
)
SEP = "-" * len(HEADER)


def print_row(r: dict) -> None:
    ok = "✓" if r["ok"] else "✗"
    print(
        f"{r['label']:<28} | "
        f"{r['w_oblig']:>5.0%} {r['w_act']:>5.0%} {r['w_immo']:>5.0%} | "
        f"{r['mu_p']:>6.2%} {r['sigma_p']:>6.2%} | "
        f"{r['VaR_95']:>6.2%} {r['CVaR_95']:>6.2%} | "
        f"{ok:>7}"
    )


# ──────────────────────────────────────────────────────────────────────────────
# TODO 2 : Allocations prédéfinies (analogue au notebook)
# ──────────────────────────────────────────────────────────────────────────────

PRESETS = [
    ("100% Obligataire",           [1.00, 0.00, 0.00]),
    ("100% Actions",               [0.00, 1.00, 0.00]),
    ("100% Immobilier",            [0.00, 0.00, 1.00]),
    ("40% Oblig / 40% Act / 20% Immo", [0.40, 0.40, 0.20]),
    ("60% Oblig / 20% Act / 20% Immo", [0.60, 0.20, 0.20]),
    ("20% Oblig / 30% Act / 50% Immo", [0.20, 0.30, 0.50]),
    ("50% Oblig / 50% Immo",       [0.50, 0.00, 0.50]),
]


# ──────────────────────────────────────────────────────────────────────────────
# TODO 5 : Optimisation (scipy.optimize) — max rendement s.c. CVaR < 5 %
# ──────────────────────────────────────────────────────────────────────────────

def optimize_portfolio() -> dict:
    """
    Maximise μ_p sous contraintes :
      - CVaR₉₅ ≤ 5 %
      - Σ wᵢ = 1
      - wᵢ ≥ 0  (pas de vente à découvert)
    """
    def neg_return(w):
        mu_p, _ = portfolio_distribution(w)
        return -mu_p                          # minimiser ⇒ maximiser rendement

    constraints = [
        {"type": "eq",   "fun": lambda w: w.sum() - 1.0},          # Σ wᵢ = 1
        {"type": "ineq", "fun": lambda w: CVAR_CONSTRAINT            # CVaR ≤ 5 %
                                          - compute_cvar(*portfolio_distribution(w))},
    ]
    bounds = [(0, 1)] * 3

    best = None
    # Multi-start pour éviter les minima locaux
    for w0 in [[1/3, 1/3, 1/3], [0.7, 0.15, 0.15], [0.5, 0.3, 0.2]]:
        res = minimize(neg_return, w0, method="SLSQP",
                       bounds=bounds, constraints=constraints,
                       options={"ftol": 1e-9, "maxiter": 1000})
        if res.success and (best is None or res.fun < best.fun):
            best = res

    if best is None or not best.success:
        raise RuntimeError("Optimisation échouée — aucune solution trouvée.")

    return analyse_portfolio(best.x, "★ Optimum scipy (CVaR ≤ 5%)")


# ──────────────────────────────────────────────────────────────────────────────
# BONUS : Grille discrète (pas = 5 %) → meilleur portefeuille admissible
# ──────────────────────────────────────────────────────────────────────────────

def grid_search(step: float = 0.05) -> dict | None:
    """
    Parcourt toutes les allocations sur une grille 'step' et retourne
    celle qui maximise le rendement sous contrainte CVaR < 5 %.
    """
    ticks = np.arange(0, 1 + step / 2, step)
    best_r = None

    for w1, w2 in itertools.product(ticks, ticks):
        w3 = round(1.0 - w1 - w2, 10)
        if w3 < -1e-9 or w3 > 1 + 1e-9:
            continue
        w = np.array([w1, w2, max(w3, 0.0)])
        if abs(w.sum() - 1.0) > 1e-6:
            continue
        mu_p, sigma_p = portfolio_distribution(w)
        cvar = compute_cvar(mu_p, sigma_p)
        if cvar < CVAR_CONSTRAINT:
            if best_r is None or mu_p > best_r["mu_p"]:
                lbl = f"Grid {w[0]:.0%}/{w[1]:.0%}/{w[2]:.0%}"
                best_r = analyse_portfolio(w, lbl)

    return best_r


# ──────────────────────────────────────────────────────────────────────────────
# MAIN
# ──────────────────────────────────────────────────────────────────────────────

def main() -> None:
    print("=" * len(HEADER))
    print("  PORTFOLIO AVEC CONTRAINTES DE RISQUE  (VaR / CVaR à 95 %)")
    print("=" * len(HEADER))

    # ── Description des actifs ──────────────────────────────────────────────
    print("\n── Actifs disponibles ──")
    print(f"  {'Actif':<14} | {'μ':>6} | {'σ':>6}")
    print(f"  {'-'*14}-+-{'-'*6}-+-{'-'*6}")
    for name, p in ASSETS.items():
        print(f"  {name:<14} | {p['mu']:>5.1%} | {p['sigma']:>5.1%}")

    print(f"\n  Niveau de confiance : {CONFIDENCE:.0%}  →  z = {Z:.4f},  φ(z) = {PHI_Z:.4f}")
    print(f"  Contrainte CVaR     : < {CVAR_CONSTRAINT:.0%}")

    # ── Allocations prédéfinies ─────────────────────────────────────────────
    print(f"\n── Allocations prédéfinies ──\n")
    print(HEADER)
    print(SEP)
    for label, w in PRESETS:
        print_row(analyse_portfolio(np.array(w), label))

    # ── Optimisation scipy ──────────────────────────────────────────────────
    print(f"\n── Optimisation (scipy SLSQP) ──\n")
    print(HEADER)
    print(SEP)
    opt = optimize_portfolio()
    print_row(opt)
    print()
    print(f"  → Poids optimaux  : Obligataire {opt['w_oblig']:.1%} | "
          f"Actions {opt['w_act']:.1%} | Immobilier {opt['w_immo']:.1%}")
    print(f"  → Rendement espéré: {opt['mu_p']:.2%}")
    print(f"  → Volatilité      : {opt['sigma_p']:.2%}")
    print(f"  → VaR  95%        : {opt['VaR_95']:.2%}   (perte max probable)")
    print(f"  → CVaR 95%        : {opt['CVaR_95']:.2%}   (perte moyenne au-delà de VaR)")

    # ── Grille discrète (bonus) ──────────────────────────────────────────────
    print(f"\n── Bonus : Grille discrète (pas 5 %) ──\n")
    print(HEADER)
    print(SEP)
    best_grid = grid_search(step=0.05)
    if best_grid:
        print_row(best_grid)
    else:
        print("  Aucune allocation admissible trouvée sur la grille.")

    # ── Synthèse pédagogique ────────────────────────────────────────────────
    print(f"""
── Synthèse pédagogique ──

  • 100% Actions est la plus rentable ({analyse_portfolio(np.array([0,1,0]),'')['mu_p']:.0%})
    mais sa CVaR = {analyse_portfolio(np.array([0,1,0]),'')['CVaR_95']:.1%} viole la contrainte.

  • 100% Obligataire respecte la contrainte mais n'offre que {analyse_portfolio(np.array([1,0,0]),'')['mu_p']:.0%}.

  • L'optimum se situe à la frontière CVaR = 5 % : on maximise le rendement
    tout en acceptant exactement le risque autorisé.

  • L'Immobilier (5% / 8%) joue un rôle de diversification :
    faible corrélation supposée avec les Actions.

  Formules clés rappelées :
    VaR₉₅  = -(μ_p - 1.645 · σ_p)
    CVaR₉₅ = -(μ_p - σ_p · φ(1.645) / 0.05)
    μ_p    = Σ wᵢ μᵢ           (combinaison linéaire)
    σ_p    = √(Σ wᵢ² σᵢ²)     (indépendance des actifs)
""")


if __name__ == "__main__":
    main()