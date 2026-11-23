"""Verdict bootstrap du candidat BTC-VolTarget (#21143, ligue #19821).

Regle pre-enregistree dans l'issue AVANT tout backtest : difference de Sharpe
(annualise, taux sans risque nul) du mode base contre chaque reference
(hold-btc, sixty40), bootstrap CIRCULAIRE par blocs de 21 seances, 10 000
tirages, graine 18921, correction de Holm sur la famille des references.

Entrees : des CSV ``date,valeur`` exportes du graphique shadow (une valeur de
portefeuille par barre journaliere). Les deux series d'une paire sont alignees
sur leurs dates communes ; l'annualisation compte les barres communes par an
(mediane), ce qui rend la comparaison equitable entre calendrier BTC 7/7 et
calendrier boursier.

Usage :
    python significance.py base.csv hold-btc.csv sixty40.csv

Sortie : JSON sur stdout -- Sharpe annuel de chaque serie, difference
annualisee par reference, p-valeur bootstrap unilaterale (H1 : base meilleure)
et p-valeur corrigee de Holm, sur 10 000 tirages a graine fixe.
"""

import csv
import json
import math
import sys
from datetime import date

BLOCK = 21          # blocs de 21 seances (pre-enregistre)
DRAWS = 10_000      # tirages (pre-enregistre)
SEED = 18921        # graine (pre-enregistre)


def load_series(path):
    """Lit un CSV date,valeur -> liste triee de (date, valeur)."""
    rows = []
    with open(path, newline="", encoding="utf-8") as fh:
        for row in csv.reader(fh):
            if not row or row[0].strip().lower().startswith(("date", "#")):
                continue
            raw_date, raw_value = row[0].strip(), row[1].strip()
            if not raw_value:
                continue
            y, m, d = (int(part) for part in raw_date.split("-"))
            rows.append((date(y, m, d), float(raw_value)))
    rows.sort()
    return rows


def daily_returns(rows):
    """Rendements journaliers simples d'une serie de portefeuille."""
    out = []
    for (_, prev), (_, cur) in zip(rows, rows[1:]):
        if prev > 0:
            out.append(cur / prev - 1.0)
    return out


def sharpe(returns, per_year):
    """Sharpe annualise a taux sans risque nul."""
    n = len(returns)
    if n < 2:
        return float("nan")
    mean = sum(returns) / n
    var = sum((r - mean) ** 2 for r in returns) / (n - 1)
    if var <= 0:
        return float("nan")
    return mean / math.sqrt(var) * math.sqrt(per_year)


def bars_per_year(dates):
    """Nombre median de barres par annee civile (annualisation de la serie)."""
    by_year = {}
    for d in dates:
        by_year[d.year] = by_year.get(d.year, 0) + 1
    counts = sorted(by_year.values())
    if not counts:
        return 365.0
    mid = len(counts) // 2
    median = counts[mid] if len(counts) % 2 else (counts[mid - 1] + counts[mid]) / 2
    # Annees tronquees (debut/fin de fenetre) tirent la mediane vers le bas :
    # on rabat vers le calendrier le plus proche, 365 (BTC 7/7) ou 252 (boursier).
    return 365.0 if median > 300 else 252.0


def align(a, b):
    """Intersection des dates de deux series (comparaison appariee)."""
    map_b = dict(b)
    common = sorted(set(dict(a)) & set(map_b))
    return [dict(a)[d] for d in common], [map_b[d] for d in common], common


def circular_block_bootstrap(base_ret, ref_ret, per_year, rng):
    """Bootstrap circulaire APPARIE : meme tirage de blocs pour les deux jambes.

    Les deux strategies vivent sur les memes seances ; resampler chaque jambe
    independamment fabriquerait de la decorrelation artificielle. Un seul jeu
    d'indices de blocs est tire, applique aux deux. Chaque depart de bloc est
    tire INDEPENDAMMENTMENT uniforme dans [0, n) -- des departs systematiquement
    espaces de BLOCK tessellent le cercle quand pgcd(BLOCK, n) = 1 et ne font
    que reordonner la serie entiere (Sharpe invariant par permutation : aucune
    variabilite de tirage, p dans {0, 0.5, 1}), ce n'est pas un bootstrap.
    """
    n = len(base_ret)
    nblocks = -(-n // BLOCK)
    diff_sharpes = []
    for _ in range(DRAWS):
        idx = []
        for _ in range(nblocks):
            start = rng.randrange(n)
            idx.extend((start + j) % n for j in range(BLOCK))
        del idx[n:]
        b = [base_ret[i] for i in idx]
        r = [ref_ret[i] for i in idx]
        diff_sharpes.append(sharpe(b, per_year) - sharpe(r, per_year))
    return diff_sharpes


def p_value_one_sided(diff_sharpes):
    """P-valeur unilaterale H0 : difference <= 0 (base pas meilleure)."""
    # Proportion de tirages ou la difference n'est pas positive ; la moitie des
    # tirages nuls est comptee (convention conservatrice usuelle).
    nonpos = sum(1 for d in diff_sharpes if d <= 0)
    zeros = sum(1 for d in diff_sharpes if d == 0.0)
    return (nonpos - zeros / 2.0) / len(diff_sharpes)


def holm(pvals):
    """Correction de Holm-Bonferroni, ordre croissant des p-valeurs brutes."""
    order = sorted(range(len(pvals)), key=lambda i: pvals[i])
    m = len(pvals)
    adjusted = [0.0] * m
    running = 0.0
    for rank, i in enumerate(order):
        running = max(running, (m - rank) * pvals[i])
        adjusted[i] = min(1.0, running)
    return adjusted


def main(argv):
    if len(argv) < 3:
        print(__doc__)
        return 1
    base_path = argv[1]
    base_rows = load_series(base_path)
    references = argv[2:]

    rng = _Random(SEED)
    result = {
        "block": BLOCK,
        "draws": DRAWS,
        "seed": SEED,
        "base": {
            "series": base_path,
            "bars": len(base_rows),
        },
        "references": [],
    }
    pvals = []
    for ref_path in references:
        ref_rows = load_series(ref_path)
        base_vals, ref_vals, common_dates = align(base_rows, ref_rows)
        base_ret = daily_returns(list(zip(common_dates, base_vals)))
        ref_ret = daily_returns(list(zip(common_dates, ref_vals)))
        per_year = bars_per_year(common_dates)
        s_base = sharpe(base_ret, per_year)
        s_ref = sharpe(ref_ret, per_year)
        diff_sharpes = circular_block_bootstrap(base_ret, ref_ret, per_year, rng)
        p = p_value_one_sided(diff_sharpes)
        pvals.append(p)
        result["references"].append({
            "series": ref_path,
            "common_bars": len(common_dates),
            "per_year": per_year,
            "sharpe_base": round(s_base, 4),
            "sharpe_ref": round(s_ref, 4),
            "diff_sharpe": round(s_base - s_ref, 4),
            "p_bootstrap": round(p, 5),
        })

    adjusted = holm(pvals)
    for entry, adj in zip(result["references"], adjusted):
        entry["p_holm"] = round(adj, 5)
        entry["significant_005"] = adj < 0.05

    print(json.dumps(result, indent=2, default=str))
    return 0


class _Random:
    """Generateur congruentiel lineaire minimal, reproductible partout.

    Le module random de CPython n'est pas garanti stable de version en version
    (Mersenne Twister : OK en pratique, mais l'etat depend de l'implementation).
    Un LCG 64 bits aux constantes de Knuth suffit pour un bootstrap et fige la
    graine 18921 dans un comportement identique sur toute machine.
    """

    def __init__(self, seed):
        self._state = (seed * 6364136223846793005 + 1442695040888963407) % (1 << 64)

    def randrange(self, n):
        self._state = (self._state * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        return (self._state >> 33) % n


if __name__ == "__main__":
    sys.exit(main(sys.argv))
