"""Instrument du verdict pre-enregistre (#19678) -- bootstrap par blocs + placebo.

Le pre-enregistrement de #19678 gele le test avant toute lecture OOS :

    Test de difference de Sharpe par bootstrap par blocs sur les rendements
    nets journaliers (bloc = 21 seances, 10 000 reechantillonnages, graine 42).
    Le verdict ``BEATS`` exige p < 0,05 ET un ecart de Sharpe de signe attendu.
    Un p >= 0,05 rend ``INCONCLUSIVE``, jamais ``BEATS``.
    Placebo : rendements de la baseline decales de 21 seances vers le futur,
    meme metrique recalculee.

Ce fichier est l'instrument de ce test, versionne avec le projet pour que le
verdict soit reproductible : deux courbes d'equity en entree, un verdict en
sortie, aucune place pour un ajustement apres coup.

Usage :

    python verdict_stats.py --strategy equity_strategy.json \\
                            --baseline equity_xle_hold.json
    python verdict_stats.py --selftest

L'auto-test est la partie qui compte : il verifie que l'instrument rend les
TROIS verdicts possibles (BEATS sur un avantage injecte, INCONCLUSIVE sur un
null, et un p eleve sur un desavantage injecte), donc qu'il n'est pas un
dispositif a sens unique.

Les rendements sont lus sur les courbes d'equity, qui sont **nettes de frais**
(LEAN deduit les frais de l'equity) : aucune hypothese de cout n'est rajoutee
ici, et la comparaison strategie/baseline se fait sous le meme harnais.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

PERIODS_PER_YEAR = 252
BLOCK = 21
N_RESAMPLES = 10_000
SEED = 42


def daily_returns(equity: list[float]) -> list[float]:
    """Rendements journaliers simples d'une courbe d'equity."""
    out: list[float] = []
    for prev, cur in zip(equity, equity[1:]):
        if prev <= 0:
            raise ValueError(f"equity non positive ({prev}) -- courbe inutilisable")
        out.append(cur / prev - 1.0)
    return out


def sharpe(returns: list[float], periods_per_year: int = PERIODS_PER_YEAR) -> float:
    """Sharpe annualise. Ecart-type d'echantillon (ddof=1), comme LEAN."""
    n = len(returns)
    if n < 2:
        return 0.0
    mean = sum(returns) / n
    var = sum((r - mean) ** 2 for r in returns) / (n - 1)
    sd = var ** 0.5
    if sd == 0:
        return 0.0
    return mean / sd * (periods_per_year ** 0.5)


def _block_resample_index(n: int, block: int, rng: random.Random) -> list[int]:
    """Indices d'un reechantillonnage par blocs circulaires.

    Les blocs sont preleves sur la serie circulaire : chaque bloc conserve
    l'ordre interne des seances, ce qui preserve l'autocorrelation court terme
    que le bootstrap i.i.d. detruirait.
    """
    idx: list[int] = []
    n_blocks = (n + block - 1) // block
    for _ in range(n_blocks):
        start = rng.randrange(n)
        idx.extend((start + k) % n for k in range(block))
    return idx[:n]


def block_bootstrap_p(
    strategy: list[float],
    baseline: list[float],
    block: int = BLOCK,
    n_resamples: int = N_RESAMPLES,
    seed: int = SEED,
) -> dict:
    """Deux p unilaterales sous reechantillonnage apparie.

    L'appariement est essentiel : strategie et baseline sont reechantillonnees
    avec les MEMES indices, donc le test porte sur la difference des deux
    series seance par seance, pas sur deux marginales independantes.

    Deux p et non une seule : une p unique orientee « la strategie bat » ne
    peut pas conclure un desavantage, et sur un null strict (series
    identiques) la distribution est une masse de points en zero qui rendrait
    p = 1 dans les deux sens. La regle de demi-egalite (une egalite compte
    pour une demi-observation) ramene ce cas a p = 0,5 de part et d'autre,
    ce qui est le comportement attendu d'un test centre sur un null.
    """
    n = min(len(strategy), len(baseline))
    if n < block * 2:
        raise ValueError(f"serie trop courte ({n} seances) pour des blocs de {block}")
    strategy, baseline = strategy[:n], baseline[:n]

    observed = sharpe(strategy) - sharpe(baseline)
    rng = random.Random(seed)
    below = equal = 0
    for _ in range(n_resamples):
        idx = _block_resample_index(n, block, rng)
        diff = sharpe([strategy[i] for i in idx]) - sharpe([baseline[i] for i in idx])
        if diff < 0:
            below += 1
        elif diff == 0:
            equal += 1
    p_beats = (below + 0.5 * equal) / n_resamples
    p_under = (n_resamples - below - 0.5 * equal) / n_resamples
    return {
        "n_sessions": n,
        "block": block,
        "n_resamples": n_resamples,
        "seed": seed,
        "sharpe_strategy": round(sharpe(strategy), 4),
        "sharpe_baseline": round(sharpe(baseline), 4),
        "sharpe_diff": round(observed, 4),
        "p_beats": p_beats,
        "p_under": p_under,
    }


def verdict(p_beats: float, p_under: float, sharpe_diff: float,
            alpha: float = 0.05) -> str:
    """Verdict du pre-enregistrement : p < alpha ET ecart de signe attendu."""
    if sharpe_diff > 0 and p_beats < alpha:
        return "BEATS"
    if sharpe_diff < 0 and p_under < alpha:
        return "UNDERPERFORMS"
    return "INCONCLUSIVE"


def placebo(baseline: list[float], shift: int = BLOCK) -> list[float]:
    """Baseline decalee de `shift` seances vers le futur (placebo gele)."""
    if shift >= len(baseline):
        raise ValueError("decalage superieur a la serie")
    return baseline[shift:]


def _load_series(path: Path) -> list[float]:
    """Extrait une serie de valeurs d'un JSON d'equity.

    Accepte les formes rendues par l'export de courbe (liste de scalaires,
    liste de paires [t, v], ou dict portant 'values'/'series'), pour ne pas
    dependre d'un detail de transport.
    """
    raw = json.loads(path.read_text(encoding="utf-8"))

    def walk(node) -> list[float] | None:
        if isinstance(node, list) and node:
            if all(isinstance(x, (int, float)) for x in node):
                return [float(x) for x in node]
            if all(isinstance(x, (list, tuple)) and len(x) >= 2 for x in node):
                return [float(x[-1]) for x in node]
            for item in node:
                got = walk(item)
                if got:
                    return got
        elif isinstance(node, dict):
            for key in ("values", "series", "equity", "data"):
                if key in node:
                    got = walk(node[key])
                    if got:
                        return got
            for value in node.values():
                got = walk(value)
                if got:
                    return got
        return None

    series = walk(raw)
    if not series:
        raise ValueError(f"aucune serie numerique trouvee dans {path}")
    return series


def _selftest() -> int:
    """Prouve que l'instrument rend les trois verdicts -- faux positifs compris."""
    rng = random.Random(7)
    n = 504
    noise = [rng.gauss(0.0, 0.01) for _ in range(n)]
    base = [0.0002 + e for e in noise]

    # Avantage injecte : meme bruit, derive superieure.
    better = [0.0008 + e for e in noise]
    r_better = block_bootstrap_p(better, base, n_resamples=2000)
    v_better = verdict(r_better["p_beats"], r_better["p_under"], r_better["sharpe_diff"])

    # Null strict : series identiques.
    r_null = block_bootstrap_p(list(base), list(base), n_resamples=2000)
    v_null = verdict(r_null["p_beats"], r_null["p_under"], r_null["sharpe_diff"])

    # Desavantage injecte.
    worse = [0.0002 + e - 0.0006 for e in noise]
    r_worse = block_bootstrap_p(worse, base, n_resamples=2000)
    v_worse = verdict(r_worse["p_beats"], r_worse["p_under"], r_worse["sharpe_diff"])

    print("=== selftest verdict_stats ===")
    for label, res, v in (
        ("avantage injecte", r_better, v_better),
        ("null strict", r_null, v_null),
        ("desavantage injecte", r_worse, v_worse),
    ):
        print(f"  {label:22s} diff={res['sharpe_diff']:+.4f} "
              f"p_beats={res['p_beats']:.4f} p_under={res['p_under']:.4f} -> {v}")

    ok = True
    if v_better != "BEATS":
        print("  ECHEC : un avantage injecte n'est pas detecte"); ok = False
    if v_null != "INCONCLUSIVE":
        print("  ECHEC : un null strict est declare concluant"); ok = False
    if v_worse != "UNDERPERFORMS":
        print("  ECHEC : un desavantage n'est pas classe"); ok = False
    if not (0.2 < r_null["p_beats"] < 0.8):
        print(f"  ECHEC : p du null ({r_null['p_beats']}) hors de la plage attendue"); ok = False

    # Le placebo ne doit pas fabriquer d'avantage sur un null.
    shifted = placebo(list(base))
    r_plac = block_bootstrap_p(list(base)[: len(shifted)], shifted, n_resamples=2000)
    v_plac = verdict(r_plac["p_beats"], r_plac["p_under"], r_plac["sharpe_diff"])
    print(f"  {'placebo sur null':22s} diff={r_plac['sharpe_diff']:+.4f} "
          f"p_beats={r_plac['p_beats']:.4f} -> {v_plac}")
    if v_plac == "BEATS":
        print("  ECHEC : le placebo fabrique un BEATS sur un null"); ok = False

    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strategy", type=Path, help="JSON d'equity de la strategie")
    ap.add_argument("--baseline", type=Path, help="JSON d'equity de la baseline XLE")
    ap.add_argument("--out", type=Path, help="ecrire le resultat JSON ici")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)

    if args.selftest:
        return _selftest()
    if not args.strategy or not args.baseline:
        ap.error("--strategy et --baseline requis (ou --selftest)")

    strat_returns = daily_returns(_load_series(args.strategy))
    base_returns = daily_returns(_load_series(args.baseline))

    main_res = block_bootstrap_p(strat_returns, base_returns)
    main_res["verdict"] = verdict(
        main_res["p_beats"], main_res["p_under"], main_res["sharpe_diff"]
    )

    shifted = placebo(base_returns)
    plac_res = block_bootstrap_p(strat_returns[: len(shifted)], shifted)
    plac_res["verdict"] = verdict(
        plac_res["p_beats"], plac_res["p_under"], plac_res["sharpe_diff"]
    )

    result = {"main": main_res, "placebo": plac_res}
    print(json.dumps(result, indent=2, ensure_ascii=False))
    if args.out:
        args.out.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
