"""Instrument du verdict pre-enregistre (#19678) -- bootstrap par blocs + placebo.

Le pre-enregistrement de #19678 gele le test avant toute lecture OOS :

    Test de difference de Sharpe par bootstrap par blocs sur les rendements
    nets journaliers (bloc = 21 seances, 10 000 reechantillonnages, graine 42).
    Le verdict ``BEATS`` exige p < 0,05 ET un ecart de Sharpe de signe attendu.
    Un p >= 0,05 rend ``INCONCLUSIVE``, jamais ``BEATS``.
    Placebo : rendements de la baseline decales de 21 seances vers le futur,
    meme metrique recalculee.

Ce fichier est l'instrument de ce test, versionne avec le projet pour que le
verdict soit reproductible : deux courbes en entree, un verdict en sortie,
aucune place pour un ajustement apres coup.

Usage :

    python verdict_stats.py --strategy strat1.json strat2.json \\
                            --baseline baseline_full.json
    python verdict_stats.py --selftest

L'auto-test est la partie qui compte : il verifie que l'instrument rend les
TROIS verdicts possibles (BEATS sur un avantage injecte, INCONCLUSIVE sur un
null, UNDERPERFORMS sur un desavantage injecte), donc qu'il n'est pas un
dispositif a sens unique.

## Pourquoi lire `Return` et non `Equity`

Mesure sur un run de ce projet (2020-08-17 -> 2026-09-30, 2235 points) : le
chart « Strategy Equity » porte DEUX series, et elles n'ont pas la meme maille.

``Equity`` est echantillonnee sur une grille pilotee par le parametre `count`
de la requete (mesure : ~63 000 s d'ecart, soit ~17,5 h) : en tirer des
rendements donne des rendements de 17,5 h, pas journaliers.
``Return`` est exactement journaliere (ecart mesure 86 400 s sur 2222 des 2234
intervalles) et c'est la serie officielle du harnais, en pourcent.

## Les points a zero ne sont pas des seances

La serie est un point par jour CALENDAIRE. Mesure de la repartition par jour de
la semaine, sur les memes 2235 points : lundi 320 points dont **0 non nul**,
dimanche 319 points dont **0 non nul**, et les vraies seances tombent
mardi..samedi (285 a 318 non nuls par jour). Le harnais horodate chaque
rendement a minuit US/Eastern, si bien que le rendement de la seance `D` est
porte par l'horodatage `D+1` : les lundis et dimanches sont donc du remplissage
structurel a 100 %, pas des seances plates.

Les garder ne changerait ni le rendement cumule ni le drawdown (mesures egales
a celles du harnais), mais fausserait le bootstrap gele, qui compte des
**seances** : avec des blocs de 21 points melant 1/3 de remplissage, un bloc
couvre ~15 seances au lieu de 21. On les retire donc, en gardant les zeros
INTERNES a mardi..samedi : ceux-la sont des jours feries (68 mesures sur la
meme fenetre, contre ~54 attendus), et une seance reellement plate a un
rendement de 0 % -- les confondre avec du remplissage serait une erreur dans
l'autre sens.

## Caveat : le niveau du Sharpe du harnais n'est pas reproduit

Le champ ``sharpeRatio`` du harnais ne se reproduit depuis aucune variante de la
serie exportee. Mesure sur deux jambes (baseline `xle_hold` annonce 0,746 ;
premiere tranche strategie annonce 0,204) : tous points/sqrt(252) -> 0,813 et
0,513 ; tous points/sqrt(365) -> 0,978 et 0,618 ; seances/sqrt(252) -> 0,962 et
0,608 ; non nuls/sqrt(252) -> 0,984 et 0,619. Un taux sans risque commun est
aussi refute : il faudrait 1,53 %/an sur une jambe et 0,45 %/an sur l'autre.

En revanche le rendement cumule et le drawdown maximal SE reproduisent (mesures
ci-dessous), donc la serie est la bonne -- c'est la convention d'agregation du
Sharpe qui differe. La comparaison restant appariee et construite a l'identique
des deux cotes, le test garde sa valeur ; le niveau absolu, lui, est rapporte
tel quel par tranche depuis le harnais, et jamais substitue par le notre.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from datetime import datetime, timezone
from pathlib import Path

PERIODS_PER_YEAR = 252
BLOCK = 21
N_RESAMPLES = 10_000
SEED = 42

# Jours de la semaine a jeter : mesure sur 2235 points, lundi et dimanche sont a
# 0 non nul sur 0 (639 points de remplissage structurel). Voir l'en-tete.
JOURS_DE_REMPLISSAGE = frozenset({6, 0})  # dimanche, lundi


def daily_returns(equity: list[float]) -> list[float]:
    """Rendements journaliers simples d'une courbe d'equity.

    Conserve pour les series qui n'exposent pas de rendements (repli), et pour
    l'auto-test.
    """
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


# --------------------------------------------------------------------------
# Lecture des charts
# --------------------------------------------------------------------------


def _as_points(node) -> list[tuple[int, float]] | None:
    """Convertit une liste de paires [t, v] (ou de scalaires) en points horodates."""
    if not isinstance(node, list) or not node:
        return None
    if all(isinstance(x, (int, float)) for x in node):
        return [(i, float(x)) for i, x in enumerate(node)]
    if all(isinstance(x, (list, tuple)) and len(x) >= 2 for x in node):
        # Equity est en [t, o, h, l, c] : on lit le close, dernier element.
        # Return est en [t, v] : le dernier element est la valeur.
        return [(int(x[0]), float(x[-1])) for x in node]
    return None


def _serie_du_chart(doc, nom: str) -> list[tuple[int, float]] | None:
    """Rend la serie `nom` d'un chart, ou None si elle est absente."""
    series = doc.get("series")
    if isinstance(series, dict) and nom in series:
        bloc = series[nom]
        if isinstance(bloc, dict):
            return _as_points(bloc.get("values"))
        return _as_points(bloc)
    return None


def load_points(path: Path) -> list[tuple[int, float]]:
    """Points (horodatage, rendement en fraction) d'un export de chart.

    Prefere la serie ``Return`` -- journaliere et officielle, en pourcent.
    Repli sur ``Equity`` (closes) si elle manque, avec un horodatage
    positionnel : ce repli est une approximation assumee, la grille
    d'``Equity`` etant pilotee par le parametre `count` de la requete.
    """
    doc = json.loads(path.read_text(encoding="utf-8"))

    serie = _serie_du_chart(doc, "Return")
    if serie:
        # Unite '%' mesuree : on convertit en fraction.
        return sorted(((t, v / 100.0) for t, v in serie), key=lambda p: p[0])

    serie = _serie_du_chart(doc, "Equity")
    if serie:
        print(
            f"  [WARN] {path.name}: serie 'Return' absente, repli sur 'Equity' "
            f"-- maille non journaliere, le resultat n'est pas comparable",
            file=sys.stderr,
        )
        closes = [v for _, v in serie]
        ts = [t for t, _ in serie]
        return list(zip(ts[1:], daily_returns(closes)))

    # Dernier repli : une simple liste de valeurs, deja des rendements.
    plat = _as_points(doc)
    if plat:
        print(
            f"  [WARN] {path.name}: ni 'Return' ni 'Equity', lecture d'une liste plate",
            file=sys.stderr,
        )
        return plat
    raise ValueError(f"aucune serie exploitable dans {path}")


def seances(points: list[tuple[int, float]]) -> list[tuple[int, float]]:
    """Retire le remplissage structurel (lundi, dimanche) et dedoublonne."""
    par_ts: dict[int, float] = {}
    for ts, v in points:
        wd = datetime.fromtimestamp(ts, tz=timezone.utc).weekday()
        if wd in JOURS_DE_REMPLISSAGE:
            continue
        if ts in par_ts and not math.isclose(par_ts[ts], v, rel_tol=1e-9, abs_tol=1e-12):
            print(
                f"  [WARN] horodatage {ts} present deux fois avec des valeurs "
                f"differentes ({par_ts[ts]} vs {v}) -- joint de tranche",
                file=sys.stderr,
            )
        par_ts[ts] = v
    return sorted(par_ts.items())


def concatener(chemins: list[Path]) -> list[tuple[int, float]]:
    """Fusionne plusieurs tranches en une serie de seances continue."""
    fusion: list[tuple[int, float]] = []
    for c in chemins:
        pts = seances(load_points(c))
        if pts:
            print(
                f"  {c.name}: {len(pts)} seances "
                f"({datetime.fromtimestamp(pts[0][0], tz=timezone.utc):%Y-%m-%d} -> "
                f"{datetime.fromtimestamp(pts[-1][0], tz=timezone.utc):%Y-%m-%d})"
            )
        fusion.extend(pts)
    # Dedoublonnage final : une seance partagee par deux tranches adjacentes
    # n'apparait qu'une fois (la derniere valeur gagne, l'ecart est signale).
    par_ts: dict[int, float] = {}
    for ts, v in sorted(fusion):
        if ts in par_ts and not math.isclose(par_ts[ts], v, rel_tol=1e-9, abs_tol=1e-12):
            print(f"  [WARN] seance {ts} divergente entre tranches", file=sys.stderr)
        par_ts[ts] = v
    return sorted(par_ts.items())


def aligner(
    strat: list[tuple[int, float]], base: list[tuple[int, float]]
) -> tuple[list[float], list[float], int, int]:
    """Jointure interne sur les horodatages : le test reste apparie."""
    d_base = dict(base)
    ts = [t for t, _ in strat if t in d_base]
    if not ts:
        raise ValueError("aucune seance commune entre strategie et baseline")
    s = [v for t, v in strat if t in d_base]
    b = [d_base[t] for t in ts]
    return s, b, ts[0], ts[-1]


def cumul_et_drawdown(rets: list[float]) -> tuple[float, float]:
    """Rend (rendement cumule, drawdown maximal) -- les deux champs qui se reproduisent."""
    eq, peak, dd = 1.0, 1.0, 0.0
    for r in rets:
        eq *= 1.0 + r
        peak = max(peak, eq)
        dd = min(dd, eq / peak - 1.0)
    return eq - 1.0, dd


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

    # --- Chargement : le decodage de chart est la partie qui a un vrai piege ---
    # Un lundi et un dimanche a zero doivent tomber ; un zero interne reste.
    lundi = 1597622400      # 2020-08-17 04:00Z, un lundi
    jour = 86400
    points_factices = [
        (lundi, 0.0),
        (lundi + jour, 0.01),          # mardi : garde
        (lundi + 2 * jour, 0.0),       # mercredi a plat : garde (ferie ou seance plate)
        (lundi + 6 * jour, 0.0),       # dimanche : jete
    ]
    gardees = seances(points_factices)
    print(f"  {'filtre des seances':22s} 4 points -> {len(gardees)} "
          f"(attendu 2 : mardi + mercredi)")
    if [v for _, v in gardees] != [0.01, 0.0]:
        print("  ECHEC : le filtre des seances ne garde pas les bons points"); ok = False

    # Le rendement cumule doit ignorer le remplissage : c'est ce qui se reproduit
    # chez le harnais, et c'est le controle du filtre.
    brut = 1.0
    for _, v in points_factices:
        brut *= 1.0 + v
    garde = 1.0
    for _, v in gardees:
        garde *= 1.0 + v
    if not math.isclose(brut, garde, rel_tol=1e-12):
        print("  ECHEC : le filtre change le rendement cumule"); ok = False

    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strategy", type=Path, nargs="+",
                    help="un ou plusieurs JSON de tranches strategie")
    ap.add_argument("--baseline", type=Path, nargs="+",
                    help="un ou plusieurs JSON de tranches baseline XLE")
    ap.add_argument("--out", type=Path, help="ecrire le resultat JSON ici")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)

    if args.selftest:
        return _selftest()
    if not args.strategy or not args.baseline:
        ap.error("--strategy et --baseline requis (ou --selftest)")

    print("== Chargement ==")
    strat_pts = concatener(args.strategy)
    base_pts = concatener(args.baseline)
    print(f"  STRAT {len(strat_pts)} seances ; BASE {len(base_pts)} seances")

    s, b, t0, t1 = aligner(strat_pts, base_pts)
    print(f"  aligne sur {len(s)} seances communes "
          f"({datetime.fromtimestamp(t0, tz=timezone.utc):%Y-%m-%d} -> "
          f"{datetime.fromtimestamp(t1, tz=timezone.utc):%Y-%m-%d})")

    cum_s, dd_s = cumul_et_drawdown(s)
    cum_b, dd_b = cumul_et_drawdown(b)
    print(f"  cumul strategie {cum_s * 100:+.3f} %  drawdown {dd_s * 100:.3f} %")
    print(f"  cumul baseline  {cum_b * 100:+.3f} %  drawdown {dd_b * 100:.3f} %")

    main_res = block_bootstrap_p(s, b)
    main_res["verdict"] = verdict(
        main_res["p_beats"], main_res["p_under"], main_res["sharpe_diff"]
    )
    main_res["cumul_strategy"] = round(cum_s, 6)
    main_res["cumul_baseline"] = round(cum_b, 6)

    shifted = placebo(b)
    plac_res = block_bootstrap_p(s[: len(shifted)], shifted)
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
