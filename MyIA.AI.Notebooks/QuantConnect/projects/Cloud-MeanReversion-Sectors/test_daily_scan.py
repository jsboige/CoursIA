"""Tests hors QC de `_daily_scan` (#23257) — lecture seule du code de main.py.

Le module sert de banc d'essai a la decision, pas au remplissage : `_daily_scan`
est extraite de `main.py` par AST et compilee seule. Aucun `import
AlgorithmImports`, aucune modification de `sys.modules` : le code source de
`main.py` est execute, rien d'autre.

Modele simplifie du remplissage journalier (hors frais, grille de prix et
arrondis propres a Lean) :
  - les ordres sont emis au scan (30 min apres l'ouverture) ;
  - ils se remplissent tous a la cloture, dans l'ordre d'emission ;
  - une quantite cible vaut int(poids * valeur_portefeuille / prix), et un
    `set_holdings` n'emet que l'ecart avec la position ENCORE DETENUE au moment
    de l'appel (l'ordre de liquidation n'est pas encore rempli).

Lancer : python -I test_daily_scan.py -v
Option : CMR_LEGACY_MAIN=<chemin d'une copie de main.py anterieure> active les
tests de non-regression contre cette copie (fix=off legacy, invariance v1/v2).
"""
import ast
import math
import os
import unittest
from pathlib import Path
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
# CMR_MAIN sert au controle negatif : pointer une copie d'avant patch doit
# faire echouer T1/T2/T6, et seulement ceux-la.
MAIN = Path(os.environ.get("CMR_MAIN", HERE / "main.py"))
LEGACY = Path(os.environ["CMR_LEGACY_MAIN"]) if os.environ.get("CMR_LEGACY_MAIN") else None

ETFS = ["XLK", "XLF", "XLE", "XLV", "XLI", "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC"]

# Parametres des variantes, tels que main.py les pose dans initialize().
PARAMS = {
    "v1": dict(oversold=35, exit=55, n=3, hold=20, stop=999.0, regime=False),
    "v2": dict(oversold=40, exit=60, n=4, hold=15, stop=999.0, regime=True),
    "v3": dict(oversold=40, exit=60, n=4, hold=15, stop=0.08, regime=True),
}


def load_scan(path):
    """Extrait _daily_scan et la compile seule, sans executer le module."""
    src = Path(path).read_text(encoding="utf-8")
    tree = ast.parse(src)
    cls = next(n for n in tree.body
               if isinstance(n, ast.ClassDef) and n.name == "CloudMeanReversionSectors")
    fn = next(n for n in cls.body
              if isinstance(n, ast.FunctionDef) and n.name == "_daily_scan")
    mod = ast.Module(body=[fn], type_ignores=[])
    ast.fix_missing_locations(mod)
    ns = {}
    exec(compile(mod, str(path), "exec"), ns)
    return ns["_daily_scan"]


SCAN = load_scan(MAIN)
SCAN_LEGACY = load_scan(LEGACY) if LEGACY else None


class Ind:
    def __init__(self, value=50.0, ready=True):
        self.current = SimpleNamespace(value=value)
        self.is_ready = ready


class Sec:
    def __init__(self, price):
        self.price = price
        self.has_data = True


class Portfolio:
    def __init__(self, algo):
        self._a = algo

    @property
    def invested(self):
        return any(q != 0 for q in self._a.holdings.values())

    def values(self):
        return []


def run(scan, variant, fix, prices, rsis, holdings, cash, day, entries):
    """Joue un scan et retourne l'algo apres application des ordres."""
    p = PARAMS[variant]
    a = SimpleNamespace(
        _fix=fix,
        is_warming_up=False,
        use_regime_filter=p["regime"],
        rsi_oversold=p["oversold"],
        rsi_exit=p["exit"],
        num_positions=p["n"],
        holding_period=p["hold"],
        stop_loss_pct=p["stop"],
        position_weight=1.0 / p["n"],
        day_count=day,
        sector_etfs=list(ETFS),
        symbols={e: e for e in ETFS},
        securities={e: Sec(pr) for e, pr in prices.items()},
        rsi_indicators={e: Ind(rsis.get(e, 50.0)) for e in ETFS},
        entry_days={e: d for e, (d, _) in entries.items()},
        entry_prices={e: pr for e, (_, pr) in entries.items()},
        holdings=dict(holdings),
        cash=cash,
        _reentries=0,
        orders=[],
        pending=[],
        spy="SPY",
        spy_sma=Ind(0.0, ready=False),   # desactive le filtre de regime
    )
    a.portfolio = Portfolio(a)

    def total_value():
        return a.cash + sum(q * a.securities[e].price for e, q in a.holdings.items() if q)

    def liquidate(symbol=None):
        if symbol is None:
            for e in list(a.holdings):
                if a.holdings.get(e):
                    a.orders.append(("SELL", e, a.holdings[e]))
                    a.pending.append((e, -a.holdings[e]))
            return
        q = a.holdings.get(symbol, 0)
        if q:
            a.orders.append(("SELL", symbol, q))
            a.pending.append((symbol, -q))

    def set_holdings(symbol, weight):
        price = a.securities[symbol].price
        qty = int(weight * total_value() / price)
        delta = qty - a.holdings.get(symbol, 0)
        if delta:
            a.orders.append(("BUY" if delta > 0 else "SELL", symbol, abs(delta)))
            a.pending.append((symbol, delta))

    a.total_value = total_value
    a.liquidate = liquidate
    a.set_holdings = set_holdings

    scan(a)

    for sym, q in a.pending:
        a.holdings[sym] = a.holdings.get(sym, 0) + q
        a.cash -= q * a.securities[sym].price
    a.pending = []
    a.shorts = sorted(s for s, q in a.holdings.items() if q < 0)
    a.held = {s: q for s, q in a.holdings.items() if q}
    a.weight = {s: q * a.securities[s].price / a.total_value() for s, q in a.held.items()}
    return a


# ---------------------------------------------------------------- etats types
P_STOP = {e: 100.0 for e in ETFS}
P_STOP["XLE"] = 90.0          # -10 % contre l'entree a 100 -> stop v3
P_UP = {e: 100.0 for e in ETFS}
P_UP["XLE"] = 110.0
R_OVERSOLD = {"XLE": 30.0}    # sous 35 (v1) et sous 40 (v3)
R_OVERBOUGHT = {"XLE": 70.0}


def state_stop(qty=268, entry_price=100.0, cash=None, entries=None):
    cash = (100000 - qty * entry_price) if cash is None else cash
    return dict(prices=P_STOP, rsis=R_OVERSOLD, holdings={"XLE": qty}, cash=cash,
                day=25, entries=entries or {"XLE": (20, entry_price)})


class StopTests(unittest.TestCase):
    """T1/T2/T6 : le stop doit solder la ligne, sans rachat le meme jour."""

    def test_t1_stop_liquidates_without_rebuy(self):
        st = state_stop()
        a = run(SCAN, "v3", "on", **st)
        self.assertEqual(a.orders, [("SELL", "XLE", 268)])
        self.assertEqual(a.held, {})
        self.assertNotIn("XLE", a.entry_days)
        self.assertEqual(a.shorts, [])

    def test_t2_no_short_even_after_portfolio_slump(self):
        # Quatre lignes a 1/4, portefeuille en chute, brut > 1, et RSI encore
        # survendu sur les quatre : le cas ou un stop re-selectionne restait
        # detenu, et ou liquidate() + set_holdings produisait une vente en trop.
        prices = {e: 90.0 for e in ETFS}
        holdings = {e: 260 for e in ETFS[:4]}
        entries = {e: (0, 100.0) for e in ETFS[:4]}
        rsis = {e: 30.0 for e in ETFS[:4]}
        a = run(SCAN, "v3", "on", prices, rsis, holdings, -4000.0, 30, entries)
        self.assertEqual(a.shorts, [])
        self.assertEqual(len(a.orders), 4)
        for side, etf, qty in a.orders:
            self.assertEqual((side, qty), ("SELL", 260), etf)
        self.assertEqual(a.held, {})
        self.assertEqual(a.entry_days, {})

    def test_t6_slot_freed_by_stop_goes_to_next_candidate(self):
        prices = dict(P_STOP)
        prices["XLF"] = 99.0
        a = run(SCAN, "v3", "on", prices, {"XLE": 30.0, "XLF": 22.0},
                {"XLE": 333}, 100000 - 333 * 100, 25, {"XLE": (20, 100.0)})
        self.assertEqual([o for o in a.orders if o[1] == "XLE"], [("SELL", "XLE", 333)])
        self.assertEqual([o for o in a.orders if o[1] == "XLF"], [("BUY", "XLF", 244)])
        self.assertNotIn("XLE", a.entry_days)
        self.assertIn("XLF", a.entry_days)


class PeriodTests(unittest.TestCase):
    """T3/T4/T5 : la re-entree de periode garde la ligne (correctif #23257)."""

    def test_t3_holding_period_reentry_keeps_full_line(self):
        a = run(SCAN, "v1", "on", P_STOP, R_OVERSOLD, {"XLE": 333},
                100000 - 333 * 100, 25, {"XLE": (5, 100.0)})
        self.assertEqual(a.orders, [("BUY", "XLE", 25)])
        self.assertAlmostEqual(a.weight["XLE"], 1 / 3, places=2)
        self.assertIn("XLE", a.entry_days)
        self.assertEqual(a._reentries, 1)

    def test_t4_signal_exit_without_reselection_liquidates(self):
        a = run(SCAN, "v1", "on", P_UP, R_OVERBOUGHT, {"XLE": 300},
                100000 - 300 * 100, 25, {"XLE": (20, 100.0)})
        self.assertEqual(a.orders, [("SELL", "XLE", 300)])
        self.assertEqual(a.held, {})

    def test_t5_v1_no_short_when_line_is_above_entry(self):
        a = run(SCAN, "v1", "on", P_UP, R_OVERSOLD, {"XLE": 333},
                100000 - 333 * 100, 25, {"XLE": (0, 100.0)})
        self.assertEqual(a.orders, [("SELL", "XLE", 20)])
        self.assertEqual(a.shorts, [])
        self.assertAlmostEqual(a.weight["XLE"], 1 / 3, places=2)


class LegacyTests(unittest.TestCase):
    """fix=off doit reproduire le code d'origine (`github/main`, sha 6cda5ec4)."""

    GOLDEN = {
        # flux mesures sur le code d'origine : liquidate() puis set_holdings()
        "S1_v3_stop_ligne_lourde": [("SELL", "XLE", 333), ("SELL", "XLE", 65)],
        "S1r_v3_stop_poids_entree": [("SELL", "XLE", 268), ("BUY", "XLE", 2)],
        "S1b_v1_periode_au_dessus": [("SELL", "XLE", 333), ("SELL", "XLE", 20)],
        "S2_v1_periode_en_baisse": [("SELL", "XLE", 333), ("BUY", "XLE", 25)],
        "S3_v1_signal_seul": [("SELL", "XLE", 300)],
    }

    def test_fix_off_reproduces_origin_streams(self):
        cases = {
            "S1_v3_stop_ligne_lourde": dict(prices=P_STOP, rsis=R_OVERSOLD,
                                            holdings={"XLE": 333},
                                            cash=100000 - 333 * 100, day=25,
                                            entries={"XLE": (20, 100.0)}),
            "S1r_v3_stop_poids_entree": dict(prices=P_STOP, rsis=R_OVERSOLD,
                                             holdings={"XLE": 268},
                                             cash=100000 - 268 * 100, day=25,
                                             entries={"XLE": (20, 100.0)}),
            "S1b_v1_periode_au_dessus": dict(prices=P_UP, rsis=R_OVERSOLD,
                                             holdings={"XLE": 333},
                                             cash=100000 - 333 * 100, day=25,
                                             entries={"XLE": (0, 100.0)}),
            "S2_v1_periode_en_baisse": dict(prices=P_STOP, rsis=R_OVERSOLD,
                                            holdings={"XLE": 333},
                                            cash=100000 - 333 * 100, day=25,
                                            entries={"XLE": (5, 100.0)}),
            "S3_v1_signal_seul": dict(prices=P_UP, rsis=R_OVERBOUGHT,
                                      holdings={"XLE": 300},
                                      cash=100000 - 300 * 100, day=25,
                                      entries={"XLE": (20, 100.0)}),
        }
        for variant, name in (("v3", "S1_v3_stop_ligne_lourde"),
                              ("v3", "S1r_v3_stop_poids_entree"),
                              ("v1", "S1b_v1_periode_au_dessus"),
                              ("v1", "S2_v1_periode_en_baisse"),
                              ("v1", "S3_v1_signal_seul")):
            with self.subTest(name=name):
                a = run(SCAN, variant, "off", **cases[name])
                self.assertEqual(a.orders, self.GOLDEN[name])

    @unittest.skipUnless(SCAN_LEGACY, "CMR_LEGACY_MAIN non fourni")
    def test_fix_off_matches_legacy_copy_and_on_preserves_v1_v2(self):
        for variant in ("v1", "v2", "v3"):
            with self.subTest(variant=variant, fix="off"):
                cur, _ = path_stream(SCAN, variant, "off")
                old, _ = path_stream(SCAN_LEGACY, variant, "off")
                self.assertEqual(cur, old)
        for variant in ("v1", "v2"):
            with self.subTest(variant=variant, fix="on"):
                cur, _ = path_stream(SCAN, variant, "on")
                old, _ = path_stream(SCAN_LEGACY, variant, "on")
                self.assertEqual(cur, old)


def path(day, i):
    price = 100.0 * (1.0 + 0.12 * math.sin(0.35 * day + i * 0.7))
    rsi = 50.0 + 30.0 * math.sin(0.5 * day + i * 0.9)
    return round(price, 4), round(rsi, 4)


def path_stream(scan, variant, fix, days=60):
    """Chemin synthetique deterministe ; retourne (ordres, jours de stop vus)."""
    holdings, cash, entries, day_count = {}, 100000.0, {}, 0
    stream = []
    for d in range(1, days + 1):
        day_count += 1
        prices, rsis = {}, {}
        for i, e in enumerate(ETFS):
            p, r = path(d, i)
            prices[e] = p
            rsis[e] = r
        a = run(scan, variant, fix, prices, rsis, holdings, cash, day_count, entries)
        stream.extend((d,) + o for o in a.orders)
        holdings = dict(a.held)
        cash = a.cash
        entries = {e: (a.entry_days[e], a.entry_prices[e]) for e in a.entry_days}
    return stream, None


class InvariantTests(unittest.TestCase):
    """Invariants globaux sur 60 seances, toutes variantes, fix=on."""

    def test_no_short_no_orphan_entry_on_path(self):
        for variant in ("v1", "v2", "v3"):
            with self.subTest(variant=variant):
                holdings, cash, entries, day = {}, 100000.0, {}, 0
                for d in range(1, 61):
                    day += 1
                    prices = {e: path(d, i)[0] for i, e in enumerate(ETFS)}
                    rsis = {e: path(d, i)[1] for i, e in enumerate(ETFS)}
                    a = run(SCAN, variant, "on", prices, rsis, holdings, cash, day, entries)
                    self.assertEqual(a.shorts, [], f"{variant} j{d}")
                    self.assertLessEqual(set(a.entry_days), set(a.held), f"{variant} j{d}")
                    self.assertLessEqual(len(a.entry_days), PARAMS[variant]["n"])
                    holdings, cash = dict(a.held), a.cash
                    entries = {e: (a.entry_days[e], a.entry_prices[e]) for e in a.entry_days}


if __name__ == "__main__":
    unittest.main(verbosity=2)
