"""Mesure de l'ecart entre le carnet QC-Py-45 et le backtest LEAN de ce projet.

Copie declaree du moteur vectorise du carnet QC-Py-45 (cellules de donnees et de
simulation), restreinte aux variantes que ``main.py`` sait jouer. Motif de la copie :
rejouer le moteur du carnet a l'identique, puis lui ajouter deux bascules qui
reproduisent, une par une, les deux differences d'execution de LEAN :

- ``mode_stop`` :
    - ``"carnet"`` : le stop est actif tous les jours, y compris le jour d'un ordre ;
    - ``"ouvertes"`` : pas de stop le jour ou la ligne est ouverte ;
    - ``"ordres"`` : pas de stop le jour de tout ordre sur la ligne, ouverture ou
      redimensionnement (comportement de ``main.py``, qui annule le stop avant l'ordre
      ``MarketOnOpen`` et le repose a son execution) ;
- ``cc_lendemain`` : la seance a -3 % n'est connue qu'a la cloture ; la liquidation
  part a l'ouverture suivante et le retour se fait a l'ouverture d'apres.

Les entrees sont celles du chemin momentum par defaut ; ``choix`` y substitue une autre
regle, par exemple ``entrees_aleatoires(graine)``, le tirage du carnet (une suite par
simulation, un tirage de 10 lignes par rebalancement), que ``ablation_lean.py`` utilise.

Fenetre 2015-01-02 -> 2026-07-31, liquidites remunerees a 0 %, comme les backtests LEAN.
Donnees yfinance ajustees : un nouveau telechargement peut decaler les chiffres de
quelques centiemes de point.

Lancer : ``python mesure_ecart_carnet.py`` (numpy, pandas, yfinance).
"""
from __future__ import annotations

import numpy as np
import pandas as pd
import yfinance as yf

GROUPES = {
    "Actions US": ["XLB", "XLE", "XLF", "XLI", "XLK", "XLP", "XLU", "XLV", "XLY", "IWM"],
    "Actions hors US": ["EFA", "EEM", "EWJ", "VGK"],
    "Obligations": ["TLT", "IEF", "LQD", "HYG", "TIP"],
    "Matieres premieres et immobilier": ["GLD", "SLV", "DBC", "VNQ"],
}
TICKERS = [t for g in GROUPES.values() for t in g]
DEBUT, FIN = "2015-01-02", "2026-07-31"
# variante : (poids par ligne, stops, plafond de groupe, coupe-circuit)
VARIANTES = {"nokernel": (0.10, False, False, False), "exposure90": (0.09, False, False, False),
             "kernel_nocb": (0.09, True, True, False), "kernel": (0.09, True, True, True)}
FRAIS = 0.0005
SEUIL_CC = -0.03
MULT_STOP = 2.0
PLAFOND_GROUPE = 0.40
TOP_N = 10


def charger() -> dict:
    """Telecharge les donnees et prepare les tableaux du moteur, comme le carnet."""
    raw = yf.download(TICKERS, start="2014-01-01", end="2026-08-01",
                      auto_adjust=True, progress=False)
    o, h, l, c = (raw[k][TICKERS] for k in ("Open", "High", "Low", "Close"))
    dates = c.loc[DEBUT:FIN].index
    veille = c.shift(1)
    tr = pd.concat([h - l, (h - veille).abs(), (l - veille).abs()]).groupby(level=0).max()
    atr14 = tr.rolling(14).mean()
    mom = c.shift(5) / c.shift(131) - 1
    semaine = dates.to_series().dt.to_period("W")
    return {
        "dates": dates,
        "rebal": np.asarray(semaine.ne(semaine.shift(1)).values),
        "groupe": np.array([next(i for i, g in enumerate(GROUPES.values()) if t in g)
                            for t in TICKERS]),
        "o": o.loc[dates].values,
        "l": l.loc[dates].values,
        "c": c.loc[dates].values,
        "atr": atr14.shift(1).loc[dates].values,
        "mom": mom.shift(1).loc[dates].values,
    }


def poids_cibles(d: dict, lignes: np.ndarray, w_ligne: float, plafond: bool) -> np.ndarray:
    w = np.zeros(len(TICKERS))
    w[lignes] = w_ligne
    if plafond:
        for g in np.unique(d["groupe"]):
            m = (d["groupe"] == g) & (w > 0)
            if w[m].sum() > PLAFOND_GROUPE + 1e-12:
                w[m] *= PLAFOND_GROUPE / w[m].sum()
    return w


def entrees_aleatoires(graine: int):
    """Tirage du carnet : une suite par simulation, 10 lignes par rebalancement."""
    rng = np.random.default_rng(graine)
    return lambda t: rng.choice(len(TICKERS), TOP_N, replace=False)


def simuler(d: dict, variante: str, mode_stop: str = "carnet",
            cc_lendemain: bool = False, choix=None) -> tuple[np.ndarray, dict]:
    """Moteur du carnet, avec les deux bascules decrites en tete de fichier."""
    w_ligne, stops, plafond, coupe = VARIANTES[variante]
    n = len(TICKERS)
    cash, parts = 1.0, np.zeros(n)
    stop = np.full(n, np.nan)
    stoppee = np.zeros(n, bool)
    lignes, reentree, liquider = None, False, False
    valeur = np.empty(len(d["dates"]))
    veille = 1.0
    journal = {"stops": 0, "stops_evites": 0, "coupures": []}
    for t in range(len(d["dates"])):
        o, l, c = d["o"][t], d["l"][t], d["c"][t]
        sans_stop = np.zeros(n, bool)
        if d["rebal"][t]:
            lignes = choix(t) if choix is not None else np.argsort(-d["mom"][t])[:TOP_N]
            stoppee[:] = False
        if liquider:
            # Coupe-circuit LEAN : liquidation a l'ouverture qui suit la seance a -3 %.
            liquider = False
            cash += np.sum(parts * o) * (1 - FRAIS)
            parts[:] = 0.0
            stop[:] = np.nan
            reentree = True
        elif d["rebal"][t] or reentree:
            reentree = False
            w = poids_cibles(d, lignes, w_ligne, plafond)
            w[stoppee] = 0.0
            v_ouv = cash + np.sum(parts * o)
            ecart = w * v_ouv / o - parts
            vente = np.minimum(ecart, 0.0)
            cash -= np.sum(vente * o) * (1 - FRAIS)
            parts += vente
            achat = np.maximum(ecart, 0.0)
            besoin = np.sum(achat * o) * (1 + FRAIS)
            if besoin > cash:
                achat *= cash / besoin
            cash -= np.sum(achat * o) * (1 + FRAIS)
            ouverte = (achat > 0) & (parts <= 0)
            parts += achat
            if stops:
                niveau = o - MULT_STOP * d["atr"][t]
                stop = np.where(ouverte, niveau, np.where(parts > 0, stop, np.nan))
            if mode_stop == "ouvertes":
                sans_stop = ouverte
            elif mode_stop == "ordres":
                sans_stop = (vente < 0) | (achat > 0)
        if stops:
            arme = (parts > 0) & (l <= stop)
            touche = arme & ~sans_stop
            journal["stops_evites"] += int((arme & sans_stop).sum())
            if touche.any():
                prix = np.minimum(o, stop)
                cash += np.sum(parts[touche] * prix[touche]) * (1 - FRAIS)
                parts[touche] = 0.0
                stop[touche] = np.nan
                stoppee |= touche
                journal["stops"] += int(touche.sum())
        v = cash + np.sum(parts * c)
        if coupe and v / veille - 1 <= SEUIL_CC and parts.sum() > 0:
            journal["coupures"].append(str(d["dates"][t].date()))
            if cc_lendemain:
                stop[:] = np.nan          # main.py annule les stops des la detection
                liquider = True
            else:
                cash += np.sum(parts * c) * (1 - FRAIS)
                parts[:] = 0.0
                stop[:] = np.nan
                reentree = True
                v = cash
        valeur[t] = v
        veille = v
    return valeur, journal


def mesures(valeur: np.ndarray) -> tuple[float, float, float]:
    """CAGR, Sharpe a taux nul, drawdown maximal."""
    r = np.diff(valeur) / valeur[:-1]
    dd = valeur / np.maximum.accumulate(valeur) - 1
    return valeur[-1] ** (252 / len(valeur)) - 1, r.mean() / r.std() * np.sqrt(252), dd.min()


REGLAGES = [
    ("kernel_nocb", "carnet", False, "carnet"),
    ("kernel_nocb", "ouvertes", False, "pas de stop le jour de l'ouverture"),
    ("kernel_nocb", "ordres", False, "pas de stop le jour d'un ordre (LEAN)"),
    ("kernel", "carnet", False, "carnet"),
    ("kernel", "carnet", True, "coupe-circuit le lendemain"),
    ("kernel", "ordres", False, "pas de stop le jour d'un ordre"),
    ("kernel", "ouvertes", True, "ouverture seule + coupe-circuit le lendemain"),
    ("kernel", "ordres", True, "les deux bascules (LEAN)"),
]

if __name__ == "__main__":
    donnees = charger()
    print(f"{len(donnees['dates'])} seances du {donnees['dates'][0].date()} "
          f"au {donnees['dates'][-1].date()}")
    for variante, mode, ccl, nom in REGLAGES:
        val, jrn = simuler(donnees, variante, mode, ccl)
        cagr, sharpe, mdd = mesures(val)
        print(f"{variante:12s} {nom:46s} CAGR {100 * cagr:+.2f} %  Sharpe {sharpe:.3f}  "
              f"MaxDD {100 * mdd:+.1f} %  stops {jrn['stops']:4d} "
              f"(evites {jrn['stops_evites']:3d})  coupures {len(jrn['coupures'])}")
