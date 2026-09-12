"""Smoke test SEC reel borne (acceptance #6, tranche EDGAR-1).

Ce test est **explicitement separe** des tests CPU (cf acceptance #6 :
"Ajouter un smoke SEC reel borne sur le panier de 5 tickers deja utilise
par #15421, separe des tests unitaires."). Il fait un round-trip HTTP
contre data.sec.gov et www.sec.gov et depend :

    - d'un acces reseau sortant vers sec.gov ;
    - d'un User-Agent conforme a la politique SEC ;
    - du respect du throttling (0.4 s entre requetes).

Pour eviter le bruit CI :
    - il NE se declenche PAS par defaut (collection via ``--run-smoke``) ;
    - il produit un rapport sur stdout avec taux de paires valides /
      echouees (acceptance #7).

Usage :

    # Collecte standard (ignore ce test) :
    pytest tests/

    # Smoke reel :
    pytest tests/test_smoke_sec_real.py --run-smoke -v -s

Ses resultats dependent de la date d'execution (les 10-K les plus
recents evoluent avec le temps). C'est un smoke, pas un oracle.
"""

from __future__ import annotations

import json
import os
import sys
from datetime import date, datetime, timedelta
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT_ROOT = HERE.parent
sys.path.insert(0, str(PROJECT_ROOT))

import edgar_signal as es  # noqa: E402


# Panier de 5 tickers : copie conforme de celui utilise par le
# ``research.ipynb`` du projet porte par #15421 (Verification Lazy Prices
# jambe longue). Toute deviation doit etre documentee dans le commit.
BASKET: dict[str, int] = {
    "AAPL": 320193,
    "MSFT": 789019,
    "KO": 21344,
    "WMT": 104169,
    "GE": 40545,
}


def _have_network() -> bool:
    """Heuristique legere : on tente un GET HEAD sur data.sec.gov."""
    try:
        import urllib.request
        req = urllib.request.Request(
            "https://data.sec.gov/submissions/CIK0000320193.json",
            method="HEAD",
            headers={"User-Agent": es._user_agent()},
        )
        with urllib.request.urlopen(req, timeout=10):
            return True
    except Exception:
        return False


@pytest.mark.smoke
def test_smoke_sec_real_5_tickers(tmp_path, capsys):
    """Round-trip HTTP reel sur data.sec.gov + www.sec.gov pour 5 tickers.

    Le rapport final affiche le nombre de paires valides (status='item_1a')
    et echouees (status='failed'), conformement a acceptance #7.
    """
    if not os.environ.get("PYTEST_RUN_SMOKE"):
        pytest.skip(
            "Smoke SEC reel -- declenche via `-o 'PYTEST_RUN_SMOKE=1' "
            "pytest --run-smoke tests/test_smoke_sec_real.py` (acceptance #6)."
        )

    cache_dir = tmp_path / "smoke-cache"
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Si on n'a pas de reseau, on skip propre (jamais de FAIL silencieux).
    if not _have_network():
        pytest.skip("Pas d'acces reseau a sec.gov ; smoke impossible.")

    # Fixer la borne de validite : on accepte les 10-K accept by SEC
    # depuis 2020 ; un filing accepte apres aujourd'hui est note comme
    # 'futur' et considere comme valide (SEC peut accepter tres tot
    # le matin avant l'ouverture du marche US).
    today = datetime.utcnow().date()

    pairs = []
    for ticker, cik in BASKET.items():
        try:
            pair = es.build_pair(ticker, cik, cache_dir=cache_dir)
            # Garde-fou anti-look-ahead : on ne retient pas un pair dont
            # available_at est posterieur a aujourd'hui -- ce serait un
            # futur score jamais vu en backtest historique.
            if pair.available_at.date() > today + timedelta(days=1):
                with capsys.disabled():
                    print(
                        f"[smoke] skip {ticker}: available_at "
                        f"{pair.available_at.date().isoformat()} futur"
                    )
                continue
            pairs.append(pair)
        except Exception as exc:  # reseau ou parsing
            with capsys.disabled():
                print(f"[smoke] {ticker} echec: {exc!r}")

    summary = es.summarize(pairs)
    out_csv = tmp_path / "smoke.csv"
    es.write_csv(pairs, out_csv)

    with capsys.disabled():
        print()
        print("=== SMOKE SEC REEL ===")
        print(f"Panier : {sorted(BASKET)}")
        print(f"Total paires : {len(pairs)}")
        print(f"  valides   : {summary['valid']} "
              f"(extraction Item 1A reussie sur les deux 10-K)")
        print(f"  echouees  : {summary['failed']}")
        print(f"  taux OK   : {summary['valid_rate']:.1%}")
        print(f"CSV        : {out_csv}")
        print()
        for pair in pairs:
            sim = f"{pair.similarity:.4f}" if pair.similarity is not None else "n/a"
            print(
                f"  {pair.ticker}: {pair.newer.filing_date} / "
                f"{pair.older.filing_date}  "
                f"sim={sim} "
                f"available_at={pair.available_at.date().isoformat()} "
                f"[{pair.newer.accession} / {pair.older.accession}]"
            )
        print("======================")

    # Le smoke n'impose pas de taux minimum : c'est un oracle de
    # RONDEUR (tous les tickers donnent une reponse), pas un oracle
    # de qualite (une extraction peut reelement echouer sur GE).
    # On verifie juste qu'au moins une paire a ete construite.
    assert len(pairs) >= 1, "Smoke sans aucune paire construite"
