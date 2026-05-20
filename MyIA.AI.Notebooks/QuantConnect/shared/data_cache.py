"""
Cache intelligent pour les telechargements yfinance.

Stocke les donnees en Parquet pour eviter les re-telechargements
lors de l'execution Papermill des notebooks ESGF.

Usage:
    from shared.data_cache import get_yf_data, get_yf_batch

    spy = get_yf_data('SPY', '2020-01-01', '2023-12-31')
    sectors = get_yf_batch(['XLK', 'XLF'], '2015-01-01', '2025-02-18')
"""

import time
from pathlib import Path
from typing import Optional, Union

import pandas as pd
import yfinance as yf

DEFAULT_CACHE_DIR = Path(__file__).parent.parent / "ESGF-2026" / "examples" / ".data_cache"


def _cache_path(ticker: str, start: str, end: str, column: str,
                cache_dir: Path) -> Path:
    safe = ticker.replace("^", "IDX_").replace("/", "_")
    s = start.replace("-", "")
    e = end.replace("-", "")
    return cache_dir / f"{safe}_{s}_{e}_{column}.parquet"


def _age_days(path: Path) -> float:
    return (time.time() - path.stat().st_mtime) / 86400


def get_yf_data(
    ticker: str,
    start: str,
    end: str,
    column: str = "Close",
    cache_dir: Optional[str] = None,
    max_age_days: Optional[float] = None,
    verbose: bool = True,
) -> pd.Series:
    """
    Telecharge une serie de prix avec cache Parquet.

    Args:
        ticker: Symbole (ex: 'SPY', '^VIX')
        start: Date debut 'YYYY-MM-DD'
        end: Date fin 'YYYY-MM-DD'
        column: Colonne yfinance ('Close', 'Adj Close', etc.)
        cache_dir: Repertoire cache (defaut: ESGF-2026/examples/.data_cache/)
        max_age_days: Age max du cache en jours (None = pas de limite)
        verbose: Afficher les messages de statut

    Returns:
        pd.Series indexee par date
    """
    cdir = Path(cache_dir) if cache_dir else DEFAULT_CACHE_DIR
    cdir.mkdir(parents=True, exist_ok=True)
    cpath = _cache_path(ticker, start, end, column, cdir)

    if cpath.exists() and (max_age_days is None or _age_days(cpath) <= max_age_days):
        if verbose:
            print(f"  [cache] {ticker}: hit ({_age_days(cpath):.0f}j)")
        data = pd.read_parquet(cpath)
        return data.iloc[:, 0] if isinstance(data, pd.DataFrame) else data

    if verbose:
        print(f"  [cache] {ticker}: download {start} -> {end}...")

    try:
        df = yf.download(ticker, start=start, end=end, progress=False)
    except Exception as e:
        if cpath.exists():
            if verbose:
                print(f"  [cache] {ticker}: download failed ({e}), using stale cache")
            data = pd.read_parquet(cpath)
            return data.iloc[:, 0] if isinstance(data, pd.DataFrame) else data
        raise

    if df.empty:
        raise ValueError(f"Aucune donnee pour {ticker} ({start} a {end})")

    raw = df[column]
    series = raw.iloc[:, 0] if isinstance(raw, pd.DataFrame) else raw

    df_to_save = series.to_frame(column)
    df_to_save.to_parquet(cpath)

    if verbose:
        print(f"  [cache] {ticker}: {len(series)} jours mis en cache")

    return series


def get_yf_batch(
    tickers: list,
    start: str,
    end: str,
    column: str = "Close",
    cache_dir: Optional[str] = None,
    max_age_days: Optional[float] = None,
    verbose: bool = True,
) -> pd.DataFrame:
    """
    Telecharge plusieurs tickers avec cache Parquet.

    Utilise le cache par ticker, puis assemble en DataFrame.

    Args:
        tickers: Liste de symboles
        start: Date debut 'YYYY-MM-DD'
        end: Date fin 'YYYY-MM-DD'
        column: Colonne yfinance ('Close', 'Adj Close', etc.)
        cache_dir: Repertoire cache
        max_age_days: Age max du cache en jours
        verbose: Afficher les messages

    Returns:
        pd.DataFrame avec tickers en colonnes
    """
    result = {}
    for ticker in tickers:
        try:
            result[ticker] = get_yf_data(
                ticker, start, end, column, cache_dir, max_age_days, verbose
            )
        except Exception as e:
            if verbose:
                print(f"  [cache] {ticker}: skip ({e})")
    return pd.DataFrame(result)


def clear_cache(cache_dir: Optional[str] = None) -> list:
    """Supprime tous les fichiers du cache et retourne la liste des fichiers supprimes."""
    cdir = Path(cache_dir) if cache_dir else DEFAULT_CACHE_DIR
    if not cdir.exists():
        return []
    removed = []
    for f in cdir.glob("*.parquet"):
        f.unlink()
        removed.append(f.name)
    return removed
