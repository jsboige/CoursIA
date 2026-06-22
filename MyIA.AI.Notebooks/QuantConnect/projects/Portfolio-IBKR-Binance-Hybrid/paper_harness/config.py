"""Configuration loader for the Phase 4 paper-trading harness.

Reads credentials and parameters from the project-root ``.env`` file
(gitignored). Values are loaded into typed frozen dataclasses. No secret is
ever printed by this module; callers that need a value access the attribute,
never ``repr()`` the config in logs.
"""
from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path


def _project_root() -> Path:
    # paper_harness/config.py -> project root (two parents up).
    return Path(__file__).resolve().parent.parent


def _load_env_file(path: Path) -> dict[str, str]:
    env: dict[str, str] = {}
    if not path.is_file():
        return env
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        env[key.strip()] = value.strip()
    return env


def _get(env: dict[str, str], key: str, default: str = "") -> str:
    # Precedence: real process environment (if set non-empty) then .env file.
    val = os.environ.get(key)
    if val:
        return val
    return env.get(key, default)


def _get_bool(env: dict[str, str], key: str, default: bool) -> bool:
    fallback = "true" if default else "false"
    return _get(env, key, fallback).strip().lower() in {"1", "true", "yes", "on"}


def _get_float(env: dict[str, str], key: str, default: float) -> float:
    raw = _get(env, key, "").strip()
    try:
        return float(raw) if raw else default
    except ValueError:
        return default


def _get_int(env: dict[str, str], key: str, default: int) -> int:
    raw = _get(env, key, "").strip()
    try:
        return int(raw) if raw else default
    except ValueError:
        return default


@dataclass(frozen=True)
class IBKRConfig:
    username: str
    password: str
    account_id: str
    trading_mode: str  # paper | live
    initial_capital_usd: float
    host: str
    port: int
    client_id: int

    @property
    def is_paper(self) -> bool:
        return self.trading_mode.lower() == "paper"


@dataclass(frozen=True)
class BinanceConfig:
    api_key: str
    api_secret: str
    testnet: bool
    initial_capital_usd: float
    base_quote: str  # e.g. USDT

    @property
    def has_credentials(self) -> bool:
        return bool(self.api_key and self.api_secret)


@dataclass(frozen=True)
class PortfolioConfig:
    total_capital_usd: float
    alloc_ibkr: float
    alloc_binance: float
    rebalance_freq: str
    rebalance_threshold: float


@dataclass(frozen=True)
class RiskConfig:
    max_dd_pct: float            # 0.10 = -10% live drawdown circuit breaker
    daily_var_pct: float         # 0.03 = 3% daily loss alert/halt
    vol_spike_threshold: float   # 2.0 = 2 sigma vs 30d baseline
    max_position_pct: float = 0.25   # max single position / sleeve capital
    max_gross_exposure: float = 1.0   # max gross exposure / sleeve capital


@dataclass(frozen=True)
class HarnessConfig:
    ibkr: IBKRConfig
    binance: BinanceConfig
    portfolio: PortfolioConfig
    risk: RiskConfig
    env_path: Path


def load_config(env_path: Path | None = None) -> HarnessConfig:
    path = env_path or (_project_root() / ".env")
    env = _load_env_file(path)
    return HarnessConfig(
        ibkr=IBKRConfig(
            username=_get(env, "IBKR_USERNAME"),
            password=_get(env, "IBKR_PASSWORD"),
            account_id=_get(env, "IBKR_ACCOUNT_ID"),
            trading_mode=_get(env, "IBKR_TRADING_MODE", "paper"),
            initial_capital_usd=_get_float(env, "IBKR_INITIAL_CAPITAL_USD", 0.0),
            host=_get(env, "IBKR_HOST", "127.0.0.1"),
            # 4002 = modern IB Gateway paper API (10.x+). Older builds use 4001.
            port=_get_int(env, "IBKR_PORT", 4002),
            client_id=_get_int(env, "IBKR_CLIENT_ID", 1),
        ),
        binance=BinanceConfig(
            api_key=_get(env, "BINANCE_API_KEY"),
            api_secret=_get(env, "BINANCE_API_SECRET"),
            testnet=_get_bool(env, "BINANCE_TESTNET", True),
            initial_capital_usd=_get_float(env, "BINANCE_INITIAL_CAPITAL_USD", 0.0),
            base_quote=_get(env, "BINANCE_BASE_QUOTE", "USDT"),
        ),
        portfolio=PortfolioConfig(
            total_capital_usd=_get_float(env, "PORTFOLIO_TOTAL_CAPITAL_USD", 0.0),
            alloc_ibkr=_get_float(env, "PORTFOLIO_ALLOC_IBKR", 0.5),
            alloc_binance=_get_float(env, "PORTFOLIO_ALLOC_BINANCE", 0.5),
            rebalance_freq=_get(env, "PORTFOLIO_REBALANCE_FREQ", "monthly"),
            rebalance_threshold=_get_float(env, "PORTFOLIO_REBALANCE_THRESHOLD", 0.05),
        ),
        risk=RiskConfig(
            max_dd_pct=_get_float(env, "RISK_MAX_DD_PCT", 0.10),
            daily_var_pct=_get_float(env, "RISK_DAILY_VAR_PCT", 0.03),
            vol_spike_threshold=_get_float(env, "RISK_VOL_SPIKE_THRESHOLD", 2.0),
            max_position_pct=_get_float(env, "RISK_MAX_POSITION_PCT", 0.25),
            max_gross_exposure=_get_float(env, "RISK_MAX_GROSS_EXPOSURE", 1.0),
        ),
        env_path=path,
    )
