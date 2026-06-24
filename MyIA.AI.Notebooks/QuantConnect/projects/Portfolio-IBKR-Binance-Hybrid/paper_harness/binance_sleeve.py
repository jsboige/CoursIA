"""Binance Spot sleeve for the Phase 4 paper harness.

Wraps :mod:`binance` (python-binance) in a small adapter so the orchestrator
can talk to both sleeves through a uniform interface. In paper mode it
connects to the public Spot Test Network (``testnet=True``), so all balances
and fills are fictitious — see ``.env`` ``BINANCE_TESTNET``.

SOTA-OK (Prong A): this drives the real python-binance library against the
real Binance testnet, no degraded workaround. Order submission is
implemented but not exercised by the smoke test; the orchestrator enables it
once circuit breakers are reviewed.
"""
from __future__ import annotations

from dataclasses import dataclass

from .config import BinanceConfig


@dataclass(frozen=True)
class Balance:
    asset: str
    free: float
    locked: float


class BinanceSleeve:
    """Thin adapter around ``binance.client.Client``.

    Deliberately small: connect, read balances/prices, and expose typed
    order helpers. ``binance`` is imported lazily in :meth:`connect` so that
    config-only tooling does not require the library to be installed.
    """

    def __init__(self, cfg: BinanceConfig):
        self.cfg = cfg
        self._client = None

    # -- lifecycle --------------------------------------------------------

    def connect(self) -> "BinanceSleeve":
        from binance.client import Client

        if not self.cfg.has_credentials:
            raise RuntimeError(
                "Binance credentials missing in .env "
                "(BINANCE_API_KEY / BINANCE_API_SECRET)"
            )
        self._client = Client(
            self.cfg.api_key,
            self.cfg.api_secret,
            testnet=self.cfg.testnet,
        )
        return self

    @property
    def client(self):
        if self._client is None:
            raise RuntimeError("BinanceSleeve not connected — call connect() first")
        return self._client

    # -- read-only market & account --------------------------------------

    def system_status(self) -> dict:
        return self.client.get_system_status()

    def account_info(self) -> dict:
        return self.client.get_account()

    def quote_balance(self) -> float:
        """Free balance denominated in the base quote (e.g. USDT)."""
        for b in self.account_info().get("balances", []):
            if b["asset"] == self.cfg.base_quote:
                return float(b["free"])
        return 0.0

    def balances(self, only_nonzero: bool = True) -> list[Balance]:
        out: list[Balance] = []
        for b in self.account_info().get("balances", []):
            bal = Balance(b["asset"], float(b["free"]), float(b["locked"]))
            if only_nonzero and bal.free == 0 and bal.locked == 0:
                continue
            out.append(bal)
        return out

    def price(self, symbol: str) -> float:
        return float(self.client.get_symbol_ticker(symbol=symbol)["price"])

    # -- order helpers (not exercised by the smoke test) ------------------

    def market_buy(self, symbol: str, quote_quantity: float) -> dict:
        """Buy ``symbol`` spending ``quote_quantity`` of the quote asset."""
        return self.client.order_market_buy(
            symbol=symbol, quoteOrderQty=self._fmt(quote_quantity)
        )

    def market_sell(self, symbol: str, base_quantity: float) -> dict:
        return self.client.order_market_sell(
            symbol=symbol, quantity=self._fmt(base_quantity)
        )

    def cancel(self, symbol: str, order_id: int) -> dict:
        return self.client.cancel_order(symbol=symbol, orderId=order_id)

    @staticmethod
    def _fmt(x: float) -> str:
        return f"{x:.8f}".rstrip("0").rstrip(".")
