"""Coinbase Advanced Trade sleeve for the Phase 4 paper harness (MiCA).

Wraps the official ``coinbase-advanced-py`` SDK (``coinbase.rest.RESTClient``)
in a small adapter so the orchestrator can talk to both sleeves through a
uniform interface. This is the **ACTIVE** crypto venue for the hybrid
portfolio post-MiCA.

MiCA migration (2026-06-28, see ../README.md): Binance France services cease
2026-07-01 (no CASP MiCA licence); Coinbase holds CASP MiCA France + is the
QC-native crypto market (``Market.COINBASE`` in ``main.py``). The legacy
``binance_sleeve.py`` is preserved as a fallback but is NOT the active path.

SOTA-OK (Prong A): this drives the real ``coinbase-advanced-py`` SDK against
the real Coinbase Advanced Trade API (``get_accounts`` / ``get_product`` /
``market_order_buy``), no degraded workaround. Order submission is implemented
but not exercised by the smoke test; the orchestrator enables it once circuit
breakers are reviewed.

USER-HAND gate (cf ../README.md Phase-B, #1027): Coinbase live/sandbox creds
(CDP API key + Ed25519/ECDSA private key) must be created in the Coinbase
Developer Platform by the user — account opening is user-side. Until then the
SDK is imported lazily in :meth:`connect` (so config-only tooling needs no
creds) and the smoke test reports RECOVERABLE-USER-HAND (exit 2). Coinbase
Advanced Trade has no public testnet like Binance: "sandbox" means a paper /
sandbox Coinbase account whose API key is used against the same endpoint, not
a separate URL. This is documented honestly rather than worked around.
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass

from .config import CoinbaseConfig


@dataclass(frozen=True)
class Balance:
    asset: str
    free: float
    locked: float


class CoinbaseSleeve:
    """Thin adapter around ``coinbase.rest.RESTClient``.

    Mirrors :class:`BinanceSleeve` so the (future) orchestrator can treat the
    two sleeves uniformly. ``coinbase`` is imported lazily in :meth:`connect`
    so that config-only tooling does not require the library to be installed.

    Product IDs on Coinbase Advanced Trade use a dash separator
    (``"BTC-USDT"``), built from ``(base, base_quote)``. The base quote
    defaults to USDT to match ``main.py``'s account currency; set
    ``COINBASE_BASE_QUOTE=USD`` if the live account is USD-denominated.
    """

    def __init__(self, cfg: CoinbaseConfig):
        self.cfg = cfg
        self._client = None

    # -- lifecycle --------------------------------------------------------

    def connect(self) -> "CoinbaseSleeve":
        from coinbase.rest import RESTClient

        if not self.cfg.has_credentials:
            raise RuntimeError(
                "Coinbase credentials missing in .env "
                "(COINBASE_API_KEY / COINBASE_API_SECRET) — USER-HAND "
                "(create a CDP API key, see ../README.md Phase-B)"
            )
        self._client = RESTClient(
            self.cfg.api_key,
            self.cfg.api_secret,
        )
        return self

    @property
    def client(self):
        if self._client is None:
            raise RuntimeError("CoinbaseSleeve not connected — call connect() first")
        return self._client

    # -- helpers ----------------------------------------------------------

    def product_id(self, base: str) -> str:
        """Build a Coinbase product id, e.g. ``BTC`` -> ``BTC-USDT``."""
        return f"{base}-{self.cfg.base_quote}"

    # -- read-only market & account --------------------------------------

    def account_info(self) -> dict:
        """Raw ``get_accounts`` response (paginated; first page only)."""
        return self.client.get_accounts()

    def quote_balance(self) -> float:
        """Free balance denominated in the base quote (e.g. USDT/USD)."""
        for acct in self.account_info().get("accounts", []):
            if acct.get("currency") == self.cfg.base_quote:
                bal = acct.get("available_balance") or {}
                try:
                    return float(bal.get("value", 0))
                except (TypeError, ValueError):
                    return 0.0
        return 0.0

    def balances(self, only_nonzero: bool = True) -> list[Balance]:
        out: list[Balance] = []
        for acct in self.account_info().get("accounts", []):
            asset = acct.get("currency")
            free = _to_float((acct.get("available_balance") or {}).get("value"))
            locked = _to_float((acct.get("hold") or {}).get("value"))
            if only_nonzero and free == 0 and locked == 0:
                continue
            out.append(Balance(asset, free, locked))
        return out

    def price(self, base_or_product: str) -> float:
        """Last trade price. Accepts ``"BTC"`` (-> BTC-USDT) or ``"BTC-USDT"``."""
        pid = base_or_product if "-" in base_or_product else self.product_id(base_or_product)
        product = self.client.get_product(pid)
        try:
            return float(product.get("price", 0))
        except (TypeError, ValueError):
            return 0.0

    # -- order helpers (not exercised by the smoke test) ------------------

    def market_buy(self, base: str, quote_quantity: float) -> dict:
        """Spend ``quote_quantity`` of the quote asset to buy ``base``.

        ``market_order_buy`` takes ``quote_size`` (quote-currency notional),
        so this is the quote-denominated counterpart of Binance's
        ``order_market_buy(quoteOrderQty=...)``.
        """
        pid = base if "-" in base else self.product_id(base)
        return self.client.market_order_buy(
            client_order_id=self._order_id(),
            product_id=pid,
            quote_size=self._fmt(quote_quantity),
        )

    def market_sell(self, base: str, base_quantity: float) -> dict:
        pid = base if "-" in base else self.product_id(base)
        return self.client.market_order_sell(
            client_order_id=self._order_id(),
            product_id=pid,
            base_size=self._fmt(base_quantity),
        )

    def cancel(self, order_id: str) -> dict:
        # ``cancel_orders`` (plural) takes a list; verified against the SDK.
        return self.client.cancel_orders(order_ids=[order_id])

    @staticmethod
    def _order_id() -> str:
        # Coinbase requires a unique client_order_id per order.
        return str(uuid.uuid4())

    @staticmethod
    def _fmt(x: float) -> str:
        return f"{x:.8f}".rstrip("0").rstrip(".")


def _to_float(value) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0
