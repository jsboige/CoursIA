# IchimokuEnergySector-QC — Ichimoku Clouds In The Energy Sector

QC Cloud port of QuantConnect research **9031 — "Ichimoku Clouds In The Energy Sector"**
(Derek Melchin, draft/pending review):
<https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/>.
French is the primary README (`README.md`); this is its English sibling.

- Grain: `DEEP/qc` — lane `myia-po-2023:CoursIA` — See #19678 (seed + acceptance), EPIC
  #11698 (QC-research harvesting).
- QC Cloud project: `IchimokuEnergySector-9031` (id 37468246), executed via the
  `quantconnect/mcp-server` MCP — never a fake local run.

## What the strategy does

The article applies the **Ichimoku Kinko Hyo** indicator to the top-10 energy-sector
market caps (monthly fine-fundamental universe, `MorningstarSectorCode.ENERGY`):

- the AlphaModel goes **long** when the **Chikou** line crosses the cloud top
  (Senkou A/B) from below, **short** when it crosses the cloud bottom from above;
- daily 1-day insights hold the position between crossovers;
- equal-weight portfolio construction, immediate execution, adjusted daily data.

The article confronts the strategy against the **XLE** benchmark (energy ETF) over four
windows and honestly concludes that **the strategy does not beat the benchmark** — exactly
what this port measures.

## Documented adaptations (a1-a6)

See `README.md` (French) for the full a1-a6 table — identical code on both sides.
Highlights: parametrized window/cash under IBKR fees (a1), an `xle_hold` comparator mode
sharing the exact same harness (a2), instance-level symbol data (a3), removed-symbol
cleanup (a4), explicit XLE benchmark (a5), and a typed `history[TradeBar]` warm-up
replacing the article's pandas pattern that throws `Runtime Error` on current LEAN (a6,
measured on first run).

## Reproduced metrics (IBKR fees, 1M cash)

### Strategy vs article — reproduction

<!-- TABLE_REPRO -->

### XLE buy-and-hold (same harness)

<!-- TABLE_XLE -->

### Out-of-sample extension (2020-08-17 → 2026-09-30)

<!-- TABLE_OOS -->

## BEATS / NO BEATS verdict

<!-- VERDICT -->

## Reference

Gurrib, I., Kamalov, F., & Elshareif, E. (2021). *Can the leading US energy stock prices be
predicted using the Ichimoku cloud?* International Journal of Energy Economics and Policy,
11(1), 41–51. https://doi.org/10.32479/ijeep.10260 (SSRN version 2020, abstract 3520582).
PDF archived in the shared bibliography under `Trading/`.

The reference study uses a **fixed selection built on end-of-period weights** (look-ahead
bias documented by the QC article itself); the port keeps the QC article's **monthly**
fine-fundamental universe, which removes that bias — absolute Sharpe levels are therefore
not directly comparable to Gurrib et al.; the **strategy-vs-XLE confrontation under the
same harness** is what counts.
