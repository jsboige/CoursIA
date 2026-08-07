# Quantbooks Stop&Repair Pipeline Report — 20260806_172234

**Scope** : 8 quantbooks #6891 (DualMomentum 28692516, EMA-Cross-Alpha 28885488 = deja cloud-id).
**Creds QC** : ABSENTES (dry-run only)

## Phase Audit

- **AllWeather** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
- **DualMomentum** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
    - `cloud_id` = `28692516`
- **EMA-Cross-Alpha** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
    - `cloud_id` = `28885488`
- **FuturesTrend** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
- **MomentumStrategy** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
- **RiskParity** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
- **SectorMomentum** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`
- **TurnOfMonth** : `HEALTHY`
    - `exists` = `True`
    - `config_json` = `True`

## Phase Push

- **AllWeather** : `DRY_RUN_PUSH_PENDING`
- **DualMomentum** : `SKIP_ALREADY_PUSHED`
    - `cloud_id` = `28692516`
- **EMA-Cross-Alpha** : `SKIP_ALREADY_PUSHED`
    - `cloud_id` = `28885488`
- **FuturesTrend** : `DRY_RUN_PUSH_PENDING`
- **MomentumStrategy** : `DRY_RUN_PUSH_PENDING`
- **RiskParity** : `DRY_RUN_PUSH_PENDING`
- **SectorMomentum** : `DRY_RUN_PUSH_PENDING`
- **TurnOfMonth** : `DRY_RUN_PUSH_PENDING`

## Phase Exec

- **AllWeather** : `DRY_RUN_EXEC_PENDING`
- **DualMomentum** : `DRY_RUN_EXEC_PENDING`
- **EMA-Cross-Alpha** : `DRY_RUN_EXEC_PENDING`
- **FuturesTrend** : `DRY_RUN_EXEC_PENDING`
- **MomentumStrategy** : `DRY_RUN_EXEC_PENDING`
- **RiskParity** : `DRY_RUN_EXEC_PENDING`
- **SectorMomentum** : `DRY_RUN_EXEC_PENDING`
- **TurnOfMonth** : `DRY_RUN_EXEC_PENDING`

## Phase Verify

- **?** : `PASS`
    - `scanner` = `scripts/notebook_tools/detect_fabricated_outputs.py`
    - `stdout_tail` = `['Notebooks scanned     : 205', 'Fabricated outputs   : 0', 'Affected notebooks   : 0', '', 'No fabricated text outputs detected (Row N / zero-stats dataframe check).']`
- **?** : `PASS`
    - `scanner` = `scripts/notebook_tools/detect_blank_figures.py`
    - `stdout_tail` = `['Notebooks scanned  : 205', 'Degenerate figures : 0', 'Affected notebooks : 0', '', 'No degenerate figures detected (deterministic dimension/size check).']`
