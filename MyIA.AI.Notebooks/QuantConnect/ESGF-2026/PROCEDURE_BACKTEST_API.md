# Procédure Backtests Automatisés via API QC

## Credentials (jsboige@gmail.com)

**User ID**: 46613
**Access Token**: 5dc8bd3dbebd8ef004d3386b6c3ab288
**Compte**: Payant (backtests autorisés)

## Procédure Complète

### 1. Compiler le projet
```
MCP QC: create_compile
Parameters: {"projectId": XXXXX}
```

### 2. Attendre 15-30 secondes (BuildSuccess)

### 3. Créer le backtest
```python
import requests

access_token = '5dc8bd3dbebd8ef004d3386b6c3ab288'
project_id = 19898232
compile_id = 'compile_id_from_step_1'

backtest_url = f'https://www.quantconnect.com/api/v2/projects/{project_id}/backtests'

backtest_data = {
    'compileId': compile_id,
    'backtestName': 'My-Backtest-Name'
}

headers = {
    'Authorization': f'Bearer {access_token}',
    'Content-Type': 'application/json'
}

response = requests.post(backtest_url, headers=headers, json=backtest_data)
```

### 4. Suivre le backtest
- URL: https://www.quantconnect.com/project/{PROJECT_ID}/backtests
- Attendre 5-15 minutes pour completion
- Résultats disponibles via `read_backtest` MCP QC

## Backtests Lancés (2026-02-18)

| Stratégie | Project ID | Compile ID | Nom Backtest | URL |
|-----------|-----------|------------|--------------|-----|
| BTC-MACD-ADX | 19898232 | 9617edf1... | Optimized-Window80-Pct5-85 | [Lien](https://www.quantconnect.com/project/19898232) |
| ETF-Pairs | 19865767 | 245d1c57... | Optimized-HalfLife-Filter | [Lien](https://www.quantconnect.com/project/19865767) |
| Sector-Momentum | 20216980 | ae012932... | Optimized-VIX-Filter | [Lien](https://www.quantconnect.com/project/20216980) |

## Paramètres Optimisés

### BTC-MACD-ADX (Project 19898232)
- **Approche**: MACD+ADX conservée (pas EMA cross)
- **Window**: 140 → **80** (plus réactif)
- **Lower percentile**: 6 → **5**
- **Upper percentile**: 86 → **85**
- **Période**: 2019-04-01 → now
- **Sharpe attendu**: +0.35 (vs -0.035)

### ETF-Pairs (Project 19865767)
- **Half-life filter**: < 30 jours
- **Duration adaptive**: 2 × half-life
- **Stops per-leg**: désactivés (neutralité préservée)
- **Sharpe attendu**: 0.3-0.7 (vs -0.759)

### Sector-Momentum (Project 20216980)
- **VIX filter**: Skip si VIX > 25
- **Leverage**: 2x → **1.5x**
- **Période**: 2015-01-01 → now
- **Sharpe attendu**: 0.8-1.0+ (vs 0.5-0.8 sans VIX)

## Commandes MCP QC Disponibles

```bash
# Lancer compilation
mcp__qc-mcp__create_compile {"projectId": 19898232}

# Lire status compilation
mcp__qc-mcp__read_compile {"projectId": 19898232, "compileId": "..."}

# Lister backtests
mcp__qc-mcp__list_backtests {"projectId": 19898232}

# Lire résultats backtest
mcp__qc-mcp__read_backtest {"projectId": 19898232, "backtestId": "..."}
```

## Leçon Apprise

✅ **L'API QC fonctionne avec compte payant**
✅ **Workflow**: create_compile → attendre → create_backtest
✅ **Tokens stockés** dans .env (user 46613)
✅ **Backtests lancés automatiquement** - plus besoin de UI web !

À mémoriser pour les prochaines fois !
