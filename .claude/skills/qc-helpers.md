# QC Helpers Skill

Skill de reference pour les operations QuantConnect via MCP.

## Type

Reference (auto-loaded)

## Description

Documente les patterns et helpers pour utiliser les outils MCP QuantConnect.

## Outils MCP disponibles

### Gestion de projets

| Outil | Description | Exemple |
|-------|-------------|---------|
| `list_projects` | Lister tous les projets | `{"model": {}}` |
| `read_project_nodes` | Lire les noeuds de compilation | `{"model": {"projectId": 123}}` |
| `update_project` | Modifier nom/description | `{"model": {"projectId": 123, "name": "New Name"}}` |

### Fichiers

| Outil | Description | Exemple |
|-------|-------------|---------|
| `read_file` | Lire un fichier du cloud | `{"model": {"projectId": 123, "name": "main.py"}}` |
| `update_file_contents` | Modifier un fichier | `{"model": {"projectId": 123, "name": "main.py", "content": "..."}}` |
| `update_file_name` | Renommer un fichier | `{"model": {"projectId": 123, "name": "old.py", "newName": "new.py"}}` |

### Compilation

| Outil | Description | Exemple |
|-------|-------------|---------|
| `create_compile` | Demarrer une compilation | `{"model": {"projectId": 123}}` |
| `read_compile` | Lire le resultat | `{"model": {"projectId": 123, "compileId": "xxx"}}` |

### Backtests

| Outil | Description | Exemple |
|-------|-------------|---------|
| `list_backtests` | Lister les backtests | `{"model": {"projectId": 123, "includeStatistics": true}}` |
| `read_backtest` | Lire un backtest | `{"model": {"projectId": 123, "backtestId": "xxx"}}` |
| `read_backtest_orders` | Lire les ordres | `{"model": {"projectId": 123, "backtestId": "xxx"}}` |
| `read_backtest_chart` | Lire un chart | `{"model": {"projectId": 123, "backtestId": "xxx", "name": "Strategy Equity", ...}}` |

### Optimisation

| Outil | Description | Exemple |
|-------|-------------|---------|
| `list_optimizations` | Lister les optimisations | `{"model": {"projectId": 123}}` |
| `read_optimization` | Lire une optimisation | `{"model": {"projectId": 123, "optimizationId": "xxx"}}` |

## Patterns courants

### Pattern: Compiler un projet

```python
# 1. Demarrer la compilation
result = mcp__qc-mcp__create_compile(model={"projectId": 22298373})
compile_id = result["compileId"]

# 2. Attendre (5-10 secondes)
time.sleep(5)

# 3. Lire le resultat
compile_result = mcp__qc-mcp__read_compile(model={
    "projectId": 22298373,
    "compileId": compile_id
})

# 4. Verifier le statut
if compile_result["state"] == "BuildSuccess":
    print("Compilation reussie!")
else:
    print(f"Erreur: {compile_result.get('errors')}")
```

### Pattern: Analyser les backtests

```python
# 1. Lister les backtests avec statistiques
backtests = mcp__qc-mcp__list_backtests(model={
    "projectId": 19865767,
    "includeStatistics": True
})

# 2. Trier par Sharpe
sorted_backtests = sorted(
    backtests["backtests"],
    key=lambda x: x.get("sharpeRatio", -999),
    reverse=True
)

# 3. Analyser le meilleur
best = sorted_backtests[0]
print(f"Best Sharpe: {best['sharpeRatio']}")
print(f"Net Profit: {best['netProfit']}%")
print(f"Max DD: {best['drawdown']}%")

# 4. Lire les details
details = mcp__qc-mcp__read_backtest(model={
    "projectId": 19865767,
    "backtestId": best["backtestId"]
})

# 5. Analyser les erreurs
if details["backtest"]["status"] == "Runtime Error":
    print(f"Error: {details['backtest']['error']}")
```

### Pattern: Synchroniser local -> cloud

```python
# 1. Lire le fichier local
with open("path/to/main.py", "r", encoding="utf-8") as f:
    content = f.read()

# 2. Verifier la taille (< 32K)
if len(content) > 32000:
    raise ValueError("Fichier trop volumineux, diviser en modules")

# 3. Pousser vers le cloud
result = mcp__qc-mcp__update_file_contents(model={
    "projectId": 22298373,
    "name": "main.py",
    "content": content,
    "codeSourceId": "claude-code-iterative"
})

# 4. Compiler pour verifier
# ... (voir pattern compilation)
```

### Pattern: Analyser une erreur runtime

```python
# 1. Lire le backtest avec erreur
backtest = mcp__qc-mcp__read_backtest(model={
    "projectId": 22298373,
    "backtestId": "xxx"
})

# 2. Extraire l'erreur
if backtest["backtest"]["status"] == "Runtime Error":
    error = backtest["backtest"]["error"]
    stacktrace = backtest["backtest"]["stacktrace"]

    # 3. Parser la stacktrace
    # Exemple: "'ClassName' object has no attribute 'attr_name'"
    #          in main.py: line 329

    import re
    match = re.search(r"in (\w+\.py): line (\d+)", stacktrace)
    if match:
        file_name = match.group(1)
        line_number = int(match.group(2))
        print(f"Erreur dans {file_name} ligne {line_number}")
```

## Metriques de reference

### Classification des projets

| Statut | Sharpe | DD | Trades | Description |
|--------|--------|-----|--------|-------------|
| HEALTHY | > 0.5 | < 30% | > 0 | Performances acceptables |
| NEEDS_IMPROVEMENT | 0-0.5 | 30-50% | > 0 | A ameliorer |
| BROKEN | < 0 | > 50% | 0 | A corriger |
| NO_DATA | - | - | 0 | Pas de backtest |

### Metriques cibles

| Metrique | Target | Seuil acceptable |
|----------|--------|------------------|
| Sharpe Ratio | > 1.0 | > 0.5 |
| Max Drawdown | < 20% | < 30% |
| Win Rate | > 55% | > 45% |
| Profit Factor | > 1.5 | > 1.0 |
| CAGR | > 15% | > 10% |

## Limitations connues

1. **API Backtest payante**: `create_backtest` necessite un compte payant
2. **Taille de fichier**: Maximum 32K caracteres par fichier
3. **MCP timeout**: Connexions peuvent echouer, reessayer apres 5s
4. **Warnings non-bloquants**: Les linter warnings n'empechent pas la compilation

## Troubleshooting

### Erreur: "All connection attempts failed"

```
Solution:
1. Attendre 5-10 secondes
2. Reessayer la requete
3. Si persiste, verifier la configuration MCP
```

### Erreur: "Please upgrade to paid account"

```
Solution:
Cette fonctionnalite necessite un compte payant.
Workaround: Utiliser l'interface web QC pour les backtests.
```

### Erreur: "File too large"

```
Solution:
1. Diviser le fichier en modules (helpers, mixin, etc.)
2. Utiliser des imports relatifs
3. Pousser chaque fichier separement
```

### Warning: "has no attribute"

```
Ces warnings sont normaux pour:
- Mixins utilisant des attributs de la classe principale
- Enums QC (le linter ne connait pas toutes les valeurs)
- Imports dynamiques

Ils sont non-bloquants si la compilation reussit.
```

## Configuration MCP

Le MCP `qc-mcp` est configure dans `~/.claude.json`:

```json
{
  "mcpServers": {
    "qc-mcp": {
      "command": "docker",
      "args": [
        "run", "-i", "--rm", "--platform", "linux/amd64",
        "-e", "QUANTCONNECT_USER_ID=46613",
        "-e", "QUANTCONNECT_API_TOKEN=***",
        "-e", "AGENT_NAME=claude-code-coursia",
        "quantconnect/mcp-server"
      ]
    }
  }
}
```

## Project IDs ESGF-2026

| Projet | Cloud ID | Statut |
|--------|----------|--------|
| Crypto-MultiCanal | 22298373 | BROKEN (0 trades) |
| ETF-Pairs-Trading | 19865767 | BROKEN (Sharpe -0.76) |
| BTC-MachineLearning | 21047688 | NO_DATA |
| Multi-Layer-EMA | 20216947 | HEALTHY |
| Sector-Momentum | 20216980 | HEALTHY |
| Trend-Following | 20216930 | HEALTHY |
| Options-VGT | 21113806 | HEALTHY |
| Option-Wheel-Strategy | 20216898 | HEALTHY |
| CSharp-BTC-MACD-ADX | 19898232 | HEALTHY |
| CSharp-BTC-EMA-Cross | 19050970 | HEALTHY |
| CSharp-CTG-Momentum | 19225388 | HEALTHY |
