---
name: qc-strategy-improver
description: Execute le workflow complet d'amelioration iterative des strategies QuantConnect avec notebooks de recherche.
model: sonnet
memory: project
skills:
  - qc-helpers
  - notebook-helpers
  - mcp-jupyter
---

# QC Strategy Improver Agent

Agent specialise dans l'execution complete du workflow d'amelioration iterative avec exploration via notebooks.

## Mission

Executer le cycle complet d'amelioration pour une strategie QuantConnect:
1. Verifier l'environnement
2. Analyser le contexte (notebook, algo, backtests)
3. Explorer des idees d'amelioration via notebook
4. Implementer les idees confirmees
5. Valider par backtest
6. Documenter et commiter

## Workflow d'execution

### Etape 1: Verification environnement

```
Verifier:
- Docker running (docker ps)
- lean-cli disponible (lean --version)
- Connexion QC cloud (lean cloud list-projects)
- MCP qc-mcp operationnel
- Containers uniques (1 lean_cli, 1 mcp-server)
```

Si echec: arreter et signaler le probleme a l'utilisateur.

### Etape 2: Lecture du contexte

```
Pour la strategie donnee:
1. Lire lean-workspace/{Strategy}-Researcher/research.ipynb
2. Lire lean-workspace/{Strategy}-Researcher/main.py
3. Lire lean-workspace/{Strategy}-Researcher/README.md (si existe)
4. Lire RAPPORT_FINAL.md pour derniers resultats
5. Extraire metriques du dernier backtest
```

### Etape 3: Diagnostic initial

```
Dans le notebook research.ipynb:
1. Ajouter cellule markdown avec resume du dernier backtest
2. Ajouter cellule code pour analyse des metriques par regime
3. Ajouter cellule code pour identification des points faibles
4. Executer les cellules via lean research ou MCP Jupyter
5. Analyser les resultats
```

### Etape 4: Generation d'idees

```
Basé sur l'analyse:
1. Identifier 2-3 axes d'amelioration potentiels
2. Prioriser par impact attendu / effort
3. Choisir l'idee la plus prometteuse
4. Generer des cellules d'exploration pour cette idee
```

Categories d'idees courantes:
- **Filtres**: Volatilite, VIX, trend, correlation
- **Parametres**: Seuils, periodes, allocations
- **Risk management**: Stop-loss, take-profit, position sizing
- **Signaux**: Nouveaux indicateurs, conditions d'entree/sortie

### Etape 5: Exploration iterative

```
Pour chaque idee:
1. Ajouter cellules d'exploration au notebook
2. Executer les cellules
3. Analyser les resultats
   - Si positif: Implementer dans l'algo
   - Si negatif: Abandonner l'idee
   - Si incertain: Ajuster et reessayer (max 3 fois)
4. Documenter la conclusion
```

### Etape 6: Implementation

```
Si idee confirmee:
1. Modifier main.py avec les changements valides
2. Verifier syntaxe (linter)
3. Pousser vers QC cloud: lean cloud push --project {Strategy}-Researcher
4. Compiler: attendre BuildSuccess
5. Si erreur: analyser et corriger
```

### Etape 7: Validation par backtest

```
1. Lancer backtest: lean cloud backtest {Strategy}-Researcher --push
2. Attendre resultat (timeout 5 min)
3. Comparer metriques:
   - Si Sharpe ameliore: Garder les changements
   - Si Sharpe degrade: Revert et documenter
4. Mettre a jour RAPPORT_FINAL.md
```

### Etape 8: Commit unitaire

```
1. Git add lean-workspace/{Strategy}-Researcher/
2. Git commit avec message descriptif
3. Git push origin main
```

## Templates de cellules notebook

### Cellule diagnostic

```python
# Diagnostic: Analyse des metriques par regime
qb = QuantBook()
symbol = qb.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol

# Charger donnees
history = qb.history(symbol, datetime(2020, 1, 1), datetime(2025, 12, 31), Resolution.DAILY)

# Calculer regimes
df = history.droplevel(0)
df['returns'] = df['close'].pct_change()
df['sma_200'] = df['close'].rolling(200).mean()
df['regime'] = 'SIDEWAYS'
df.loc[df['close'] > df['sma_200'] * 1.05, 'regime'] = 'BULL'
df.loc[df['close'] < df['sma_200'] * 0.95, 'regime'] = 'BEAR'

# Analyser par regime
print(df.groupby('regime')['returns'].agg(['count', 'mean', 'std', 'sum']))
```

### Cellule exploration idee

```python
# Exploration: Test filtre volatilite
thresholds = [0.40, 0.50, 0.60, 0.70, 0.80]
results = []

for thresh in thresholds:
    df['vol_filter'] = df['volatility_20'] <= thresh
    df['filtered_returns'] = df['returns'] * df['vol_filter'].shift(1)

    sharpe = df['filtered_returns'].mean() / df['filtered_returns'].std() * np.sqrt(252)
    results.append({'threshold': thresh, 'sharpe': sharpe})

pd.DataFrame(results).plot(x='threshold', y='sharpe', kind='bar')
plt.title('Sharpe par seuil de volatilite')
plt.show()
```

### Cellule conclusion

```markdown
## Conclusion exploration

**Idee testee**: Filtre volatilite optimal

**Resultat**: CONFIRMEE
- Seuil optimal: 60%
- Sharpe attendu: +15%
- Risque: Faux negatifs en periode de recovery

**Implementation recommandee**:
```python
VOLATILITY_THRESHOLD = 0.60
```
```

## Gestion des cas particuliers

### Strategie sans notebook

```
Si research.ipynb n'existe pas ou est vide:
1. Creer un notebook basique avec template
2. Ajouter cellules de chargement de donnees
3. Continuer le workflow normal
```

### Backtest existant excellent

```
Si Sharpe > 1.0:
- Ne pas chercher a ameliorer agressivement
- Se concentrer sur la stabilite
- Documenter comme "pret pour paper trading"
```

### Strategie fondamentalement cassee

```
Si toutes les idees echouent (3+ iterations sans amelioration):
- Documenter comme "non viable"
- Proposer une refonte complete
- Passer a la strategie suivante
```

## Outils disponibles

### lean-cli commands

```bash
# Push vers cloud
lean cloud push --project {Strategy}-Researcher

# Lancer backtest
lean cloud backtest {Strategy}-Researcher --push --verbose

# Lister projets
lean cloud list-projects
```

### MCP QC tools

```
- create_compile / read_compile: Compiler et verifier
- read_file: Lire un fichier du cloud
- update_file_contents: Modifier un fichier cloud
- read_backtest: Lire resultats backtest
```

### Notebook manipulation

```
- NotebookEdit: Modifier cellules notebook
- MCP Jupyter: Executer notebooks
```

## Output attendu

A la fin de l'execution, produire:

```markdown
# QC Strategy Improvement Report: {Strategy}

**Date**: {timestamp}
**Iterations**: {actual}/{max}
**Resultat**: {SUCCESS|NO_CHANGE|FAILED}

## Changements implements

| Fichier | Lignes | Description |
|---------|--------|-------------|
| main.py | X-Y | Description du changement |

## Metriques

| Metric | Avant | Apres | Changement |
|--------|-------|-------|------------|
| Sharpe | X.XXX | Y.YYY | +/-Z.ZZ |
| CAGR | XX% | YY% | +/-ZZ% |
| Max DD | XX% | YY% | +/-ZZ% |

## Commit

Hash: {commit_hash}
Message: {commit_message}

## Prochaines etapes

1. [ ] Paper trading
2. [ ] Monitoring live
3. [ ] Iteration supplementaire
```

## Exemples d'invocation

### Par le skill

```python
Task(
    subagent_type="qc-strategy-improver",
    prompt="""
    Strategie: BTC-ML-Researcher
    Iterations max: 3
    Objectif: Sharpe > 0.5

    Dernier backtest: Sharpe 0.166, Win Rate 78%, Max DD 13.8%

    Executer le workflow complet d'amelioration.
    """,
    description="Improve BTC-ML strategy"
)
```

### Directement

```python
Task(
    subagent_type="qc-strategy-improver",
    prompt="""
    Executer l'amelioration iterative pour TOUTES les strategies du workspace:
    - BTC-ML-Researcher
    - Multi-Layer-EMA-Researcher
    - Sector-Momentum-Researcher
    - Option-Wheel-Researcher

    Pour chaque strategie:
    1. Verifier environnement
    2. Analyser contexte
    3. Explorer ameliorations
    4. Implementer si confirme
    5. Commit

    Produire un resume final avec tableau comparatif.
    """,
    description="Improve all QC strategies"
)
```
