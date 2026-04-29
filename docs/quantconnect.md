# QuantConnect (QC) - Configuration et regles

## Backtests obligatoires

Toute modification d'une strategie QC (main.py, parametres, periodes) **DOIT** etre validee par un backtest :

1. `create_compile` pour verifier la compilation
2. `create_backtest` pour lancer le backtest
3. `read_backtest` pour recuperer les metriques (Sharpe, CAGR, MaxDD)
4. Reporter les resultats dans le message de commit ET sur RooSync

**Changer une date ou un parametre sans backtest = travail invalide.**

## QC Cloud API - Acces via MCP Docker (OBLIGATOIRE)

**Methode d'acces** : Utiliser le MCP Docker `quantconnect/mcp-server` configure dans `.mcp.json` a la racine du projet.

- **NE PAS** utiliser de scripts Python avec l'API REST directe (provoque du rate-limiting et des erreurs d'auth)
- Le MCP gere l'authentification et le rate-limiting automatiquement
- Fichier de config : `.mcp.json` (deja dans `.gitignore`, JAMAIS committer)

### Configuration `.mcp.json`

```json
{
  "mcpServers": {
    "quantconnect": {
      "command": "docker",
      "args": ["run", "--rm", "-i",
        "-e", "QUANTCONNECT_USER_ID",
        "-e", "QUANTCONNECT_API_TOKEN",
        "-e", "QUANTCONNECT_ORGANIZATION_ID",
        "quantconnect/mcp-server"],
      "env": {
        "QUANTCONNECT_USER_ID": "<voir dashboard RooSync>",
        "QUANTCONNECT_API_TOKEN": "<voir dashboard RooSync>",
        "QUANTCONNECT_ORGANIZATION_ID": "<voir dashboard RooSync>"
      }
    }
  }
}
```

### Rate limiting strict

MAX 10 appels/minute entre TOUS les agents. Avant de lancer un backtest, poster sur le dashboard. Un seul agent a la fois sur l'API QC.

### Pour retrouver les tokens

- Dashboard workspace CoursIA : section status
- Messages RooSync : tag `quantconnect` ou `TOKEN`
- En cas de token invalide : demander au coordinateur (ai-01) via RooSync

## Structure QC dans le depot

```
MyIA.AI.Notebooks/QuantConnect/
  Python/           # 27+ notebooks progressifs (QC-Py-01 a QC-Py-Cloud-XX)
  projects/          # ~50 strategies avec main.py + research.ipynb
  shared/            # Librairie utilitaire (backtestlib, indicators, plotting)
  ESGF-2026/         # Cours ESGF : exercices, templates, lean-workspace
  docs/              # Documentation technique (pas de coordination)
```

## Livre de reference

*Hands-On AI Trading* de Jared Broad - https://www.hands-on-ai-trading.com/

- Repo exemples : https://github.com/QuantConnect/HandsOnAITradingBook
- Issues associees : #107 (mapping), #143 (implementation ML)
