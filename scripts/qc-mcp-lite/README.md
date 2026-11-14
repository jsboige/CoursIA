# QC MCP Lite

Lightweight MCP server for QuantConnect API — 12 tools, <5k tokens schema.

Replaces the heavy `quantconnect/mcp-server` Docker container (~40k tokens) for standard backtesting workflows.

> **Trois voies d'accès MCP.** Ce serveur REST-lite est la voie canonique de la flotte ; le conteneur Docker officiel reste disponible (section « Reverting to Full MCP ») ; le **MCP distant officiel** (`https://www.quantconnect.com/api/v2/mcp`) existe mais exige un nœud assistant payant (A1-1 minimum, $24/mo) et n'est pas qualifié — état mesuré le 2026-11-08 (#24679) : [docs/qc/quantconnect.md](../../docs/qc/quantconnect.md).

## Tools

| Tool | Description |
|------|-------------|
| `create_compile` | Create a compile job |
| `read_compile` | Read compile status |
| `create_backtest` | Create a backtest from compiled project |
| `read_backtest` | Read backtest results (Sharpe, CAGR, MaxDD) |
| `read_backtest_chart` | Écrit un graphique de backtest (equity, exposition, rotation, graphique personnalisé) dans un fichier JSON ; rend le nombre de points par série, jamais les valeurs |
| `list_backtests` | List backtests for a project |
| `create_project` | Create a new QC project (paramètre optionnel `organization_id` pour choisir l'organisation, #19760) |
| `list_projects` | List all QC projects |
| `read_project` | Read project details and files (liste lue via `/files/read`) |
| `read_file` | Read file(s) from a project |
| `update_file_contents` | Update a file in a project |
| `create_file` | Create a new file in a project |

### Séries d'un backtest

`read_backtest` ne rend que le résumé. Pour comparer des variantes jour par jour, `read_backtest_chart` lit les graphiques enregistrés par QC :

- les graphiques par défaut (`Strategy Equity` avec `Equity` et `Return`, `Exposure` avec `Equity - Long Ratio` et `Equity - Short Ratio`, `Portfolio Turnover`) ne sont **pas** journaliers sur une longue période : sur 2007-2026, ils sont stockés sur une grille uniforme d'environ 1,32 jour, week-ends compris (5 433 points pour 4 946 séances, mesuré). Une moyenne d'exposition s'y lit, pas un rendement par séance ;
- un graphique personnalisé (`self.plot`) dont les points sont espacés de plus d'un pas de grille garde ses vraies dates. Pour une série par séance, tracer **cinq séries entrelacées**, chacune recevant un point toutes les 5 séances : l'expérience #18921 retrouve ainsi les 4 946 clôtures, toutes à des dates de séance ;
- l'ObjectStore n'est pas une alternative : son export par l'API est réservé aux comptes Institutional (« Due to data licensing restrictions »).

Les fichiers JSON écrits restent hors dépôt quand ils portent des séries complètes (cf. `.claude/rules/results-artifact-policy.md`).

## Mesure de stratégies — `qc_measure.py`

CLI générique de mesure d'une stratégie sur QC Cloud. Comparer une stratégie à des témoins sur plusieurs jeux de paramètres recompilait chaque fois la même plomberie (création du projet, envoi des fichiers, compilation, un backtest par passe, attente, lecture, tableau) et y commettait toujours les mêmes erreurs : statistiques lues avant la fin du backtest, clés cherchées sous le mauvais nom, backtests relancés en double après une coupure de session, limite de débit dépassée. `qc_measure.py` factorise cette plomberie à côté du serveur et réutilise son client REST et sa lecture d'identifiants **par import** : pas de second client HTTP, pas d'autre façon de lire le jeton, jeton jamais affiché (variables `QC_API_USER_ID` / `QC_API_ACCESS_TOKEN`).

Sous-commandes :

- `plan` — écrit le squelette `<workdir>/<label>/plan.json` : nom de projet, langage, fichiers à envoyer (empreinte sha256 mesurée à l'écriture), passes nommées avec leur dictionnaire de paramètres, organisation optionnelle ;
- `run` — idempotent et reprenable : crée le projet s'il n'est pas noté dans l'état (sinon le retrouve par nom), envoie les fichiers avec relecture de contrôle, compile et attend `BuildSuccess`, lance les backtests des passes non encore lancées (un à la fois par défaut, `--parallel N` optionnel), attend leur fin. Chaque étape faite est écrite aussitôt dans `<workdir>/<label>/state.json` (écriture atomique) : une relance après coupure ne recrée ni projet ni backtest déjà noté — un backtest du bon nom déjà présent est **adopté**, pas relancé ;
- `status` — état de chaque passe (`--refresh` interroge l'API pour actualiser les passes lancées) ;
- `read` — attend la fin de chaque backtest (champ `completed` de l'API), **refuse** de rendre des statistiques tant que le backtest n'est pas terminé (un backtest en cours affiche `totalOrders: 0` et des statistiques à `"-"`, indiscernables d'un run terminé sans ordre), relit un nombre borné de fois si un backtest terminé a les statistiques vides (il le dit, il n'affiche pas de tirets), normalise les clés des trois formes observées (`statistics` « Sharpe Ratio » / `runtimeStatistics` « CAGR » / forme camelCase du serveur) et sort un tableau Markdown — colonnes : passe, Sharpe, CAGR, MaxDD, PSR, bêta, ordres, taux de réussite, identifiant du backtest, identifiant du projet — ou `--json`.

Débit : cadenceur commun à **tous** les appels — 6 appels/min au plus par défaut (`--max-calls-per-min`, plafonné à 10, la limite flotte), intervalle de sondage d'au moins 20 s.

Exemple complet à deux passes :

```bash
export QC_API_USER_ID=... QC_API_ACCESS_TOKEN=...
python scripts/qc-mcp-lite/qc_measure.py plan mesures/vol --label volt-2026-11 \
    --project-name "Mesure-Volt-2026-11" \
    --file strategie/main.py --file strategie/indicateurs.py \
    --passe base --passe 'rapide:{"lookback": 10}'
python scripts/qc-mcp-lite/qc_measure.py run mesures/vol/volt-2026-11
python scripts/qc-mcp-lite/qc_measure.py status mesures/vol/volt-2026-11 --refresh
python scripts/qc-mcp-lite/qc_measure.py read mesures/vol/volt-2026-11
```

Précisions :

- les chemins de fichiers du plan se résolvent depuis le dossier du plan, puis depuis le répertoire courant ;
- un fichier modifié alors que des backtests sont déjà notés est refusé (« repartez sur un nouveau label ») : les noms de backtest sont uniques par projet sur QC, un backtest noté correspond à un code gelé — re-mesurer un code changé exige de nouvelles passes ;
- codes de sortie : `0` succès ; `1` au moins une passe sans statistiques exploitables (non terminée, en erreur, statistiques vides) ; `2` blocage (plan invalide, compilation en échec, identifiants absents) ;
- tests (faux client en mémoire, aucun réseau) : `python -m pytest scripts/qc-mcp-lite/tests/test_qc_measure.py`.

## Setup

### 1. Set environment variables

```bash
export QC_API_USER_ID="your_user_id"
export QC_API_ACCESS_TOKEN="your_api_token"
```

Or add to your `.env` file (gitignored).

### 2. Configure in `.mcp.json`

Replace the Docker-based `qc-mcp` with:

```json
{
  "mcpServers": {
    "qc-mcp-lite": {
      "command": "python",
      "args": ["scripts/qc-mcp-lite/server.py"],
      "env": {
        "QC_API_USER_ID": "your_user_id",
        "QC_API_ACCESS_TOKEN": "your_api_token"
      }
    }
  }
}
```

### 3. Verify

```bash
python -c "from server import list_projects; print(list_projects())"
```

## Auth

Uses the QC API v2 authentication pattern:
- `SHA256(token:timestamp)` hash
- `Basic userId:hash` authorization header
- `Timestamp` header

## Rate Limiting

10 calls/min enforced in-process. Matches the fleet-wide QC API rate limit.

## Reverting to Full MCP

To switch back to the official Docker MCP:

```json
{
  "mcpServers": {
    "qc-mcp": {
      "command": "docker",
      "args": ["run", "-i", "--rm",
        "-e", "QUANTCONNECT_USER_ID=46613",
        "-e", "QUANTCONNECT_API_TOKEN=your_token",
        "-e", "AGENT_NAME=claude-code",
        "quantconnect/mcp-server"
      ]
    }
  }
}
```
