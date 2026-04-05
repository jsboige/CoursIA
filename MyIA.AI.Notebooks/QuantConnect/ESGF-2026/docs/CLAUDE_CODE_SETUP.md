# Guide : Claude Code + OpenRouter pour le Trading Algorithmique

Configuration de Claude Code CLI avec OpenRouter comme fournisseur API, integre avec QuantConnect pour le cours ESGF 2026.

---

## 1. Installation de Claude Code

### Prerequis

- **Node.js** 18+ : [nodejs.org](https://nodejs.org)
- **Git** : [git-scm.com](https://git-scm.com)
- Un terminal (PowerShell, Windows Terminal, ou VS Code)

### Installation

```bash
npm install -g @anthropic-ai/claude-code
```

Verifier l'installation :

```bash
claude --version
```

### Premier lancement

```bash
claude
```

Au premier lancement, Claude Code vous demandera de vous authentifier. Si vous utilisez OpenRouter (section 2), choisissez "Skip" pour l'authentification Anthropic.

---

## 2. Configuration d'OpenRouter

[OpenRouter](https://openrouter.ai) est un routeur d'API qui donne acces a des centaines de modeles (Claude, GPT, Gemini, Llama, etc.) avec un seul compte.

### 2.1 Creer un compte OpenRouter

1. Aller sur [openrouter.ai](https://openrouter.ai)
2. Creer un compte (email + mot de passe)
3. Aller dans **Keys** et creer une cle API
4. Copier la cle (format : `sk-or-v1-...`)

### 2.2 Ajouter du credit

OpenRouter fonctionne au pay-per-use. Ajoutez du credit (minimum $5) dans **Credits**.

Pour le cours, $5-10 devrait suffire pour plusieurs jours d'utilisation.

### 2.3 Configurer Claude Code avec OpenRouter

Creer ou modifier le fichier `~/.claude.json` (dans votre dossier utilisateur) :

```json
{
  "apiProvider": "openrouter",
  "openRouterApiKey": "sk-or-v1-VOTRE_CLE_ICI",
  "openRouterModel": "anthropic/claude-sonnet-4-20250514"
}
```

**Modeles recommandes** :

| Modele | ID OpenRouter | Prix/1M tokens | Usage |
|--------|--------------|---------------|-------|
| Claude Sonnet 4 | `anthropic/claude-sonnet-4-20250514` | $3/$15 | Recommande - bon rapport qualite/prix |
| Claude Haiku 3.5 | `anthropic/claude-haiku-3-5-20241022` | $0.80/$4 | Economique pour taches simples |
| Gemini 2.5 Flash | `google/gemini-2.5-flash-preview` | $0.15/$0.60 | Le moins cher, correct pour du code simple |
| GPT-4o | `openai/gpt-4o` | $2.50/$10 | Alternative solide |

> **Conseil** : Commencez avec Claude Sonnet 4. C'est le modele qui comprend le mieux le code QuantConnect.

### 2.4 Verifier la configuration

```bash
claude "Dis bonjour en une phrase"
```

Si vous obtenez une reponse, la configuration est correcte.

---

## 3. Workflow avec QuantConnect Cloud

### 3.1 Creer un projet sur QuantConnect Cloud

1. Se connecter sur [quantconnect.com](https://www.quantconnect.com)
2. Aller dans **Lab** > **Create New Project**
3. Choisir **Python** comme langage
4. Nommer le projet (ex: `ESGF-EMA-Starter`)
5. Ouvrir le fichier `main.py` genere par defaut

### 3.2 Structure d'un projet QuantConnect

```
mon-projet/
  main.py          # Algorithme principal (OBLIGATOIRE)
  research.ipynb   # Notebook de recherche (optionnel)
  README.md        # Documentation (optionnel)
```

Le fichier `main.py` doit contenir une classe qui herite de `QCAlgorithm` avec au minimum `Initialize()` et `OnData()`.

### 3.3 Utiliser Claude Code pour ecrire un algorithme

#### Methode 1 : Copier-coller

1. Ouvrir Claude Code dans un dossier quelconque
2. Demander : "Ecris un algorithme QuantConnect qui fait du croisement EMA sur BTCUSDT"
3. Copier le code genere dans QuantConnect Lab
4. Compiler et backtester

#### Methode 2 : Projet local (recommande)

```bash
mkdir mon-projet && cd mon-projet
git init
claude
```

Puis dans Claude Code :

```
> Cree un fichier main.py avec une strategie EMA crossover sur BTCUSDT.
> La strategie doit acheter quand EMA 12 croise au-dessus de EMA 26
> et vendre quand EMA 12 croise en dessous de EMA 26.
```

Recuperer le fichier genere, Copier le contenu dans QuantConnect Lab.

---

## 4. Exemples pratiques

### 4.1 Strategie Starter : EMA Crossover

Prompt pour Claude Code :

```
Ecris un algorithme QuantConnect en Python avec :
- Backtest du 1er janvier 2023 au 31 decembre 2024
- Capital initial : 10 000 USDT
- Actif : BTCUSDT sur Binance, resolution horaire
- Indicateurs : EMA rapide (12h) et EMA lente (26h)
- Logique : acheter quand EMA rapide > EMA lente, vendre sinon
- Prechauffage de 26 bougies
- Benchmark sur BTC
```

### 4.2 Ajouter un filtre RSI

Prompt pour ameliorer la strategie :

```
Modifie l'algorithme precedent pour ajouter :
- Un indicateur RSI(14) en resolution horaire
- Ne pas acheter si RSI > 70 (surachat)
- Ne pas vendre si RSI < 30 (survente)
- Ajouter un Debug message quand un trade est filtre par RSI
```

### 4.3 Ajouter un stop-loss

```
Ajoute un stop-loss a -5% sur chaque position :
- Suivre le prix d'entree dans une variable self.entry_price
- Dans OnData, si le prix actuel est plus de 5% sous self.entry_price, liquider
- Reinitialiser self.entry_price apres liquidation
```

### 4.4 Analyser un backtest

Apres avoir lance un backtest sur QuantConnect Cloud, vous pouvez demander a Claude Code :

```
Mon backtest EMA sur BTCUSDT (2023-2024) donne :
- Sharpe Ratio : 0.85
- CAGR : 22.3%
- Max Drawdown : 35.2%
- Win Rate : 48%
- Total Trades : 156

Peux-tu analyser ces resultats et suggerer des ameliorations ?
```

---

## 5. Conseils pour de bons prompts

### Bonnes pratiques

**Soyez specifique** :
- "Ecris une strategie EMA crossover sur BTCUSDT en resolution horaire" (bon)
- "Fais une strategie de trading" (trop vague)

**Fournissez le contexte** :
- Mentionnez que vous utilisez QuantConnect
- Precisez la resolution des donnees (Hour, Daily, Minute)
- Indiquez la classe d'actif (Crypto, Equity, Forex)

**Iterez progressivement** :
1. Commencez par une strategie simple (EMA crossover)
2. Ajoutez des filtres un par un (RSI, stop-loss, volume)
3. Backtestez apres chaque modification
4. Analysez les resultats avant la prochaine iteration

### Structure d'un bon prompt QuantConnect

```
Contexte : Je cree une strategie [type] sur [actif]
Objectif : [ce que la strategie doit faire]
Contraintes :
- Periode : [dates]
- Capital : [montant]
- Resolution : [Hour/Daily/Minute]
- Actif : [symbole] sur [marche]

Code actuel (si modification) :
```python
# collez votre code ici
```

Ce que je veux changer : [description precise]
```

---

## 6. Workflow complet (pas a pas)

### Premier projet

1. **Creer le projet** sur QuantConnect Cloud (Lab > New Project > Python)
2. **Ouvrir Claude Code** dans un terminal
3. **Generer le code** :

```
Ecris un algorithme QuantConnect Python avec :
- Classe heritant de QCAlgorithm
- Initialize() : periode 2023-2024, 10000 USDT, BTCUSDT Hourly Binance
- EMA 12 et EMA 26
- OnData() : acheter si EMA rapide > EMA lente, liquider sinon
- SetWarmUp(26)
```

4. **Copier le code** dans QuantConnect Lab
5. **Compiler** (Build > Build) -- verifier qu'il n'y a pas d'erreurs
6. **Backtester** (Build > Backtest) -- attendre les resultats
7. **Analyser** le rapport (Sharpe, CAGR, Drawdown, trades)
8. **Iterer** avec Claude Code pour ameliorer

### Iteration

Apres chaque backtest, copiez les metriques cles dans Claude Code :

```
Mon backtest EMA BTCUSDT donne :
- Sharpe : [valeur]
- CAGR : [valeur]
- Max Drawdown : [valeur]
- Trades : [nombre]
- Win Rate : [valeur]

Suggerere 3 ameliorations concretes avec le code a modifier.
```

---

## 7. Limites et precautions

### Ce que Claude Code peut faire

- Ecrire et modifier du code QuantConnect
- Expliquer des concepts de trading (indicateurs, signaux, gestion de risque)
- Sugerer des ameliorations basees sur les metriques de backtest
- Debugger des erreurs de compilation
- Creer des notebooks de recherche (fichiers .ipynb)

### Ce que Claude Code NE peut PAS faire

- Executer des backtests directement (sauf via MCP, section 8)
- Acceder a votre compte QuantConnect
- Garantir la rentabilite d'une strategie
- Remplacer la comprehension des concepts (apprenez d'abord, puis automatisez)

### Bonnes pratiques

- **Toujours backtester** avant de considerer une strategie validee
- **Comprendre le code** que Claude genere -- ne copiez jamais aveugle
- **Ne pas sur-optimiser** sur les donnees historiques (risque d'overfitting)
- **Garder des strategies simples** -- la complexite n'ameliore pas toujours les performances

---

## 8. Configuration avancee : QuantConnect MCP (optionnel)

Le MCP (Model Context Protocol) permet a Claude Code d'interagir directement avec QuantConnect Cloud pour creer des projets, compiler et backtester sans copier-coller.

### 8.1 Prerequis

- Un token API QuantConnect : **Account** > **API Access** > **Request Token**
- L'ID de votre organisation ESGF (fourni par le professeur)

### 8.2 Configuration

Creer un fichier `.mcp.json` a la racine de votre projet :

```json
{
  "mcpServers": {
    "quantconnect": {
      "command": "docker",
      "args": [
        "run", "--rm", "-i",
        "-e", "QUANTCONNECT_USER_ID",
        "-e", "QUANTCONNECT_API_TOKEN",
        "-e", "QUANTCONNECT_ORGANIZATION_ID",
        "quantconnect/mcp-server"
      ],
      "env": {
        "QUANTCONNECT_USER_ID": "VOTRE_USER_ID",
        "QUANTCONNECT_API_TOKEN": "VOTRE_TOKEN",
        "QUANTCONNECT_ORGANIZATION_ID": "VOTRE_ORG_ID"
      }
    }
  }
}
```

> **Important** : Ne commettez JAMAIS le fichier `.mcp.json` dans git (il contient vos tokens).

### 8.3 Utilisation

Avec le MCP configure, Claude Code peut :

- `create_project` : Creer un projet sur QC Cloud
- `create_file` : Ajouter un fichier au projet
- `create_compile` : Compiler le code
- `create_backtest` : Lancer un backtest
- `read_backtest` : Lire les resultats

Exemple de workflow complet avec MCP :

```
Cree un projet "ESGF-EMA-Starter" sur QuantConnect Cloud avec une
strategie EMA crossover sur BTCUSDT, compile-le, et lance un backtest
sur 2023-2024.
```

---

## 9. Ressources complementaires

### Documentation QuantConnect

- [Documentation officielle](https://www.quantconnect.com/docs)
- [Examples de strategies](https://www.quantconnect.com/strategies/)
- [Forum communautaire](https://www.quantconnect.com/forum/)

### Notre depot de cours

- [Catalogue de strategies](../projects/README.md) : 67 strategies backtestees
- [Notebooks progressifs](../Python/) : 28 notebooks QC-Py-01 a QC-Py-28
- [Templates ESGF](../templates/) : Starter, Intermediate, Advanced

### Claude Code

- [Documentation Claude Code](https://docs.anthropic.com/en/docs/claude-code)
- [OpenRouter](https://openrouter.ai) : Routeur API multi-modeles

---

## 10. FAQ

### "Claude Code me dit qu'il ne connait pas QuantConnect"

Ajoutez ce contexte dans votre prompt :

```
Tu es un expert QuantConnect. Les algorithmes QuantConnect en Python
herient de QCAlgorithm et doivent implementer Initialize() et OnData().
Les imports se font via `from AlgorithmImports import *`.
```

### "Le code genere ne compile pas sur QC Cloud"

Erreurs courantes :
- Oubli de `from AlgorithmImports import *`
- Méthodes mal orthographiées (`OnData` pas `onData`)
- Indentation incorrecte (Python est sensible)
- Utilisation de bibliotheques non disponibles sur QC Cloud

Copiez le message d'erreur dans Claude Code pour qu'il corrige.

### "Comment choisir entre les modeles ?"

- **Debutant** : Utilisez Gemini Flash (moins cher, correct pour du code simple)
- **Standard** : Claude Sonnet (meilleur pour comprendre et generer du code QC)
- **Probleme complexe** : Claude Opus ou GPT-4o (plus cher mais plus capable)

### "Combien ca coute ?"

Avec OpenRouter, vous payez au token. Estimation :
- Une session typique (1h) : $0.10 - $0.50 avec Sonnet
- Un projet complet (3-4h) : $0.50 - $2.00
- Avec Gemini Flash : 10x moins cher

---

*Derniere mise a jour : Avril 2026*
