# Notebooks Interactifs Claude CLI

Cette série de notebooks Jupyter permet d'apprendre et d'expérimenter avec Claude Code en ligne de commande (`claude -p "..."`).

## Prérequis

Avant d'exécuter ces notebooks, assurez-vous d'avoir :

1. **Claude Code CLI installé** :
   ```bash
   claude --version
   ```

2. **OpenRouter configuré** (ou Anthropic directement) :
   ```bash
   claude /status
   ```

3. **Python 3.9+** avec les dépendances :
   ```bash
   pip install jupyter ipykernel
   ```

## Notebooks Disponibles

| Notebook | Durée | Niveau | Description |
|----------|-------|--------|-------------|
| [01-Claude-CLI-Bases](01-Claude-CLI-Bases.ipynb) | 20 min | Débutant | Installation, première commande, formats de sortie |
| [02-Claude-CLI-Sessions](02-Claude-CLI-Sessions.ipynb) | 25 min | Débutant | Gestion des conversations et sessions |
| [03-Claude-CLI-References](03-Claude-CLI-References.ipynb) | 25 min | Intermédiaire | @-mentions, contexte fichiers, CLAUDE.md |
| [04-Claude-CLI-Agents](04-Claude-CLI-Agents.ipynb) | 30 min | Intermédiaire | Agents Explore, Plan, subagents |
| [05-Claude-CLI-Automatisation](05-Claude-CLI-Automatisation.ipynb) | 30 min | Avancé | Pipelines, scripts, hooks |

**Durée totale estimée : 2h10**

## Structure du Répertoire

```
notebooks/
├── README.md                    # Ce fichier
├── 01-Claude-CLI-Bases.ipynb
├── 02-Claude-CLI-Sessions.ipynb
├── 03-Claude-CLI-References.ipynb
├── 04-Claude-CLI-Agents.ipynb
├── 05-Claude-CLI-Automatisation.ipynb
├── helpers/
│   ├── __init__.py
│   └── claude_cli.py            # Fonctions utilitaires
└── examples/
    ├── sample_project/          # Mini-projet pour demos
    │   ├── main.py
    │   ├── utils.py
    │   └── tests/
    │       └── test_utils.py
    └── CLAUDE.md                # Exemple de fichier CLAUDE.md
```

## Utilisation

### Execution Standard

Ouvrez les notebooks dans VS Code ou Jupyter Lab :

```bash
# VS Code
code 01-Claude-CLI-Bases.ipynb

# Jupyter Lab
jupyter lab
```

### Mode Simulation (Sans API)

Si vous n'avez pas de clé API configurée, les notebooks peuvent fonctionner en mode simulation. Definissez la variable dans la première cellule :

```python
SIMULATION_MODE = True
```

Les appels a Claude seront simules avec des réponses d'exemple.

## Coûts API

Chaque exécution de cellule consomme des tokens. Estimation par notebook :

| Notebook | Tokens estimés | Coût approximatif* |
|----------|---------------|-------------------|
| 01-Bases | ~2,000 | ~$0.01 |
| 02-Sessions | ~3,000 | ~$0.02 |
| 03-References | ~5,000 | ~$0.03 |
| 04-Agents | ~8,000 | ~$0.05 |
| 05-Automatisation | ~10,000 | ~$0.06 |

*Basé sur les tarifs OpenRouter avec GLM-4.7-Flash. Les coûts varient selon le modèle utilise.

## Module Helpers

Le module `helpers/claude_cli.py` fournit des fonctions utilitaires :

```python
from helpers.claude_cli import (
    run_claude,           # Execute claude -p et retourne stdout/stderr
    run_claude_json,      # Execute et parse la reponse JSON
    run_claude_continue,  # Continue une session avec -c
    run_claude_command,   # Execute une commande slash (/sessions, /status)
    get_claude_version,   # Retourne la version de Claude CLI
    check_claude_status,  # Verifie la connexion
    verify_installation   # Verifie l'installation
)

# Exemple
stdout, stderr, code = run_claude("Bonjour", model="haiku")
print(stdout)

# Continuer une conversation
stdout, stderr, code = run_claude_continue("Et pour les tuples ?")

# Commande slash
stdout, stderr, code = run_claude_command("/sessions")
```

## Fichiers Exemples

Le répertoire `examples/` contient des fichiers pour les exercices des notebooks 03-05 :

- **sample_project/** : Mini-projet Python avec structure standard
- **CLAUDE.md** : Exemple de fichier de contexte projet

## Résolution de Problèmes

### "claude: command not found"

1. Vérifiez l'installation : `where.exe claude` (Windows) ou `which claude` (macOS/Linux)
2. Ajoutez Claude au PATH si nécessaire
3. Redémarrez votre terminal/VS Code

### "Authentication failed"

1. Vérifiez les variables d'environnement :
   ```bash
   echo $ANTHROPIC_BASE_URL
   echo $ANTHROPIC_AUTH_TOKEN
   ```
2. Consultez [INSTALLATION-CLAUDE-CODE.md](../docs/INSTALLATION-CLAUDE-CODE.md)

### Timeout lors de l'exécution

Certaines commandes peuvent prendre du temps. Augmentez le timeout :

```python
stdout, stderr, code = run_claude("Question complexe", timeout=120)
```

### Réponses qui décrivent votre propre configuration Claude Code

Lancés depuis une session Claude Code (terminal intégré de l'extension, ou agent qui exécute les carnets avec papermill), les appels `claude -p` des cellules héritent de cette session :

- ses variables d'environnement (`CLAUDECODE`, `CLAUDE_CODE_*`, `MCP_*`) ;
- votre `CLAUDE.md` global, vos serveurs MCP, vos hooks et vos skills.

Les réponses décrivent alors votre propre configuration (outils MCP bloqués, fichier écrit « dans le scratchpad », permissions refusées « ce cycle ») au lieu de ce qu'obtient une personne qui vient de cloner le dépôt. Certaines cellules dépassent aussi leur délai.

Pour une exécution propre, retirez ces variables et activez le mode sûr de la CLI. `CLAUDE_CODE_SAFE_MODE=1` équivaut à l'option `--safe-mode` : `CLAUDE.md`, serveurs MCP, hooks, skills et plugins sont désactivés, et l'authentification par les variables `ANTHROPIC_*` est conservée. Depuis un terminal bash (Git Bash sous Windows) :

```bash
cd MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks
U=$(env | grep -E '^(CLAUDECODE|CLAUDE_[A-Z_]*|MCP_[A-Z_]*)=' | cut -d= -f1 | sed 's/^/-u /' | tr '\n' ' ')
env $U CLAUDE_CODE_SAFE_MODE=1 python -m papermill 04-Claude-CLI-Agents.ipynb 04-Claude-CLI-Agents.ipynb -k python3 --cwd .
```

Un dossier de configuration vide (`CLAUDE_CONFIG_DIR` pointé vers un répertoire neuf) ne convient pas : la CLI s'y considère comme non connectée.

Après l'exécution, cherchez dans les sorties les mots `scratchpad`, `MCP`, `cycle`, `permission` et `session` : chacun peut signaler une fuite de la configuration locale.

### « Les permissions bloquent l'écriture / l'exécution »

Ce message ne vient pas de votre configuration, et tout lecteur le verrait. En mode `-p`, personne ne peut approuver une action : tout outil qui demanderait une autorisation (écrire un fichier, lancer une commande) est refusé automatiquement. L'agent avait pris l'initiative de vérifier son travail, et il l'annonce non vérifié.

La parade est de donner à chaque agent les outils de son rôle, et eux seuls :

- un agent d'analyse reçoit les seuls outils de lecture : `--tools "Read,Glob,Grep"` ;
- un agent qui écrit et exécute travaille dans une copie temporaire du projet, avec des droits précis : `--allowedTools Write "Bash(python -m pytest *)"`.

Le carnet [04-Claude-CLI-Agents](04-Claude-CLI-Agents.ipynb) applique ces deux voies (section « Les permissions en mode `claude -p` ») ; le helper les transmet par `run_claude(..., extra_args=[...])`.

## Ressources

- [Guide Installation](../docs/INSTALLATION-CLAUDE-CODE.md)
- [Modèles Alternatifs OpenRouter](../docs/INSTALLATION-CLAUDE-CODE.md#modeles-alternatifs-via-openrouter)
- [Cheat Sheet](../docs/CHEAT-SHEET.md)
- [Documentation Officielle Claude Code](https://docs.claude.com/code)

---

*Ces notebooks font partie de la série Vibe-Coding du cours GenAI.*
