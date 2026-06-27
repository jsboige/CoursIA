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
| [01-Claude-CLI-Bases](01-Claude-CLI-Bases.ipynb) | 20 min | Débutant | Installation, premiere commande, formats de sortie |
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

Si vous n'avez pas de clé API configurée, les notebooks peuvent fonctionner en mode simulation. Definissez la variable dans la premiere cellule :

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

## Ressources

- [Guide Installation](../docs/INSTALLATION-CLAUDE-CODE.md)
- [Modèles Alternatifs OpenRouter](../docs/INSTALLATION-CLAUDE-CODE.md#modeles-alternatifs-via-openrouter)
- [Cheat Sheet](../docs/CHEAT-SHEET.md)
- [Documentation Officielle Claude Code](https://docs.claude.com/code)

---

*Ces notebooks font partie de la série Vibe-Coding du cours GenAI.*
