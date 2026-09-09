# Demo 1 - Première Session avec Claude Code

## Objectif

Installer Claude Code, configurer l'accès via OpenRouter, et réaliser votre première interaction avec l'assistant.

## Durée estimée

**45 minutes**

## Prérequis

- VS Code installé
- Node.js 18+ installé (`node --version`) — requis uniquement pour le proxy OpenRouter (brique d'accès aux modèles), pas pour l'installation native de Claude Code
- Compte OpenRouter avec clé API

## Étapes

### Étape 1 : Installation de Claude Code CLI (10 min)

#### Chemin canonique : installation native

C'est la méthode par défaut de la documentation officielle Anthropic — Node.js n'est pas requis pour cette étape :

- **Windows** : installateur depuis [claude.com/code](https://claude.com/code)
- **macOS** : `brew install --cask claude-code`
- **Linux / WSL** : `curl -fsSL https://install.claude.com | sh`

Alternative npm (uniquement si votre poste interdit les binaires hors gestionnaire de paquets) : voir le [guide d'installation canonique](../../docs/INSTALLATION-CLAUDE-CODE.md).

#### Vérification

```bash
claude --version
```

Vous devriez voir quelque chose comme : `claude-code v1.x.x`

### Étape 2 : Configuration OpenRouter (10 min)

OpenRouter permet d'accéder à plusieurs modèles avec une clé unique. **Suivez le guide canonique** [Quickstart : Claude Code + OpenRouter](../../docs/OPENROUTER_SETUP.md) : il installe le proxy local, définit les variables d'environnement et mappe les modèles, étape par étape avec checkpoints.

En résumé : la configuration passe par le proxy local `openrouter-proxy` (`ANTHROPIC_BASE_URL = http://127.0.0.1:8899/api`). Les requêtes OpenRouter ne sont pas strictement compatibles avec le protocole Anthropic utilisé par Claude Code (bug connu) — le proxy traduit les requêtes. Ne pointez pas `ANTHROPIC_BASE_URL` directement vers `https://openrouter.ai/api`.

### Étape 3 : Première session interactive (15 min)

#### Lancer Claude Code

```bash
claude
```

Vous entrez dans une session interactive. Le prompt change pour indiquer que vous parlez à Claude.

#### Commandes de base

| Commande | Description |
|----------|-------------|
| `/help` | Affiche l'aide |
| `/status` | Vérifie la connexion |
| `/clear` | Efface l'historique |
| `/exit` ou `Ctrl+C` | Quitte la session |

#### Première question

Posez une question simple pour vérifier que tout fonctionne :

```
Bonjour Claude ! Peux-tu te présenter brièvement ?
```

### Étape 4 : Explorer les modes d'interaction (10 min)

#### Mode interactif (conversation)

```bash
claude
```

Permet une conversation continue avec historique.

#### Mode query (question unique)

```bash
claude -p "Quelle est la syntaxe d'une boucle for en Python ?"
```

Exécute une seule question et retourne au terminal.

#### Continuer une session

```bash
claude -c
```

Reprend la dernière conversation où vous l'aviez laissée.

#### Changer de modèle

```bash
# Modèle par défaut (sonnet)
claude

# Modèle plus puissant
claude --model opus

# Modèle rapide et économique
claude --model haiku
```

## Exercice pratique

### Questions progressives

Créez un fichier `mes-premieres-questions.md` et documentez vos échanges avec Claude en posant ces 5 questions :

1. **Question factuelle** : "Qu'est-ce que le pattern MVC en développement web ?"

2. **Question de comparaison** : "Quelles sont les différences entre REST et GraphQL ?"

3. **Question de recommandation** : "Je débute en Python, quelles bibliothèques dois-je apprendre en priorité ?"

4. **Question de génération** : "Génère un exemple de classe Python représentant un utilisateur avec nom, email et méthodes de validation."

5. **Question d'analyse** : "Voici du code : `[1,2,3].map(x => x*2)`. Explique ce qu'il fait et traduis-le en Python."

### Format du livrable

```markdown
# Mes Premières Questions - Claude Code

## Question 1 : Pattern MVC
**Ma question** : Qu'est-ce que le pattern MVC en développement web ?

**Réponse de Claude** :
[Copiez la réponse ici]

**Mon analyse** : [Votre ressenti sur la réponse]

---

## Question 2 : REST vs GraphQL
...
```

## Points clés à retenir

1. **Installation** : chemin canonique = installation native (défaut officiel, Node.js non requis) ; npm reste une alternative conditionnelle

2. **Configuration OpenRouter** : 3 variables d'environnement à définir

3. **Modes d'interaction** :
   - `claude` : session interactive
   - `claude -p "..."` : question unique
   - `claude -c` : continuer session

4. **Modèles disponibles** :
   - `sonnet` : équilibré (défaut)
   - `opus` : puissant
   - `haiku` : rapide

## Dépannage

### "command not found: claude"

- Installation native : le binaire vit sous `~/.local/bin` — vérifiez que ce répertoire est dans votre PATH, puis redémarrez votre terminal
- Alternative npm (si c'est le chemin que vous avez choisi) : vérifiez Node.js (`node --version`), réinstallez avec `npm install -g @anthropic-ai/claude-code`, vérifiez le PATH avec `npm bin -g`

### "Authentication failed"

- Vérifiez votre clé OpenRouter
- Assurez-vous que les variables d'environnement sont définies
- Testez avec : `echo $ANTHROPIC_AUTH_TOKEN` (Linux/Mac) ou `$env:ANTHROPIC_AUTH_TOKEN` (PowerShell)

### Réponse très lente

- Vérifiez votre connexion internet
- Essayez le modèle haiku : `claude --model haiku`

## Ressources

- [Guide d'installation détaillé](../../docs/INSTALLATION-CLAUDE-CODE.md)
- [Documentation officielle](https://docs.anthropic.com/en/docs/claude-code)

---

**Prochaine étape** : [Demo 2 - Références et Contexte](../demo-2-references-contexte/)
