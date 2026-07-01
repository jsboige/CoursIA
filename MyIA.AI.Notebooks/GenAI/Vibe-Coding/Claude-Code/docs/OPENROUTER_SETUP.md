# Quickstart : Claude Code + OpenRouter

**15 minutes pour être opérationnel.**

Ce guide vous prend par la main pour configurer Claude Code avec OpenRouter comme fournisseur de modèles. Suivez les étapes dans l'ordre, et validez chaque checkpoint avant de passer a la suivante.

> **Pourquoi OpenRouter ?** Au lieu d'utiliser l'API Anthropic (payante, compte obligatoire), OpenRouter vous donne accès a des modèles performants a moindre coût, avec une clé unique pour plusieurs modèles.
>
> **Compatibilité OpenRouter** : Les requêtes OpenRouter ne sont pas strictement compatibles avec le protocole Anthropic utilise par Claude Code (bug connu). L'installation du proxy [openrouter-proxy](https://github.com/ahaostudy/openrouter-proxy) résout le problème. La configuration ci-dessous inclut cette étape.

---

## Étape 0 : Installer le proxy OpenRouter (2 min)

Claude Code utilise le protocole Anthropic pour communiquer avec les modèles. OpenRouter ne respecte pas strictement ce protocole, ce qui provoque des erreurs (réponses mal formatées, échecs d'authentification intermittents). Le proxy [openrouter-proxy](https://github.com/ahaostudy/openrouter-proxy) traduit les requêtes correctement.

### Installation

```bash
# Installer le proxy globalement via npm
npm install -g openrouter-proxy
```

### Démarrage

```bash
# Lance le proxy sur le port 8899 par defaut
openrouter-proxy
```

Le proxy tourne en arrière-plan et traduit les requêtes Claude Code vers OpenRouter. Gardez-le actif tant que vous utilisez Claude Code.

### Lancement automatique (optionnel)

Pour éviter de le lancer manuellement a chaque session :

**Windows** - Ajoutez a votre profil PowerShell (`notepad $PROFILE`) :

```powershell
Start-Process -WindowStyle Hidden -FilePath "openrouter-proxy"
```

**macOS / Linux** - Ajoutez a `~/.zshrc` ou `~/.bashrc` :

```bash
(openrouter-proxy &>/dev/null &)
```

**Checkpoint :** Vérifiez que le proxy tourne :

```bash
curl http://127.0.0.1:8899/api/v1/models
```

Si vous voyez une réponse JSON avec des modèles, le proxy fonctionne.

---

## Étape 1 : Installer Claude Code (3 min)

### Windows

Téléchargez l'installateur depuis [claude.com/code](https://claude.com/code), exécutez le `.exe`, suivez les instructions.

### macOS

```bash
brew install --cask claude-code
```

### Linux / WSL

```bash
curl -fsSL https://install.claude.com | sh
```

### Vérifier

```bash
claude --version
```

**Checkpoint :** Vous devez voir un numero de version. Sinon, redémarrez votre terminal et réessayez.

---

## Étape 2 : Obtenir votre clé API OpenRouter (2 min)

**La clé vous est fournie par le formateur.** Elle ressemble a `sk-or-v1-xxxxxxxxxx`.

Si vous voulez votre propre clé :
1. Allez sur [openrouter.ai](https://openrouter.ai/)
2. Créez un compte
3. [Settings > API Keys](https://openrouter.ai/settings/keys) > "Create Key"
4. Copiez la clé (elle ne sera plus affichée après)

**Checkpoint :** Vous avez une clé qui commence par `sk-or-v1-`.

---

## Étape 3 : Configurer les variables d'environnement (5 min)

C'est l'étape la plus importante. Vous devez définir **3 variables obligatoires** + **3 variables de mapping de modèles** (fortement recommandées).

### Ce que vous configurez

| Variable | Valeur | Role |
|----------|--------|------|
| `ANTHROPIC_BASE_URL` | `http://127.0.0.1:8899/api` | Passe par le proxy OpenRouter (Étape 0) au lieu d'Anthropic |
| `ANTHROPIC_AUTH_TOKEN` | `sk-or-v1-VOTRE_CLE` | Votre clé d'authentification OpenRouter |
| `ANTHROPIC_API_KEY` | *(vide)* | Doit être vide pour ne pas conflit avec OpenRouter |
| `ANTHROPIC_DEFAULT_OPUS_MODEL` | `qwen/qwen3.6-plus` | Modèle "opus" = Qwen 3.6 Plus (raisonnement complexe) |
| `ANTHROPIC_DEFAULT_SONNET_MODEL` | `minimax/minimax-m2.7` | Modèle "sonnet" = MiniMax M2.7 (usage quotidien) |
| `ANTHROPIC_DEFAULT_HAIKU_MODEL` | `qwen/qwen3.6-35b-a3b` | Modèle "haiku" = Qwen 3.6 35B-A3B (taches rapides) |

### Pourquoi le mapping des modèles ?

Sans les variables `ANTHROPIC_DEFAULT_*_MODEL`, Claude Code essaie d'utiliser les modèles Claude natifs (`claude-sonnet-4-20250514`, etc.), qui **ne sont pas disponibles via OpenRouter**. Vous obtiendrez une erreur "Model not found".

Le mapping dit a Claude Code : "quand on te demande 'sonnet', utilise MiniMax M2.7 sur OpenRouter au lieu de chercher un modèle Anthropic".

### Méthode recommandée : fichier settings.json

Créez le fichier de configuration machine. C'est la méthode la plus fiable car elle fonctionne dans tous les contextes (terminal, VS Code, scripts).

**Windows** : Créez le fichier `C:\Users\<VOTRE_USER>\.claude\settings.json`

**macOS / Linux** : Créez le fichier `~/.claude/settings.json`

Contenu (remplacez `sk-or-v1-VOTRE_CLE` par votre vraie clé) :

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "http://127.0.0.1:8899/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": "",
    "ANTHROPIC_DEFAULT_OPUS_MODEL": "qwen/qwen3.6-plus",
    "ANTHROPIC_DEFAULT_SONNET_MODEL": "minimax/minimax-m2.7",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL": "qwen/qwen3.6-35b-a3b"
  }
}
```

### Alternative : variables d'environnement PowerShell (Windows)

Si vous preferez les variables d'environnement, ouvrez votre profil :

```powershell
notepad $PROFILE
```

Ajoutez a la fin :

```powershell
# Configuration OpenRouter pour Claude Code
$env:ANTHROPIC_BASE_URL = "http://127.0.0.1:8899/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE"
$env:ANTHROPIC_API_KEY = ""
$env:ANTHROPIC_DEFAULT_OPUS_MODEL = "qwen/qwen3.6-plus"
$env:ANTHROPIC_DEFAULT_SONNET_MODEL = "minimax/minimax-m2.7"
$env:ANTHROPIC_DEFAULT_HAIKU_MODEL = "qwen/qwen3.6-35b-a3b"
```

Sauvegardez et rechargez :

```powershell
. $PROFILE
```

### Alternative : variables d'environnement macOS/Linux

Éditez `~/.zshrc` (ou `~/.bashrc` si vous utilisez bash) :

```bash
nano ~/.zshrc
```

Ajoutez a la fin :

```bash
# Configuration OpenRouter pour Claude Code
export ANTHROPIC_BASE_URL="http://127.0.0.1:8899/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE"
export ANTHROPIC_API_KEY=""
export ANTHROPIC_DEFAULT_OPUS_MODEL="qwen/qwen3.6-plus"
export ANTHROPIC_DEFAULT_SONNET_MODEL="minimax/minimax-m2.7"
export ANTHROPIC_DEFAULT_HAIKU_MODEL="qwen/qwen3.6-35b-a3b"
```

Rechargez :

```bash
source ~/.zshrc
```

**Checkpoint :** Fermez et rouvrez votre terminal, puis vérifiez :

```bash
# Windows
echo $env:ANTHROPIC_BASE_URL       # doit afficher: http://127.0.0.1:8899/api
echo $env:ANTHROPIC_AUTH_TOKEN      # doit afficher: sk-or-v1-...

# macOS/Linux
echo $ANTHROPIC_BASE_URL            # doit afficher: http://127.0.0.1:8899/api
echo $ANTHROPIC_AUTH_TOKEN          # doit afficher: sk-or-v1-...
```

Si les variables sont vides, le fichier settings.json n'est pas au bon endroit ou le profil n'a pas ete recharge.

---

## Étape 4 : Installer l'extension VS Code (3 min)

1. Ouvrez VS Code
2. `Ctrl+Shift+X` (Windows/Linux) ou `Cmd+Shift+X` (macOS)
3. Recherchez **"Claude Code"**
4. Installez l'extension par **Anthropic**

### Réglage CRITIQUE : "Disable Login Prompt"

Sans ce réglage, VS Code vous demandera de vous connecter avec un compte Anthropic (inutile avec OpenRouter).

1. `Ctrl+,` / `Cmd+,` (Settings)
2. Recherchez **"Claude Code"**
3. Cochez **"Disable Login Prompt"**

**Checkpoint :** L'extension est installee et "Disable Login Prompt" est active.

---

## Étape 5 : Vérifier que tout fonctionne (2 min)

### Test CLI

```bash
claude -p "Reponds juste 'OK' pour confirmer que tu fonctionnes"
```

Vous devez recevoir une réponse du modèle (MiniMax M2.7 par défaut).

### Test des modèles

```bash
# Modele par defaut (sonnet = MiniMax M2.7)
claude -p "Reponds 'Sonnet OK'"

# Modele opus (Qwen 3.6 Plus)
claude --model opus -p "Reponds 'Opus OK'"

# Modele haiku (Qwen 3.6 35B-A3B)
claude --model haiku -p "Reponds 'Haiku OK'"
```

### Test VS Code

1. Cliquez sur l'icone Claude Code dans la barre laterale
2. Tapez : `Bonjour, confirme que tu fonctionnes`
3. Vous devez voir une réponse du modèle

**Checkpoint :** Les 3 modèles répondent en CLI et l'extension VS Code fonctionne.

---

## Étape 6 : Premiers pas dans un projet (optionnel)

Ouvrez un dossier de projet dans votre terminal :

```bash
cd /chemin/vers/votre/projet
claude
```

Puis tapez :

```
/init
```

Claude Code va analyser votre projet et créer un fichier `CLAUDE.md` avec le contexte du projet. Ce fichier aide Claude a comprendre votre codebase.

---

## Les 3 modèles et quand les utiliser

| Alias | Modèle | Quand l'utiliser |
|-------|--------|-----------------|
| **sonnet** (défaut) | MiniMax M2.7 | Développement quotidien, debug, questions |
| **opus** | Qwen 3.6 Plus | Refactoring complexe, architecture, documentation |
| **haiku** | Qwen 3.6 35B-A3B | Questions rapides, exploration, prototypage |

Pour changer de modèle dans une session :

```bash
claude --model opus    # utilise Qwen 3.6 Plus
claude --model sonnet  # utilise MiniMax M2.7 (defaut)
claude --model haiku   # utilise Qwen 3.6 35B-A3B
```

---

## Problèmes fréquents

### "Authentication failed"

```
Verifiez que ANTHROPIC_AUTH_TOKEN est definie :
  Windows : echo $env:ANTHROPIC_AUTH_TOKEN
  macOS   : echo $ANTHROPIC_AUTH_TOKEN

Si vide : le fichier settings.json est mal place ou le profil n'est pas recharge.
```

### "Model not found"

```
Verifiez que les variables ANTHROPIC_DEFAULT_*_MODEL sont definies.
Sans elles, Claude Code cherche les modeles Anthropic natifs (inexistants sur OpenRouter).
```

### L'extension VS Code demande une connexion Anthropic

```
Activez "Disable Login Prompt" dans les parametres VS Code.
Voir Etape 4.
```

### "Rate limit exceeded"

```
Attendez quelques secondes et reessayez.
Verifiez vos credits sur openrouter.ai/activity
```

### Les variables d'environnement sont vides dans VS Code

```
VS Code ne lit pas toujours les variables du shell.
Preferez le fichier settings.json (Methode recommandee, Etape 3).
Sinon, redemarrez VS Code COMPLETEMENT (pas juste recharger la fenetre).
```

---

## Pour aller plus loin

- **Guide complet** : [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md) (installation avancée, MCP, configuration détaillée)
- **Aide-memoire** : [CHEAT-SHEET.md](./CHEAT-SHEET.md)
- **Concepts avancés** : [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md) (Skills, Subagents, Hooks)
- **Introduction** : [INTRO-CLAUDE-CODE.md](./INTRO-CLAUDE-CODE.md)
