# Quickstart : Claude Code + OpenRouter

**15 minutes pour etre operationnel.**

Ce guide vous prend par la main pour configurer Claude Code avec OpenRouter comme fournisseur de modeles. Suivez les etapes dans l'ordre, et validez chaque checkpoint avant de passer a la suivante.

> **Pourquoi OpenRouter ?** Au lieu d'utiliser l'API Anthropic (payante, compte obligatoire), OpenRouter vous donne acces a des modeles performants a moindre cout, avec une cle unique pour plusieurs modeles.
>
> **Compatibilite OpenRouter** : Les requetes OpenRouter ne sont pas strictement compatibles avec le protocole Anthropic utilise par Claude Code (bug connu). L'installation du proxy [openrouter-proxy](https://github.com/ahaostudy/openrouter-proxy) resout le probleme. La configuration ci-dessous inclut cette etape.

---

## Etape 0 : Installer le proxy OpenRouter (2 min)

Claude Code utilise le protocole Anthropic pour communiquer avec les modeles. OpenRouter ne respecte pas strictement ce protocole, ce qui provoque des erreurs (reponses mal formatees, echecs d'authentification intermittents). Le proxy [openrouter-proxy](https://github.com/ahaostudy/openrouter-proxy) traduit les requetes correctement.

### Installation

```bash
# Installer le proxy globalement via npm
npm install -g openrouter-proxy
```

### Demarrage

```bash
# Lance le proxy sur le port 8899 par defaut
openrouter-proxy
```

Le proxy tourne en arriere-plan et traduit les requetes Claude Code vers OpenRouter. Gardez-le actif tant que vous utilisez Claude Code.

### Lancement automatique (optionnel)

Pour eviter de le lancer manuellement a chaque session :

**Windows** - Ajoutez a votre profil PowerShell (`notepad $PROFILE`) :

```powershell
Start-Process -WindowStyle Hidden -FilePath "openrouter-proxy"
```

**macOS / Linux** - Ajoutez a `~/.zshrc` ou `~/.bashrc` :

```bash
(openrouter-proxy &>/dev/null &)
```

**Checkpoint :** Verifiez que le proxy tourne :

```bash
curl http://127.0.0.1:8899/api/v1/models
```

Si vous voyez une reponse JSON avec des modeles, le proxy fonctionne.

---

## Etape 1 : Installer Claude Code (3 min)

### Windows

Telechargez l'installateur depuis [claude.com/code](https://claude.com/code), executez le `.exe`, suivez les instructions.

### macOS

```bash
brew install --cask claude-code
```

### Linux / WSL

```bash
curl -fsSL https://install.claude.com | sh
```

### Verifier

```bash
claude --version
```

**Checkpoint :** Vous devez voir un numero de version. Sinon, redemarrez votre terminal et reessayez.

---

## Etape 2 : Obtenir votre cle API OpenRouter (2 min)

**La cle vous est fournie par le formateur.** Elle ressemble a `sk-or-v1-xxxxxxxxxx`.

Si vous voulez votre propre cle :
1. Allez sur [openrouter.ai](https://openrouter.ai/)
2. Creez un compte
3. [Settings > API Keys](https://openrouter.ai/settings/keys) > "Create Key"
4. Copiez la cle (elle ne sera plus affichee apres)

**Checkpoint :** Vous avez une cle qui commence par `sk-or-v1-`.

---

## Etape 3 : Configurer les variables d'environnement (5 min)

C'est l'etape la plus importante. Vous devez definir **3 variables obligatoires** + **3 variables de mapping de modeles** (fortement recommandees).

### Ce que vous configurez

| Variable | Valeur | Role |
|----------|--------|------|
| `ANTHROPIC_BASE_URL` | `http://127.0.0.1:8899/api` | Passe par le proxy OpenRouter (Etape 0) au lieu d'Anthropic |
| `ANTHROPIC_AUTH_TOKEN` | `sk-or-v1-VOTRE_CLE` | Votre cle d'authentification OpenRouter |
| `ANTHROPIC_API_KEY` | *(vide)* | Doit etre vide pour ne pas conflit avec OpenRouter |
| `ANTHROPIC_DEFAULT_OPUS_MODEL` | `qwen/qwen3.6-plus` | Modele "opus" = Qwen 3.6 Plus (raisonnement complexe) |
| `ANTHROPIC_DEFAULT_SONNET_MODEL` | `minimax/minimax-m2.7` | Modele "sonnet" = MiniMax M2.7 (usage quotidien) |
| `ANTHROPIC_DEFAULT_HAIKU_MODEL` | `qwen/qwen3.5-27b` | Modele "haiku" = Qwen 3.5 27B (taches rapides) |

### Pourquoi le mapping des modeles ?

Sans les variables `ANTHROPIC_DEFAULT_*_MODEL`, Claude Code essaie d'utiliser les modeles Claude natifs (`claude-sonnet-4-20250514`, etc.), qui **ne sont pas disponibles via OpenRouter**. Vous obtiendrez une erreur "Model not found".

Le mapping dit a Claude Code : "quand on te demande 'sonnet', utilise MiniMax M2.7 sur OpenRouter au lieu de chercher un modele Anthropic".

### Methode recommandee : fichier settings.json

Creez le fichier de configuration machine. C'est la methode la plus fiable car elle fonctionne dans tous les contextes (terminal, VS Code, scripts).

**Windows** : Creez le fichier `C:\Users\<VOTRE_USER>\.claude\settings.json`

**macOS / Linux** : Creez le fichier `~/.claude/settings.json`

Contenu (remplacez `sk-or-v1-VOTRE_CLE` par votre vraie cle) :

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "http://127.0.0.1:8899/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": "",
    "ANTHROPIC_DEFAULT_OPUS_MODEL": "qwen/qwen3.6-plus",
    "ANTHROPIC_DEFAULT_SONNET_MODEL": "minimax/minimax-m2.7",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL": "qwen/qwen3.5-27b"
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
$env:ANTHROPIC_DEFAULT_HAIKU_MODEL = "qwen/qwen3.5-27b"
```

Sauvegardez et rechargez :

```powershell
. $PROFILE
```

### Alternative : variables d'environnement macOS/Linux

Editez `~/.zshrc` (ou `~/.bashrc` si vous utilisez bash) :

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
export ANTHROPIC_DEFAULT_HAIKU_MODEL="qwen/qwen3.5-27b"
```

Rechargez :

```bash
source ~/.zshrc
```

**Checkpoint :** Fermez et rouvrez votre terminal, puis verifiez :

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

## Etape 4 : Installer l'extension VS Code (3 min)

1. Ouvrez VS Code
2. `Ctrl+Shift+X` (Windows/Linux) ou `Cmd+Shift+X` (macOS)
3. Recherchez **"Claude Code"**
4. Installez l'extension par **Anthropic**

### Reglage CRITIQUE : "Disable Login Prompt"

Sans ce reglage, VS Code vous demandera de vous connecter avec un compte Anthropic (inutile avec OpenRouter).

1. `Ctrl+,` / `Cmd+,` (Settings)
2. Recherchez **"Claude Code"**
3. Cochez **"Disable Login Prompt"**

**Checkpoint :** L'extension est installee et "Disable Login Prompt" est active.

---

## Etape 5 : Verifier que tout fonctionne (2 min)

### Test CLI

```bash
claude -p "Reponds juste 'OK' pour confirmer que tu fonctionnes"
```

Vous devez recevoir une reponse du modele (MiniMax M2.7 par defaut).

### Test des modeles

```bash
# Modele par defaut (sonnet = MiniMax M2.7)
claude -p "Reponds 'Sonnet OK'"

# Modele opus (Qwen 3.6 Plus)
claude --model opus -p "Reponds 'Opus OK'"

# Modele haiku (Qwen 3.5 27B)
claude --model haiku -p "Reponds 'Haiku OK'"
```

### Test VS Code

1. Cliquez sur l'icone Claude Code dans la barre laterale
2. Tapez : `Bonjour, confirme que tu fonctionnes`
3. Vous devez voir une reponse du modele

**Checkpoint :** Les 3 modeles repondent en CLI et l'extension VS Code fonctionne.

---

## Etape 6 : Premiers pas dans un projet (optionnel)

Ouvrez un dossier de projet dans votre terminal :

```bash
cd /chemin/vers/votre/projet
claude
```

Puis tapez :

```
/init
```

Claude Code va analyser votre projet et creer un fichier `CLAUDE.md` avec le contexte du projet. Ce fichier aide Claude a comprendre votre codebase.

---

## Les 3 modeles et quand les utiliser

| Alias | Modele | Quand l'utiliser |
|-------|--------|-----------------|
| **sonnet** (defaut) | MiniMax M2.7 | Developpement quotidien, debug, questions |
| **opus** | Qwen 3.6 Plus | Refactoring complexe, architecture, documentation |
| **haiku** | Qwen 3.5 27B | Questions rapides, exploration, prototypage |

Pour changer de modele dans une session :

```bash
claude --model opus    # utilise Qwen 3.6 Plus
claude --model sonnet  # utilise MiniMax M2.7 (defaut)
claude --model haiku   # utilise Qwen 3.5 27B
```

---

## Problemes frequents

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

- **Guide complet** : [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md) (installation avancee, MCP, configuration detaillee)
- **Aide-memoire** : [CHEAT-SHEET.md](./CHEAT-SHEET.md)
- **Concepts avances** : [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md) (Skills, Subagents, Hooks)
- **Introduction** : [INTRO-CLAUDE-CODE.md](./INTRO-CLAUDE-CODE.md)
