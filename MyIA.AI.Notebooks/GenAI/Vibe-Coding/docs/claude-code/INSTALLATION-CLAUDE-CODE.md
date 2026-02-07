# Guide d'Installation de Claude Code

Ce guide vous explique comment installer et configurer Claude Code (CLI et extension VS Code) pour la formation, en utilisant OpenRouter comme fournisseur de modeles.

## Prerequis

- **Visual Studio Code** version 1.98.0 ou superieure : [Telecharger](https://code.visualstudio.com/)
- **Terminal** : PowerShell (Windows), bash/zsh (macOS/Linux)
- **Connexion internet**
- **Cle API OpenRouter** : Fournie par le formateur

## Installation de Claude Code

### Option 1 : Installation Native (Recommandee)

L'installation native ne necessite pas Node.js et fonctionne sur tous les systemes d'exploitation.

#### Windows

1. Telechargez l'installateur depuis [claude.com/code](https://claude.com/code)
1. Executez l'installateur `.exe`
1. Suivez les instructions a l'ecran
1. Redemarrez votre terminal

**Verification :**

```powershell
claude --version
```

#### macOS

```bash
# Via Homebrew
brew install --cask claude-code

# Ou telechargement direct
# Telechargez le .dmg depuis claude.com/code
```

**Verification :**

```bash
claude --version
```

#### Linux / WSL

```bash
# Installation via script
curl -fsSL https://install.claude.com | sh

# Ajouter au PATH (si necessaire)
echo 'export PATH="$HOME/.claude/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

**Verification :**

```bash
claude --version
```

### Option 2 : Installation via npm

Si vous avez deja Node.js 18+ installe :

```bash
npm install -g @anthropic-ai/claude-code
```

**Note :** L'installation native est preferee car elle evite les conflits de versions Node.js.

## Installation de l'Extension VS Code

### Methode 1 : Via VS Code Marketplace

1. Ouvrez **Visual Studio Code**
1. Appuyez sur `Ctrl+Shift+X` (Windows/Linux) ou `Cmd+Shift+X` (macOS)
1. Recherchez **"Claude Code"**
1. Trouvez l'extension officielle **"Claude Code" par Anthropic**
1. Cliquez sur **Installer**
1. Redemarrez VS Code si demande

### Methode 2 : Lien Direct

Cliquez sur ce lien : [Installer Claude Code pour VS Code](vscode:extension/anthropic.claude-code)

### Methode 3 : Command Palette

1. `Cmd+Shift+P` / `Ctrl+Shift+P`
1. Tapez : `Extensions: Install Extensions`
1. Recherchez **"Claude Code"**
1. Installez

## Configuration avec OpenRouter

### Etape 1 : Obtenir la Cle API OpenRouter

**La cle API vous sera fournie par le formateur.** Conservez-la precieusement.

Si vous souhaitez creer votre propre compte OpenRouter :

1. Visitez [openrouter.ai](https://openrouter.ai/)
1. Creez un compte
1. Accedez a [Settings > API Keys](https://openrouter.ai/settings/keys)
1. Creez une nouvelle cle API

### Etape 2 : Configuration des Variables d'Environnement

Pour utiliser Claude Code avec OpenRouter, vous devez configurer trois variables de base, plus optionnellement les aliases de modeles alternatifs.

#### Windows (PowerShell)

**Configuration temporaire (session actuelle) :**

```powershell
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "VOTRE_CLE_OPENROUTER"
$env:ANTHROPIC_API_KEY = ""
```

**Configuration permanente (profil PowerShell) :**

Ouvrez votre profil PowerShell :

```powershell
notepad $PROFILE
```

Ajoutez les lignes suivantes :

```powershell
# ============================================
# Configuration OpenRouter pour Claude Code
# ============================================

# Configuration de base OpenRouter
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE_OPENROUTER"
$env:ANTHROPIC_API_KEY = ""

# Mapping des aliases de modeles (optionnel - voir section Modeles Alternatifs)
$env:ANTHROPIC_DEFAULT_OPUS_MODEL = "z-ai/glm-4.7"
$env:ANTHROPIC_DEFAULT_SONNET_MODEL = "qwen/qwen3-coder-next"
$env:ANTHROPIC_DEFAULT_HAIKU_MODEL = "z-ai/glm-4.7-flash"
```

Sauvegardez et rechargez :

```powershell
. $PROFILE
```

#### macOS / Linux (Zsh/Bash)

**Quel fichier editer ?** Sur macOS moderne (Catalina+), le shell par defaut est **zsh**. Selon votre configuration, editez **l'un** des fichiers suivants :

- **`~/.zshrc`** : Source pour tous les shells zsh interactifs (Terminal + VSCode). **Recommande** - couvre tous les cas.
- **`~/.zprofile`** : Source uniquement pour les shells zsh de connexion (login). Fonctionne avec Terminal.app/iTerm2, mais **pas toujours** avec le terminal VSCode.
- **`~/.bashrc`** : Shells bash interactifs. Uniquement si vous utilisez bash (`chsh -s /bin/bash`).
- **`~/.bash_profile`** : Shells bash de connexion. Meme remarque que `.zprofile` pour bash.

> **Conseil :** Si vous avez deja un `~/.zprofile` mais pas de `~/.zshrc`, le plus simple est de creer `~/.zshrc` ou d'ajouter les exports dans votre `~/.zprofile` existant. Les deux fonctionnent depuis Terminal.app. Si vous utilisez aussi le terminal integre de VSCode, preferez `~/.zshrc`.

Pour verifier quel shell vous utilisez :

```bash
echo $SHELL    # Affiche /bin/zsh ou /bin/bash
```

Pour verifier quels fichiers de profil existent deja :

```bash
ls -la ~/.zshrc ~/.zprofile ~/.bashrc ~/.bash_profile 2>/dev/null
```

Editez le fichier adapte (exemple avec `~/.zshrc`) :

```bash
nano ~/.zshrc    # ou: nano ~/.zprofile si c'est votre seul fichier de profil
```

Ajoutez les lignes suivantes a la fin du fichier :

```bash
# ============================================
# Configuration OpenRouter pour Claude Code
# ============================================

# Configuration de base OpenRouter
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE_OPENROUTER"
export ANTHROPIC_API_KEY=""

# Mapping des aliases de modeles (optionnel - voir section Modeles Alternatifs)
export ANTHROPIC_DEFAULT_OPUS_MODEL="z-ai/glm-4.7"
export ANTHROPIC_DEFAULT_SONNET_MODEL="qwen/qwen3-coder-next"
export ANTHROPIC_DEFAULT_HAIKU_MODEL="z-ai/glm-4.7-flash"
```

Rechargez le fichier (adaptez selon le fichier que vous avez modifie) :

```bash
source ~/.zshrc       # Si vous avez edite .zshrc
# ou
source ~/.zprofile    # Si vous avez edite .zprofile
```

> **Important :** Apres avoir recharge, **fermez et rouvrez votre terminal** (et VSCode si vous l'utilisez) pour que les variables soient prises en compte partout. Un simple `source` ne suffit pas toujours pour les applications lancees depuis le Finder ou Spotlight.

### Etape 3 : Configuration via fichier settings.json (Alternative)

Au lieu des variables d'environnement, vous pouvez configurer Claude Code via un fichier JSON. **Choisissez l'une ou l'autre methode, pas les deux a la fois.**

#### Option A : Fichier machine (recommande)

Creez ou editez le fichier de settings de votre machine :

- **Windows** : `C:\Users\<UTILISATEUR>\.claude\settings.json`
- **macOS / Linux** : `~/.claude/settings.json`

Contenu :

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE_OPENROUTER",
    "ANTHROPIC_API_KEY": "",
    "ANTHROPIC_DEFAULT_OPUS_MODEL": "z-ai/glm-4.7",
    "ANTHROPIC_DEFAULT_SONNET_MODEL": "qwen/qwen3-coder-next",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL": "z-ai/glm-4.7-flash"
  }
}
```

Ce fichier s'applique a **tous vos projets** sur cette machine et ne risque pas d'etre commite dans un depot git.

#### Option B : Fichier projet (si configuration specifique)

Creez `.claude/settings.json` a la racine du projet :

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE_OPENROUTER",
    "ANTHROPIC_API_KEY": ""
  }
}
```

**Important :** Ajoutez-le a votre `.gitignore` pour ne pas exposer votre cle API :

```bash
echo ".claude/settings.json" >> .gitignore
```

#### Ordre de priorite des settings

Claude Code charge les configurations dans cet ordre (la derniere ecrase les precedentes) :

1. Configuration par defaut de Claude Code
1. `~/.claude/settings.json` (fichier machine)
1. `.claude/settings.json` (fichier projet)
1. Variables d'environnement (PowerShell/Bash, cf. Etape 2)

### Etape 4 : Verification de la Configuration

#### Via CLI

```bash
claude /status
```

Vous devriez voir :

```text
Connected to OpenRouter
Model: qwen/qwen3-coder-next (sonnet alias)
Base URL: https://openrouter.ai/api
```

#### Via VS Code Extension

1. Ouvrez Claude Code dans VS Code (icone ou `Cmd+Shift+P` > "Claude Code")
1. Desactivez la demande de connexion :
   - `Cmd+,` > Extensions > Claude Code
   - Activez **"Disable Login Prompt"**
1. Tapez un message de test : `Bonjour, peux-tu me confirmer que tu fonctionnes ?`

#### Tester chaque modele

```bash
# Test du modele par defaut (Sonnet)
claude -p "Reponds juste 'OK' pour confirmer que tu fonctionnes"

# Test Opus
claude --model opus -p "Reponds 'Opus OK'"

# Test Haiku
claude --model haiku -p "Reponds 'Haiku OK'"
```

---

## Modeles Alternatifs via OpenRouter

OpenRouter permet d'utiliser des modeles alternatifs a Claude, souvent moins chers et performants pour le code.

### Pourquoi des modeles alternatifs ?

- **Couts** : Jusqu'a 30x moins cher que les modeles Claude natifs
- **Flexibilite** : Tester differents modeles selon vos besoins
- **Experimentation** : Comparer les performances sur vos cas d'usage
- **Disponibilite** : Avoir des alternatives en cas d'indisponibilite

### Modeles Recommandes (Fevrier 2026)

| Alias Claude | Modele Alternatif | Identifiant OpenRouter | Context | Prix (Input/Output per M) |
| ------------ | ----------------- | ---------------------- | ------- | ------------------------- |
| `opus` | GLM-4.7 | `z-ai/glm-4.7` | 200K | $0.40 / $1.50 |
| `sonnet` | Qwen3 Coder Next | `qwen/qwen3-coder-next` | 256K | Variable |
| `haiku` | GLM-4.7 Flash | `z-ai/glm-4.7-flash` | 200K | $0.07 / $0.40 |

### Commandes CLI

```bash
# Utiliser le modele par defaut (Sonnet -> Qwen3 Coder Next)
claude -p "Explique ce code"

# Utiliser explicitement un modele
claude --model opus -p "Refactore ce projet"    # GLM-4.7
claude --model sonnet -p "Corrige ce bug"       # Qwen3 Coder Next
claude --model haiku -p "Liste les fichiers"    # GLM-4.7 Flash

# Forcer un modele specifique (bypass alias)
claude --model z-ai/glm-4.7 -p "Question complexe"
```

### Presentation des Modeles

#### GLM-4.7 (Alias Opus)

**Identifiant :** `z-ai/glm-4.7`

GLM-4.7 est le modele flagship de Z.AI (anciennement Zhipu AI) :

- **Context window** : 200K tokens
- **Forces** : Programmation avancee, raisonnement multi-etapes, taches agentiques complexes
- **Cas d'usage ideaux** : Refactoring complexe, architecture de projets, documentation technique
- **Prix** : $0.40 / $1.50 per million tokens (input/output)

#### Qwen3 Coder Next (Alias Sonnet)

**Identifiant :** `qwen/qwen3-coder-next`

Modele MoE (Mixture of Experts) optimise pour le code :

- **Architecture** : 80B parametres totaux, 3B actives par token
- **Context window** : 256K tokens (extensible a 1M)
- **Forces** : Coding agentique, function calling, raisonnement sur larges codebases, tres rapide
- **Cas d'usage ideaux** : Developpement quotidien, debug, generation de tests, refactoring
- **Prix** : Variable selon le provider

#### GLM-4.7 Flash (Alias Haiku)

**Identifiant :** `z-ai/glm-4.7-flash`

Version optimisee pour la vitesse :

- **Taille** : ~30B parametres
- **Context window** : 200K tokens
- **Forces** : Equilibre performance/cout, coding renforce, planification long-horizon
- **Cas d'usage ideaux** : Exploration rapide, questions simples, taches repetitives, prototypage
- **Prix** : $0.07 / $0.40 per million tokens (input/output)

### Comparaison avec les Modeles Claude Natifs

| Aspect | Claude Opus | GLM-4.7 | Claude Sonnet | Qwen3 Coder Next | Claude Haiku | GLM-4.7 Flash |
| ---------------- | ----------- | ------- | ------------- | ---------------- | ------------ | ------------- |
| **Context** | 200K | 200K | 200K | 256K | 200K | 200K |
| **Prix Input** | $15.00 | $0.40 | $3.00 | Variable | $0.25 | $0.07 |
| **Prix Output** | $75.00 | $1.50 | $15.00 | Variable | $1.25 | $0.40 |
| **Coding** | Excellent | Excellent | Tres bon | Excellent | Bon | Tres bon |
| **Raisonnement** | Excellent | Excellent | Tres bon | Tres bon | Bon | Bon |

**Note :** Les prix sont indicatifs. Consultez [OpenRouter Models](https://openrouter.ai/models) pour les tarifs a jour.

### Dans les Subagents

Vous pouvez assigner des modeles differents aux subagents :

```json
{
  "reviewer": {
    "description": "Code reviewer",
    "model": "opus",
    "tools": ["Read", "Grep"]
  },
  "explorer": {
    "description": "Fast exploration",
    "model": "haiku",
    "tools": ["Read", "Glob"]
  }
}
```

---

## Configuration de l'Extension VS Code

### Parametres Recommandes

1. Ouvrez les parametres : `Cmd+,` / `Ctrl+,`
1. Allez dans **Extensions > Claude Code**
1. Configurez :

| Parametre | Valeur Recommandee | Description |
| ------------------------- | ------------------ | ------------------------------------ |
| **Disable Login Prompt** | Active | Evite la connexion Anthropic |
| **Initial Permission Mode** | `default` | Demande avant chaque action |
| **Preferred Location** | `sidebar` | Position dans l'interface |
| **Autosave** | Active | Sauvegarde avant lecture/ecriture |
| **Respect Git Ignore** | Active | Exclut les fichiers ignores |

### Raccourcis Clavier

Personnalisez vos raccourcis : `Cmd+K Cmd+S` / `Ctrl+K Ctrl+S`

**Raccourcis par defaut :**

- **Toggle Claude Code** : `Cmd+Esc` / `Ctrl+Esc`
- **New Conversation (Tab)** : `Cmd+Shift+Esc` / `Ctrl+Shift+Esc`
- **Insert @-mention** : `Alt+K`

## Configuration des MCP Servers

Les serveurs MCP etendent les capacites de Claude Code.

### Installation de Serveurs MCP Recommandes

#### 1. Serveur de Recherche Web (SearXNG)

```bash
claude mcp add --transport http searxng https://search.myia.io/
```

#### 2. Serveur Playwright (Automatisation Navigateur)

Permet d'interagir avec des pages web, remplir des formulaires, prendre des captures d'ecran.

```bash
claude mcp add --transport stdio playwright -- npx -y @anthropic/mcp-server-playwright
```

#### 3. Serveur GitHub

```bash
claude mcp add --transport http github https://api.githubcopilot.com/mcp/
```

#### 4. Context7 (Documentation a jour)

Fournit de la documentation actualisee et des exemples de code specifiques aux versions pour vos prompts. Evite les informations obsoletes des LLMs.

```bash
claude mcp add --transport stdio context7 -- npx -y @upstash/context7-mcp
```

**Utilisation** : Ajoutez "use context7" a votre question ou precisez l'ID de la librairie.

#### 5. OpenMemory (Memoire persistante)

Permet a Claude de memoriser le contexte entre les sessions. Plus besoin de re-expliquer votre projet a chaque nouvelle conversation.

```bash
claude mcp add --transport stdio openmemory -- npx -y @mem0/openmemory-mcp
```

**Avantages** : Memoire locale, cross-client (fonctionne avec Cursor, VS Code, etc.).

#### 6. Serena (Agent de code semantique)

Toolkit d'agent de codage offrant recuperation et edition semantique via LSP. Supporte 30+ langages de programmation.

```bash
claude mcp add --transport stdio serena -- uvx --from git+https://github.com/oraios/serena serena start-mcp-server --context claude-code --project "$(pwd)"
```

**Note** : Utilisez `--context claude-code` pour eviter les conflits avec les outils natifs de Claude Code.

### Gestion des Serveurs MCP

**Lister les serveurs configures :**

```bash
claude mcp list
```

**Voir les details d'un serveur :**

```bash
claude mcp get searxng
```

**Supprimer un serveur :**

```bash
claude mcp remove searxng
```

**Verifier le statut (dans Claude Code) :**

```text
/mcp
```

### Configuration par Portee (Scope)

**Serveur personnel (utilisateur) :**

```bash
claude mcp add --transport http --scope user mon-serveur https://...
```

**Serveur partage (projet - versionne) :**

```bash
claude mcp add --transport http --scope project mon-serveur https://...
```

Creera un fichier `.mcp.json` dans votre projet.

## Premiers Pas

### Test CLI

**Session interactive de base :**

```bash
claude
```

**Poser une question :**

```text
> Explique-moi la structure de ce projet
```

**Query ponctuelle :**

```bash
claude -p "Liste les fichiers Python de ce projet"
```

**Continuer la derniere conversation :**

```bash
claude -c
```

### Test Extension VS Code

1. **Ouvrir un fichier dans VS Code**
1. **Cliquer sur l'icone (spark)** dans la barre d'outils
1. **Selectionner du code**
1. **Appuyer sur `Alt+K`** pour creer une reference
1. **Poser une question :** `Explique-moi ce code`
1. **Examiner la reponse et les diffs proposes**

### Generer CLAUDE.md pour Votre Projet

```bash
cd /chemin/vers/votre/projet
claude
```

Puis dans Claude :

```text
/init
```

Claude generera automatiquement un fichier `CLAUDE.md` adapte a votre projet.

## Resolution de Problemes

### Probleme : "Command not found: claude"

**Solution :**

- Verifiez l'installation : `which claude` (macOS/Linux) ou `where.exe claude` (Windows)
- Ajoutez au PATH si necessaire
- Redemarrez votre terminal

### Probleme : "Authentication failed" avec OpenRouter

**Solution :**

Verifiez que les variables d'environnement sont bien definies :

```bash
echo $ANTHROPIC_BASE_URL       # Doit afficher https://openrouter.ai/api
echo $ANTHROPIC_AUTH_TOKEN     # Doit afficher votre cle sk-or-v1-...
echo $ANTHROPIC_API_KEY        # Doit afficher une ligne vide
```

Verifiez votre cle API sur [openrouter.ai/settings/keys](https://openrouter.ai/settings/keys).

Sur macOS, verifiez que les exports sont dans le bon fichier de profil (voir Etape 2).

### Probleme : Extension VS Code ne se connecte pas

**Solution :**

1. Activez **"Disable Login Prompt"** dans les parametres
1. Redemarrez VS Code **completement** (pas juste recharger la fenetre)
1. Verifiez les logs : `Cmd+Shift+P` > "Developer: Show Logs"

### Probleme : "Model not found"

Verifiez que l'identifiant du modele est correct sur [OpenRouter Models](https://openrouter.ai/models).

### Probleme : "Rate limit exceeded"

1. Attendez quelques secondes et reessayez
1. Verifiez vos credits sur [OpenRouter Activity](https://openrouter.ai/activity)
1. Considerez un plan payant pour des limites plus elevees

### Probleme : Le modele ne repond pas comme attendu

Certains modeles alternatifs ont des comportements differents. Ajustez vos prompts :

```bash
# Etre plus explicite sur le format attendu
claude -p "Reponds UNIQUEMENT avec du code Python, sans explication"

# Specifier le contexte
claude -p "En tant qu'expert Python, analyse ce code : ..."
```

### Probleme : MCP server ne repond pas (Windows)

Pour les serveurs locaux `npx` sur Windows, utilisez le wrapper `cmd /c` :

```bash
claude mcp add --transport stdio mon-serveur -- cmd /c npx -y @package/nom
```

## Commandes Utiles

**Mettre a jour Claude Code :**

```bash
claude update
```

**Afficher l'aide :**

```bash
claude --help
```

**Afficher la version :**

```bash
claude --version
```

**Mode debug :**

```bash
claude --debug
```

**Desactiver la persistance de session :**

```bash
claude -p --no-session-persistence "query"
```

## Configuration Avancee

### Personnalisation du System Prompt

**Ajouter des instructions globales :**

```bash
claude --append-system-prompt "Toujours utiliser TypeScript et inclure des tests"
```

**Remplacer completement le system prompt :**

```bash
claude --system-prompt "Tu es un expert Python specialise en data science"
```

### Definir des Agents Personnalises

Creez un fichier `custom-agents.json` :

```json
{
  "reviewer": {
    "description": "Expert en revue de code. Utiliser apres modifications.",
    "prompt": "Tu es un senior code reviewer. Concentre-toi sur qualite, securite et best practices.",
    "tools": ["Read", "Grep", "Glob"],
    "model": "sonnet"
  },
  "tester": {
    "description": "Specialiste des tests. Utiliser pour debugging.",
    "prompt": "Tu es un expert en tests et debugging. Analyse les erreurs et propose des fixes."
  }
}
```

Utilisez-le :

```bash
claude --agents @custom-agents.json
```

### Configuration des Permissions

Editez `.claude/settings.json` :

```json
{
  "permissionMode": "default",
  "allowedTools": [
    "Read",
    "Glob",
    "Grep",
    "Bash(git log:*)",
    "Bash(git diff:*)",
    "Bash(git status:*)"
  ],
  "disallowedTools": [
    "Write(/etc/*:*)",
    "Bash(rm:*)"
  ]
}
```

---

## Ressources

### Documentation Officielle

- [Quickstart](https://code.claude.com/docs/en/quickstart)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [VS Code Documentation](https://code.claude.com/docs/en/vs-code)
- [MCP Guide](https://code.claude.com/docs/en/mcp)

### OpenRouter

- [Documentation OpenRouter](https://openrouter.ai/docs)
- [Guide d'integration Claude Code](https://openrouter.ai/docs/guides/claude-code-integration)
- [Tarifs et modeles](https://openrouter.ai/models)
- [GLM-4.7 sur OpenRouter](https://openrouter.ai/z-ai/glm-4.7)
- [GLM-4.7 Flash sur OpenRouter](https://openrouter.ai/z-ai/glm-4.7-flash)
- [Qwen3 Coder sur OpenRouter](https://openrouter.ai/qwen/qwen3-coder-next)
- [Z.AI Blog - GLM-4.7](https://z.ai/blog/glm-4.7)

### Communaute

- [GitHub - Claude Code](https://github.com/anthropics/claude-code)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)
- [SkillsMP Marketplace](https://skillsmp.com/)

---

## Checklist d'Installation

- [ ] Claude Code CLI installe et fonctionnel (`claude --version`)
- [ ] Extension VS Code installee
- [ ] Variables d'environnement OpenRouter configurees (ou settings.json)
- [ ] Test CLI reussi (`claude /status`)
- [ ] Test Extension VS Code reussi
- [ ] Au moins 1 serveur MCP configure
- [ ] Fichier CLAUDE.md genere pour votre projet (`/init`)
- [ ] Raccourcis clavier personnalises (optionnel)
- [ ] Modeles alternatifs configures (optionnel)

---

*Pour decouvrir les concepts et cas d'usage, consultez [INTRO-CLAUDE-CODE.md](./INTRO-CLAUDE-CODE.md)*

*Pour approfondir Skills, Subagents, Hooks et MCP, consultez [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md)*
