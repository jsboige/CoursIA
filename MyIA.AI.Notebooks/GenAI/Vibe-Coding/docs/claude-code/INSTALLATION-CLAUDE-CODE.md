# Guide d'Installation de Claude Code

Ce guide vous explique comment installer et configurer Claude Code (CLI et extension VS Code) pour la formation, en utilisant OpenRouter comme fournisseur de modèles.

## Prérequis

- **Visual Studio Code** version 1.98.0 ou supérieure : [Télécharger](https://code.visualstudio.com/)
- **Terminal** : PowerShell (Windows), bash/zsh (macOS/Linux)
- **Connexion internet**
- **Clé API OpenRouter** : Fournie par le formateur

## Installation de Claude Code

### Option 1 : Installation Native (Recommandée)

L'installation native ne nécessite pas Node.js et fonctionne sur tous les systèmes d'exploitation.

#### Windows

1. Téléchargez l'installateur depuis [claude.com/code](https://claude.com/code)
2. Exécutez l'installateur `.exe`
3. Suivez les instructions à l'écran
4. Redémarrez votre terminal

**Vérification :**
```powershell
claude --version
```

#### macOS

```bash
# Via Homebrew
brew install --cask claude-code

# Ou téléchargement direct
# Téléchargez le .dmg depuis claude.com/code
```

**Vérification :**
```bash
claude --version
```

#### Linux / WSL

```bash
# Installation via script
curl -fsSL https://install.claude.com | sh

# Ajouter au PATH (si nécessaire)
echo 'export PATH="$HOME/.claude/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

**Vérification :**
```bash
claude --version
```

### Option 2 : Installation via npm

Si vous avez déjà Node.js 18+ installé :

```bash
npm install -g @anthropic-ai/claude-code
```

**Note :** L'installation native est préférée car elle évite les conflits de versions Node.js.

## Installation de l'Extension VS Code

### Méthode 1 : Via VS Code Marketplace

1. Ouvrez **Visual Studio Code**
2. Appuyez sur `Ctrl+Shift+X` (Windows/Linux) ou `Cmd+Shift+X` (macOS)
3. Recherchez **"Claude Code"**
4. Trouvez l'extension officielle **"Claude Code" par Anthropic**
5. Cliquez sur **Installer**
6. Redémarrez VS Code si demandé

### Méthode 2 : Lien Direct

Cliquez sur ce lien : [Installer Claude Code pour VS Code](vscode:extension/anthropic.claude-code)

### Méthode 3 : Command Palette

1. `Cmd+Shift+P` / `Ctrl+Shift+P`
2. Tapez : `Extensions: Install Extensions`
3. Recherchez **"Claude Code"**
4. Installez

## Configuration avec OpenRouter

### Étape 1 : Obtenir la Clé API OpenRouter

**La clé API vous sera fournie par le formateur.** Conservez-la précieusement.

Si vous souhaitez créer votre propre compte OpenRouter :
1. Visitez [openrouter.ai](https://openrouter.ai/)
2. Créez un compte
3. Accédez à [Settings → API Keys](https://openrouter.ai/settings/keys)
4. Créez une nouvelle clé API

### Étape 2 : Configuration des Variables d'Environnement

Pour utiliser Claude Code avec OpenRouter, vous devez configurer trois variables d'environnement :

#### Windows (PowerShell)

**Configuration temporaire (session actuelle) :**
```powershell
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "VOTRE_CLE_OPENROUTER"
$env:ANTHROPIC_API_KEY = ""
```

**Configuration permanente (profil PowerShell) :**

1. Ouvrez votre profil PowerShell :
```powershell
notepad $PROFILE
```

2. Ajoutez les lignes suivantes :
```powershell
# Configuration OpenRouter pour Claude Code
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "VOTRE_CLE_OPENROUTER"
$env:ANTHROPIC_API_KEY = ""
```

3. Sauvegardez et rechargez :
```powershell
. $PROFILE
```

#### macOS / Linux (Bash)

**Configuration permanente (~/.bashrc ou ~/.zshrc) :**

1. Éditez votre fichier de configuration :
```bash
# Pour bash
nano ~/.bashrc

# Pour zsh (macOS par défaut)
nano ~/.zshrc
```

2. Ajoutez les lignes suivantes à la fin :
```bash
# Configuration OpenRouter pour Claude Code
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="VOTRE_CLE_OPENROUTER"
export ANTHROPIC_API_KEY=""
```

3. Rechargez la configuration :
```bash
# Pour bash
source ~/.bashrc

# Pour zsh
source ~/.zshrc
```

### Étape 3 : Configuration Projet (Alternative)

Au lieu de configurer globalement, vous pouvez configurer par projet :

1. Dans la racine de votre projet, créez le dossier `.claude` :
```bash
mkdir .claude
```

2. Créez le fichier `.claude/settings.local.json` :
```json
{
  "anthropic": {
    "baseURL": "https://openrouter.ai/api",
    "authToken": "VOTRE_CLE_OPENROUTER",
    "apiKey": ""
  }
}
```

**⚠️ Important :** Ajoutez `.claude/settings.local.json` à votre `.gitignore` pour ne pas partager vos clés :
```bash
echo ".claude/settings.local.json" >> .gitignore
```

### Étape 4 : Vérification de la Configuration

#### Via CLI

```bash
claude /status
```

Vous devriez voir :
```
✓ Connected to OpenRouter
✓ Model: anthropic/claude-sonnet-4
✓ Base URL: https://openrouter.ai/api
```

#### Via VS Code Extension

1. Ouvrez Claude Code dans VS Code (icône ✱ ou `Cmd+Shift+P` → "Claude Code")
2. Désactivez la demande de connexion :
   - `Cmd+,` → Extensions → Claude Code
   - Activez **"Disable Login Prompt"**
3. Tapez un message de test : `Bonjour, peux-tu me confirmer que tu fonctionnes ?`

### Étape 5 : Sélection du Modèle

Claude Code utilise des alias de modèles. Avec OpenRouter, vous pouvez les mapper :

**Modèles disponibles via OpenRouter :**

```bash
# Utiliser Claude Sonnet (par défaut)
claude

# Utiliser Claude Opus (plus puissant)
claude --model opus

# Utiliser Claude Haiku (plus rapide)
claude --model haiku

# Utiliser un modèle OpenAI via OpenRouter
export ANTHROPIC_DEFAULT_SONNET_MODEL="openai/gpt-4o"
claude
```

**Configuration des modèles par défaut :**

Éditez `.claude/settings.json` :
```json
{
  "anthropic": {
    "baseURL": "https://openrouter.ai/api",
    "authToken": "VOTRE_CLE_OPENROUTER",
    "apiKey": "",
    "defaultModels": {
      "sonnet": "anthropic/claude-sonnet-4",
      "opus": "anthropic/claude-opus-4",
      "haiku": "anthropic/claude-haiku-4"
    }
  }
}
```

## Configuration de l'Extension VS Code

### Paramètres Recommandés

1. Ouvrez les paramètres : `Cmd+,` / `Ctrl+,`
2. Allez dans **Extensions → Claude Code**
3. Configurez :

| Paramètre | Valeur Recommandée | Description |
|-----------|-------------------|-------------|
| **Disable Login Prompt** | ✅ Activé | Évite la connexion Anthropic |
| **Initial Permission Mode** | `default` | Demande avant chaque action |
| **Preferred Location** | `sidebar` | Position dans l'interface |
| **Autosave** | ✅ Activé | Sauvegarde avant lecture/écriture |
| **Respect Git Ignore** | ✅ Activé | Exclut les fichiers ignorés |

### Raccourcis Clavier

Personnalisez vos raccourcis : `Cmd+K Cmd+S` / `Ctrl+K Ctrl+S`

**Raccourcis par défaut :**
- **Toggle Claude Code** : `Cmd+Esc` / `Ctrl+Esc`
- **New Conversation (Tab)** : `Cmd+Shift+Esc` / `Ctrl+Shift+Esc`
- **Insert @-mention** : `Alt+K`

## Configuration des MCP Servers

Les serveurs MCP étendent les capacités de Claude Code.

### Installation de Serveurs MCP Recommandés

#### 1. Serveur de Recherche Web (SearXNG)

```bash
claude mcp add --transport http searxng https://search.myia.io/
```

#### 2. Serveur Playwright (Automatisation Navigateur)

Permet d'interagir avec des pages web, remplir des formulaires, prendre des captures d'écran.

```bash
claude mcp add --transport stdio playwright -- npx -y @anthropic/mcp-server-playwright
```

#### 3. Serveur GitHub

```bash
claude mcp add --transport http github https://api.githubcopilot.com/mcp/
```

#### 4. Context7 (Documentation à jour)

Fournit de la documentation actualisée et des exemples de code spécifiques aux versions pour vos prompts. Évite les informations obsolètes des LLMs.

```bash
claude mcp add --transport stdio context7 -- npx -y @upstash/context7-mcp
```

**Utilisation** : Ajoutez "use context7" à votre question ou précisez l'ID de la librairie.

#### 5. OpenMemory (Mémoire persistante)

Permet à Claude de mémoriser le contexte entre les sessions. Plus besoin de ré-expliquer votre projet à chaque nouvelle conversation.

```bash
claude mcp add --transport stdio openmemory -- npx -y @mem0/openmemory-mcp
```

**Avantages** : Mémoire locale, cross-client (fonctionne avec Cursor, VS Code, etc.).

#### 6. Serena (Agent de code sémantique)

Toolkit d'agent de codage offrant récupération et édition sémantique via LSP. Supporte 30+ langages de programmation.

```bash
claude mcp add --transport stdio serena -- uvx --from git+https://github.com/oraios/serena serena start-mcp-server --context claude-code --project "$(pwd)"
```

**Note** : Utilisez `--context claude-code` pour éviter les conflits avec les outils natifs de Claude Code.

### Gestion des Serveurs MCP

**Lister les serveurs configurés :**
```bash
claude mcp list
```

**Voir les détails d'un serveur :**
```bash
claude mcp get searxng
```

**Supprimer un serveur :**
```bash
claude mcp remove searxng
```

**Vérifier le statut (dans Claude Code) :**
```
/mcp
```

### Configuration par Portée (Scope)

**Serveur personnel (utilisateur) :**
```bash
claude mcp add --transport http --scope user mon-serveur https://...
```

**Serveur partagé (projet - versionné) :**
```bash
claude mcp add --transport http --scope project mon-serveur https://...
```

Créera un fichier `.mcp.json` dans votre projet.

## Premiers Pas

### Test CLI

1. **Session interactive de base :**
```bash
claude
```

2. **Poser une question :**
```
> Explique-moi la structure de ce projet
```

3. **Query ponctuelle :**
```bash
claude -p "Liste les fichiers Python de ce projet"
```

4. **Continuer la dernière conversation :**
```bash
claude -c
```

### Test Extension VS Code

1. **Ouvrir un fichier dans VS Code**
2. **Cliquer sur l'icône ✱ (spark)** dans la barre d'outils
3. **Sélectionner du code**
4. **Appuyer sur `Alt+K`** pour créer une référence
5. **Poser une question :** `Explique-moi ce code`
6. **Examiner la réponse et les diffs proposés**

### Générer CLAUDE.md pour Votre Projet

```bash
cd /chemin/vers/votre/projet
claude
```

Puis dans Claude :
```
/init
```

Claude générera automatiquement un fichier `CLAUDE.md` adapté à votre projet.

## Résolution de Problèmes

### Problème : "Command not found: claude"

**Solution :**
- Vérifiez l'installation : `which claude` (macOS/Linux) ou `where.exe claude` (Windows)
- Ajoutez au PATH si nécessaire
- Redémarrez votre terminal

### Problème : "Authentication failed" avec OpenRouter

**Solution :**
1. Vérifiez que les variables d'environnement sont bien définies :
```bash
echo $ANTHROPIC_BASE_URL
echo $ANTHROPIC_AUTH_TOKEN
```

2. Vérifiez que `ANTHROPIC_API_KEY` est vide :
```bash
echo $ANTHROPIC_API_KEY
# Doit afficher une ligne vide
```

3. Vérifiez votre clé API sur [openrouter.ai/settings/keys](https://openrouter.ai/settings/keys)

### Problème : Extension VS Code ne se connecte pas

**Solution :**
1. Activez **"Disable Login Prompt"** dans les paramètres
2. Configurez `.claude/settings.local.json` dans votre projet
3. Redémarrez VS Code
4. Vérifiez les logs : `Cmd+Shift+P` → "Developer: Show Logs"

### Problème : Modèles non disponibles

**Solution :**
1. Vérifiez les crédits OpenRouter : [openrouter.ai/activity](https://openrouter.ai/activity)
2. Les modèles Claude nécessitent le support de "tool use"
3. Utilisez `/status` pour voir le modèle actif

### Problème : MCP server ne répond pas (Windows)

**Solution :**
Pour les serveurs locaux `npx` sur Windows, utilisez le wrapper `cmd /c` :
```bash
claude mcp add --transport stdio mon-serveur -- cmd /c npx -y @package/nom
```

## Commandes Utiles

**Mettre à jour Claude Code :**
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

**Désactiver la persistance de session :**
```bash
claude -p --no-session-persistence "query"
```

## Configuration Avancée

### Personnalisation du System Prompt

**Ajouter des instructions globales :**
```bash
claude --append-system-prompt "Toujours utiliser TypeScript et inclure des tests"
```

**Remplacer complètement le system prompt :**
```bash
claude --system-prompt "Tu es un expert Python spécialisé en data science"
```

### Définir des Agents Personnalisés

Créez un fichier `custom-agents.json` :
```json
{
  "reviewer": {
    "description": "Expert en revue de code. Utiliser après modifications.",
    "prompt": "Tu es un senior code reviewer. Concentre-toi sur qualité, sécurité et best practices.",
    "tools": ["Read", "Grep", "Glob"],
    "model": "sonnet"
  },
  "tester": {
    "description": "Spécialiste des tests. Utiliser pour debugging.",
    "prompt": "Tu es un expert en tests et debugging. Analyse les erreurs et propose des fixes."
  }
}
```

Utilisez-le :
```bash
claude --agents @custom-agents.json
```

### Configuration des Permissions

Éditez `.claude/settings.json` :
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

## Ressources Complémentaires

### Documentation Officielle
- [Quickstart](https://code.claude.com/docs/en/quickstart)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [VS Code Documentation](https://code.claude.com/docs/en/vs-code)
- [MCP Guide](https://code.claude.com/docs/en/mcp)

### OpenRouter
- [Documentation OpenRouter](https://openrouter.ai/docs)
- [Guide d'intégration Claude Code](https://openrouter.ai/docs/guides/guides/claude-code-integration)
- [Tarifs et modèles](https://openrouter.ai/models)

### Communauté
- [GitHub - Claude Code](https://github.com/anthropics/claude-code)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)
- [SkillsMP Marketplace](https://skillsmp.com/)

---

## Checklist d'Installation

- [ ] Claude Code CLI installé et fonctionnel (`claude --version`)
- [ ] Extension VS Code installée
- [ ] Variables d'environnement OpenRouter configurées
- [ ] Test CLI réussi (`claude /status`)
- [ ] Test Extension VS Code réussi
- [ ] Au moins 1 serveur MCP configuré
- [ ] Fichier CLAUDE.md généré pour votre projet (`/init`)
- [ ] Raccourcis clavier personnalisés (optionnel)
- [ ] Agents personnalisés configurés (optionnel)

**Vous êtes prêt à utiliser Claude Code !** 🚀

---

*Pour découvrir les concepts et cas d'usage, consultez [INTRO-CLAUDE-CODE.md](./INTRO-CLAUDE-CODE.md)*

*Pour approfondir Skills, Subagents, Hooks et MCP, consultez [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md)*
