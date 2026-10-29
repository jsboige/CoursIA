# Quickstart : Claude Code + OpenRouter

**15 minutes pour être opérationnel.**

Ce guide vous prend par la main pour configurer Claude Code avec OpenRouter comme fournisseur de modèles. Suivez les étapes dans l'ordre, et validez chaque checkpoint avant de passer a la suivante.

> **Pourquoi OpenRouter ?** Au lieu d'utiliser l'API Anthropic (payante, compte obligatoire), OpenRouter vous donne accès a des modèles performants a moindre coût, avec une clé unique pour plusieurs modèles.
>
> **Compatibilité OpenRouter** : OpenRouter expose son propre point d'entree compatible avec le protocole Anthropic (`https://openrouter.ai/api`), mesure le 2026-10-29 — **aucun proxy n'est a installer**. Le guide demandait auparavant de faire tourner [openrouter-proxy](https://github.com/ahaostudy/openrouter-proxy) en local ; cette etape est obsolete, et l'Etape 0 explique la mesure qui l'a etabli.

---

## Etape 0 : rien a installer — OpenRouter sert nativement l'API Anthropic

**Il n'y a plus de proxy a lancer.** Le guide demandait jusqu'ici de cloner `openrouter-proxy` et de faire tourner `node proxy.js` sur le port 8899, au motif que « les requetes OpenRouter ne sont pas strictement compatibles avec le protocole Anthropic ». Ce n'est plus vrai.

> **Mesure du 2026-10-29 (issue #23276, lane `myia-po-2023:CoursIA-2`).** OpenRouter expose desormais `POST https://openrouter.ai/api/v1/messages`, qui parle le protocole Anthropic et rend ses erreurs au **format Anthropic** :
>
> | Sonde | Resultat | Ce que ca prouve |
> |---|---|---|
> | `POST /api/v1/nonexistent-xyz-42` (temoin) | **404** | un chemin absent rend bien 404 |
> | `POST /api/v1/messages` sans cle | **401** | la route **existe**, elle demande une authentification |
> | `POST /api/v1/messages` avec cle invalide | `{"type":"error","error":{"type":"authentication_error",...}}` | le format d'erreur est celui d'**Anthropic**, pas celui d'OpenAI |
> | `GET /api/v1/messages` | **404** | la route est **POST seule**, comme chez Anthropic |
> | `claude -p` avec `ANTHROPIC_BASE_URL=https://openrouter.ai/api` | **repond `OK`, code retour 0** | la chaine complete fonctionne **sans proxy** |
>
> Le temoin 404 est la piece qui rend la mesure valide : sans lui, un 401 sur `/messages` ne distinguerait pas « route presente » de « tout rend 401 ».

**Le proxy reste utile dans un seul cas** : si vous devez parler a un fournisseur qui n'implemente que l'API OpenAI. Pour OpenRouter, ce n'est pas le cas.

### Si vous aviez deja installe le proxy

Vous pouvez l'arreter et supprimer le clone. Le seul geste a faire est de changer la valeur de `ANTHROPIC_BASE_URL` (Etape 3) : `https://openrouter.ai/api` devient `https://openrouter.ai/api`.

## Étape 1 : Installer Claude Code (3 min)

> **Chemin canonique : l'installation native** (défaut de la documentation officielle Anthropic, Node.js non requis pour cette étape). Guide complet et alternative npm : [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md).

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
| `ANTHROPIC_BASE_URL` | `https://openrouter.ai/api` | Va directement au point d'entree Anthropic d'OpenRouter (Etape 0), au lieu d'Anthropic |
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
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": "",
    "ANTHROPIC_DEFAULT_OPUS_MODEL": "qwen/qwen3.6-plus",
    "ANTHROPIC_DEFAULT_SONNET_MODEL": "minimax/minimax-m2.7",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL": "qwen/qwen3.6-35b-a3b"
  }
}
```

### Alternative : variables d'environnement PowerShell (Windows)

Si vous préférez les variables d'environnement, ouvrez votre profil :

```powershell
notepad $PROFILE
```

Ajoutez a la fin :

```powershell
# Configuration OpenRouter pour Claude Code
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
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
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
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
echo $env:ANTHROPIC_BASE_URL       # doit afficher: https://openrouter.ai/api
echo $env:ANTHROPIC_AUTH_TOKEN      # doit afficher: sk-or-v1-...

# macOS/Linux
echo $ANTHROPIC_BASE_URL            # doit afficher: https://openrouter.ai/api
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

## Étape 5 bis : Depuis Google Colab (le cas qui echouait en TP)

Colab est une **machine Linux ephemere** avec un terminal et un acces Internet. Claude Code y fonctionne, a condition de ne pas suivre les etapes concues pour un poste de travail.

### Ce qui ne marche pas dans Colab

| Geste | Pourquoi il echoue |
|---|---|
| `claude auth login` | Ouvre un **navigateur** et attend un retour par callback. La VM Colab n'en a pas : la commande reste suspendue. |
| Lancer `node proxy.js` | Le proxy ouvert dans une cellule meurt avec elle ; la cellule suivante ne le trouve plus. C'est une des causes plausibles de l'echec du TP, **non etablie** (cf. plus bas). |
| `brew`, installateur `.exe` | Ce sont des voies macOS / Windows. |

### La recette testee

```bash
# 1. Installer la CLI (Node est deja present dans Colab)
npm install -g @anthropic-ai/claude-code

# 2. Verifier
claude --version

# 3. Authentifier par JETON, jamais par navigateur
import os
os.environ["ANTHROPIC_BASE_URL"]    = "https://openrouter.ai/api"
os.environ["ANTHROPIC_AUTH_TOKEN"]  = "sk-or-v1-VOTRE_CLE"   # jamais en clair dans un notebook committe
os.environ["ANTHROPIC_MODEL"]       = "anthropic/claude-haiku-5.5"

# 4. Tester — doit rendre un mot et un code retour 0
!claude -p "Reponds uniquement: OK"
```

En cellule shell pure, les trois `export` remplacent le bloc Python.

> **Ne mettez pas la cle dans le notebook.** Lisez-la depuis les *Secrets* Colab (`google.colab.userdata`) ou une variable d'environnement de session. Un notebook committe avec une cle en clair est un incident de securite (regle `secrets-hygiene`) — le secret est rotation a faire, pas un `revert`.

### Les deux modes d'echec, mesures

Les deux produisent un **symptome muet**, et c'est ce qui rend le diagnostic difficile en TP :

| Cause | Ce qu'on observe | Mesure |
|---|---|---|
| `ANTHROPIC_BASE_URL` pose **sans jeton** | La commande **ne rend jamais la main** et **n'affiche aucune erreur** | `claude -p` sans `ANTHROPIC_AUTH_TOKEN` : `rc=124` (arrete au bout de 60 s), stdout vide, une seule ligne sur stderr |
| Ancien montage par proxy, proxy arrete | `fetch failed` / `connection refused` vers `127.0.0.1:8899` | erreur de connexion explicite, donc plus facile a diagnostiquer |

Le premier cas est le piege : **une cellule qui tourne indefiniment n'est pas une cellule lente, c'est une authentification absente.** Si un `claude -p` ne rend rien au bout d'une minute dans Colab, verifiez `ANTHROPIC_AUTH_TOKEN` avant toute autre chose.

**Ce que cette mesure n'etablit pas** : laquelle de ces causes a fait echouer le TP etudiant d'origine. L'issue #23276 le dit explicitement (« cause exacte a reproduire, non etablie »), et je ne tranche pas a sa place — les deux modes sont reproductibles, aucun temoignage ne les departage.

### Les lignes `unrecognized_model`

Claude Code affiche sur sa sortie d'erreur des lignes de la forme :

```
[claude-code:unrecognized_model] {"model":"anthropic/claude-haiku-5.5","query_source":"sdk"}
```

Elles signalent que le nom du modele n'appartient pas au registre interne de Claude Code. **La requete part quand meme et la reponse est correcte** (`rc=0`) — c'est du bruit, pas une panne. Ne les confondez pas avec l'absence de jeton ci-dessus, qui elle ne produit aucune reponse.

### Modeles disponibles

Verifie le 2026-10-29 aupres de `https://openrouter.ai/api/v1/models` : les modeles Anthropic courants y sont, sous la forme `anthropic/claude-haiku-5.5`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-opus-5.5` (contexte annonce 1 000 000). Les identifiants plus anciens sont retires : `anthropic/claude-sonnet-4` repond desormais « retired on June 15, 2026 ». Epinglez un identifiant, et re-verifiez-le si une session se met a echouer sans raison apparente.

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
