# Configuration OpenRouter - Modeles Alternatifs

Ce guide explique comment configurer Claude Code avec des modeles alternatifs via OpenRouter, permettant d'experimenter avec differents LLMs tout en gardant la meme interface de travail.

## Pourquoi utiliser des modeles alternatifs ?

OpenRouter permet d'acceder a une grande variete de modeles LLM via une API unifiee. Cela offre plusieurs avantages :

- **Flexibilite** : Tester differents modeles selon vos besoins
- **Couts** : Certains modeles sont moins chers que les modeles Claude natifs
- **Experimentation** : Comparer les performances sur vos cas d'usage specifiques
- **Disponibilite** : Avoir des alternatives en cas d'indisponibilite d'un modele

## Modeles Recommandes (Fevrier 2026)

| Role | Alias Claude | Modele Alternatif | Identifiant OpenRouter | Context | Prix (Input/Output per M) |
|------|--------------|-------------------|------------------------|---------|---------------------------|
| Large (Opus) | `opus` | GLM-4.7 | `z-ai/glm-4.7` | 200K | $0.40 / $1.50 |
| Moyen (Sonnet) | `sonnet` | Qwen3 Coder Next | `qwen/qwen3-coder-next` | 256K | Variable |
| Petit (Haiku) | `haiku` | GLM-4.7 Flash | `z-ai/glm-4.7-flash` | 200K | $0.07 / $0.40 |

---

## Configuration Detaillee

### Etape 1 : Obtenir une cle API OpenRouter

1. Visitez [openrouter.ai](https://openrouter.ai/)
2. Creez un compte ou connectez-vous
3. Accedez a [Settings > API Keys](https://openrouter.ai/settings/keys)
4. Creez une nouvelle cle API et copiez-la

### Etape 2 : Configurer les variables d'environnement

#### Windows (PowerShell - Configuration permanente)

Editez votre profil PowerShell :

```powershell
notepad $PROFILE
```

Ajoutez les lignes suivantes :

```powershell
# ============================================
# Configuration OpenRouter pour Claude Code
# Modeles alternatifs GLM-4.7 / Qwen3 Coder
# ============================================

# Configuration de base OpenRouter
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE_OPENROUTER"
$env:ANTHROPIC_API_KEY = ""

# Mapping des aliases de modeles
$env:ANTHROPIC_DEFAULT_OPUS_MODEL = "z-ai/glm-4.7"
$env:ANTHROPIC_DEFAULT_SONNET_MODEL = "qwen/qwen3-coder-next"
$env:ANTHROPIC_DEFAULT_HAIKU_MODEL = "z-ai/glm-4.7-flash"
```

Rechargez le profil :

```powershell
. $PROFILE
```

#### macOS / Linux (Bash/Zsh - Configuration permanente)

Editez `~/.bashrc` ou `~/.zshrc` :

```bash
# ============================================
# Configuration OpenRouter pour Claude Code
# Modeles alternatifs GLM-4.7 / Qwen3 Coder
# ============================================

# Configuration de base OpenRouter
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE_OPENROUTER"
export ANTHROPIC_API_KEY=""

# Mapping des aliases de modeles
export ANTHROPIC_DEFAULT_OPUS_MODEL="z-ai/glm-4.7"
export ANTHROPIC_DEFAULT_SONNET_MODEL="qwen/qwen3-coder-next"
export ANTHROPIC_DEFAULT_HAIKU_MODEL="z-ai/glm-4.7-flash"
```

Rechargez :

```bash
source ~/.bashrc  # ou ~/.zshrc
```

### Etape 3 : Configuration via fichier settings.json (Alternative)

Creez ou editez `.claude/settings.json` dans votre projet :

```json
{
  "anthropic": {
    "baseURL": "https://openrouter.ai/api",
    "authToken": "sk-or-v1-VOTRE_CLE_OPENROUTER",
    "apiKey": "",
    "defaultModels": {
      "opus": "z-ai/glm-4.7",
      "sonnet": "qwen/qwen3-coder-next",
      "haiku": "z-ai/glm-4.7-flash"
    }
  }
}
```

**Important :** Ajoutez ce fichier a votre `.gitignore` :

```bash
echo ".claude/settings.json" >> .gitignore
```

---

## Presentation des Modeles

### GLM-4.7 (Alias Opus)

**Identifiant :** `z-ai/glm-4.7`

GLM-4.7 est le modele flagship de Z.AI (anciennement Zhipu AI). Il offre :

- **Context window** : 200K tokens
- **Forces** :
  - Capacites de programmation avancees
  - Raisonnement multi-etapes stable
  - Execution de taches agentiques complexes
  - Conversations naturelles
- **Cas d'usage ideaux** :
  - Refactoring de code complexe
  - Architecture de projets
  - Taches necessitant un raisonnement approfondi
  - Generation de documentation technique

**Prix** : $0.40 / $1.50 per million tokens (input/output)

### Qwen3 Coder Next (Alias Sonnet)

**Identifiant :** `qwen/qwen3-coder-next`

Qwen3 Coder Next est un modele MoE (Mixture of Experts) optimise pour le code :

- **Architecture** : 80B parametres totaux, 3B actives par token
- **Context window** : 256K tokens (extensible a 1M)
- **Forces** :
  - Optimise pour les taches de coding agentique
  - Function calling et tool use excellents
  - Raisonnement sur de larges codebases
  - Tres rapide grace a l'architecture MoE
- **Cas d'usage ideaux** :
  - Developpement quotidien
  - Debug et correction de bugs
  - Generation de tests
  - Refactoring standard

**Prix** : Variable selon le provider

### GLM-4.7 Flash (Alias Haiku)

**Identifiant :** `z-ai/glm-4.7-flash`

GLM-4.7 Flash est la version optimisee pour la vitesse :

- **Taille** : ~30B parametres
- **Context window** : 200K tokens
- **Forces** :
  - Equilibre performance/cout
  - Capacites de coding renforcees
  - Planification de taches long-horizon
  - Collaboration avec outils
- **Cas d'usage ideaux** :
  - Exploration rapide de code
  - Questions simples sur le code
  - Taches repetitives
  - Tests et prototypage

**Prix** : $0.07 / $0.40 per million tokens (input/output)

---

## Utilisation Pratique

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

### Dans les subagents

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

## Verification de la Configuration

### Verifier la connexion

```bash
claude /status
```

Sortie attendue :

```
Connected to OpenRouter
Model: qwen/qwen3-coder-next (sonnet alias)
Base URL: https://openrouter.ai/api
```

### Tester chaque modele

```bash
# Test GLM-4.7 (Opus)
claude --model opus -p "Reponds 'GLM-4.7 fonctionne' si tu es GLM"

# Test Qwen3 Coder Next (Sonnet)
claude --model sonnet -p "Reponds 'Qwen3 fonctionne' si tu es Qwen"

# Test GLM-4.7 Flash (Haiku)
claude --model haiku -p "Reponds 'GLM Flash fonctionne' si tu es GLM Flash"
```

### Verifier les couts

Surveillez votre consommation sur [OpenRouter Activity](https://openrouter.ai/activity).

---

## Comparaison avec les Modeles Claude Natifs

| Aspect | Claude Opus | GLM-4.7 | Claude Sonnet | Qwen3 Coder Next | Claude Haiku | GLM-4.7 Flash |
|--------|-------------|---------|---------------|------------------|--------------|---------------|
| **Context** | 200K | 200K | 200K | 256K | 200K | 200K |
| **Prix Input** | $15.00 | $0.40 | $3.00 | Variable | $0.25 | $0.07 |
| **Prix Output** | $75.00 | $1.50 | $15.00 | Variable | $1.25 | $0.40 |
| **Coding** | Excellent | Excellent | Tres bon | Excellent | Bon | Tres bon |
| **Raisonnement** | Excellent | Excellent | Tres bon | Tres bon | Bon | Bon |

**Note :** Les prix sont indicatifs et peuvent varier. Consultez [OpenRouter Models](https://openrouter.ai/models) pour les tarifs a jour.

---

## Cas d'Usage Recommandes

### Utiliser GLM-4.7 (Opus) pour :

- Architecture de projets complexes
- Refactoring majeur avec preservation de la logique
- Generation de documentation technique approfondie
- Taches necessitant une comprehension globale du projet
- Decisions architecturales

### Utiliser Qwen3 Coder Next (Sonnet) pour :

- Developpement quotidien
- Debug et correction de bugs
- Generation et modification de code
- Creation de tests unitaires
- Revue de code standard

### Utiliser GLM-4.7 Flash (Haiku) pour :

- Exploration rapide du code
- Questions simples et ponctuelles
- Taches repetitives (renommage, formatage)
- Prototypage rapide
- Estimation de la complexite avant tache plus approfondie

---

## Resolution de Problemes

### Erreur "Model not found"

Verifiez que l'identifiant du modele est correct sur [OpenRouter Models](https://openrouter.ai/models).

### Erreur "Rate limit exceeded"

OpenRouter applique des limites de taux. Solutions :

1. Attendez quelques secondes et reessayez
2. Verifiez vos credits sur [Activity](https://openrouter.ai/activity)
3. Considerez un plan payant pour des limites plus elevees

### Erreur "Authentication failed"

1. Verifiez que `ANTHROPIC_AUTH_TOKEN` contient votre cle OpenRouter
2. Verifiez que `ANTHROPIC_API_KEY` est vide (pas la cle Anthropic)
3. Verifiez que `ANTHROPIC_BASE_URL` pointe vers `https://openrouter.ai/api`

### Le modele ne repond pas comme attendu

Certains modeles ont des comportements differents. Ajustez vos prompts :

```bash
# Etre plus explicite sur le format attendu
claude -p "Reponds UNIQUEMENT avec du code Python, sans explication"

# Specifier le contexte
claude -p "En tant qu'expert Python, analyse ce code : ..."
```

---

## Ressources

- [GLM-4.7 sur OpenRouter](https://openrouter.ai/z-ai/glm-4.7)
- [GLM-4.7 Flash sur OpenRouter](https://openrouter.ai/z-ai/glm-4.7-flash)
- [Qwen3 Coder sur OpenRouter](https://openrouter.ai/qwen/qwen3-coder-next)
- [Documentation OpenRouter](https://openrouter.ai/docs)
- [Guide Claude Code + OpenRouter](https://openrouter.ai/docs/guides/claude-code-integration)
- [Z.AI Blog - GLM-4.7](https://z.ai/blog/glm-4.7)

---

*Pour l'installation de base de Claude Code, consultez [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md)*

*Pour les concepts avances (Skills, Subagents, Hooks), consultez [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md)*
