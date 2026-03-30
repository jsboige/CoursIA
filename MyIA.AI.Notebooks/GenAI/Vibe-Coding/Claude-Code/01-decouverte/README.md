# Atelier 01 - Découverte de Claude Code

## Objectifs pédagogiques

À la fin de cet atelier, vous serez capable de :

- Installer et configurer Claude Code (CLI et Extension VS Code)
- Lancer une session interactive et poser des questions efficaces
- Utiliser les @-mentions pour référencer fichiers et dossiers
- Comprendre et personnaliser le fichier CLAUDE.md
- Choisir le bon modèle selon vos besoins (sonnet, opus, haiku)

## Prérequis

- VS Code installé
- Node.js 18+ installé
- Compte OpenRouter avec clé API
- Terminal accessible (PowerShell, bash, zsh)

## Durée estimée

**2 à 3 heures**

## Structure de l'atelier

| Demo | Titre | Durée | Description |
|------|-------|-------|-------------|
| 1 | [Première Session](demo-1-premiere-session/) | 45 min | Installation, configuration et première interaction |
| 2 | [Références et Contexte](demo-2-references-contexte/) | 45 min | @-mentions, CLAUDE.md et gestion du contexte |

## Démos

### Demo 1 - Première Session

**Objectif** : Installer Claude Code et réaliser votre première interaction.

Vous apprendrez à :
- Installer Claude Code CLI via npm
- Configurer OpenRouter pour l'accès multi-modèles
- Lancer une session interactive
- Poser des questions efficaces
- Utiliser les commandes de base (`/help`, `/status`)

**Livrable** : Fichier `mes-premieres-questions.md` avec 5 questions progressives.

### Demo 2 - Références et Contexte

**Objectif** : Maîtriser les références de fichiers et le contexte projet.

Vous apprendrez à :
- Utiliser les @-mentions (`@fichier.py`, `@dossier/`)
- Générer un fichier CLAUDE.md avec `/init`
- Personnaliser CLAUDE.md pour votre projet
- Comprendre la hiérarchie des fichiers de configuration

**Livrable** : CLAUDE.md personnalisé pour un projet exemple.

## Commandes essentielles

```bash
# Lancer une session interactive
claude

# Query ponctuelle (sans session)
claude -p "ta question ici"

# Continuer la dernière session
claude -c

# Changer de modèle
claude --model opus
claude --model sonnet
claude --model haiku

# Afficher l'aide
claude /help

# Vérifier le statut
claude /status

# Générer CLAUDE.md
claude
> /init
```

## Concepts clés

### Modèles disponibles

| Modèle | Caractéristiques | Usage recommandé |
|--------|------------------|------------------|
| **Sonnet** | Équilibré, rapide | Usage quotidien, tâches variées |
| **Opus** | Plus puissant, réfléchi | Tâches complexes, architecture |
| **Haiku** | Très rapide, économique | Tâches simples, questions rapides |

### @-mentions

Les @-mentions permettent d'inclure du contexte dans votre conversation :

```
@fichier.py          → Inclut le contenu du fichier
@src/                → Inclut la structure du dossier
@package.json        → Inclut le fichier de config
```

### CLAUDE.md

Le fichier CLAUDE.md est la "mémoire projet" de Claude Code :

```markdown
# Mon Projet

## Stack technique
- Python 3.11
- FastAPI
- PostgreSQL

## Conventions
- Docstrings Google-style
- Tests avec pytest

## Commandes utiles
- `make test` : Lancer les tests
- `make dev` : Serveur de développement
```

## Ressources

- [Guide d'installation complet](../../docs/claude-code/INSTALLATION-CLAUDE-CODE.md)
- [Cheat-Sheet](../../docs/claude-code/CHEAT-SHEET.md)
- [Documentation officielle](https://docs.anthropic.com/en/docs/claude-code)

## Exercices bonus

1. **Explorer les modèles** : Posez la même question avec les 3 modèles et comparez les réponses
2. **CLAUDE.md avancé** : Ajoutez des sections pour les conventions de code et les commandes personnalisées
3. **Multi-fichiers** : Utilisez plusieurs @-mentions dans une même question

## Checklist de validation

- [ ] Claude Code CLI installé et fonctionnel
- [ ] OpenRouter configuré correctement
- [ ] Extension VS Code installée
- [ ] Première session interactive réussie
- [ ] @-mentions maîtrisées
- [ ] CLAUDE.md généré et personnalisé

---

**Prochaine étape** : [Atelier 02 - Orchestration de Tâches](../02-orchestration-taches/)
