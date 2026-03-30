# Atelier 03 - Assistant Développeur

## Objectifs pédagogiques

À la fin de cet atelier, vous serez capable de :

- Utiliser `/commit` pour créer des commits Git propres et descriptifs
- Utiliser `/review` pour analyser les changements de code
- Débugger efficacement avec l'aide de Claude Code
- Refactorer du code legacy de manière sécurisée
- Analyser les dépendances et la qualité du code

## Prérequis

- Ateliers 01 et 02 complétés
- Git installé et configuré
- Un projet avec historique Git (ou en créer un)

## Durée estimée

**3 heures**

## Concepts clés

### Commandes Git intégrées

Claude Code intègre des commandes spéciales pour Git :

| Commande | Description |
|----------|-------------|
| `/commit` | Analyse les changements et crée un commit avec message descriptif |
| `/review` | Analyse les changements non commités ou une PR |

### Workflow de développement assisté

```
Modifier → /review → Ajuster → /commit → Pousser
```

## Structure de l'atelier

| Demo | Titre | Durée | Description |
|------|-------|-------|-------------|
| 1 | [Commits et Reviews](demo-1-commit-review/) | 45 min | Workflow Git professionnel |
| 2 | [Debug et Refactoring](demo-2-debug-refactor/) | 50 min | Correction de bugs et amélioration |
| 3 | [Analyse de Code](demo-3-analyse-code/) | 40 min | Qualité et dépendances |

## Démos

### Demo 1 - Commits et Reviews

**Objectif** : Maîtriser le workflow Git avec Claude Code.

Vous apprendrez à :
- Analyser vos changements avant de commiter
- Générer des messages de commit descriptifs
- Revoir votre code pour détecter les problèmes
- Maintenir un historique Git propre

**Exemple** :
```
/commit
```
Claude analyse les changements, propose un message structuré (type, scope, description).

### Demo 2 - Debug et Refactoring

**Objectif** : Corriger des bugs et améliorer du code existant.

Vous apprendrez à :
- Identifier la cause racine d'un bug
- Corriger sans introduire de régression
- Refactorer du code de manière sécurisée
- Valider les corrections avec des tests

**Exemple** :
```
@buggy.py Ce code lève une erreur sur les listes vides. Corrige le bug.
```

### Demo 3 - Analyse de Code

**Objectif** : Évaluer la qualité et comprendre les dépendances.

Vous apprendrez à :
- Analyser les métriques de qualité
- Cartographier les dépendances
- Identifier les code smells
- Proposer des améliorations

**Exemple** :
```
Analyse la qualité de @src/ et identifie les points d'amélioration.
```

## Commandes essentielles

```bash
# Analyser les changements et commiter
claude
> /commit

# Revoir les changements non commités
> /review

# Revoir une PR spécifique
> /review #123

# Debug avec contexte
> @fichier.py Ce code ne fonctionne pas quand X, corrige-le

# Refactoring
> @legacy.py Refactore ce code en appliquant le pattern Repository

# Analyse de qualité
> Analyse la complexité cyclomatique de @src/
```

## Conventions de commits

Claude Code suit les conventions Conventional Commits :

```
<type>(<scope>): <description>

[body]

[footer]
```

### Types courants

| Type | Description |
|------|-------------|
| `feat` | Nouvelle fonctionnalité |
| `fix` | Correction de bug |
| `refactor` | Refactoring sans changement fonctionnel |
| `docs` | Documentation |
| `test` | Ajout/modification de tests |
| `chore` | Maintenance, dépendances |

### Exemples

```
feat(auth): add JWT refresh token support

Implement refresh token mechanism with:
- 7-day expiry for refresh tokens
- Automatic rotation on use
- Secure storage recommendations

Closes #123
```

```
fix(api): handle empty list in calculate_average

The function now returns 0 for empty lists instead of
raising ZeroDivisionError.

Fixes #456
```

## Bonnes pratiques

### Pour les commits

1. **Un commit = un changement logique**
2. **Message descriptif** : Expliquez le "pourquoi"
3. **Revue avant commit** : Utilisez `/review` d'abord
4. **Tests inclus** : Commitez code et tests ensemble

### Pour le debug

1. **Reproduire d'abord** : Comprenez le problème
2. **Isoler** : Identifiez le code fautif
3. **Corriger minimalement** : Ne touchez que le nécessaire
4. **Tester** : Validez la correction

### Pour le refactoring

1. **Tests en place** : Avant de refactorer
2. **Petites étapes** : Un changement à la fois
3. **Valider souvent** : Tests après chaque étape
4. **Documenter** : Expliquez les changements majeurs

## Ressources

- [Conventional Commits](https://www.conventionalcommits.org/)
- [Git Best Practices](https://git-scm.com/book/en/v2)
- [Refactoring Guru](https://refactoring.guru/)

## Checklist de validation

- [ ] Sait utiliser `/commit` efficacement
- [ ] Sait utiliser `/review` avant de commiter
- [ ] Capable de débugger avec l'aide de Claude
- [ ] Sait refactorer de manière sécurisée
- [ ] Comprend les métriques de qualité de code

---

**Prochaine étape** : [Atelier 04 - Création de Code](../04-creation-code/)
