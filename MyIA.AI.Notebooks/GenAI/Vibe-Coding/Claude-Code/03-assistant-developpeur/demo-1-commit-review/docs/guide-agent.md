# Guide Agent - Demo 1 : Commits et Reviews

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Maîtriser `/commit` pour des commits propres
- Utiliser `/review` avant de commiter
- Comprendre les conventions Conventional Commits
- Adopter un workflow Git professionnel

## Points de vigilance

### Configuration Git

1. **Git non configuré**
   - Vérifier : `git config user.name` et `git config user.email`
   - Configurer si nécessaire avant de commiter

2. **Pas dans un repo Git**
   - `/commit` échouera silencieusement
   - Toujours vérifier avec `git status`

### Qualité des reviews

1. **Review superficielle**
   - Si peu de problèmes détectés, demander une review ciblée
   - Exemple : "Review avec focus sur la sécurité"

2. **Trop de problèmes**
   - Prioriser les corrections
   - Corriger par catégorie (sécurité d'abord)

## Déroulé suggéré

### Phase 1 : Setup (5 min)

1. Vérifier Git configuré
2. Créer ou cloner un projet de test
3. Vérifier qu'on est dans un repo Git

### Phase 2 : Premier /commit (15 min)

1. Créer un fichier simple
2. Montrer `/commit`
3. Expliquer le format du message
4. Valider le commit

### Phase 3 : /review (15 min)

1. Ajouter du code problématique
2. Montrer `/review`
3. Analyser les retours
4. Corriger et re-review

### Phase 4 : Workflow complet (10 min)

1. Montrer le cycle complet
2. Review → Correction → Review → Commit

## Réponses aux questions fréquentes

### "Le message de commit est en anglais, je veux du français"

```
/commit avec message en français
```

Ou définir dans CLAUDE.md :
```markdown
## Instructions pour Claude
- Messages de commit en français
```

### "Comment modifier un commit déjà fait ?"

Claude Code ne modifie pas l'historique par défaut. Pour amender :
```bash
git commit --amend
```

Ou demander :
```
Aide-moi à modifier le dernier commit
```

### "Puis-je reviewer une branche entière ?"

```
Review tous les commits de la branche feature/auth par rapport à main
```

### "Comment faire des commits partiels ?"

```
Je veux commiter uniquement les changements dans utils.py, pas les autres fichiers
```

## Critères de validation

L'apprenant a réussi cette démo si :

- [ ] A créé au moins 3 commits avec `/commit`
- [ ] A utilisé `/review` avant chaque commit
- [ ] Comprend le format Conventional Commits
- [ ] Sait corriger les problèmes identifiés par review
- [ ] Messages de commit descriptifs

## Format des messages de commit

### Structure complète

```
<type>(<scope>): <subject>
<BLANK LINE>
<body>
<BLANK LINE>
<footer>
```

### Types standard

| Type | Emoji | Description |
|------|-------|-------------|
| feat | ✨ | Nouvelle fonctionnalité |
| fix | 🐛 | Correction de bug |
| docs | 📚 | Documentation |
| style | 💅 | Formatage (pas de changement logique) |
| refactor | ♻️ | Refactoring |
| test | ✅ | Ajout/modification de tests |
| chore | 🔧 | Maintenance |

### Exemples

**Bon commit** :
```
feat(user): add email verification on signup

- Send verification email after registration
- Add verification endpoint
- Expire tokens after 24h

Closes #234
```

**Mauvais commit** :
```
fix stuff
```

## Erreurs courantes

### Commit vide

**Cause** : Pas de changements staged

**Solution** :
```bash
git add .
# puis /commit
```

### Message trop long

**Cause** : Description trop détaillée dans le sujet

**Solution** : Sujet < 50 chars, détails dans le body

### Commit avec fichiers non voulus

**Cause** : `git add .` trop large

**Solution** :
```
Crée un commit uniquement avec les fichiers .py, ignore les .log
```

## Ressources pour le formateur

- [Conventional Commits](https://www.conventionalcommits.org/)
- [Git Best Practices](https://sethrobertson.github.io/GitBestPractices/)
- [Commit Message Guidelines](https://gist.github.com/robertpainsi/b632364184e70900af4ab688decf6f53)
