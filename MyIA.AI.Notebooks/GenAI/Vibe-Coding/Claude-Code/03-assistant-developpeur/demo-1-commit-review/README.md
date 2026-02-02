# Demo 1 - Commits et Reviews

## Objectif

Maîtriser le workflow Git avec les commandes `/commit` et `/review` de Claude Code pour maintenir un historique propre et du code de qualité.

## Durée estimée

**45 minutes**

## Concepts

### La commande /commit

`/commit` analyse automatiquement vos changements et :
- Liste les fichiers modifiés
- Comprend la nature des changements
- Propose un message de commit structuré
- Crée le commit après votre validation

### La commande /review

`/review` analyse votre code avant le commit pour :
- Détecter les bugs potentiels
- Identifier les problèmes de style
- Suggérer des améliorations
- Vérifier la cohérence

## Étapes

### Étape 1 : Préparer un projet Git (5 min)

```bash
# Créer un nouveau projet
mkdir mon-projet-git
cd mon-projet-git
git init

# Créer un premier fichier
echo "# Mon Projet" > README.md
git add README.md
git commit -m "Initial commit"
```

### Étape 2 : Premier /commit (10 min)

1. Créez un fichier Python :
   ```python
   # calculatrice.py
   def additionner(a: float, b: float) -> float:
       """Additionne deux nombres."""
       return a + b

   def soustraire(a: float, b: float) -> float:
       """Soustrait b de a."""
       return a - b
   ```

2. Lancez Claude Code :
   ```bash
   claude
   ```

3. Utilisez `/commit` :
   ```
   /commit
   ```

4. Observez :
   - Claude détecte les nouveaux fichiers
   - Propose un message type `feat(math): add basic calculator functions`
   - Attend votre validation

5. Validez ou modifiez le message proposé

### Étape 3 : Utiliser /review (15 min)

1. Ajoutez du code avec des problèmes subtils :
   ```python
   # Dans calculatrice.py, ajoutez :

   def diviser(a, b):
       return a / b  # Pas de gestion division par zéro

   def moyenne(nombres):
       return sum(nombres) / len(nombres)  # Pas de gestion liste vide

   API_KEY = "sk-secret-12345"  # Secret en dur !
   ```

2. Demandez une review :
   ```
   /review
   ```

3. Analysez les retours :
   - Division par zéro non gérée
   - Liste vide non gérée
   - Secret exposé dans le code

4. Corrigez les problèmes :
   ```
   Corrige les problèmes identifiés dans la review.
   ```

5. Nouvelle review puis commit :
   ```
   /review
   /commit
   ```

### Étape 4 : Workflow avancé (15 min)

#### Commits atomiques

Faites plusieurs changements distincts :

1. Ajoutez une fonction :
   ```python
   def puissance(base: float, exposant: float) -> float:
       """Calcule base^exposant."""
       return base ** exposant
   ```

2. Modifiez une fonction existante :
   ```python
   def diviser(a: float, b: float) -> float:
       """Divise a par b avec gestion d'erreur."""
       if b == 0:
           raise ValueError("Division par zéro impossible")
       return a / b
   ```

3. Demandez des commits séparés :
   ```
   Je veux créer deux commits distincts :
   1. L'ajout de la fonction puissance
   2. L'amélioration de la fonction diviser
   Aide-moi à faire ça.
   ```

#### Review d'une PR

Si vous travaillez avec GitHub :
```
/review #42
```

Claude analysera la PR #42 et donnera un retour détaillé.

## Exercice pratique

### Mission

Créez un module complet avec un workflow Git professionnel.

### Étapes

1. **Créer le module de base**
   ```
   Crée un module Python pour gérer une liste de tâches (todo list)
   avec ajout, suppression et marquage comme fait.
   ```

2. **Review initiale**
   ```
   /review
   ```

3. **Corriger et améliorer**

4. **Commit initial**
   ```
   /commit
   ```

5. **Ajouter des fonctionnalités** (une par commit)
   - Filtrage par statut
   - Sauvegarde JSON
   - Recherche

6. **Review finale du module complet**

### Livrables

- Module `todo.py` fonctionnel
- Historique Git avec 3-4 commits propres
- Chaque commit correspond à une fonctionnalité

## Bonnes pratiques

### Messages de commit

| Bon | Mauvais |
|-----|---------|
| `feat(auth): add password reset flow` | `update code` |
| `fix(api): handle timeout in requests` | `fix bug` |
| `refactor(db): extract query builder` | `refactoring` |

### Structure d'un bon message

```
type(scope): description courte (< 50 chars)

Corps optionnel avec plus de détails.
Expliquez le "pourquoi" pas le "quoi".

Références:
- Closes #123
- Related to #456
```

### Fréquence de review

- Avant chaque commit important
- Après un refactoring
- Avant une PR
- Quand vous avez un doute

## Points clés à retenir

1. **Review avant commit** : `/review` puis `/commit`

2. **Commits atomiques** : Un changement logique par commit

3. **Messages descriptifs** : Expliquez le "pourquoi"

4. **Pas de secrets** : La review détecte les données sensibles

## Dépannage

### /commit ne détecte pas mes changements

- Vérifiez que vous êtes dans un repo Git : `git status`
- Vérifiez que les fichiers sont dans le working tree

### Le message proposé ne me convient pas

- Donnez des instructions : `/commit avec un message en français`
- Modifiez manuellement après la proposition

### /review est trop permissif

- Soyez explicite : `/review avec focus sur la sécurité`
- Demandez des critères spécifiques

---

**Prochaine étape** : [Demo 2 - Debug et Refactoring](../demo-2-debug-refactor/)
