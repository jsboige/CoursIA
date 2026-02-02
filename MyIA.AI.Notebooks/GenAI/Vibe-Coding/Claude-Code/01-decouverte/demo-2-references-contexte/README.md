# Demo 2 - Références et Contexte

## Objectif

Maîtriser les @-mentions pour référencer des fichiers et comprendre le fichier CLAUDE.md comme mémoire de projet.

## Durée estimée

**45 minutes**

## Prérequis

- Demo 1 complétée
- Claude Code fonctionnel
- Un projet de test (fourni dans les ressources)

## Concepts clés

### @-mentions

Les @-mentions permettent d'inclure du contexte dans votre conversation avec Claude :

| Syntaxe | Description | Exemple |
|---------|-------------|---------|
| `@fichier.py` | Inclut le contenu d'un fichier | `@main.py Analyse ce code` |
| `@dossier/` | Inclut la structure d'un dossier | `@src/ Quelle est l'architecture ?` |
| `@*.py` | Pattern matching | `@tests/*.py Liste les tests` |

### CLAUDE.md

Le fichier `CLAUDE.md` est la "mémoire projet" de Claude Code. Il contient :

- Description du projet
- Stack technique
- Conventions de code
- Commandes utiles
- Instructions spécifiques pour Claude

## Étapes

### Étape 1 : Préparer le projet de test (5 min)

Copiez le projet exemple depuis `ressources/projet-exemple/` vers votre workspace :

```bash
cp -r ressources/projet-exemple/ mon-projet/
cd mon-projet/
```

Le projet contient :
```
mon-projet/
├── src/
│   ├── main.py
│   ├── utils.py
│   └── models/
│       └── user.py
├── tests/
│   └── test_utils.py
├── requirements.txt
└── README.md
```

### Étape 2 : Utiliser les @-mentions (15 min)

Lancez Claude Code dans le dossier du projet :

```bash
cd mon-projet/
claude
```

#### Exercice 2.1 : Référencer un fichier

```
@src/main.py Explique ce que fait ce fichier.
```

#### Exercice 2.2 : Référencer un dossier

```
@src/ Décris l'architecture de ce projet.
```

#### Exercice 2.3 : Références multiples

```
@src/utils.py @tests/test_utils.py Les tests couvrent-ils toutes les fonctions ?
```

#### Exercice 2.4 : Pattern matching

```
@src/**/*.py Quelles classes sont définies dans ce projet ?
```

### Étape 3 : Générer CLAUDE.md (10 min)

#### Génération automatique

Dans votre session Claude Code :

```
/init
```

Claude analyse votre projet et génère un fichier `CLAUDE.md` initial.

#### Examiner le résultat

Ouvrez le fichier `CLAUDE.md` généré et observez :
- La structure du fichier
- Les informations détectées automatiquement
- Les sections proposées

### Étape 4 : Personnaliser CLAUDE.md (15 min)

Modifiez le fichier `CLAUDE.md` pour l'enrichir :

```markdown
# Mon Projet API

## Description
API de gestion d'utilisateurs pour une application web.

## Stack technique
- Python 3.11
- Framework : Aucun (scripts utilitaires)
- Tests : pytest
- Linting : black, flake8

## Structure du projet
```
src/
├── main.py      # Point d'entrée
├── utils.py     # Fonctions utilitaires
└── models/      # Modèles de données
    └── user.py  # Classe User
```

## Conventions de code

### Nommage
- Classes : PascalCase
- Fonctions : snake_case
- Constantes : UPPER_SNAKE_CASE

### Documentation
- Docstrings format Google
- Type hints obligatoires

### Tests
- Un fichier de test par module
- Nommage : `test_<module>.py`

## Commandes utiles

```bash
# Lancer les tests
pytest

# Formater le code
black src/

# Vérifier le linting
flake8 src/
```

## Instructions pour Claude

Quand tu génères du code pour ce projet :
1. Utilise toujours des type hints
2. Ajoute des docstrings Google-style
3. Crée les tests correspondants
4. Respecte la structure existante
```

### Étape 5 : Tester le contexte (5 min)

Après avoir personnalisé CLAUDE.md, testez que Claude utilise bien ce contexte :

```
Ajoute une fonction validate_password() dans utils.py
```

Observez que Claude :
- Utilise les type hints (comme indiqué)
- Ajoute une docstring Google-style
- Respecte les conventions de nommage

## Exercice pratique

### Mission

Créez un fichier `CLAUDE.md` complet pour un projet de votre choix (réel ou fictif).

### Cahier des charges

Votre CLAUDE.md doit contenir :

1. **Description** : But du projet en 2-3 phrases
2. **Stack** : Langages, frameworks, outils
3. **Structure** : Arborescence des dossiers
4. **Conventions** : Nommage, documentation, tests
5. **Commandes** : Build, test, déploiement
6. **Instructions Claude** : Directives spécifiques

### Livrable

Fichier `CLAUDE.md` dans votre workspace.

## Points clés à retenir

1. **@-mentions** : Moyen rapide d'inclure du contexte
   - `@fichier` pour un fichier
   - `@dossier/` pour une structure
   - Combinables dans une même requête

2. **CLAUDE.md** : Mémoire persistante du projet
   - Généré avec `/init`
   - À personnaliser selon vos besoins
   - Lu automatiquement par Claude Code

3. **Hiérarchie** : Claude Code lit les CLAUDE.md de :
   - `~/.claude/CLAUDE.md` (global)
   - `./CLAUDE.md` (projet)
   - `./src/CLAUDE.md` (sous-dossier)

## Dépannage

### Les @-mentions ne fonctionnent pas

- Vérifiez que le fichier/dossier existe
- Utilisez des chemins relatifs au dossier courant
- Vérifiez les permissions de lecture

### CLAUDE.md n'est pas pris en compte

- Vérifiez que vous êtes dans le bon dossier
- Le fichier doit s'appeler exactement `CLAUDE.md`
- Relancez Claude Code après modification

## Ressources

- [Projet exemple](ressources/projet-exemple/)
- [Template CLAUDE.md](ressources/template-claude-md.md)
- [Documentation officielle](https://docs.anthropic.com/en/docs/claude-code/memory)

---

**Prochaine étape** : [Atelier 02 - Orchestration de Tâches](../../02-orchestration-taches/)
