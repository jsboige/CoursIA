# Tâches de démonstration - Atelier 01

Ce document liste des tâches concrètes à réaliser avec Claude Code pour découvrir ses capacités de base.

## Tâche 1 : Installation et premier contact

### Contexte
Vous venez d'installer Claude Code et souhaitez vérifier que tout fonctionne correctement.

### Instructions
1. Ouvrez un terminal
2. Vérifiez l'installation : `claude --version`
3. Lancez une session : `claude`
4. Posez une question simple : "Bonjour, peux-tu te présenter ?"
5. Vérifiez le statut : `/status`

### Résultat attendu
- Version de Claude Code affichée
- Réponse de Claude à votre salutation
- Statut de connexion OK

---

## Tâche 2 : Questions progressives

### Contexte
Vous souhaitez explorer les capacités de Claude Code avec des questions de complexité croissante.

### Instructions

Posez ces 5 questions dans l'ordre :

**Niveau 1 - Question simple**
```
Quelle est la différence entre une liste et un tuple en Python ?
```

**Niveau 2 - Question avec contexte**
```
Je développe une API REST en Python. Quels frameworks me recommandes-tu et pourquoi ?
```

**Niveau 3 - Question technique**
```
Explique-moi le pattern Repository en architecture logicielle avec un exemple concret en Python.
```

**Niveau 4 - Question de génération**
```
Génère une fonction Python qui valide une adresse email avec des expressions régulières. Inclus des tests unitaires.
```

**Niveau 5 - Question d'analyse**
```
Quelles sont les bonnes pratiques de sécurité pour une API REST ? Liste les 5 plus importantes avec des exemples de code.
```

### Livrable
Créez un fichier `mes-premieres-questions.md` contenant vos questions et les réponses de Claude.

---

## Tâche 3 : Exploration des modèles

### Contexte
Claude Code peut utiliser différents modèles. Vous allez comparer leurs réponses.

### Instructions

1. Posez cette question avec le modèle par défaut (sonnet) :
```
Explique le concept de récursivité en programmation.
```

2. Relancez avec opus :
```bash
claude --model opus
```
Posez la même question.

3. Relancez avec haiku :
```bash
claude --model haiku
```
Posez la même question.

### Analyse
Comparez :
- La longueur des réponses
- Le niveau de détail
- La vitesse de réponse
- La qualité des exemples

---

## Tâche 4 : Utilisation des @-mentions

### Contexte
Vous avez un projet Python et souhaitez que Claude analyse votre code.

### Instructions

1. Créez un fichier `calculatrice.py` :
```python
def additionner(a, b):
    return a + b

def soustraire(a, b):
    return a - b

def multiplier(a, b):
    return a * b

def diviser(a, b):
    if b == 0:
        raise ValueError("Division par zéro impossible")
    return a / b
```

2. Lancez Claude Code et utilisez une @-mention :
```
@calculatrice.py Analyse ce code et suggère des améliorations.
```

3. Demandez d'ajouter des fonctionnalités :
```
@calculatrice.py Ajoute une fonction pour calculer la puissance et une pour la racine carrée.
```

### Résultat attendu
- Claude analyse le fichier référencé
- Propose des améliorations pertinentes
- Génère du code compatible avec l'existant

---

## Tâche 5 : Génération de CLAUDE.md

### Contexte
Vous souhaitez configurer Claude Code pour un nouveau projet.

### Instructions

1. Créez un dossier pour un projet fictif :
```bash
mkdir mon-projet-api
cd mon-projet-api
```

2. Lancez Claude Code et générez CLAUDE.md :
```
/init
```

3. Personnalisez le fichier généré en ajoutant :
   - Stack technique de votre choix
   - Conventions de code
   - Commandes de build/test

### Exemple de personnalisation

```markdown
# Mon Projet API

## Description
API REST pour la gestion d'une bibliothèque de livres.

## Stack technique
- Python 3.11
- FastAPI
- SQLAlchemy
- PostgreSQL
- pytest

## Structure du projet
```
src/
├── api/          # Routes FastAPI
├── models/       # Modèles SQLAlchemy
├── services/     # Logique métier
└── tests/        # Tests unitaires
```

## Conventions
- Docstrings format Google
- Type hints obligatoires
- Tests pour chaque endpoint

## Commandes
- `uvicorn src.main:app --reload` : Démarrer le serveur
- `pytest` : Lancer les tests
- `black .` : Formater le code
```

---

## Tâche 6 : Session de debug

### Contexte
Vous avez un bug dans votre code et souhaitez que Claude vous aide à le résoudre.

### Instructions

1. Créez un fichier `buggy.py` avec ce code volontairement bugué :
```python
def trouver_maximum(liste):
    maximum = liste[0]
    for i in range(len(liste)):
        if liste[i] > maximum:
            maximum = liste[i]
    return maximum

def calculer_moyenne(nombres):
    total = 0
    for n in nombres:
        total += n
    return total / len(nombres)

# Tests
print(trouver_maximum([]))  # Bug: liste vide
print(calculer_moyenne([]))  # Bug: division par zéro
```

2. Demandez à Claude d'identifier et corriger les bugs :
```
@buggy.py Ce code a des bugs. Peux-tu les identifier et proposer des corrections ?
```

### Résultat attendu
- Identification des cas limites (liste vide)
- Propositions de corrections avec gestion d'erreurs
- Explication des bonnes pratiques

---

## Tâche 7 : Documentation de code

### Contexte
Vous avez du code sans documentation et souhaitez l'améliorer.

### Instructions

1. Utilisez le fichier `calculatrice.py` créé précédemment
2. Demandez à Claude de documenter :
```
@calculatrice.py Ajoute des docstrings complètes (format Google) et des type hints à ce code.
```

### Résultat attendu
```python
def additionner(a: float, b: float) -> float:
    """Additionne deux nombres.

    Args:
        a: Premier nombre.
        b: Deuxième nombre.

    Returns:
        La somme de a et b.

    Examples:
        >>> additionner(2, 3)
        5
    """
    return a + b
```

---

## Récapitulatif des livrables

| Tâche | Livrable |
|-------|----------|
| 1 | Capture d'écran du `/status` |
| 2 | `mes-premieres-questions.md` |
| 3 | Comparatif des modèles |
| 4 | `calculatrice.py` amélioré |
| 5 | `CLAUDE.md` personnalisé |
| 6 | `buggy.py` corrigé |
| 7 | Code documenté |

---

## Pour aller plus loin

- Explorez la commande `/help` pour découvrir toutes les options
- Testez différentes formulations pour une même question
- Essayez de combiner plusieurs @-mentions dans une même requête
