# Exemples de Questions pour Claude Code

## Questions de découverte

### Niveau 1 : Questions simples

```
Qu'est-ce qu'une variable en programmation ?
```

```
Quelle est la différence entre == et === en JavaScript ?
```

```
Comment créer une liste en Python ?
```

```
C'est quoi un API ?
```

### Niveau 2 : Questions avec contexte

```
Je débute en Python et je veux créer un script qui lit un fichier CSV.
Par où commencer ?
```

```
J'ai une application React qui devient lente. Quelles sont les techniques
d'optimisation les plus courantes ?
```

```
Je travaille sur un projet Node.js et j'ai besoin de gérer des variables
d'environnement. Quelle est la meilleure approche ?
```

### Niveau 3 : Questions techniques

```
Explique le fonctionnement du garbage collector en Java et comment
optimiser la gestion mémoire dans une application.
```

```
Quelles sont les différences entre les design patterns Factory,
Abstract Factory et Builder ? Donne un exemple d'utilisation pour chacun.
```

```
Comment implémenter une authentification OAuth 2.0 dans une API REST ?
Détaille le flow et les endpoints nécessaires.
```

## Questions de génération de code

### Fonctions utilitaires

```
Génère une fonction Python qui :
- Prend une liste de dictionnaires en entrée
- Filtre ceux qui ont une clé "active" à True
- Trie par la clé "date" (format ISO)
- Retourne les 10 premiers
Ajoute des type hints et une docstring.
```

### Classes et structures

```
Crée une classe Python pour représenter un panier d'achat avec :
- Ajout/suppression d'articles
- Calcul du total avec réduction possible
- Sérialisation en JSON
- Tests unitaires
```

### Scripts complets

```
Génère un script Python qui :
1. Se connecte à une API REST (utilise requests)
2. Récupère des données paginées
3. Les sauvegarde dans un fichier CSV
4. Gère les erreurs réseau avec retry
Utilise les bonnes pratiques (logging, configuration externe).
```

## Questions d'analyse et debug

### Analyse de code

```
Analyse ce code et identifie :
1. Les problèmes de performance potentiels
2. Les failles de sécurité
3. Les améliorations possibles

[coller le code ici]
```

### Debug

```
Ce code devrait afficher les nombres pairs de 1 à 10, mais il ne
fonctionne pas. Trouve le bug :

for i in range(1, 10):
    if i % 2 = 0:
        print(i)
```

### Revue de code

```
Fais une code review de cette fonction en évaluant :
- Lisibilité
- Maintenabilité
- Performance
- Gestion d'erreurs

[coller le code ici]
```

## Questions d'architecture

### Conception système

```
Je dois concevoir une application de réservation de salles de réunion.
Fonctionnalités :
- Voir les disponibilités
- Réserver/annuler
- Notifications par email

Propose une architecture technique avec les composants,
les technologies recommandées et les interactions.
```

### Choix technologiques

```
Je dois choisir entre MongoDB et PostgreSQL pour une application
de e-commerce avec :
- ~100k produits
- ~10k commandes/jour
- Recherche full-text
- Rapports analytiques

Quels sont les avantages/inconvénients de chaque option ?
```

## Questions de documentation

### README

```
Génère un README.md professionnel pour un projet Python qui :
- Est une CLI pour convertir des fichiers Markdown en PDF
- S'installe via pip
- A des dépendances listées dans requirements.txt
- Supporte plusieurs thèmes
```

### API Documentation

```
Génère la documentation OpenAPI/Swagger pour cet endpoint :
- POST /api/users
- Crée un utilisateur
- Body : { name, email, password }
- Réponses : 201 Created, 400 Bad Request, 409 Conflict
```

## Questions de test

### Tests unitaires

```
Génère des tests unitaires (pytest) pour cette fonction :

def calculate_discount(price: float, discount_percent: float) -> float:
    if discount_percent < 0 or discount_percent > 100:
        raise ValueError("Discount must be between 0 and 100")
    return price * (1 - discount_percent / 100)

Couvre les cas normaux et les cas limites.
```

### Tests d'intégration

```
Comment tester cette fonction qui appelle une API externe ?
Montre-moi comment mocker les appels HTTP avec pytest.

def get_user_data(user_id: str) -> dict:
    response = requests.get(f"https://api.example.com/users/{user_id}")
    response.raise_for_status()
    return response.json()
```

## Questions de workflow

### Git

```
J'ai fait des modifications sur la mauvaise branche. Comment :
1. Sauvegarder mes changements
2. Les appliquer sur la bonne branche
3. Nettoyer la branche incorrecte
```

### CI/CD

```
Génère un workflow GitHub Actions pour un projet Python qui :
- Exécute les tests sur push
- Vérifie le linting (flake8)
- Publie sur PyPI lors d'un tag
```

## Modèles de questions

### Template : Demande d'aide

```
Contexte : [décris ton projet/situation]
Problème : [décris ce qui ne fonctionne pas]
Ce que j'ai essayé : [liste tes tentatives]
Comportement attendu : [ce que tu veux obtenir]
Code/Logs : [éléments pertinents]
```

### Template : Demande de génération

```
Génère [type de code] pour [contexte]

Spécifications :
- [spec 1]
- [spec 2]

Contraintes :
- [contrainte 1]
- [contrainte 2]

Format souhaité : [précisions sur le format]
```

### Template : Demande d'explication

```
Explique [concept] pour quelqu'un qui [niveau de connaissance]

Inclus :
- Définition simple
- Exemple concret
- Cas d'usage
- Erreurs courantes à éviter
```
