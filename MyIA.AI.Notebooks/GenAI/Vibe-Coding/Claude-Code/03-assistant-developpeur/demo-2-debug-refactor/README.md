# Demo 2 - Debug et Refactoring

## Objectif

Apprendre à utiliser Claude Code pour identifier, corriger des bugs et améliorer du code existant de manière sécurisée.

## Durée estimée

**50 minutes**

## Concepts

### Debug avec Claude Code

Claude Code peut vous aider à :
- Identifier la cause racine d'un bug
- Proposer des corrections
- Suggérer des tests pour éviter les régressions
- Expliquer pourquoi le bug se produit

### Refactoring assisté

Le refactoring avec Claude Code :
- Analyse le code existant
- Propose des améliorations structurées
- Applique des design patterns
- Maintient la compatibilité

## Étapes

### Étape 1 : Debug simple (15 min)

#### Le bug

Créez ce fichier avec un bug évident :

```python
# gestionnaire_stock.py

class GestionnaireStock:
    def __init__(self):
        self.produits = {}

    def ajouter_produit(self, nom, quantite, prix):
        if nom in self.produits:
            self.produits[nom]['quantite'] += quantite
        else:
            self.produits[nom] = {
                'quantite': quantite,
                'prix': prix
            }

    def retirer_produit(self, nom, quantite):
        if nom not in self.produits:
            return False
        self.produits[nom]['quantite'] -= quantite  # Bug: peut devenir négatif
        return True

    def valeur_totale(self):
        total = 0
        for produit in self.produits.values():
            total += produit['prix']  # Bug: oubli * quantite
        return total
```

#### Demandez l'analyse

```
@gestionnaire_stock.py Ce code a des bugs.
Quand je retire plus de produits que le stock, ça devient négatif.
Et la valeur totale semble incorrecte.
Identifie et corrige les bugs.
```

#### Observez

Claude va :
1. Identifier les deux bugs
2. Expliquer pourquoi ils se produisent
3. Proposer des corrections
4. Suggérer des améliorations

### Étape 2 : Debug complexe (15 min)

#### Le bug subtil

```python
# cache.py

class Cache:
    def __init__(self, max_size=100):
        self.max_size = max_size
        self.data = {}
        self.access_order = []

    def get(self, key):
        if key in self.data:
            # Mettre à jour l'ordre d'accès
            self.access_order.remove(key)
            self.access_order.append(key)
            return self.data[key]
        return None

    def set(self, key, value):
        if key in self.data:
            self.data[key] = value
            return

        # Éviction si cache plein
        if len(self.data) >= self.max_size:
            oldest = self.access_order.pop(0)
            del self.data[oldest]

        self.data[key] = value
        self.access_order.append(key)

    def clear(self):
        self.data = {}
        # Bug: access_order n'est pas vidé !
```

#### Demandez une analyse approfondie

```
@cache.py Ce cache LRU a un comportement étrange après un clear().
Analyse le code et trouve le bug.
Propose aussi des améliorations pour le rendre plus robuste.
```

### Étape 3 : Refactoring basique (10 min)

#### Code à refactorer

```python
# user_service.py

def handle_user_request(request_type, data):
    if request_type == 'create':
        if not data.get('email'):
            return {'error': 'Email requis'}
        if not data.get('password'):
            return {'error': 'Mot de passe requis'}
        if len(data['password']) < 8:
            return {'error': 'Mot de passe trop court'}

        import hashlib
        hashed = hashlib.sha256(data['password'].encode()).hexdigest()

        # Simulation DB
        print(f"Creating user: {data['email']}")
        return {'success': True, 'id': 123}

    elif request_type == 'update':
        if not data.get('id'):
            return {'error': 'ID requis'}
        print(f"Updating user: {data['id']}")
        return {'success': True}

    elif request_type == 'delete':
        if not data.get('id'):
            return {'error': 'ID requis'}
        print(f"Deleting user: {data['id']}")
        return {'success': True}

    else:
        return {'error': 'Type de requête inconnu'}
```

#### Demandez le refactoring

```
@user_service.py Refactore ce code en appliquant :
1. Le principe de responsabilité unique
2. Des classes séparées pour chaque opération
3. Une meilleure gestion des erreurs avec des exceptions
4. Un pattern qui facilite l'ajout de nouvelles opérations
```

### Étape 4 : Refactoring avec pattern (10 min)

#### Demande spécifique

```
Applique le pattern Command au code refactoré pour :
- Encapsuler chaque opération
- Permettre l'annulation (undo)
- Faciliter le logging
```

#### Résultat attendu

```python
from abc import ABC, abstractmethod

class UserCommand(ABC):
    @abstractmethod
    def execute(self) -> dict:
        pass

    @abstractmethod
    def undo(self) -> dict:
        pass

class CreateUserCommand(UserCommand):
    def __init__(self, data: dict):
        self.data = data
        self.created_id = None

    def execute(self) -> dict:
        # Validation et création
        ...

    def undo(self) -> dict:
        # Suppression de l'utilisateur créé
        ...
```

## Exercice pratique

### Mission

Corrigez et refactorez un module complet.

### Code fourni

Utilisez le fichier dans `ressources/projet-buggy/app.py`.

### Étapes

1. **Identifier les bugs**
   ```
   @app.py Liste tous les bugs et problèmes de ce code.
   ```

2. **Corriger les bugs** (un par un)
   ```
   Corrige le bug de [description]. Montre-moi le diff.
   ```

3. **Ajouter des tests** pour chaque correction

4. **Refactorer** le code corrigé
   ```
   Maintenant que les bugs sont corrigés, refactore le code
   pour améliorer sa maintenabilité.
   ```

5. **Review finale**
   ```
   /review
   ```

### Livrables

- Code corrigé
- Tests unitaires
- Code refactoré
- Historique Git propre

## Bonnes pratiques

### Pour le debug

1. **Reproduire d'abord**
   - Comprendre quand le bug se produit
   - Avoir un cas de test qui échoue

2. **Isoler**
   - Identifier le fichier/fonction concerné
   - Réduire le scope de l'analyse

3. **Corriger minimalement**
   - Ne pas profiter pour "améliorer" autre chose
   - Une correction = un changement

4. **Tester**
   - Test qui reproduit le bug
   - Test qui vérifie la correction
   - Tests de non-régression

### Pour le refactoring

1. **Tests d'abord**
   - Avoir des tests avant de refactorer
   - Ils valident que le comportement ne change pas

2. **Petites étapes**
   - Un changement à la fois
   - Commit après chaque étape qui passe les tests

3. **Patterns appropriés**
   - Ne pas sur-architecturer
   - Le pattern doit résoudre un problème réel

4. **Documenter**
   - Expliquer les choix architecturaux
   - Mettre à jour la documentation

## Points clés à retenir

1. **Debug ≠ Refactoring** : Corrigez d'abord, améliorez ensuite

2. **Tests obligatoires** : Pas de refactoring sans filet de sécurité

3. **Petits pas** : Changements incrémentaux, validés à chaque étape

4. **Review systématique** : `/review` après chaque modification

---

**Prochaine étape** : [Demo 3 - Analyse de Code](../demo-3-analyse-code/)
