# Tâches de démonstration - Atelier 03

Ce document liste des tâches concrètes pour maîtriser le workflow de développement avec Claude Code.

## Tâche 1 : Premier commit assisté

### Contexte
Vous avez fait des modifications et souhaitez créer un commit propre.

### Instructions

1. Créez ou modifiez un fichier dans un projet Git :
   ```python
   # calculatrice.py
   def additionner(a, b):
       """Additionne deux nombres."""
       return a + b

   def multiplier(a, b):
       """Multiplie deux nombres."""
       return a * b
   ```

2. Lancez Claude Code et utilisez `/commit` :
   ```
   /commit
   ```

3. Observez :
   - L'analyse des changements
   - Le message proposé
   - La structure du commit

### Résultat attendu
Un commit avec un message formaté type Conventional Commits.

---

## Tâche 2 : Review avant commit

### Contexte
Vous voulez vérifier vos changements avant de les commiter.

### Instructions

1. Faites plusieurs modifications dans votre projet

2. Demandez une review :
   ```
   /review
   ```

3. Claude va analyser :
   - Les fichiers modifiés
   - La qualité des changements
   - Les problèmes potentiels
   - Les suggestions d'amélioration

4. Corrigez les problèmes identifiés

5. Faites un nouveau `/review` puis `/commit`

### Résultat attendu
- Liste des problèmes détectés
- Code amélioré
- Commit propre

---

## Tâche 3 : Debug d'un bug simple

### Contexte
Une fonction ne gère pas correctement les cas limites.

### Instructions

1. Créez ce fichier bugué :
   ```python
   # stats.py
   def moyenne(nombres):
       total = sum(nombres)
       return total / len(nombres)

   def maximum(nombres):
       max_val = nombres[0]
       for n in nombres:
           if n > max_val:
               max_val = n
       return max_val

   # Tests qui échouent
   print(moyenne([]))  # ZeroDivisionError
   print(maximum([]))  # IndexError
   ```

2. Demandez à Claude de corriger :
   ```
   @stats.py Ces fonctions plantent avec des listes vides. Corrige-les
   en ajoutant une gestion d'erreur appropriée.
   ```

3. Vérifiez la correction et les tests

### Résultat attendu
```python
def moyenne(nombres):
    if not nombres:
        return 0  # ou raise ValueError
    return sum(nombres) / len(nombres)
```

---

## Tâche 4 : Debug d'un bug complexe

### Contexte
Un bug subtil provoque des résultats incorrects.

### Instructions

1. Créez ce code avec un bug logique :
   ```python
   # panier.py
   class Panier:
       def __init__(self):
           self.articles = []

       def ajouter(self, nom, prix, quantite=1):
           for article in self.articles:
               if article['nom'] == nom:
                   article['quantite'] += quantite
                   return
           self.articles.append({
               'nom': nom,
               'prix': prix,
               'quantite': quantite
           })

       def total(self):
           total = 0
           for article in self.articles:
               total += article['prix']  # Bug: oubli de * quantite
           return total

       def appliquer_reduction(self, pourcentage):
           for article in self.articles:
               article['prix'] = article['prix'] * (1 - pourcentage)
           # Bug: modifie le prix de base, pas le total
   ```

2. Demandez une analyse :
   ```
   @panier.py Analyse ce code et identifie les bugs logiques.
   Le total ne semble pas correct quand j'ajoute plusieurs fois le même article.
   ```

3. Demandez la correction :
   ```
   Corrige les bugs identifiés et ajoute des tests unitaires.
   ```

### Résultat attendu
- Identification des deux bugs
- Correction du calcul du total
- Correction de la réduction
- Tests unitaires

---

## Tâche 5 : Refactoring simple

### Contexte
Du code fonctionnel mais mal structuré.

### Instructions

1. Créez ce code à refactorer :
   ```python
   # user_manager.py
   def process_user(data):
       # Validation
       if not data.get('email'):
           return {'error': 'Email required'}
       if '@' not in data['email']:
           return {'error': 'Invalid email'}
       if not data.get('password'):
           return {'error': 'Password required'}
       if len(data['password']) < 8:
           return {'error': 'Password too short'}

       # Création
       import hashlib
       password_hash = hashlib.sha256(data['password'].encode()).hexdigest()

       user = {
           'email': data['email'].lower(),
           'password_hash': password_hash,
           'created_at': __import__('datetime').datetime.now().isoformat()
       }

       # Sauvegarde (simulée)
       print(f"Saving user: {user['email']}")

       return {'success': True, 'user': user}
   ```

2. Demandez un refactoring :
   ```
   @user_manager.py Refactore ce code en appliquant :
   - Séparation des responsabilités
   - Classes dédiées pour validation et création
   - Meilleure gestion des erreurs
   ```

### Résultat attendu
- Classe `UserValidator`
- Classe `UserFactory` ou `UserService`
- Exceptions personnalisées
- Code testable

---

## Tâche 6 : Refactoring avec pattern

### Contexte
Appliquer un design pattern à du code existant.

### Instructions

1. Partez de ce code :
   ```python
   # notifications.py
   def send_notification(user, message, channel):
       if channel == 'email':
           print(f"Sending email to {user['email']}: {message}")
           # logique email...
       elif channel == 'sms':
           print(f"Sending SMS to {user['phone']}: {message}")
           # logique SMS...
       elif channel == 'push':
           print(f"Sending push to {user['device_id']}: {message}")
           # logique push...
       else:
           raise ValueError(f"Unknown channel: {channel}")
   ```

2. Demandez l'application du pattern Strategy :
   ```
   @notifications.py Refactore ce code en utilisant le pattern Strategy
   pour gérer les différents canaux de notification.
   Rends le code extensible pour ajouter facilement de nouveaux canaux.
   ```

### Résultat attendu
- Interface `NotificationChannel`
- Implémentations : `EmailChannel`, `SMSChannel`, `PushChannel`
- `NotificationService` utilisant le pattern
- Code extensible

---

## Tâche 7 : Analyse de qualité

### Contexte
Évaluer la qualité d'un module avant de le modifier.

### Instructions

1. Utilisez un projet existant ou créez plusieurs fichiers liés

2. Demandez une analyse complète :
   ```
   Analyse la qualité de @src/ en évaluant :
   - Complexité cyclomatique
   - Couplage entre modules
   - Couverture de documentation
   - Respect des conventions PEP 8
   - Code smells détectés
   ```

3. Demandez un rapport :
   ```
   Génère un rapport de qualité avec :
   - Score global
   - Points forts
   - Points à améliorer
   - Actions recommandées par priorité
   ```

### Livrable
Fichier `quality-report.md`

---

## Tâche 8 : Workflow complet

### Contexte
Simuler un cycle de développement complet.

### Instructions

1. **Créer une branche**
   ```bash
   git checkout -b feature/validation-email
   ```

2. **Implémenter une fonctionnalité**
   ```
   Ajoute une fonction de validation d'email avancée à @utils.py
   avec vérification du format et du domaine.
   ```

3. **Review**
   ```
   /review
   ```

4. **Corriger les problèmes** détectés

5. **Ajouter des tests**
   ```
   Génère des tests complets pour la nouvelle fonction de validation.
   ```

6. **Review finale**
   ```
   /review
   ```

7. **Commit**
   ```
   /commit
   ```

### Résultat attendu
- Branche avec commits propres
- Code reviewé et corrigé
- Tests complets
- Historique Git professionnel

---

## Récapitulatif des livrables

| Tâche | Livrable |
|-------|----------|
| 1 | Premier commit formaté |
| 2 | Code reviewé et amélioré |
| 3 | Bug simple corrigé avec tests |
| 4 | Bug complexe corrigé avec tests |
| 5 | Code refactoré (responsabilités) |
| 6 | Code refactoré (pattern Strategy) |
| 7 | `quality-report.md` |
| 8 | Branche feature complète |

---

## Pour aller plus loin

- Configurez des hooks Git pour lancer `/review` automatiquement
- Créez des templates de commit personnalisés
- Intégrez Claude Code dans votre CI/CD
