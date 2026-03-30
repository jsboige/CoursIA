# Demo 2 - Agent Plan

## Objectif

Utiliser le mode Plan de Claude Code pour concevoir des implémentations structurées avant de coder.

## Durée estimée

**40 minutes**

## Concepts

### Qu'est-ce que le mode Plan ?

Le mode Plan est une approche de travail où Claude :

1. **Analyse** le problème et le contexte existant
2. **Propose** un plan d'implémentation détaillé
3. **Attend** votre validation avant de modifier le code
4. **Exécute** le plan étape par étape

### Avantages du mode Plan

| Sans Plan | Avec Plan |
|-----------|-----------|
| Modifications immédiates | Réflexion préalable |
| Risque de mauvaise direction | Vision globale validée |
| Corrections en cascade | Approche structurée |
| Difficile à réviser | Facile à ajuster |

### Quand utiliser Plan ?

- ✅ Nouvelles fonctionnalités complexes
- ✅ Refactoring important
- ✅ Changements d'architecture
- ✅ Intégration de nouvelles dépendances
- ❌ Petites corrections de bugs
- ❌ Ajouts simples et isolés

## Étapes

### Étape 1 : Activer le mode Plan (5 min)

Il y a deux façons d'utiliser le mode Plan :

#### Option 1 : Via la ligne de commande

```bash
claude --permission-mode plan
```

En mode plan, Claude ne peut que lire et explorer, pas modifier.

#### Option 2 : En demandant explicitement

```
Planifie comment implémenter [fonctionnalité] sans modifier le code pour l'instant.
```

### Étape 2 : Décrire le besoin (10 min)

Pour un bon plan, fournissez :
- Le contexte du projet
- L'objectif de la fonctionnalité
- Les contraintes techniques
- Les critères de succès

#### Exemple de demande

```
Contexte : J'ai une API Flask qui gère des utilisateurs.

Objectif : Ajouter un système de cache Redis pour les requêtes GET fréquentes.

Contraintes :
- Doit fonctionner avec et sans Redis (fallback)
- Cache invalidé quand les données changent
- TTL configurable

Planifie cette implémentation en détaillant :
1. Les fichiers à créer/modifier
2. Les dépendances à ajouter
3. L'ordre des étapes
4. Les tests nécessaires
```

### Étape 3 : Analyser le plan proposé (10 min)

Claude va proposer un plan structuré. Analysez :

- **Complétude** : Toutes les étapes sont-elles couvertes ?
- **Ordre** : La séquence est-elle logique ?
- **Risques** : Les cas limites sont-ils gérés ?
- **Tests** : La stratégie de test est-elle adéquate ?

#### Questions de validation

```
Quels sont les risques de cette approche ?
```

```
Comment gères-tu le cas où Redis n'est pas disponible ?
```

```
Y a-t-il des alternatives à considérer ?
```

### Étape 4 : Affiner le plan (10 min)

Demandez des ajustements :

```
Ajoute au plan :
- Une stratégie de monitoring du cache
- Des métriques de hit/miss ratio
```

```
Simplifie l'étape 3, je préfère commencer sans le fallback complexe.
```

### Étape 5 : Exécuter le plan (5 min)

Une fois satisfait :

```
Le plan me convient. Exécute-le étape par étape.
```

Claude va alors :
1. Implémenter chaque étape
2. Vous montrer les changements
3. Attendre votre validation avant de continuer

## Exercice pratique

### Mission

Planifiez l'ajout d'une fonctionnalité d'authentification à un projet.

### Contexte fourni

Utilisez le projet exemple de l'atelier 01 ou créez un nouveau projet simple.

### Demande

```
Je veux ajouter un système d'authentification JWT à mon API.

Fonctionnalités requises :
- Inscription (email/mot de passe)
- Connexion (retourne un JWT)
- Route protégée nécessitant un token valide
- Refresh token

Contraintes :
- Stockage des utilisateurs en base de données
- Hachage bcrypt pour les mots de passe
- Tokens avec expiration configurable

Planifie cette implémentation complète.
```

### Livrable

Document `plan-authentification.md` contenant :
- Le plan validé
- Vos questions/ajustements
- La version finale du plan

## Exemples de plans bien structurés

### Structure type d'un bon plan

```markdown
# Plan d'implémentation : [Fonctionnalité]

## 1. Vue d'ensemble
[Description de l'approche choisie]

## 2. Dépendances à ajouter
- package1 : [raison]
- package2 : [raison]

## 3. Fichiers à créer
- `src/auth/jwt.py` : Gestion des tokens
- `src/auth/middleware.py` : Middleware de vérification

## 4. Fichiers à modifier
- `src/routes/api.py` : Ajouter les routes auth
- `src/models/user.py` : Ajouter champs password_hash

## 5. Étapes d'implémentation
### Étape 1 : Configuration (5 min)
[Détails]

### Étape 2 : Modèle User (10 min)
[Détails]

### Étape 3 : Service Auth (15 min)
[Détails]

## 6. Tests à créer
- `tests/test_auth.py` : Tests unitaires auth
- `tests/test_integration.py` : Tests d'intégration

## 7. Documentation à mettre à jour
- README.md : Section authentification
- API.md : Nouveaux endpoints

## 8. Risques et mitigations
| Risque | Mitigation |
|--------|------------|
| [Risque 1] | [Solution] |
```

## Points clés à retenir

1. **Plan avant d'agir** : Pour les tâches complexes, toujours planifier

2. **Itérez sur le plan** : N'hésitez pas à demander des ajustements

3. **Validez les risques** : Un bon plan identifie les problèmes potentiels

4. **Gardez une trace** : Le plan devient documentation

## Commandes utiles

```bash
# Démarrer en mode plan
claude --permission-mode plan

# Dans une session, demander un plan
> Planifie [tâche] sans modifier le code

# Valider et exécuter
> Exécute le plan

# Exécuter une seule étape
> Exécute uniquement l'étape 1 du plan
```

---

**Prochaine étape** : [Demo 3 - Recherche Web](../demo-3-recherche-web/)
