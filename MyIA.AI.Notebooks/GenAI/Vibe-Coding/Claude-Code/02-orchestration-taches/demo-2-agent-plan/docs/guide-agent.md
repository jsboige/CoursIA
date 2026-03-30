# Guide Agent - Demo 2 : Agent Plan

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Comprendre l'intérêt de planifier avant de coder
- Savoir formuler une demande de plan efficace
- Apprendre à valider et itérer sur un plan
- Exécuter un plan de manière contrôlée

## Points de vigilance

### Formulation de la demande

1. **Trop vague**
   - "Ajoute des fonctionnalités" → Plan superficiel
   - Encourager à préciser contexte, objectifs, contraintes

2. **Trop détaillé**
   - Si tout est déjà décidé, pas besoin de plan
   - Le plan doit apporter de la réflexion

### Qualité du plan

1. **Plan trop ambitieux**
   - Découper en phases si nécessaire
   - Valider la première phase avant de continuer

2. **Plan incomplet**
   - Demander explicitement tests, documentation, edge cases

## Déroulé suggéré

### Phase 1 : Introduction (5 min)

Expliquer pourquoi planifier :
- Éviter les impasses
- Valider l'approche avant l'effort
- Documentation intégrée
- Meilleure estimation du travail

### Phase 2 : Démo du mode Plan (10 min)

Montrer le processus complet :
1. Activer le mode plan
2. Formuler une demande
3. Recevoir et analyser le plan
4. Poser des questions
5. Exécuter

### Phase 3 : Pratique guidée (15 min)

Accompagner les apprenants dans la création d'un plan pour une fonctionnalité au choix.

### Phase 4 : Exercice autonome (10 min)

Plan d'authentification complet.

## Réponses aux questions fréquentes

### "Comment savoir si j'ai besoin d'un plan ?"

Règle simple : si la tâche touche plus de 3 fichiers ou introduit un nouveau concept, planifiez.

### "Le plan est-il toujours respecté ?"

Le plan est un guide, pas un contrat. Pendant l'exécution, Claude peut proposer des ajustements si des problèmes apparaissent.

### "Puis-je modifier le plan en cours d'exécution ?"

Oui, vous pouvez :
- Arrêter et demander un nouveau plan
- Ajuster les étapes restantes
- Sauter des étapes non pertinentes

### "Le plan prend en compte le code existant ?"

Oui, Claude explore le projet avant de planifier. C'est pourquoi le plan est pertinent pour votre contexte spécifique.

## Critères de validation

L'apprenant a réussi cette démo si :

- [ ] Comprend quand utiliser le mode Plan
- [ ] Sait formuler une demande de plan complète
- [ ] A posé des questions pour améliorer un plan
- [ ] A créé un plan structuré et validé
- [ ] Comprend comment exécuter un plan

## Structure de plan recommandée

```markdown
# Plan : [Titre]

## Contexte
[Résumé de la situation actuelle]

## Objectif
[Ce que nous voulons atteindre]

## Approche choisie
[Pourquoi cette approche vs alternatives]

## Dépendances
- [ ] Dépendance 1
- [ ] Dépendance 2

## Étapes

### 1. [Nom de l'étape] (Xmin)
**Fichiers** : `path/to/file.py`
**Actions** :
- Action 1
- Action 2
**Validation** : [Comment savoir que c'est fait]

### 2. [Nom de l'étape] (Xmin)
...

## Tests
- [ ] Test unitaire 1
- [ ] Test intégration 1

## Rollback
[Comment revenir en arrière si problème]

## Risques
| Risque | Probabilité | Impact | Mitigation |
|--------|-------------|--------|------------|
```

## Erreurs courantes

### Plan trop long

**Cause** : Tâche trop ambitieuse

**Solution** :
```
Ce plan est trop long. Découpe-le en 3 phases.
Phase 1 devrait être livrable indépendamment.
```

### Plan sans tests

**Cause** : Oubli ou demande incomplète

**Solution** :
```
Ajoute au plan une stratégie de test complète avec exemples.
```

### Plan générique

**Cause** : Claude n'a pas assez exploré le projet

**Solution** :
```
Explore d'abord le projet, puis propose un plan adapté à l'existant.
```

## Exemples de bonnes demandes

### Complète

```
Contexte : API Flask existante avec SQLAlchemy et PostgreSQL.
Actuellement pas d'authentification.

Objectif : Ajouter authentification JWT avec :
- Inscription/Connexion
- Tokens avec refresh
- Middleware de protection

Contraintes :
- Compatible avec la structure existante
- Tests avec pytest
- Documentation OpenAPI

Planifie en détaillant fichiers, ordre, et risques.
```

### Itérative

```
Première demande :
"Quelles sont les options pour ajouter du caching ?"

Après réponse :
"Planifie l'option Redis avec fallback mémoire."

Après plan :
"Ajoute des métriques de monitoring au plan."
```

## Ressources pour le formateur

- [Plan Mode Documentation](https://code.claude.com/docs/en/modes#plan)
- [Best Practices Planning](https://www.anthropic.com/engineering/claude-code-best-practices#planning)
