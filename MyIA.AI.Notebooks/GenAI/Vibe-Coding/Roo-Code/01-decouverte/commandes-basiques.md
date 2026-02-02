# 🛠️ Commandes basiques pour interagir avec Roo

Ce guide présente les interactions essentielles avec Roo en mode Ask, vous permettant de communiquer efficacement et d'obtenir les informations dont vous avez besoin.

## Principes fondamentaux d'interaction

### Structure de base des questions

Roo comprend le langage naturel, mais certaines structures de questions sont particulièrement efficaces :

- **Questions directes** : "Qu'est-ce que [concept] ?"
- **Demandes d'explication** : "Explique-moi comment [processus] fonctionne."
- **Comparaisons** : "Quelle est la différence entre [A] et [B] ?"
- **Demandes d'exemples** : "Montre-moi un exemple de [concept]."
- **Demandes de code** : "Comment implémenter [fonctionnalité] en [langage] ?"

### Commandes de contrôle de conversation

Ces "commandes" vous aident à orienter la conversation avec Roo :

- **Clarification** : "Peux-tu clarifier ce que tu entends par [terme] ?"
- **Simplification** : "Explique cela plus simplement."
- **Approfondissement** : "Développe davantage sur [aspect spécifique]."
- **Recentrage** : "Revenons à la question initiale sur [sujet]."
- **Résumé** : "Résume les points clés de ta réponse."

## Commandes spécifiques au mode Ask

### Obtenir des informations techniques

```
Explique le concept de [terme technique]
```
Exemple : "Explique le concept de programmation fonctionnelle"

```
Définis [terme] en termes simples
```
Exemple : "Définis l'injection de dépendances en termes simples"

### Demander des exemples de code

```
Montre-moi un exemple de [fonctionnalité] en [langage]
```
Exemple : "Montre-moi un exemple de tri fusion en Python"

```
Comment implémenter [fonctionnalité] avec [technologie] ?
```
Exemple : "Comment implémenter l'authentification JWT avec Express.js ?"

### Comparaisons et analyses

```
Compare [technologie A] et [technologie B] pour [cas d'usage]
```
Exemple : "Compare React et Vue.js pour une application de commerce électronique"

```
Quels sont les avantages et inconvénients de [approche] ?
```
Exemple : "Quels sont les avantages et inconvénients des microservices ?"

### Résolution de problèmes

```
Pourquoi [problème technique] se produit-il ?
```
Exemple : "Pourquoi une race condition se produit-elle dans le code asynchrone ?"

```
Comment déboguer [problème] dans [environnement] ?
```
Exemple : "Comment déboguer une fuite de mémoire dans une application Node.js ?"

### Demander des bonnes pratiques

```
Quelles sont les meilleures pratiques pour [activité] ?
```
Exemple : "Quelles sont les meilleures pratiques pour sécuriser une API REST ?"

```
Comment optimiser [processus/code] ?
```
Exemple : "Comment optimiser les requêtes à une base de données MongoDB ?"

## Techniques avancées d'interaction

### Conversation multi-tours

Pour approfondir un sujet, utilisez des questions de suivi qui font référence à la réponse précédente :

1. Question initiale : "Explique-moi les hooks dans React."
2. Suivi : "Quels sont les pièges courants lors de l'utilisation du hook useEffect ?"
3. Approfondissement : "Comment résoudre le problème de dépendances circulaires que tu as mentionné ?"

### Fournir du contexte

Pour des réponses plus pertinentes, incluez du contexte :

```
Dans le contexte de [domaine], comment [question] ?
```
Exemple : "Dans le contexte d'une application mobile avec des contraintes de batterie, comment optimiser les appels réseau ?"

### Demander des explications adaptées à votre niveau

```
Explique [concept] comme si j'étais [niveau d'expertise]
```
Exemples :
- "Explique les closures JavaScript comme si j'étais débutant"
- "Explique les closures JavaScript comme si j'avais une expérience intermédiaire"

## Conseils pour des interactions efficaces

- **Soyez précis** dans vos questions pour obtenir des réponses ciblées
- **Divisez les questions complexes** en plusieurs questions plus simples
- **Utilisez la terminologie technique appropriée** quand vous la connaissez
- **Demandez des clarifications** si la réponse n'est pas claire
- **Indiquez votre niveau de connaissance** pour obtenir des explications adaptées

## Exemples de séquences d'interaction complètes

### Apprendre un nouveau concept

1. "Qu'est-ce que le pattern Repository en développement logiciel ?"
2. "Peux-tu me donner un exemple concret en C# ?"
3. "Quels sont les avantages par rapport à l'accès direct aux données ?"
4. "Comment l'implémenter avec Entity Framework ?"

### Résoudre un problème technique

1. "Pourquoi pourrais-je rencontrer des erreurs CORS dans mon application web ?"
2. "Comment configurer correctement les en-têtes CORS dans une API Express ?"
3. "Et si mon frontend est sur un domaine différent ?"
4. "Peux-tu me montrer un exemple complet de configuration ?"

---

Pour explorer davantage les capacités de Roo, consultez le fichier [exemples-questions.md](./exemples-questions.md) qui contient une liste plus complète de questions types à essayer.