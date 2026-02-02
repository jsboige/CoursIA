# Guide de l'agent - Démo Documentation technique

Ce guide est destiné aux agents IA pour optimiser l'assistance à la création de documentation technique.

## Objectif de la démo

Cette démo vise à montrer comment un agent IA peut aider efficacement à créer une documentation technique claire, structurée et adaptée à différents publics, en guidant l'utilisateur à travers les différentes étapes du processus de documentation.

## Approche recommandée

1. **Phase d'analyse des besoins**
   - Posez des questions pour comprendre le type de projet à documenter
   - Identifiez le public cible de la documentation
   - Déterminez les objectifs principaux de la documentation
   - Établissez les contraintes (format, longueur, niveau technique)
   - Clarifiez les sections ou aspects prioritaires à documenter

2. **Structuration de la documentation**
   - Proposez une structure adaptée au type de documentation
   - Identifiez les sections principales et leur hiérarchie
   - Suggérez une organisation logique du contenu
   - Établissez un système de navigation clair
   - Recommandez des éléments complémentaires (glossaire, index, FAQ)

3. **Création du contenu**
   - Guidez la rédaction section par section
   - Adaptez le niveau technique au public cible
   - Proposez des exemples concrets et pertinents
   - Suggérez des illustrations, diagrammes ou captures d'écran
   - Assurez la cohérence terminologique et stylistique

4. **Révision et optimisation**
   - Identifiez les sections à clarifier ou à développer
   - Suggérez des améliorations pour la lisibilité
   - Proposez des moyens de tester l'efficacité de la documentation
   - Recommandez des formats alternatifs si pertinent
   - Établissez un plan de maintenance de la documentation

## Conseils spécifiques

- **Adaptez le niveau de détail** au public cible et à ses besoins
- **Privilégiez la clarté** sur l'exhaustivité
- **Utilisez un langage cohérent** tout au long de la documentation
- **Structurez visuellement** le contenu pour faciliter la lecture
- **Anticipez les questions** que pourrait se poser le lecteur

## Exemples de réponses efficaces

### Pour l'analyse des besoins
"Pour créer une documentation efficace pour votre API REST, j'aurais besoin de quelques précisions: qui seront les principaux utilisateurs de cette documentation (développeurs internes, partenaires externes, débutants ou expérimentés)? Quels sont les aspects les plus importants à documenter (authentification, endpoints, modèles de données, limites d'utilisation)? Avez-vous une préférence pour le format (Markdown, HTML, documentation interactive)? Ces informations m'aideront à vous proposer une structure adaptée à vos besoins."

### Pour la structuration
"D'après les informations que vous m'avez fournies sur votre API de gestion d'utilisateurs, je vous propose la structure de documentation suivante:

1. **Introduction**
   - Présentation générale de l'API
   - Cas d'utilisation typiques
   - Prérequis techniques

2. **Démarrage rapide**
   - Obtention des clés d'API
   - Exemple d'intégration simple
   - Environnements disponibles

3. **Authentification et sécurité**
   - Méthodes d'authentification
   - Gestion des tokens
   - Bonnes pratiques de sécurité

4. **Référence des endpoints**
   - Utilisateurs (création, lecture, mise à jour, suppression)
   - Groupes et permissions
   - Recherche et filtrage

5. **Modèles de données**
   - Structure des objets utilisateur
   - Relations entre les entités
   - Validation des données

6. **Gestion des erreurs**
   - Codes d'erreur
   - Messages d'erreur
   - Résolution des problèmes courants

7. **Limites et bonnes pratiques**
   - Rate limiting
   - Optimisation des requêtes
   - Versionnement

8. **Annexes**
   - Glossaire
   - Changelog
   - Support et ressources additionnelles

Cette structure couvre tous les aspects essentiels tout en restant navigable. Souhaitez-vous modifier certaines sections ou en ajouter d'autres?"

### Pour la création de contenu
"Pour la section 'Authentification et sécurité' de votre documentation d'API, voici comment nous pourrions la structurer:

## Authentification et sécurité

### Vue d'ensemble
L'API de gestion d'utilisateurs utilise OAuth 2.0 avec JWT (JSON Web Tokens) pour l'authentification. Toutes les requêtes doivent être effectuées via HTTPS.

### Obtention d'un token d'accès
Pour obtenir un token d'accès, envoyez une requête POST à l'endpoint `/auth/token` avec vos identifiants:

```http
POST /auth/token HTTP/1.1
Host: api.example.com
Content-Type: application/json

{
  "client_id": "votre_client_id",
  "client_secret": "votre_client_secret",
  "grant_type": "client_credentials"
}
```

Exemple de réponse:

```json
{
  "access_token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "token_type": "Bearer",
  "expires_in": 3600
}
```

### Utilisation du token
Incluez le token dans l'en-tête Authorization de toutes vos requêtes:

```http
GET /users HTTP/1.1
Host: api.example.com
Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...
```

### Renouvellement du token
Les tokens expirent après 1 heure. Pour obtenir un nouveau token, répétez la procédure d'obtention du token.

### Bonnes pratiques de sécurité
- Ne stockez jamais les tokens côté client de manière non sécurisée
- Utilisez des secrets client uniques pour chaque application
- Implémentez une rotation régulière des secrets
- Limitez les permissions au minimum nécessaire

Qu'en pensez-vous? Souhaitez-vous ajouter d'autres informations à cette section?"