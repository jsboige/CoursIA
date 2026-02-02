# API de Gestion des Tâches - Documentation

## Vue d'ensemble

L'API de Gestion des Tâches permet aux développeurs d'intégrer des fonctionnalités complètes de gestion de tâches dans leurs applications. Cette API RESTful fournit des endpoints pour créer, lire, mettre à jour et supprimer des tâches, ainsi que pour gérer les projets, les étiquettes et les utilisateurs associés.

**Version**: 2.0.0  
**Base URL**: `https://api.taskmanager.example/v2`  
**Format**: JSON  

---

## 🔑 Authentification

Notre API utilise l'authentification par jeton JWT (JSON Web Token) pour sécuriser l'accès. Pensez à ce jeton comme à une carte d'accès numérique qui vous identifie auprès de notre système.

### Comment obtenir votre jeton d'accès

Avant de pouvoir utiliser l'API, vous devez obtenir un jeton d'authentification en envoyant vos identifiants à notre endpoint d'authentification:

```http
POST /auth/token
```

#### Ce que vous envoyez:

```json
{
  "email": "votre.email@exemple.com",
  "password": "votre_mot_de_passe"
}
```

#### Ce que vous recevez:

```json
{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "expires_at": "2025-06-19T20:00:00Z",
  "user_id": "u-12345",
  "refresh_token": "rt-67890abcdef"
}
```

### Comment utiliser votre jeton

Pour toutes les requêtes suivantes, incluez votre jeton dans l'en-tête HTTP:

```http
Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...
```

### Renouvellement du jeton

Les jetons expirent après 24 heures. Pour obtenir un nouveau jeton sans avoir à vous reconnecter:

```http
POST /auth/refresh
```

#### Ce que vous envoyez:

```json
{
  "refresh_token": "rt-67890abcdef"
}
```

---

## 📋 Gestion des Tâches

### Récupérer toutes vos tâches

Pour obtenir la liste de toutes vos tâches:

```http
GET /tasks
```

#### Options de filtrage:

| Paramètre | Description | Exemple |
|-----------|-------------|---------|
| project_id | Filtrer par projet | `?project_id=p-12345` |
| status | Filtrer par statut | `?status=in_progress` |
| priority | Filtrer par priorité (1-5) | `?priority=3` |
| due_before | Tâches dues avant cette date | `?due_before=2025-06-01T00:00:00Z` |
| due_after | Tâches dues après cette date | `?due_after=2025-05-01T00:00:00Z` |
| tags | Filtrer par étiquettes (séparées par des virgules) | `?tags=urgent,client` |

#### Options de pagination:

| Paramètre | Description | Valeur par défaut | Maximum |
|-----------|-------------|------------------|---------|
| page | Numéro de page | 1 | - |
| limit | Nombre d'éléments par page | 20 | 100 |

#### Exemple de requête complète:

```http
GET /tasks?status=pending&priority=4&due_before=2025-06-01T00:00:00Z&page=1&limit=20
```

#### Ce que vous recevez:

```json
{
  "tasks": [
    {
      "id": "t-98765",
      "title": "Finaliser la documentation API",
      "description": "Compléter et réviser la documentation de l'API REST",
      "status": "in_progress",
      "priority": 3,
      "due_date": "2025-05-25T18:00:00Z",
      "created_at": "2025-05-15T14:30:00Z",
      "updated_at": "2025-05-18T09:15:00Z",
      "project_id": "p-12345",
      "assigned_to": "u-12345",
      "tags": ["documentation", "api"],
      "completion_percentage": 75
    },
    {
      "id": "t-98766",
      "title": "Corriger le bug d'authentification",
      "description": "Résoudre le problème de déconnexion aléatoire",
      "status": "pending",
      "priority": 4,
      "due_date": "2025-05-20T18:00:00Z",
      "created_at": "2025-05-17T11:20:00Z",
      "updated_at": "2025-05-17T11:20:00Z",
      "project_id": "p-12345",
      "assigned_to": "u-12345",
      "tags": ["bug", "authentication"],
      "completion_percentage": 0
    }
  ],
  "pagination": {
    "total": 42,
    "page": 1,
    "limit": 20,
    "pages": 3
  },
  "filters_applied": {
    "status": "pending",
    "priority": 4,
    "due_before": "2025-06-01T00:00:00Z"
  }
}
```

### Créer une nouvelle tâche

Pour créer une nouvelle tâche:

```http
POST /tasks
```

#### Ce que vous envoyez:

```json
{
  "title": "Préparer la présentation client",
  "description": "Créer les slides pour la démo du nouveau dashboard",
  "status": "pending",
  "priority": 4,
  "due_date": "2025-05-30T16:00:00Z",
  "project_id": "p-12345",
  "tags": ["présentation", "client", "dashboard"]
}
```

| Champ | Requis | Description | Contraintes |
|-------|--------|-------------|-------------|
| title | Oui | Titre de la tâche | 3-100 caractères |
| description | Non | Description détaillée | Max 2000 caractères |
| status | Non | Statut de la tâche | Valeurs: `pending`, `in_progress`, `review`, `done` |
| priority | Non | Priorité de la tâche | Valeurs: 1 (basse) à 5 (haute) |
| due_date | Non | Date d'échéance | Format ISO 8601 |
| project_id | Non | ID du projet associé | Doit exister |
| assigned_to | Non | ID de l'utilisateur assigné | Par défaut: vous-même |
| tags | Non | Liste d'étiquettes | Max 10 tags |

#### Ce que vous recevez:

```json
{
  "id": "t-98767",
  "title": "Préparer la présentation client",
  "description": "Créer les slides pour la démo du nouveau dashboard",
  "status": "pending",
  "priority": 4,
  "due_date": "2025-05-30T16:00:00Z",
  "created_at": "2025-05-19T20:00:00Z",
  "updated_at": "2025-05-19T20:00:00Z",
  "project_id": "p-12345",
  "assigned_to": "u-12345",
  "created_by": "u-12345",
  "tags": ["présentation", "client", "dashboard"],
  "completion_percentage": 0,
  "_links": {
    "self": "/tasks/t-98767",
    "project": "/projects/p-12345",
    "assigned_user": "/users/u-12345"
  }
}
```

### Récupérer une tâche spécifique

Pour obtenir les détails d'une tâche particulière:

```http
GET /tasks/{task_id}
```

#### Exemple:

```http
GET /tasks/t-98765
```

#### Ce que vous recevez:

```json
{
  "id": "t-98765",
  "title": "Finaliser la documentation API",
  "description": "Compléter et réviser la documentation de l'API REST",
  "status": "in_progress",
  "priority": 3,
  "due_date": "2025-05-25T18:00:00Z",
  "created_at": "2025-05-15T14:30:00Z",
  "updated_at": "2025-05-18T09:15:00Z",
  "project_id": "p-12345",
  "created_by": "u-12346",
  "assigned_to": "u-12345",
  "tags": ["documentation", "api"],
  "completion_percentage": 75,
  "comments": [
    {
      "id": "c-34567",
      "content": "J'ai ajouté les exemples de requêtes et réponses",
      "created_at": "2025-05-17T10:30:00Z",
      "user_id": "u-12345",
      "user_name": "Jean Dupont"
    }
  ],
  "attachments": [
    {
      "id": "a-23456",
      "filename": "api_schema.json",
      "size": 24680,
      "mime_type": "application/json",
      "url": "https://storage.taskmanager.example/files/api_schema.json",
      "created_at": "2025-05-16T15:45:00Z"
    }
  ],
  "history": [
    {
      "action": "status_changed",
      "from": "pending",
      "to": "in_progress",
      "timestamp": "2025-05-16T09:30:00Z",
      "user_id": "u-12345",
      "user_name": "Jean Dupont"
    }
  ],
  "_links": {
    "self": "/tasks/t-98765",
    "project": "/projects/p-12345",
    "assigned_user": "/users/u-12345",
    "creator": "/users/u-12346"
  }
}
```

### Mettre à jour une tâche

Pour modifier une tâche existante:

```http
PUT /tasks/{task_id}
```

#### Exemple:

```http
PUT /tasks/t-98765
```

#### Ce que vous envoyez:

```json
{
  "status": "done",
  "completion_percentage": 100
}
```

Vous pouvez mettre à jour n'importe quel champ mentionné dans la section "Créer une tâche". Seuls les champs que vous incluez seront modifiés.

#### Ce que vous recevez:

```json
{
  "id": "t-98765",
  "title": "Finaliser la documentation API",
  "description": "Compléter et réviser la documentation de l'API REST",
  "status": "done",
  "priority": 3,
  "due_date": "2025-05-25T18:00:00Z",
  "created_at": "2025-05-15T14:30:00Z",
  "updated_at": "2025-05-19T20:00:00Z",
  "project_id": "p-12345",
  "assigned_to": "u-12345",
  "tags": ["documentation", "api"],
  "completion_percentage": 100
}
```

### Supprimer une tâche

Pour supprimer définitivement une tâche:

```http
DELETE /tasks/{task_id}
```

#### Exemple:

```http
DELETE /tasks/t-98765
```

Si la suppression réussit, vous recevrez un code de statut 204 (No Content) sans corps de réponse.

---

## 📂 Gestion des Projets

### Récupérer tous les projets

```http
GET /projects
```

#### Ce que vous recevez:

```json
{
  "projects": [
    {
      "id": "p-12345",
      "name": "Refonte du site web",
      "description": "Modernisation complète du site corporate",
      "status": "active",
      "created_at": "2025-04-10T09:00:00Z",
      "updated_at": "2025-05-15T14:30:00Z",
      "owner_id": "u-12345",
      "task_count": 18,
      "completion_percentage": 65
    },
    {
      "id": "p-12346",
      "name": "Application mobile v2",
      "description": "Développement de la nouvelle version de l'app",
      "status": "active",
      "created_at": "2025-05-01T10:15:00Z",
      "updated_at": "2025-05-18T16:45:00Z",
      "owner_id": "u-12345",
      "task_count": 24,
      "completion_percentage": 30
    }
  ],
  "pagination": {
    "total": 5,
    "page": 1,
    "limit": 20,
    "pages": 1
  }
}
```

### Créer un nouveau projet

```http
POST /projects
```

#### Ce que vous envoyez:

```json
{
  "name": "Campagne marketing Q3",
  "description": "Préparation et exécution de la campagne du troisième trimestre",
  "status": "planning",
  "start_date": "2025-07-01T00:00:00Z",
  "end_date": "2025-09-30T23:59:59Z",
  "members": ["u-12345", "u-12346", "u-12347"]
}
```

---

## 👥 Gestion des Utilisateurs

### Récupérer les informations de l'utilisateur courant

```http
GET /users/me
```

#### Ce que vous recevez:

```json
{
  "id": "u-12345",
  "email": "jean.dupont@exemple.com",
  "name": "Jean Dupont",
  "role": "project_manager",
  "created_at": "2024-01-15T10:00:00Z",
  "last_login": "2025-05-19T08:30:00Z",
  "preferences": {
    "language": "fr",
    "timezone": "Europe/Paris",
    "notifications": {
      "email": true,
      "push": true
    }
  },
  "statistics": {
    "tasks_assigned": 12,
    "tasks_completed": 45,
    "projects_owned": 3
  }
}
```

### Mettre à jour les préférences utilisateur

```http
PATCH /users/me/preferences
```

#### Ce que vous envoyez:

```json
{
  "notifications": {
    "email": false,
    "push": true
  },
  "timezone": "Europe/London"
}
```

---

## 🏷️ Gestion des Étiquettes

### Récupérer toutes les étiquettes

```http
GET /tags
```

#### Ce que vous recevez:

```json
{
  "tags": [
    {
      "id": "tag-123",
      "name": "urgent",
      "color": "#FF0000",
      "usage_count": 15
    },
    {
      "id": "tag-124",
      "name": "bug",
      "color": "#FFA500",
      "usage_count": 8
    },
    {
      "id": "tag-125",
      "name": "feature",
      "color": "#0000FF",
      "usage_count": 23
    }
  ]
}
```

### Créer une nouvelle étiquette

```http
POST /tags
```

#### Ce que vous envoyez:

```json
{
  "name": "marketing",
  "color": "#00FF00"
}
```

---

## 📊 Statistiques et Rapports

### Obtenir des statistiques générales

```http
GET /stats/overview
```

#### Ce que vous recevez:

```json
{
  "tasks": {
    "total": 156,
    "completed": 98,
    "overdue": 12,
    "completion_rate": 62.8
  },
  "projects": {
    "total": 5,
    "active": 3,
    "completed": 2
  },
  "activity": {
    "tasks_created_last_7_days": 23,
    "tasks_completed_last_7_days": 18
  },
  "performance": {
    "avg_completion_time_days": 4.3,
    "on_time_completion_rate": 78.5
  }
}
```

### Générer un rapport personnalisé

```http
POST /reports/generate
```

#### Ce que vous envoyez:

```json
{
  "type": "project_progress",
  "project_id": "p-12345",
  "date_range": {
    "start": "2025-04-01T00:00:00Z",
    "end": "2025-05-19T23:59:59Z"
  },
  "group_by": "week",
  "include_users": true,
  "format": "json"
}
```

---

## 📱 Notifications

### Récupérer les notifications non lues

```http
GET /notifications
```

#### Ce que vous recevez:

```json
{
  "notifications": [
    {
      "id": "n-45678",
      "type": "task_assigned",
      "read": false,
      "created_at": "2025-05-19T14:30:00Z",
      "data": {
        "task_id": "t-98768",
        "task_title": "Préparer le rapport mensuel",
        "assigned_by": "u-12346",
        "assigned_by_name": "Marie Martin"
      }
    },
    {
      "id": "n-45679",
      "type": "comment_added",
      "read": false,
      "created_at": "2025-05-19T15:45:00Z",
      "data": {
        "task_id": "t-98765",
        "task_title": "Finaliser la documentation API",
        "comment_id": "c-34568",
        "comment_by": "u-12347",
        "comment_by_name": "Pierre Durand",
        "comment_preview": "J'ai quelques suggestions pour..."
      }
    }
  ],
  "unread_count": 2,
  "pagination": {
    "total": 2,
    "page": 1,
    "limit": 20,
    "pages": 1
  }
}
```

### Marquer une notification comme lue

```http
PATCH /notifications/{notification_id}
```

#### Ce que vous envoyez:

```json
{
  "read": true
}
```

---

## ⚠️ Gestion des erreurs

Notre API utilise des codes de statut HTTP standard et renvoie des messages d'erreur détaillés au format JSON pour vous aider à comprendre et résoudre les problèmes.

### Format des erreurs

```json
{
  "error": {
    "code": "invalid_request",
    "message": "Le champ 'title' est requis",
    "details": {
      "field": "title",
      "reason": "required"
    },
    "request_id": "req-abcdef123456",
    "documentation_url": "https://docs.taskmanager.example/errors/invalid_request"
  }
}
```

### Codes d'erreur communs

| Code HTTP | Code d'erreur | Description | Solution possible |
|-----------|---------------|-------------|-------------------|
| 400 | invalid_request | Requête mal formée | Vérifiez les paramètres de votre requête |
| 401 | unauthorized | Authentification requise | Vérifiez votre jeton d'authentification |
| 403 | forbidden | Permissions insuffisantes | Vérifiez les droits de l'utilisateur |
| 404 | not_found | Ressource non trouvée | Vérifiez l'identifiant de la ressource |
| 422 | validation_failed | Données invalides | Corrigez les données selon les indications |
| 429 | rate_limit_exceeded | Trop de requêtes | Attendez avant de réessayer |
| 500 | server_error | Erreur interne | Contactez le support |

### Exemple d'erreur de validation

```json
{
  "error": {
    "code": "validation_failed",
    "message": "La validation a échoué pour certains champs",
    "details": [
      {
        "field": "due_date",
        "reason": "invalid_format",
        "message": "La date doit être au format ISO 8601 (ex: 2025-05-30T16:00:00Z)"
      },
      {
        "field": "priority",
        "reason": "out_of_range",
        "message": "La priorité doit être comprise entre 1 et 5"
      }
    ],
    "request_id": "req-abcdef123456"
  }
}
```

---

## 🚦 Limites de débit

Pour assurer la stabilité et la disponibilité de notre API pour tous les utilisateurs, nous appliquons des limites de débit:

| Plan | Requêtes par minute | Requêtes par jour |
|------|---------------------|-------------------|
| Gratuit | 60 | 10,000 |
| Pro | 300 | 50,000 |
| Entreprise | 1,000 | 200,000 |

Les en-têtes suivants sont inclus dans chaque réponse pour vous aider à gérer votre consommation:

```
X-RateLimit-Limit: 60
X-RateLimit-Remaining: 58
X-RateLimit-Reset: 1621440000
```

### Stratégies en cas de dépassement

Si vous dépassez vos limites, vous recevrez une réponse 429 (Too Many Requests) avec un en-tête `Retry-After` indiquant le nombre de secondes à attendre avant de réessayer.

---

## 🔄 Versionnement

Notre API suit le versionnement sémantique (SemVer). La version actuelle est v2.0.0.

- Les changements majeurs (v1.0.0 → v2.0.0) peuvent introduire des modifications non rétrocompatibles
- Les changements mineurs (v2.0.0 → v2.1.0) ajoutent des fonctionnalités de manière rétrocompatible
- Les correctifs (v2.1.0 → v2.1.1) corrigent des bugs de manière rétrocompatible

Nous maintenons les versions majeures pendant au moins 12 mois après la sortie d'une nouvelle version.

---

## 🛠️ Outils et ressources

### Environnements disponibles

| Environnement | URL | Description |
|---------------|-----|-------------|
| Production | https://api.taskmanager.example/v2 | Environnement de production |
| Sandbox | https://sandbox-api.taskmanager.example/v2 | Environnement de test avec données fictives |

### SDK et bibliothèques clientes

Nous proposons des bibliothèques officielles pour faciliter l'intégration:

- [JavaScript/TypeScript](https://github.com/taskmanager/js-client)
- [Python](https://github.com/taskmanager/python-client)
- [PHP](https://github.com/taskmanager/php-client)
- [Java](https://github.com/taskmanager/java-client)
- [.NET](https://github.com/taskmanager/dotnet-client)

### Outils de développement

- [Collection Postman](https://www.postman.com/taskmanager/workspace/api-public)
- [Swagger UI](https://api.taskmanager.example/docs)
- [OpenAPI Spec](https://api.taskmanager.example/openapi.json)

---

## 📞 Support et contact

Pour toute question ou problème concernant l'API:

- **Documentation complète**: [https://docs.taskmanager.example](https://docs.taskmanager.example)
- **Status de l'API**: [https://status.taskmanager.example](https://status.taskmanager.example)
- **Email**: api-support@taskmanager.example
- **Forum développeurs**: [https://community.taskmanager.example](https://community.taskmanager.example)

Notre équipe de support est disponible du lundi au vendredi, de 9h à 18h (UTC).

---

## 📅 Feuille de route

Voici les fonctionnalités prévues pour les prochaines versions:

- **v2.1.0** (Q3 2025)
  - Webhooks pour les notifications en temps réel
  - Filtres avancés pour les rapports
  - Intégration avec des services de calendrier

- **v2.2.0** (Q4 2025)
  - API GraphQL (bêta)
  - Automatisations et workflows
  - Métriques de performance avancées

N'hésitez pas à nous faire part de vos suggestions pour les futures fonctionnalités!