# 🛠️ Bonnes Pratiques d'Intégration avec MCP

Ce document présente les bonnes pratiques pour concevoir, implémenter et maintenir des intégrations robustes entre Roo et d'autres services via le protocole MCP (Model Context Protocol).

## Table des matières

1. [Conception d'intégrations](#1-conception-dintégrations)
2. [Sécurité et confidentialité](#2-sécurité-et-confidentialité)
3. [Performance et optimisation](#3-performance-et-optimisation)
4. [Gestion des erreurs et résilience](#4-gestion-des-erreurs-et-résilience)
5. [Tests et validation](#5-tests-et-validation)
6. [Maintenance et évolution](#6-maintenance-et-évolution)
7. [Documentation](#7-documentation)
8. [Patterns d'intégration avancés](#8-patterns-dintégration-avancés)

---

## 1. Conception d'intégrations

### 1.1. Principes de conception

#### Principe de responsabilité unique
Chaque intégration doit avoir une responsabilité claire et unique. Évitez de créer des intégrations "couteau suisse" qui tentent de faire trop de choses.

```javascript
// ❌ Mauvaise pratique: Intégration avec trop de responsabilités
async function githubIntegration(repo, issue, pr, code) {
  // Gestion des issues
  // Gestion des PRs
  // Analyse de code
  // Génération de rapports
  // Notifications
  // ...
}

// ✅ Bonne pratique: Intégrations avec responsabilités distinctes
async function githubIssueManager(repo, issue) { /* ... */ }
async function githubPRReviewer(repo, pr) { /* ... */ }
async function githubCodeAnalyzer(repo, code) { /* ... */ }
```

#### Conception modulaire
Structurez vos intégrations de manière modulaire pour faciliter la réutilisation et la maintenance.

```javascript
// Structure modulaire d'intégration
const githubIntegration = {
  // Module de gestion des issues
  issues: {
    create: async (repo, title, body) => { /* ... */ },
    list: async (repo, filters) => { /* ... */ },
    update: async (repo, issueNumber, updates) => { /* ... */ }
  },
  
  // Module de gestion des PRs
  pullRequests: {
    create: async (repo, branch, title, body) => { /* ... */ },
    review: async (repo, prNumber) => { /* ... */ },
    merge: async (repo, prNumber, strategy) => { /* ... */ }
  },
  
  // Module d'analyse de code
  codeAnalysis: {
    lint: async (repo, files) => { /* ... */ },
    securityScan: async (repo) => { /* ... */ },
    qualityMetrics: async (repo) => { /* ... */ }
  }
};
```

#### Interface cohérente
Maintenez une interface cohérente entre vos différentes intégrations pour faciliter leur utilisation.

```javascript
// Interface cohérente entre différentes intégrations
const integrations = {
  github: {
    create: async (resource, data) => { /* ... */ },
    read: async (resource, id) => { /* ... */ },
    update: async (resource, id, data) => { /* ... */ },
    delete: async (resource, id) => { /* ... */ }
  },
  
  jira: {
    create: async (resource, data) => { /* ... */ },
    read: async (resource, id) => { /* ... */ },
    update: async (resource, id, data) => { /* ... */ },
    delete: async (resource, id) => { /* ... */ }
  }
};
```

### 1.2. Architecture d'intégration

#### Pattern d'adaptateur
Utilisez le pattern d'adaptateur pour normaliser les interfaces entre différents services.

```javascript
// Pattern d'adaptateur pour normaliser les interfaces
class IssueTrackingAdapter {
  constructor(service) {
    this.service = service;
  }
  
  async createIssue(title, description, priority) {
    // Implémentation spécifique selon le service
  }
  
  async getIssues(filters) {
    // Implémentation spécifique selon le service
  }
}

class GithubIssueAdapter extends IssueTrackingAdapter {
  async createIssue(title, description, priority) {
    return use_mcp_tool({
      server_name: "github",
      tool_name: "create_issue",
      arguments: {
        owner: this.service.owner,
        repo: this.service.repo,
        title: title,
        body: description,
        labels: [priority]
      }
    });
  }
  
  // Autres méthodes...
}

class JiraIssueAdapter extends IssueTrackingAdapter {
  async createIssue(title, description, priority) {
    // Implémentation pour Jira
  }
  
  // Autres méthodes...
}
```

#### Séparation des préoccupations
Séparez clairement la logique métier de la logique d'intégration.

```javascript
// Séparation des préoccupations
// 1. Couche d'accès aux données (intégration)
const dataAccess = {
  getProjectData: async (projectId) => {
    // Appel MCP pour récupérer les données
#### Architecture événementielle
Pour les intégrations complexes, envisagez une architecture basée sur les événements.

```javascript
// Architecture événementielle
const eventBus = {
  subscribers: {},
  
  subscribe: function(event, callback) {
    if (!this.subscribers[event]) {
      this.subscribers[event] = [];
    }
    this.subscribers[event].push(callback);
  },
  
  publish: function(event, data) {
    if (!this.subscribers[event]) return;
    
    this.subscribers[event].forEach(callback => {
      callback(data);
    });
  }
};

// Exemple d'utilisation
eventBus.subscribe('issue:created', async (issue) => {
  // Notification Slack
  await notifySlack(`Nouvelle issue créée: ${issue.title}`);
});

eventBus.subscribe('issue:created', async (issue) => {
  // Mise à jour du tableau de bord
  await updateDashboard(issue);
});

// Déclenchement d'un événement
async function createIssue(title, description) {
  const issue = await use_mcp_tool({
    server_name: "github",
    tool_name: "create_issue",
    arguments: { /* ... */ }
  });
  
  eventBus.publish('issue:created', issue);
  return issue;
}
```

## 2. Sécurité et confidentialité

### 2.1. Gestion des secrets

#### Ne jamais coder en dur les secrets
Ne jamais inclure directement les clés API, tokens ou mots de passe dans votre code.

```javascript
// ❌ Mauvaise pratique: Secrets en dur dans le code
const apiKey = "sk_live_1234567890abcdef";

// ✅ Bonne pratique: Utilisation de variables d'environnement
const apiKey = process.env.API_KEY;
```

#### Stockage sécurisé des secrets
Utilisez des solutions dédiées pour le stockage des secrets.

```javascript
// Exemple conceptuel d'utilisation d'un gestionnaire de secrets
async function getSecret(secretName) {
  // Récupération depuis un coffre-fort sécurisé
  return await secretManager.getSecret(secretName);
}

async function callApi() {
  const apiKey = await getSecret("api_key");
  // Utilisation de la clé
}
```

#### Rotation régulière des secrets
Mettez en place un système de rotation régulière des secrets.

```javascript
// Exemple conceptuel de vérification de l'âge d'un secret
async function checkSecretAge(secretName) {
  const metadata = await secretManager.getSecretMetadata(secretName);
  const ageInDays = (Date.now() - metadata.lastRotated) / (1000 * 60 * 60 * 24);
  
  if (ageInDays > 90) {
    // Alerte pour rotation du secret
    await notifySecretRotation(secretName);
  }
}
```

### 2.2. Contrôle d'accès

#### Principe du moindre privilège
Accordez uniquement les permissions minimales nécessaires pour chaque intégration.

```javascript
// Exemple de définition de permissions minimales
const githubPermissions = {
  issues: ["read", "write"],
  pullRequests: ["read"],
  repositories: ["read"],
  // Pas d'accès aux secrets, aux actions, etc.
};
```

#### Validation des entrées
Validez toujours les entrées avant de les transmettre aux services externes.

```javascript
// Validation des entrées
function validateIssueData(issueData) {
  if (!issueData.title \| issueData.title.length < 3) {
    throw new Error("Le titre de l'issue doit contenir au moins 3 caractères");
  }
  
  if (issueData.title.length > 255) {
    throw new Error("Le titre de l'issue ne doit pas dépasser 255 caractères");
  }
  
  // Autres validations...
  
  return true;
}

async function createIssue(issueData) {
  validateIssueData(issueData);
  
  // Création de l'issue
}
```

#### Audit et traçabilité
Mettez en place un système d'audit pour tracer toutes les opérations effectuées via les intégrations.

```javascript
// Système d'audit
async function auditOperation(operation, details) {
  await use_mcp_tool({
    server_name: "filesystem",
    tool_name: "write_file",
    arguments: {
      path: `./logs/audit_${new Date().toISOString().split('T')[0]}.log`,
      content: `${new Date().toISOString()} - ${operation} - ${JSON.stringify(details)}\n`,
      append: true
    }
  });
}

async function createIssue(issueData) {
  // Audit avant opération
  await auditOperation("issue_create_attempt", { title: issueData.title });
  
  try {
    const result = await use_mcp_tool({
      server_name: "github",
      tool_name: "create_issue",
      arguments: { /* ... */ }
    });
    
    // Audit après succès
    await auditOperation("issue_create_success", { id: result.id, title: issueData.title });
    
    return result;
  } catch (error) {
    // Audit après échec
    await auditOperation("issue_create_failure", { title: issueData.title, error: error.message });
    throw error;
  }
}
```

### 2.3. Protection des données

#### Minimisation des données
Ne collectez et ne transmettez que les données strictement nécessaires.

```javascript
// ❌ Mauvaise pratique: Transmission de données excessives
async function getUserData(userId) {
  const user = await database.getUser(userId);
  return user; // Contient potentiellement des données sensibles
}

// ✅ Bonne pratique: Transmission des données minimales nécessaires
async function getUserDisplayData(userId) {
  const user = await database.getUser(userId);
  return {
    id: user.id,
    displayName: user.displayName,
    avatarUrl: user.avatarUrl
    // Pas de données sensibles comme email, mot de passe, etc.
  };
}
```

#### Chiffrement des données sensibles
Chiffrez les données sensibles en transit et au repos.

```javascript
// Exemple conceptuel de chiffrement de données
async function encryptSensitiveData(data) {
  const encryptionKey = await getSecret("encryption_key");
  return encrypt(data, encryptionKey);
}

async function storeUserData(userId, userData) {
  const sensitiveFields = ["socialSecurityNumber", "bankAccountDetails"];
  
  // Chiffrement des champs sensibles
  for (const field of sensitiveFields) {
    if (userData[field]) {
      userData[field] = await encryptSensitiveData(userData[field]);
    }
  }
  
  // Stockage des données
  await database.storeUser(userId, userData);
}
```

#### Anonymisation et pseudonymisation
Anonymisez ou pseudonymisez les données personnelles lorsque c'est possible.

```javascript
// Exemple d'anonymisation de logs
function anonymizeLogs(logEntry) {
  // Remplacer les emails
  logEntry = logEntry.replace(/[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}/g, "[EMAIL]");
  
  // Remplacer les numéros de téléphone
  logEntry = logEntry.replace(/(\+\d{1,3}[\s.-])?\(?\d{3}\)?[\s.-]?\d{3}[\s.-]?\d{4}/g, "[PHONE]");
  
  // Remplacer les adresses IP
  logEntry = logEntry.replace(/\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b/g, "[IP]");
  
  return logEntry;
}
```

## 3. Performance et optimisation

### 3.1. Gestion des ressources

#### Mise en cache intelligente
Implémentez une stratégie de mise en cache pour réduire les appels aux services externes.

```javascript
// Système de cache simple
const cache = {
  data: {},
  
  async get(key, fetchFunction, ttlSeconds = 300) {
    const now = Date.now();
    
    // Vérification si la donnée est en cache et valide
    if (this.data[key] && this.data[key].expiry > now) {
      return this.data[key].value;
    }
    
    // Récupération de la donnée
    const value = await fetchFunction();
    
    // Mise en cache avec expiration
    this.data[key] = {
      value,
      expiry: now + (ttlSeconds * 1000)
    };
    
    return value;
  },
  
  invalidate(key) {
    delete this.data[key];
  }
};

// Utilisation du cache
async function getRepositoryInfo(owner, repo) {
  const cacheKey = `repo:${owner}/${repo}`;
  
  return cache.get(cacheKey, async () => {
    return use_mcp_tool({
      server_name: "github",
      tool_name: "get_repository",
      arguments: { owner, repo }
    });
  }, 600); // Cache valide pendant 10 minutes
}
```

#### Traitement par lots
Regroupez les opérations similaires pour réduire le nombre d'appels aux services externes.

```javascript
// Traitement par lots
async function batchProcessFiles(filePaths, operation) {
  // Regroupement par lots de 10 fichiers
  const batches = [];
  for (let i = 0; i < filePaths.length; i += 10) {
    batches.push(filePaths.slice(i, i + 10));
  }
  
  const results = [];
  
  for (const batch of batches) {
    // Traitement parallèle du lot
    const batchResults = await Promise.all(
      batch.map(filePath => operation(filePath))
    );
    
    results.push(...batchResults);
  }
  
  return results;
}

// Utilisation
const filesToProcess = ["file1.txt", "file2.txt", /* ... */];
const results = await batchProcessFiles(filesToProcess, async (filePath) => {
  // Opération sur chaque fichier
  return processFile(filePath);
});
```
  },
  saveProjectData: async (projectId, data) => {
    // Appel MCP pour sauvegarder les données
  }
};

// 2. Couche de logique métier
const businessLogic = {
  analyzeProjectHealth: async (projectId) => {
    const data = await dataAccess.getProjectData(projectId);
    // Analyse des données selon les règles métier
    return analysis;
  }
};

// 3. Couche de présentation
const presentation = {
  generateProjectReport: async (projectId) => {
    const analysis = await businessLogic.analyzeProjectHealth(projectId);
    // Formatage des résultats pour présentation
    return report;
  }
};
#### Exécution asynchrone
Pour les opérations longues, utilisez des mécanismes d'exécution asynchrone.

```javascript
// File d'attente pour traitement asynchrone
const taskQueue = [];
let isProcessing = false;

async function enqueueTask(task) {
  taskQueue.push(task);
  
  if (!isProcessing) {
    processQueue();
  }
}

async function processQueue() {
  if (taskQueue.length === 0) {
    isProcessing = false;
    return;
  }
  
  isProcessing = true;
  const task = taskQueue.shift();
  
  try {
    await task();
  } catch (error) {
    console.error("Erreur lors de l'exécution de la tâche:", error);
  }
  
  // Traitement de la tâche suivante
  processQueue();
}

// Utilisation
function generateLargeReport() {
  return new Promise(resolve => {
    enqueueTask(async () => {
      // Opération longue
      const data = await collectLargeDataSet();
      const report = await processData(data);
      
      // Notification de fin
      await notifyReportReady(report);
      
      resolve(report);
    });
  });
}
```

### 3.2. Optimisation des requêtes

#### Sélection des champs
Limitez les données récupérées aux champs nécessaires.

```javascript
// ❌ Mauvaise pratique: Récupération de toutes les données
async function getUserProfile(userId) {
  return use_mcp_tool({
    server_name: "database",
    tool_name: "query",
    arguments: {
      query: "SELECT * FROM users WHERE id = ?",
      params: [userId]
    }
  });
}

// ✅ Bonne pratique: Sélection des champs nécessaires
async function getUserProfile(userId) {
  return use_mcp_tool({
    server_name: "database",
    tool_name: "query",
    arguments: {
      query: "SELECT id, name, email, profile_picture FROM users WHERE id = ?",
      params: [userId]
    }
  });
}
```

#### Pagination
Implémentez la pagination pour les grandes collections de données.

```javascript
// Fonction de récupération paginée
async function fetchAllItems(fetchFunction, pageSize = 100) {
  let page = 1;
  let allItems = [];
  let hasMoreItems = true;
  
  while (hasMoreItems) {
    const response = await fetchFunction(page, pageSize);
    
    if (response.items.length === 0) {
      hasMoreItems = false;
    } else {
      allItems = [...allItems, ...response.items];
      page++;
    }
  }
  
  return allItems;
}

// Utilisation
async function getAllIssues(owner, repo) {
  return fetchAllItems(async (page, pageSize) => {
    return use_mcp_tool({
      server_name: "github",
      tool_name: "list_issues",
      arguments: {
        owner,
        repo,
        page,
        per_page: pageSize
      }
    });
  });
}
```

#### Compression des données
Utilisez la compression pour réduire la taille des données transmises.

```javascript
// Exemple conceptuel de compression de données
async function fetchLargeDataCompressed() {
  const response = await fetch("https://api.example.com/large-data", {
    headers: {
      "Accept-Encoding": "gzip, deflate, br"
    }
  });
  
  // Décompression automatique par fetch
  return response.json();
}
```

### 3.3. Surveillance des performances

#### Métriques clés
Identifiez et surveillez les métriques de performance clés.

```javascript
// Système de mesure de performance
const performanceMetrics = {
  timings: {},
  counts: {},
  
  startTiming(operation) {
    this.timings[operation] = {
      start: Date.now(),
      end: null,
      duration: null
    };
  },
  
  endTiming(operation) {
    if (!this.timings[operation]) return;
    
    this.timings[operation].end = Date.now();
    this.timings[operation].duration = this.timings[operation].end - this.timings[operation].start;
    
    // Enregistrement de la métrique
    this.recordMetric(`timing.${operation}`, this.timings[operation].duration);
  },
  
  incrementCount(counter) {
    this.counts[counter] = (this.counts[counter] \| 0) + 1;
    
    // Enregistrement de la métrique
    this.recordMetric(`count.${counter}`, this.counts[counter]);
  },
  
  recordMetric(name, value) {
    // Envoi à un système de monitoring
    console.log(`METRIC: ${name} = ${value}`);
  }
};

// Utilisation
async function fetchRepositoryData(owner, repo) {
  performanceMetrics.startTiming("github_repo_fetch");
  performanceMetrics.incrementCount("github_api_calls");
  
  try {
    const result = await use_mcp_tool({
      server_name: "github",
      tool_name: "get_repository",
      arguments: { owner, repo }
    });
    
    return result;
  } finally {
    performanceMetrics.endTiming("github_repo_fetch");
  }
}
```

#### Alertes de dégradation
Mettez en place des alertes en cas de dégradation des performances.

```javascript
// Système d'alerte sur les performances
function checkPerformanceThreshold(operation, duration, threshold) {
  if (duration > threshold) {
    // Alerte de dépassement de seuil
    sendAlert(`Performance dégradée: ${operation} a pris ${duration}ms (seuil: ${threshold}ms)`);
  }
}

// Utilisation avec le système de métriques
const originalEndTiming = performanceMetrics.endTiming;
performanceMetrics.endTiming = function(operation) {
  originalEndTiming.call(this, operation);
  
  const duration = this.timings[operation].duration;
  
  // Seuils spécifiques par opération
  const thresholds = {
    "github_repo_fetch": 1000, // 1 seconde
    "file_processing": 5000,   // 5 secondes
    // Autres opérations...
  };
  
  if (thresholds[operation]) {
    checkPerformanceThreshold(operation, duration, thresholds[operation]);
  }
};
```

## 4. Gestion des erreurs

### 4.1. Stratégies de gestion d'erreurs

#### Détection et classification
Détectez et classifiez les erreurs pour un traitement approprié.

```javascript
// Classification des erreurs
class ApiError extends Error {
  constructor(message, statusCode, isRetryable = false) {
    super(message);
    this.name = "ApiError";
    this.statusCode = statusCode;
    this.isRetryable = isRetryable;
  }
}

// Fonction de détection d'erreur
function detectApiError(response) {
  if (response.status >= 200 && response.status < 300) {
    return null;
  }
  
  let isRetryable = false;
  
  // Les erreurs 5xx sont généralement retentables
  if (response.status >= 500) {
    isRetryable = true;
  }
  
  // Les erreurs 429 (rate limit) sont retentables après un délai
  if (response.status === 429) {
    isRetryable = true;
  }
  
  return new ApiError(
    `API error: ${response.statusText}`,
    response.status,
    isRetryable
  );
}
```

#### Tentatives avec backoff exponentiel
Implémentez une stratégie de tentatives avec backoff exponentiel pour les erreurs transitoires.

```javascript
// Fonction de tentative avec backoff exponentiel
async function retryWithExponentialBackoff(operation, maxRetries = 3, initialDelayMs = 1000) {
  let retries = 0;
  
  while (true) {
    try {
      return await operation();
    } catch (error) {
      // Vérification si l'erreur est retentable
      const isRetryable = error.isRetryable \| 
                          error.statusCode >= 500 \| 
                          error.statusCode === 429;
      
      if (!isRetryable \| retries >= maxRetries) {
        throw error;
      }
      
      // Calcul du délai avec jitter pour éviter les tempêtes de requêtes
      const delayMs = initialDelayMs * Math.pow(2, retries) * (0.5 + Math.random() * 0.5);
      
      console.log(`Tentative ${retries + 1}/${maxRetries} échouée. Nouvelle tentative dans ${delayMs}ms`);
      
      // Attente avant nouvelle tentative
      await new Promise(resolve => setTimeout(resolve, delayMs));
      
      retries++;
    }
  }
}

// Utilisation
async function fetchRepositoryWithRetry(owner, repo) {
  return retryWithExponentialBackoff(async () => {
    const response = await fetch(`https://api.github.com/repos/${owner}/${repo}`);
    
    const error = detectApiError(response);
    if (error) throw error;
    
    return response.json();
  });
}
```

#### Circuit breaker
Implémentez un pattern de disjoncteur pour éviter de surcharger des services défaillants.

```javascript
// Implémentation d'un circuit breaker
class CircuitBreaker {
  constructor(operation, options = {}) {
    this.operation = operation;
    this.state = "CLOSED"; // CLOSED, OPEN, HALF_OPEN
    this.failureCount = 0;
    this.lastFailureTime = null;
    this.options = {
      failureThreshold: options.failureThreshold \| 5,
      resetTimeout: options.resetTimeout \| 30000, // 30 secondes
      halfOpenSuccessThreshold: options.halfOpenSuccessThreshold \| 2
    };
    this.successCount = 0;
  }
  
  async execute(...args) {
    if (this.state === "OPEN") {
      // Vérification si le temps de reset est écoulé
      if (Date.now() - this.lastFailureTime >= this.options.resetTimeout) {
        this.state = "HALF_OPEN";
        this.successCount = 0;
      } else {
        throw new Error("Circuit ouvert - Service indisponible");
      }
    }
    
    try {
      const result = await this.operation(...args);
      
      // Gestion du succès
      if (this.state === "HALF_OPEN") {
        this.successCount++;
        
        if (this.successCount >= this.options.halfOpenSuccessThreshold) {
          this.state = "CLOSED";
          this.failureCount = 0;
        }
      } else if (this.state === "CLOSED") {
        // Réinitialisation du compteur d'échecs en cas de succès
        this.failureCount = 0;
      }
      
      return result;
    } catch (error) {
      // Gestion de l'échec
      this.lastFailureTime = Date.now();
      this.failureCount++;
      
      if (this.state === "CLOSED" && this.failureCount >= this.options.failureThreshold) {
        this.state = "OPEN";
      } else if (this.state === "HALF_OPEN") {
        this.state = "OPEN";
      }
      
      throw error;
    }
  }
}

// Utilisation
const githubApiBreaker = new CircuitBreaker(
  async (owner, repo) => {
    const response = await fetch(`https://api.github.com/repos/${owner}/${repo}`);
    
    if (!response.ok) {
      throw new Error(`GitHub API error: ${response.status}`);
    }
    
    return response.json();
  },
  { failureThreshold: 3, resetTimeout: 60000 }
);

async function getRepositorySafely(owner, repo) {
  try {
    return await githubApiBreaker.execute(owner, repo);
  } catch (error) {
    if (error.message.includes("Circuit ouvert")) {
      // Fallback en cas de circuit ouvert
      return getFallbackRepositoryData(owner, repo);
    }
    throw error;
  }
}
```

### 4.2. Journalisation et monitoring

#### Journalisation structurée
Utilisez un format de journalisation structuré pour faciliter l'analyse.

```javascript
// Système de journalisation structurée
const logger = {
  levels: {
    DEBUG: 0,
    INFO: 1,
    WARN: 2,
    ERROR: 3,
    FATAL: 4
  },
  
  currentLevel: 1, // INFO par défaut
  
  log(level, message, context = {}) {
    if (this.levels[level] < this.currentLevel) return;
    
    const logEntry = {
      timestamp: new Date().toISOString(),
      level,
      message,
      ...context
    };
    
    // Sortie formatée
    console.log(JSON.stringify(logEntry));
  },
  
  debug(message, context) {
    this.log("DEBUG", message, context);
  },
  
  info(message, context) {
    this.log("INFO", message, context);
  },
  
  warn(message, context) {
    this.log("WARN", message, context);
  },
  
  error(message, context) {
    this.log("ERROR", message, context);
  },
  
  fatal(message, context) {
    this.log("FATAL", message, context);
  }
};

// Utilisation
async function createIssue(owner, repo, title, body) {
  logger.info("Création d'une issue", { owner, repo, title });
  
  try {
    const result = await use_mcp_tool({
      server_name: "github",
      tool_name: "create_issue",
      arguments: { owner, repo, title, body }
    });
    
    logger.info("Issue créée avec succès", { issueNumber: result.number });
    
    return result;
  } catch (error) {
    logger.error("Échec de création de l'issue", { 
      owner, 
      repo, 
      title,
      error: error.message,
      stack: error.stack
    });
    
    throw error;
  }
}
```

#### Corrélation des événements
Utilisez des identifiants de corrélation pour suivre les flux d'exécution.

```javascript
// Système de corrélation d'événements
const correlationContext = {
  currentId: null,
  
  withNewCorrelation(callback) {
    const previousId = this.currentId;
    this.currentId = generateUniqueId();
    
    try {
      return callback(this.currentId);
    } finally {
      this.currentId = previousId;
    }
  },
  
  getCurrentId() {
    return this.currentId;
  }
};

// Génération d'ID unique
function generateUniqueId() {
  return `${Date.now()}-${Math.random().toString(36).substring(2, 15)}`;
}

// Extension du logger pour inclure l'ID de corrélation
const originalLog = logger.log;
logger.log = function(level, message, context = {}) {
  const correlationId = correlationContext.getCurrentId();
  
  if (correlationId) {
    context.correlationId = correlationId;
  }
  
  originalLog.call(this, level, message, context);
};

// Utilisation
async function processWebhook(payload) {
  return correlationContext.withNewCorrelation(async (correlationId) => {
    logger.info("Réception d'un webhook", { payloadType: payload.type });
    
    // Traitement du webhook
    await processWebhookPayload(payload);
    
    logger.info("Traitement du webhook terminé");
  });
}
```

#### Alertes et notifications
Configurez des alertes pour les erreurs critiques.

```javascript
// Système d'alerte
const alertSystem = {
  async sendAlert(level, message, details = {}) {
    // Formatage de l'alerte
    const alert = {
      level,
      message,
      timestamp: new Date().toISOString(),
      details
    };
    
    // Envoi de l'alerte (exemple avec Slack)
    await sendSlackNotification(
      `[${level}] ${message}`,
      JSON.stringify(details, null, 2)
    );
    
    // Journalisation de l'alerte
    logger.log(level, `ALERT: ${message}`, details);
  }
};

// Extension du logger pour les alertes automatiques
const originalError = logger.error;
logger.error = function(message, context = {}) {
  originalError.call(this, message, context);
  
  // Envoi d'une alerte pour les erreurs
  alertSystem.sendAlert("ERROR", message, context);
};

const originalFatal = logger.fatal;
logger.fatal = function(message, context = {}) {
  originalFatal.call(this, message, context);
  
  // Envoi d'une alerte pour les erreurs fatales
  alertSystem.sendAlert("FATAL", message, context);
};
```
## 5. Tests et validation

### 5.1. Stratégies de test

#### Tests unitaires
Testez chaque composant d'intégration de manière isolée.

```javascript
// Exemple de test unitaire avec Jest
describe("GitHub Issue Creator", () => {
  // Mock de l'outil MCP
  const mockMcpTool = jest.fn();
  
  beforeEach(() => {
    // Réinitialisation du mock
    mockMcpTool.mockReset();
    
    // Injection du mock
    global.use_mcp_tool = mockMcpTool;
  });
  
  test("createIssue devrait appeler l'API GitHub avec les bons paramètres", async () => {
    // Configuration du mock
    mockMcpTool.mockResolvedValue({ id: 123, number: 42 });
    
    // Fonction à tester
    async function createIssue(owner, repo, title, body) {
      return use_mcp_tool({
        server_name: "github",
        tool_name: "create_issue",
        arguments: { owner, repo, title, body }
      });
    }
    
    // Exécution de la fonction
    const result = await createIssue("testowner", "testrepo", "Test Issue", "Description");
    
    // Vérifications
    expect(mockMcpTool).toHaveBeenCalledWith({
      server_name: "github",
      tool_name: "create_issue",
      arguments: {
        owner: "testowner",
        repo: "testrepo",
        title: "Test Issue",
        body: "Description"
      }
    });
    
    expect(result).toEqual({ id: 123, number: 42 });
  });
});
```

#### Tests d'intégration
Testez l'interaction entre les différents composants.

```javascript
// Exemple de test d'intégration
describe("Workflow d'issue avec notification", () => {
  // Mocks
  const mockGithub = jest.fn();
  const mockSlack = jest.fn();
  
  beforeEach(() => {
    // Configuration des mocks
    global.use_mcp_tool = jest.fn((params) => {
      if (params.server_name === "github") {
        return mockGithub(params);
      } else if (params.server_name === "slack") {
        return mockSlack(params);
      }
    });
    
    mockGithub.mockReset();
    mockSlack.mockReset();
  });
  
  test("La création d'une issue devrait déclencher une notification Slack", async () => {
    // Configuration des mocks
    mockGithub.mockResolvedValue({ id: 123, number: 42, html_url: "https://github.com/test/test/issues/42" });
    mockSlack.mockResolvedValue({ ok: true });
    
    // Fonction de workflow à tester
    async function createIssueWithNotification(owner, repo, title, body) {
      // Création de l'issue
      const issue = await use_mcp_tool({
        server_name: "github",
        tool_name: "create_issue",
        arguments: { owner, repo, title, body }
      });
      
      // Envoi de la notification
      await use_mcp_tool({
        server_name: "slack",
        tool_name: "send_message",
        arguments: {
          channel: "#github-notifications",
          text: `Nouvelle issue créée: <${issue.html_url}|#${issue.number} ${title}>`
        }
      });
      
      return issue;
    }
    
    // Exécution du workflow
    await createIssueWithNotification("testowner", "testrepo", "Test Issue", "Description");
    
    // Vérifications
    expect(mockGithub).toHaveBeenCalled();
    expect(mockSlack).toHaveBeenCalledWith({
      server_name: "slack",
      tool_name: "send_message",
      arguments: {
        channel: "#github-notifications",
        text: "Nouvelle issue créée: <https://github.com/test/test/issues/42|#42 Test Issue>"
      }
    });
  });
});
```

#### Tests de bout en bout
Testez le flux complet dans un environnement similaire à la production.

```javascript
// Exemple conceptuel de test de bout en bout
describe("Workflow complet de gestion d'issues", () => {
  // Utilisation de vrais services dans un environnement de test
  beforeAll(async () => {
    // Création d'un dépôt de test
    await setupTestRepository();
  });
  
  afterAll(async () => {
    // Nettoyage
    await cleanupTestRepository();
  });
  
  test("Devrait créer une issue, ajouter un commentaire et la fermer", async () => {
    // Création de l'issue
    const issue = await createIssue(
      "testorg",
      "testrepo",
      "Test E2E",
      "Description du test de bout en bout"
    );
    
    expect(issue.number).toBeDefined();
    
    // Ajout d'un commentaire
    const comment = await addIssueComment(
      "testorg",
      "testrepo",
      issue.number,
      "Commentaire de test"
    );
    
    expect(comment.id).toBeDefined();
    
    // Fermeture de l'issue
    const closedIssue = await closeIssue(
      "testorg",
      "testrepo",
      issue.number
    );
    
    expect(closedIssue.state).toBe("closed");
  });
});
```

### 5.2. Mocking et simulation

#### Mocks pour les services externes
Créez des mocks pour simuler les services externes pendant les tests.

```javascript
// Système de mock pour les services externes
class MockService {
  constructor(serviceName) {
    this.serviceName = serviceName;
    this.endpoints = {};
  }
  
  mockEndpoint(endpoint, responseOrFunction) {
    this.endpoints[endpoint] = responseOrFunction;
  }
  
  async call(endpoint, params) {
    if (!this.endpoints[endpoint]) {
      throw new Error(`Endpoint non mocké: ${endpoint}`);
    }
    
    const response = this.endpoints[endpoint];
    
    if (typeof response === "function") {
      return response(params);
    }
    
    return response;
  }
}

// Utilisation
const mockGithub = new MockService("github");

// Mock d'un endpoint spécifique
mockGithub.mockEndpoint("create_issue", (params) => {
  return {
    id: 12345,
    number: 42,
    title: params.arguments.title,
    body: params.arguments.body,
    html_url: `https://github.com/${params.arguments.owner}/${params.arguments.repo}/issues/42`
  };
});

// Injection du mock
global.use_mcp_tool = async (params) => {
  if (params.server_name === "github") {
    return mockGithub.call(params.tool_name, params);
  }
  
  // Autres services...
};

// Test avec le mock
async function testWithMock() {
  const issue = await use_mcp_tool({
    server_name: "github",
    tool_name: "create_issue",
    arguments: {
      owner: "testowner",
      repo: "testrepo",
      title: "Issue de test",
      body: "Description de test"
    }
  });
  
  console.log(`Issue créée: #${issue.number}`);
}
```

#### Environnements de test
Créez des environnements de test isolés pour éviter d'affecter les systèmes de production.

```javascript
// Configuration d'environnement de test
function setupTestEnvironment() {
  // Détection de l'environnement
  const isTestEnv = process.env.NODE_ENV === "test";
  
  // Configuration spécifique pour les tests
  if (isTestEnv) {
    // Utilisation de services de test
    config.githubApiUrl = "https://api.github.test";
    config.slackWebhookUrl = "https://hooks.slack.test/services/test";
    
    // Limitation des opérations dangereuses
    config.allowDangerousOperations = false;
  }
  
  return {
    isTestEnv,
    tearDown: () => {
      // Nettoyage des ressources de test
      if (isTestEnv) {
        // Suppression des données de test
      }
    }
  };
}
```

### 5.3. Validation et conformité

#### Validation des entrées et sorties
Validez systématiquement les entrées et sorties des intégrations.

```javascript
// Système de validation avec Joi
const Joi = require("joi");

// Schémas de validation
const schemas = {
  createIssue: {
    input: Joi.object({
      owner: Joi.string().required(),
      repo: Joi.string().required(),
      title: Joi.string().min(3).max(255).required(),
      body: Joi.string().allow(""),
      labels: Joi.array().items(Joi.string())
    }),
    output: Joi.object({
      id: Joi.number().required(),
      number: Joi.number().required(),
      title: Joi.string().required(),
      html_url: Joi.string().uri().required()
    })
  }
};

// Fonction de validation
function validate(data, schema) {
  const { error, value } = schema.validate(data, { abortEarly: false });
  
  if (error) {
    throw new Error(`Validation error: ${error.message}`);
  }
  
  return value;
}

// Utilisation
async function createIssue(params) {
  // Validation des entrées
  const validParams = validate(params, schemas.createIssue.input);
  
  // Appel à l'API
  const result = await use_mcp_tool({
    server_name: "github",
    tool_name: "create_issue",
    arguments: validParams
  });
  
  // Validation des sorties
  return validate(result, schemas.createIssue.output);
}
```

#### Conformité aux standards
Assurez-vous que vos intégrations respectent les standards et bonnes pratiques.

```javascript
// Vérification de conformité
function checkCompliance(integration) {
  const issues = [];
  
  // Vérification de la présence de journalisation
  if (!integration.hasLogging) {
    issues.push("La journalisation est absente ou insuffisante");
  }
  
  // Vérification de la gestion d'erreurs
  if (!integration.hasErrorHandling) {
    issues.push("La gestion d'erreurs est absente ou insuffisante");
  }
  
  // Vérification de la validation des entrées
  if (!integration.hasInputValidation) {
    issues.push("La validation des entrées est absente ou insuffisante");
  }
  
  // Vérification de la sécurité
  if (integration.usesHardcodedSecrets) {
    issues.push("Des secrets sont codés en dur dans l'intégration");
  }
  
  return {
    compliant: issues.length === 0,
    issues
  };
}
```

## 6. Maintenance et évolution

### 6.1. Versionnement

#### Gestion sémantique des versions
Utilisez le versionnement sémantique pour vos intégrations.

```javascript
// Exemple de gestion de version
const integration = {
  name: "github-integration",
  version: "1.2.3", // Major.Minor.Patch
  
  // Vérification de compatibilité
  isCompatibleWith: function(requiredVersion) {
    const current = this.version.split(".").map(Number);
    const required = requiredVersion.split(".").map(Number);
    
    // Vérification de la version majeure
    if (current[0] !== required[0]) {
      return false;
    }
    
    // Vérification de la version mineure
    if (current[1] < required[1]) {
      return false;
    }
    
    // Si même version mineure, vérification du patch
    if (current[1] === required[1] && current[2] < required[2]) {
      return false;
    }
    
    return true;
  }
};

// Utilisation
function checkIntegrationCompatibility() {
  const requiredVersion = "1.2.0";
  
  if (!integration.isCompatibleWith(requiredVersion)) {
    console.warn(`L'intégration ${integration.name} v${integration.version} n'est pas compatible avec la version requise ${requiredVersion}`);
  }
}
```

#### Gestion des dépendances
Gérez efficacement les dépendances de vos intégrations.

```javascript
// Vérification des dépendances
async function checkDependencies() {
  const dependencies = [
    { name: "github-api", minVersion: "1.2.0" },
    { name: "slack-sdk", minVersion: "2.0.0" }
  ];
  
  const issues = [];
  
  for (const dep of dependencies) {
    try {
      // Chargement dynamique de la dépendance
      const module = require(dep.name);
      
      // Vérification de la version
      if (!isVersionCompatible(module.version, dep.minVersion)) {
        issues.push(`La dépendance ${dep.name} est en version ${module.version}, mais la version minimale requise est ${dep.minVersion}`);
      }
    } catch (error) {
      issues.push(`La dépendance ${dep.name} est manquante: ${error.message}`);
    }
  }
  
  return {
    valid: issues.length === 0,
    issues
  };
}

// Vérification de compatibilité de version
function isVersionCompatible(actual, required) {
  const actualParts = actual.split(".").map(Number);
  const requiredParts = required.split(".").map(Number);
  
  for (let i = 0; i < requiredParts.length; i++) {
    if (actualParts[i] < requiredParts[i]) {
      return false;
    } else if (actualParts[i] > requiredParts[i]) {
      return true;
    }
  }
  
  return true;
}
```

### 6.2. Mise à jour et migration

#### Stratégies de mise à jour
Planifiez et exécutez les mises à jour de manière contrôlée.

```javascript
// Système de mise à jour
const updateSystem = {
  async checkForUpdates(currentVersion) {
    // Vérification des mises à jour disponibles
    const latestVersion = await fetchLatestVersion();
    
    if (isVersionNewer(latestVersion, currentVersion)) {
      return {
        available: true,
        version: latestVersion,
        releaseNotes: await fetchReleaseNotes(latestVersion)
      };
    }
    
    return { available: false };
  },
  
  async performUpdate(targetVersion) {
    // Sauvegarde de l'état actuel
    await backupCurrentState();
    
    try {
      // Téléchargement et installation de la mise à jour
      await downloadUpdate(targetVersion);
      await installUpdate(targetVersion);
      
      // Vérification post-mise à jour
      const verificationResult = await verifyUpdate();
      
      if (!verificationResult.success) {
        // Restauration en cas d'échec
        await rollbackUpdate();
        throw new Error(`Échec de la mise à jour: ${verificationResult.error}`);
      }
      
      return { success: true };
    } catch (error) {
      // Restauration en cas d'erreur
      await rollbackUpdate();
      throw error;
    }
  }
};

// Vérification si une version est plus récente
function isVersionNewer(version1, version2) {
  const v1Parts = version1.split(".").map(Number);
  const v2Parts = version2.split(".").map(Number);
  
  for (let i = 0; i < v1Parts.length; i++) {
    if (v1Parts[i] > v2Parts[i]) {
      return true;
    } else if (v1Parts[i] < v2Parts[i]) {
      return false;
    }
  }
  
  return false;
}
```

#### Scripts de migration
Créez des scripts de migration pour faciliter les transitions entre versions.

```javascript
// Système de migration
const migrationSystem = {
  migrations: [
    {
      version: "1.1.0",
      description: "Migration vers le nouveau format de configuration",
      execute: async () => {
        // Lecture de l'ancienne configuration
        const oldConfig = await readConfig();
        
        // Transformation vers le nouveau format
        const newConfig = transformConfig(oldConfig);
        
        // Sauvegarde de la nouvelle configuration
        await writeConfig(newConfig);
      }
    },
    {
      version: "1.2.0",
      description: "Mise à jour du schéma de base de données",
      execute: async () => {
        // Exécution des scripts SQL de migration
        await executeSqlScript("migrations/1.2.0_update_schema.sql");
      }
    }
  ],
  
  async migrateToVersion(targetVersion) {
    // Lecture de la version actuelle
    const currentVersion = await getCurrentVersion();
    
    // Filtrage des migrations nécessaires
    const migrationsToRun = this.migrations.filter(migration => 
      isVersionNewer(migration.version, currentVersion) && 
      !isVersionNewer(migration.version, targetVersion)
    );
    
    // Tri des migrations par version
    migrationsToRun.sort((a, b) => {
      return isVersionNewer(a.version, b.version) ? 1 : -1;
    });
    
    // Exécution des migrations
    for (const migration of migrationsToRun) {
      console.log(`Exécution de la migration vers ${migration.version}: ${migration.description}`);
      
      try {
        await migration.execute();
        
        // Mise à jour de la version après chaque migration réussie
        await updateCurrentVersion(migration.version);
      } catch (error) {
        console.error(`Échec de la migration vers ${migration.version}: ${error.message}`);
        throw error;
      }
    }
    
    console.log(`Migration vers la version ${targetVersion} terminée avec succès`);
  }
};
```

### 6.3. Surveillance et maintenance

#### Surveillance proactive
Mettez en place une surveillance proactive de vos intégrations.

```javascript
// Système de surveillance
const monitoringSystem = {
  checks: [
    {
      name: "api_health",
      description: "Vérification de la santé de l'API",
      interval: 60000, // 1 minute
      execute: async () => {
        try {
          const response = await fetch("https://api.example.com/health");
          
          if (!response.ok) {
            throw new Error(`Statut HTTP: ${response.status}`);
          }
          
          const data = await response.json();
          
          return {
            status: "ok",
            details: data
          };
        } catch (error) {
          return {
            status: "error",
            error: error.message
          };
        }
      }
    },
    {
      name: "database_connection",
      description: "Vérification de la connexion à la base de données",
      interval: 300000, // 5 minutes
      execute: async () => {
        try {
          // Vérification de la connexion
          await database.ping();
          
          return {
            status: "ok"
          };
        } catch (error) {
          return {
            status: "error",
            error: error.message
          };
        }
      }
    }
  ],
  
  async startMonitoring() {
    for (const check of this.checks) {
      // Exécution initiale
      const result = await check.execute();
      this.handleCheckResult(check, result);
      
      // Planification des exécutions périodiques
      setInterval(async () => {
        const result = await check.execute();
        this.handleCheckResult(check, result);
      }, check.interval);
    }
  },
  
  handleCheckResult(check, result) {
    // Journalisation du résultat
    logger.info(`Résultat de la vérification ${check.name}`, {
      check: check.name,
      status: result.status,
      details: result
    });
    
    // Alerte en cas d'erreur
    if (result.status === "error") {
      alertSystem.sendAlert(
        "WARN",
        `Échec de la vérification ${check.name}`,
        {
          check: check.name,
          error: result.error
        }
      );
    }
  }
};
```

#### Maintenance préventive
Effectuez une maintenance préventive régulière de vos intégrations.

```javascript
// Tâches de maintenance
const maintenanceTasks = [
  {
    name: "clean_old_logs",
    description: "Nettoyage des anciens journaux",
    schedule: "0 0 * * *", // Tous les jours à minuit
    execute: async () => {
      const logRetentionDays = 30;
      const cutoffDate = new Date();
      cutoffDate.setDate(cutoffDate.getDate() - logRetentionDays);
      
      // Suppression des anciens journaux
      await deleteLogsOlderThan(cutoffDate);
    }
  },
  {
    name: "refresh_cache",
    description: "Rafraîchissement du cache",
    schedule: "0 */4 * * *", // Toutes les 4 heures
    execute: async () => {
      // Invalidation du cache
      await cache.invalidateAll();
      
      // Préchauffage du cache
      await warmupCache();
    }
  }
];

// Planification des tâches de maintenance
function scheduleMaintenance() {
  for (const task of maintenanceTasks) {
    // Utilisation d'une bibliothèque de planification comme node-cron
    cron.schedule(task.schedule, async () => {
      logger.info(`Exécution de la tâche de maintenance: ${task.name}`);
      
      try {
        await task.execute();
        logger.info(`Tâche de maintenance ${task.name} terminée avec succès`);
      } catch (error) {
        logger.error(`Échec de la tâche de maintenance ${task.name}`, {
          error: error.message,
          stack: error.stack
        });
      }
    });
  }
}
```

## 7. Documentation

### 7.1. Documentation technique

#### Documentation du code
Documentez votre code de manière claire et complète.

```javascript
/**
 * Crée une nouvelle issue dans un dépôt GitHub.
 * 
 * @param {Object} options - Options pour la création de l'issue
 * @param {string} options.owner - Propriétaire du dépôt
 * @param {string} options.repo - Nom du dépôt
 * @param {string} options.title - Titre de l'issue
 * @param {string} options.body - Corps de l'issue
 * @param {string[]} [options.labels] - Labels à appliquer à l'issue
 * @param {string[]} [options.assignees] - Utilisateurs à assigner à l'issue
 * 
 * @returns {Promise<Object>} L'issue créée
 * @throws {ApiError} En cas d'erreur lors de l'appel à l'API GitHub
 * @throws {ValidationError} En cas de données invalides
 * 
 * @example
 * // Création d'une issue simple
 * const issue = await createIssue({
 *   owner: "octocat",
 *   repo: "hello-world",
 *   title: "Bug: Application crash on startup",
 *   body: "The application crashes when started on Windows 11."
 * });
 * 
 * @example
 * // Création d'une issue avec labels et assignés
 * const issue = await createIssue({
 *   owner: "octocat",
 *   repo: "hello-world",
 *   title: "Feature: Add dark mode",
 *   body: "Add support for dark mode in the application.",
 *   labels: ["enhancement", "ui"],
 *   assignees: ["developer1", "designer2"]
 * });
 */
async function createIssue(options) {
  // Validation des options
  validateIssueOptions(options);
  
  // Création de l'issue
  try {
    return await use_mcp_tool({
      server_name: "github",
      tool_name: "create_issue",
      arguments: options
    });
  } catch (error) {
    // Transformation de l'erreur
    throw new ApiError(`Échec de création de l'issue: ${error.message}`, error);
  }
}
```

#### Documentation des API
Documentez les API de vos intégrations.

```javascript
/**
 * @api {post} /api/integrations/github/issues Créer une issue GitHub
 * @apiName CreateGitHubIssue
 * @apiGroup GitHub Integration
 * @apiVersion 1.0.0
 * 
 * @apiDescription Crée une nouvelle issue dans un dépôt GitHub.
 * 
 * @apiParam {String} owner Propriétaire du dépôt
 * @apiParam {String} repo Nom du dépôt
 * @apiParam {String} title Titre de l'issue
 * @apiParam {String} body Corps de l'issue
 * @apiParam {String[]} [labels] Labels à appliquer à l'issue
 * @apiParam {String[]} [assignees] Utilisateurs à assigner à l'issue
 * 
 * @apiSuccess {Number} id ID de l'issue
 * @apiSuccess {Number} number Numéro de l'issue
 * @apiSuccess {String} title Titre de l'issue
 * @apiSuccess {String} body Corps de l'issue
 * @apiSuccess {String} html_url URL de l'issue
 * @apiSuccess {String} state État de l'issue (open, closed)
 * 
 * @apiSuccessExample {json} Réponse en cas de succès:
 *     HTTP/1.1 201 Created
 *     {
 *       "id": 1234567890,
 *       "number": 42,
 *       "title": "Bug: Application crash on startup",
 *       "body": "The application crashes when started on Windows 11.",
 *       "html_url": "https://github.com/octocat/hello-world/issues/42",
 *       "state": "open"
 *     }
 * 
 * @apiError BadRequest Les paramètres fournis sont invalides
 * @apiError Unauthorized Authentification requise
 * @apiError Forbidden Accès refusé
 * @apiError NotFound Dépôt non trouvé
 * 
 * @apiErrorExample {json} Erreur - Paramètres invalides:
 *     HTTP/1.1 400 Bad Request
 *     {
 *       "error": "ValidationError",
 *       "message": "Le titre de l'issue est requis"
 *     }
 */
```

### 7.2. Documentation utilisateur

#### Guides d'utilisation
Créez des guides d'utilisation clairs et détaillés.

```markdown
# Guide d'utilisation de l'intégration GitHub

## Introduction

Ce guide explique comment utiliser l'intégration GitHub pour automatiser la gestion des issues et des pull requests.

## Prérequis

- Un compte GitHub avec accès au dépôt cible
- Un token d'accès personnel GitHub avec les permissions appropriées
- Node.js v14 ou supérieur

## Installation

```bash
npm install @company/github-integration
```

## Configuration

Créez un fichier de configuration `github-config.json` :

```json
{
  "token": "votre-token-github",
  "defaultOwner": "votre-organisation",
  "defaultRepo": "votre-depot"
}
```

## Exemples d'utilisation

### Création d'une issue

```javascript
const { createIssue } = require('@company/github-integration');

async function main() {
  const issue = await createIssue({
    title: "Bug: Application crash on startup",
    body: "The application crashes when started on Windows 11."
  });
  
  console.log(`Issue créée: ${issue.html_url}`);
}

main().catch(console.error);
```

### Recherche d'issues

```javascript
const { searchIssues } = require('@company/github-integration');

async function main() {
  const issues = await searchIssues({
    state: "open",
    labels: ["bug", "high-priority"]
  });
  
  console.log(`${issues.length} issues trouvées`);
  
  for (const issue of issues) {
    console.log(`#${issue.number}: ${issue.title}`);
  }
}

main().catch(console.error);
```
```

#### Tutoriels et exemples
Fournissez des tutoriels et des exemples concrets.

```markdown
# Tutoriel : Automatisation du triage des issues GitHub

Ce tutoriel vous guide à travers la création d'un système automatisé de triage des issues GitHub.

## Objectif

Créer un workflow qui :
1. Surveille les nouvelles issues
2. Analyse leur contenu
3. Ajoute automatiquement des labels appropriés
4. Assigne les issues aux membres de l'équipe selon leur expertise

## Étape 1 : Configuration de l'environnement

Commencez par installer les dépendances nécessaires :

```bash
npm install @company/github-integration natural
```

## Étape 2 : Création du script de triage

Créez un fichier `issue-triage.js` :

```javascript
const { listenForNewIssues, addLabels, assignIssue } = require('@company/github-integration');
const natural = require('natural');

// Configuration des catégories
const categories = {
  bug: ['crash', 'error', 'fail', 'broken', 'not working'],
  enhancement: ['improve', 'enhancement', 'feature', 'add', 'new'],
  documentation: ['doc', 'documentation', 'explain', 'unclear']
};

// Configuration des experts
const experts = {
  bug: ['debugger1', 'debugger2'],
  enhancement: ['developer1', 'developer
2'],
  documentation: ['writer1', 'writer2']
};

// Fonction de triage
async function triageIssue(issue) {
  // Analyse du contenu
  const content = `${issue.title} ${issue.body}`.toLowerCase();
  
  // Détection des catégories
  const detectedLabels = [];
  
  for (const [category, keywords] of Object.entries(categories)) {
    for (const keyword of keywords) {
      if (content.includes(keyword)) {
        detectedLabels.push(category);
        break;
      }
    }
  }
  
  // Ajout des labels
  if (detectedLabels.length > 0) {
    await addLabels(issue.owner, issue.repo, issue.number, detectedLabels);
    console.log(`Labels ajoutés à l'issue #${issue.number}: ${detectedLabels.join(', ')}`);
  }
  
  // Assignation à un expert
  for (const label of detectedLabels) {
    if (experts[label]) {
      // Sélection aléatoire d'un expert dans la catégorie
      const expert = experts[label][Math.floor(Math.random() * experts[label].length)];
      
      await assignIssue(issue.owner, issue.repo, issue.number, expert);
      console.log(`Issue #${issue.number} assignée à ${expert}`);
      break;
    }
  }
}

// Démarrage de l'écoute des nouvelles issues
listenForNewIssues('votre-organisation', 'votre-depot', triageIssue);
```

## Étape 3 : Exécution du script

Lancez le script avec Node.js :

```bash
node issue-triage.js
```

## Étape 4 : Configuration comme service

Pour exécuter le script en continu, configurez-le comme un service système.

### Sur Linux (avec systemd)

Créez un fichier `/etc/systemd/system/issue-triage.service` :

```ini
[Unit]
Description=GitHub Issue Triage Service
After=network.target

[Service]
ExecStart=/usr/bin/node /path/to/issue-triage.js
WorkingDirectory=/path/to
Restart=always
User=votre-utilisateur
Environment=NODE_ENV=production

[Install]
WantedBy=multi-user.target
```

Activez et démarrez le service :

```bash
sudo systemctl enable issue-triage
sudo systemctl start issue-triage
```

## Conclusion

Vous avez maintenant un système automatisé de triage des issues GitHub. Ce système peut être étendu avec des algorithmes plus sophistiqués d'analyse de texte pour améliorer la précision de la catégorisation.
```

## 8. Modèles d'intégration avancés

### 8.1. Intégration basée sur les événements

#### Webhooks et callbacks
Utilisez des webhooks pour réagir aux événements externes.

```javascript
// Gestionnaire de webhook GitHub
const express = require('express');
const crypto = require('crypto');
const app = express();

// Middleware pour parser le JSON
app.use(express.json());

// Vérification de la signature GitHub
function verifyGitHubSignature(req, res, next) {
  const signature = req.headers['x-hub-signature-256'];
  
  if (!signature) {
    return res.status(401).send('Signature manquante');
  }
  
  const secret = process.env.GITHUB_WEBHOOK_SECRET;
  const payload = JSON.stringify(req.body);
  const hmac = crypto.createHmac('sha256', secret);
  const digest = 'sha256=' + hmac.update(payload).digest('hex');
  
  if (signature !== digest) {
    return res.status(401).send('Signature invalide');
  }
  
  next();
}

// Route pour le webhook
app.post('/webhooks/github', verifyGitHubSignature, async (req, res) => {
  const event = req.headers['x-github-event'];
  const payload = req.body;
  
  console.log(`Événement GitHub reçu: ${event}`);
  
  // Traitement selon le type d'événement
  switch (event) {
    case 'issues':
      await handleIssueEvent(payload);
      break;
    case 'pull_request':
      await handlePullRequestEvent(payload);
      break;
    case 'push':
      await handlePushEvent(payload);
      break;
    // Autres types d'événements...
  }
  
  res.status(200).send('OK');
});

// Démarrage du serveur
app.listen(3000, () => {
  console.log('Serveur de webhooks démarré sur le port 3000');
});
```

#### Architectures orientées événements
Concevez des intégrations basées sur une architecture orientée événements.

```javascript
// Système de bus d'événements
const eventBus = {
  subscribers: {},
  
  subscribe: function(event, callback) {
    if (!this.subscribers[event]) {
      this.subscribers[event] = [];
    }
    this.subscribers[event].push(callback);
    
    return () => {
      this.subscribers[event] = this.subscribers[event].filter(cb => cb !== callback);
    };
  },
  
  publish: function(event, data) {
    if (!this.subscribers[event]) return;
    
    this.subscribers[event].forEach(callback => {
      try {
        callback(data);
      } catch (error) {
        console.error(`Erreur lors du traitement de l'événement ${event}:`, error);
      }
    });
  }
};

// Exemple d'utilisation
// Abonnement aux événements
eventBus.subscribe('issue:created', async (issue) => {
  // Notification Slack
  await sendSlackNotification(`Nouvelle issue créée: ${issue.title}`);
});

eventBus.subscribe('issue:created', async (issue) => {
  // Ajout automatique de labels
  await autoLabelIssue(issue);
});

eventBus.subscribe('pull_request:merged', async (pr) => {
  // Déploiement automatique
  await triggerDeployment(pr.base.ref);
});

// Publication d'événements
async function handleWebhook(event, payload) {
  switch (event) {
    case 'issues':
      if (payload.action === 'opened') {
        eventBus.publish('issue:created', payload.issue);
      } else if (payload.action === 'closed') {
        eventBus.publish('issue:closed', payload.issue);
      }
      break;
    case 'pull_request':
      if (payload.action === 'closed' && payload.pull_request.merged) {
        eventBus.publish('pull_request:merged', payload.pull_request);
      }
      break;
    // Autres événements...
  }
}
```

### 8.2. Intégration basée sur les flux

#### Pipelines de traitement
Créez des pipelines de traitement pour les flux de données.

```javascript
// Système de pipeline
class Pipeline {
  constructor(name) {
    this.name = name;
    this.steps = [];
  }
  
  addStep(name, processor) {
    this.steps.push({ name, processor });
    return this;
  }
  
  async process(data) {
    let current = data;
    
    for (const step of this.steps) {
      try {
        console.log(`Pipeline ${this.name}: Exécution de l'étape ${step.name}`);
        current = await step.processor(current);
      } catch (error) {
        console.error(`Pipeline ${this.name}: Erreur à l'étape ${step.name}:`, error);
        throw new Error(`Échec du pipeline à l'étape ${step.name}: ${error.message}`);
      }
    }
    
    return current;
  }
}

// Exemple d'utilisation
const issuePipeline = new Pipeline('issue-processing')
  .addStep('validation', async (issue) => {
    // Validation des données
    if (!issue.title) {
      throw new Error('Le titre de l\'issue est requis');
    }
    return issue;
  })
  .addStep('enrichissement', async (issue) => {
    // Ajout d'informations supplémentaires
    issue.metadata = {
      createdAt: new Date(),
      priority: calculatePriority(issue)
    };
    return issue;
  })
  .addStep('classification', async (issue) => {
    // Classification automatique
    issue.suggestedLabels = await classifyIssue(issue);
    return issue;
  })
  .addStep('notification', async (issue) => {
    // Notification des parties prenantes
    await notifyStakeholders(issue);
    return issue;
  });

// Traitement d'une issue
async function processNewIssue(issueData) {
  try {
    const processedIssue = await issuePipeline.process(issueData);
    console.log('Issue traitée avec succès:', processedIssue);
  } catch (error) {
    console.error('Échec du traitement de l\'issue:', error);
  }
}
```

#### Transformations de données
Implémentez des transformations de données efficaces.

```javascript
// Système de transformation de données
const transformers = {
  // Transformation d'une issue GitHub en ticket Jira
  githubToJira: (githubIssue) => {
    return {
      summary: githubIssue.title,
      description: githubIssue.body,
      issuetype: {
        name: githubIssue.labels.includes('bug') ? 'Bug' : 'Task'
      },
      priority: mapGitHubPriorityToJira(githubIssue),
      reporter: mapGitHubUserToJira(githubIssue.user),
      // Autres champs...
    };
  },
  
  // Transformation d'un ticket Jira en issue GitHub
  jiraToGithub: (jiraIssue) => {
    return {
      title: jiraIssue.fields.summary,
      body: formatJiraDescription(jiraIssue.fields.description),
      labels: mapJiraLabelsToGithub(jiraIssue),
      assignees: jiraIssue.fields.assignee ? [mapJiraUserToGithub(jiraIssue.fields.assignee)] : []
    };
  },
  
  // Transformation générique avec schéma
  transform: (data, schema) => {
    const result = {};
    
    for (const [targetField, sourceField] of Object.entries(schema)) {
      if (typeof sourceField === 'string') {
        // Mapping direct
        result[targetField] = getNestedValue(data, sourceField);
      } else if (typeof sourceField === 'function') {
        // Transformation personnalisée
        result[targetField] = sourceField(data);
      }
    }
    
    return result;
  }
};

// Fonction utilitaire pour accéder aux propriétés imbriquées
function getNestedValue(obj, path) {
  return path.split('.').reduce((current, part) => current && current[part], obj);
}

// Exemple d'utilisation
async function syncIssue(githubIssue) {
  // Transformation de l'issue GitHub en ticket Jira
  const jiraTicket = transformers.githubToJira(githubIssue);
  
  // Création du ticket dans Jira
  const createdTicket = await createJiraTicket(jiraTicket);
  
  // Stockage de la référence croisée
  await storeIssueMapping({
    githubIssue: {
      owner: githubIssue.repository.owner.login,
      repo: githubIssue.repository.name,
      number: githubIssue.number
    },
    jiraTicket: {
      key: createdTicket.key,
      id: createdTicket.id
    }
  });
}
```

### 8.3. Orchestration et workflows

#### Orchestration de services
Orchestrez des services pour des workflows complexes.

```javascript
// Système d'orchestration
class Orchestrator {
  constructor() {
    this.workflows = {};
  }
  
  registerWorkflow(name, steps) {
    this.workflows[name] = steps;
  }
  
  async executeWorkflow(name, context) {
    const workflow = this.workflows[name];
    
    if (!workflow) {
      throw new Error(`Workflow non trouvé: ${name}`);
    }
    
    console.log(`Démarrage du workflow: ${name}`);
    
    const workflowContext = {
      ...context,
      results: {},
      errors: {},
      startTime: Date.now()
    };
    
    for (const step of workflow) {
      console.log(`Exécution de l'étape: ${step.name}`);
      
      try {
        // Exécution de l'étape
        const result = await step.execute(workflowContext);
        
        // Stockage du résultat
        workflowContext.results[step.name] = result;
        
        // Vérification des conditions de continuation
        if (step.condition && !step.condition(workflowContext)) {
          console.log(`Condition non remplie pour l'étape ${step.name}, arrêt du workflow`);
          break;
        }
      } catch (error) {
        console.error(`Erreur lors de l'exécution de l'étape ${step.name}:`, error);
        
        // Stockage de l'erreur
        workflowContext.errors[step.name] = error;
        
        // Gestion des erreurs selon la configuration
        if (step.errorHandler) {
          await step.errorHandler(error, workflowContext);
        }
        
        // Arrêt du workflow en cas d'erreur critique
        if (step.critical !== false) {
          break;
        }
      }
    }
    
    workflowContext.endTime = Date.now();
    workflowContext.duration = workflowContext.endTime - workflowContext.startTime;
    
    console.log(`Workflow ${name} terminé en ${workflowContext.duration}ms`);
    
    return workflowContext;
  }
}

// Exemple d'utilisation
const orchestrator = new Orchestrator();

// Définition d'un workflow de déploiement
orchestrator.registerWorkflow('deploy-application', [
  {
    name: 'validate-code',
    execute: async (context) => {
      // Validation du code
      await runTests(context.repository);
      return { status: 'success' };
    },
    critical: true
  },
  {
    name: 'build-application',
    execute: async (context) => {
      // Construction de l'application
      const buildResult = await buildApplication(context.repository);
      return buildResult;
    },
    critical: true
  },
  {
    name: 'deploy-staging',
    execute: async (context) => {
      // Déploiement en environnement de staging
      return await deployToEnvironment('staging', context.results['build-application'].artifacts);
    },
    critical: true
  },
  {
    name: 'run-integration-tests',
    execute: async (context) => {
      // Exécution des tests d'intégration
      return await runIntegrationTests('staging');
    },
    critical: true
  },
  {
    name: 'deploy-production',
    execute: async (context) => {
      // Déploiement en production
      return await deployToEnvironment('production', context.results['build-application'].artifacts);
    },
    condition: (context) => {
      // Ne déployer en production que si les tests d'intégration sont réussis
      return context.results['run-integration-tests'].success;
    }
  },
  {
    name: 'notify-team',
    execute: async (context) => {
      // Notification de l'équipe
      const success = !Object.keys(context.errors).length;
      await notifyTeam({
        workflow: 'deploy-application',
        success,
        details: context
      });
      return { notified: true };
    },
    critical: false
  }
]);

// Exécution du workflow
async function deployApplication(repository, branch) {
  return orchestrator.executeWorkflow('deploy-application', {
    repository,
    branch
  });
}
```

#### Machines à états
Utilisez des machines à états pour gérer des processus complexes.

```javascript
// Machine à états
class StateMachine {
  constructor(config) {
    this.states = config.states;
    this.transitions = config.transitions;
    this.initialState = config.initialState;
    this.currentState = this.initialState;
  }
  
  async transition(event, context) {
    const currentStateConfig = this.states[this.currentState];
    
    // Recherche de la transition
    const transition = this.transitions.find(t => 
      t.from === this.currentState && 
      t.event === event
    );
    
    if (!transition) {
      throw new Error(`Transition non définie: ${this.currentState} -> ${event}`);
    }
    
    console.log(`Transition: ${this.currentState} -> ${transition.to} (événement: ${event})`);
    
    // Exécution de l'action de sortie de l'état actuel
    if (currentStateConfig.exit) {
      await currentStateConfig.exit(context);
    }
    
    // Exécution de l'action de transition
    if (transition.action) {
      await transition.action(context);
    }
    
    // Changement d'état
    this.currentState = transition.to;
    
    // Exécution de l'action d'entrée du nouvel état
    const newStateConfig = this.states[this.currentState];
    if (newStateConfig.entry) {
      await newStateConfig.entry(context);
    }
    
    return this.currentState;
  }
  
  getState() {
    return this.currentState;
  }
  
  isInFinalState() {
    return this.states[this.currentState].final === true;
  }
}

// Exemple d'utilisation pour un processus d'approbation
const approvalProcess = new StateMachine({
  initialState: 'draft',
  states: {
    'draft': {
      entry: async (context) => {
        console.log(`Document ${context.documentId} en état de brouillon`);
      }
    },
    'submitted': {
      entry: async (context) => {
        console.log(`Document ${context.documentId} soumis pour approbation`);
        await notifyApprovers(context.documentId, context.approvers);
      }
    },
    'in_review': {
      entry: async (context) => {
        console.log(`Document ${context.documentId} en cours de revue`);
      }
    },
    'changes_requested': {
      entry: async (context) => {
        console.log(`Modifications demandées pour le document ${context.documentId}`);
        await notifyAuthor(context.documentId, context.changeRequest);
      }
    },
    'approved': {
      entry: async (context) => {
        console.log(`Document ${context.documentId} approuvé`);
        await finalizeDocument(context.documentId);
      },
      final: true
    },
    'rejected': {
      entry: async (context) => {
        console.log(`Document ${context.documentId} rejeté`);
        await notifyAuthor(context.documentId, context.rejectionReason);
      },
      final: true
    }
  },
  transitions: [
    { from: 'draft', event: 'submit', to: 'submitted' },
    { from: 'submitted', event: 'start_review', to: 'in_review' },
    { from: 'in_review', event: 'request_changes', to: 'changes_requested' },
    { from: 'in_review', event: 'approve', to: 'approved' },
    { from: 'in_review', event: 'reject', to: 'rejected' },
    { from: 'changes_requested', event: 'submit', to: 'submitted' }
  ]
});

// Utilisation de la machine à états
async function processDocumentEvent(documentId, event, data) {
  const context = {
    documentId,
    ...data
  };
  
  const newState = await approvalProcess.transition(event, context);
  
  // Mise à jour de l'état du document dans la base de données
  await updateDocumentState(documentId, newState);
  
  return newState;
}
```

## Conclusion

L'intégration d'outils et de services externes avec Roo via le protocole MCP ouvre un monde de possibilités pour automatiser et enrichir vos workflows. En suivant les bonnes pratiques présentées dans ce document, vous pourrez créer des intégrations robustes, sécurisées et performantes.

Les points clés à retenir sont :

1. **Architecture solide** : Concevez vos intégrations avec une architecture modulaire et extensible.
2. **Sécurité avant tout** : Protégez les données sensibles et appliquez le principe du moindre privilège.
3. **Performance optimale** : Utilisez des techniques comme la mise en cache et le traitement par lots pour optimiser les performances.
4. **Gestion d'erreurs robuste** : Implémentez des stratégies de gestion d'erreurs complètes pour assurer la résilience.
5. **Tests rigoureux** : Testez vos intégrations à tous les niveaux pour garantir leur fiabilité.
6. **Maintenance proactive** : Surveillez et maintenez vos intégrations pour assurer leur bon fonctionnement dans le temps.
7. **Documentation complète** : Documentez vos intégrations pour faciliter leur utilisation et leur maintenance.
8. **Modèles avancés** : Utilisez des modèles d'intégration avancés pour des cas d'utilisation complexes.

En combinant ces pratiques avec les capacités puissantes de Roo et du protocole MCP, vous pourrez créer des solutions d'intégration qui apportent une réelle valeur ajoutée à vos projets et workflows.