# 📚 Exemples d'Intégration avec MCP

Ce document présente des exemples concrets d'intégration de Roo avec d'autres services via le protocole MCP (Model Context Protocol). Chaque exemple inclut le code complet, des explications détaillées et des cas d'usage pratiques.

## Table des matières

1. [Intégration avec GitHub](#1-intégration-avec-github)
2. [Automatisation système avec win-cli](#2-automatisation-système-avec-win-cli)
3. [Recherche et synthèse avec SearXNG et JinaNavigator](#3-recherche-et-synthèse-avec-searxng-et-jinavigator)
4. [Analyse de données avec Jupyter](#4-analyse-de-données-avec-jupyter)
5. [Traitement de fichiers avec QuickFiles](#5-traitement-de-fichiers-avec-quickfiles)
6. [Intégration multi-services](#6-intégration-multi-services)

---

## 1. Intégration avec GitHub

### Cas d'usage: Gestion automatisée de projet GitHub

Cet exemple montre comment utiliser Roo pour automatiser la gestion d'un projet GitHub, incluant la création d'issues, la gestion des pull requests et l'analyse de code.

### Configuration du serveur MCP

```bash
# Installation du serveur MCP GitHub (externe)
# Depuis la racine du dépôt principal
cd mcps/external/github
npx -y @modelcontextprotocol/server-github

# Configuration avec un token GitHub (à faire une seule fois)
export GITHUB_TOKEN=ghp_votre_token_personnel
```

### Exemple: Création d'un rapport de projet

```javascript
// Exemple de workflow d'intégration avec GitHub

// 1. Récupération des issues ouvertes
const openIssues = await use_mcp_tool({
  server_name: "github",
  tool_name: "list_issues",
  arguments: {
    owner: "votre-organisation",
    repo: "votre-projet",
    state: "open"
  }
});

// 2. Analyse des pull requests
const pullRequests = await use_mcp_tool({
  server_name: "github",
  tool_name: "list_pull_requests",
  arguments: {
    owner: "votre-organisation",
    repo: "votre-projet",
    state: "open"
  }
});

// 3. Récupération des derniers commits
const recentCommits = await use_mcp_tool({
  server_name: "github",
  tool_name: "list_commits",
  arguments: {
    owner: "votre-organisation",
    repo: "votre-projet",
    perPage: 10
  }
});

// 4. Génération d'un rapport de statut
const statusReport = generateProjectStatusReport(openIssues, pullRequests, recentCommits);

// 5. Création d'une issue avec le rapport
await use_mcp_tool({
  server_name: "github",
  tool_name: "create_issue",
  arguments: {
    owner: "votre-organisation",
    repo: "votre-projet",
    title: `Rapport de statut du projet - ${new Date().toISOString().split('T')[0]}`,
    body: statusReport,
    labels: ["rapport", "automatique"]
  }
});
```

### Fonctionnalités avancées

- **Analyse de code automatisée**:
  ```javascript
  // Recherche de patterns spécifiques dans le code
  const codeSearchResults = await use_mcp_tool({
    server_name: "github",
    tool_name: "search_code",
    arguments: {
      q: "repo:votre-organisation/votre-projet language:javascript TODO"
    }
  });
  
  // Génération d'un rapport de TODOs
  const todoReport = analyzeTodos(codeSearchResults);
  ```

- **Gestion automatisée des pull requests**:
  ```javascript
  // Revue automatique des PRs
  for (const pr of pullRequests.data) {
    const files = await use_mcp_tool({
      server_name: "github",
      tool_name: "get_pull_request_files",
      arguments: {
        owner: "votre-organisation",
        repo: "votre-projet",
        pull_number: pr.number
      }
    });
    
    const review = await analyzeChanges(files);
    
    await use_mcp_tool({
      server_name: "github",
      tool_name: "create_pull_request_review",
      arguments: {
        owner: "votre-organisation",
        repo: "votre-projet",
        pull_number: pr.number,
        body: review.comments,
        event: review.recommendation
      }
    });
  }
  ```

## 2. Automatisation système avec win-cli

### Cas d'usage: Maintenance système automatisée

Cet exemple montre comment utiliser Roo pour automatiser des tâches de maintenance système sur Windows.

### Configuration du serveur MCP

```bash
# Installation du serveur MCP win-cli (externe)
# Depuis la racine du dépôt principal
cd mcps/external/win-cli
npx -y @simonb97/server-win-cli
```

### Exemple: Nettoyage et analyse système

```javascript
// Exemple de workflow d'automatisation système

// 1. Vérification de l'espace disque
const diskSpace = await use_mcp_tool({
  server_name: "win-cli",
  tool_name: "execute_command",
  arguments: {
    shell: "powershell",
    command: "Get-PSDrive C | Select-Object Used,Free"
  }
});

// 2. Identification des fichiers volumineux
const largeFiles = await use_mcp_tool({
  server_name: "win-cli",
  tool_name: "execute_command",
  arguments: {
    shell: "powershell",
    command: "Get-ChildItem -Path C:\\ -Recurse -File | Where-Object { $_.Length -gt 100MB } | Sort-Object Length -Descending | Select-Object FullName, @{Name='SizeGB';Expression={$_.Length / 1GB}}"
  }
});

// 3. Nettoyage des fichiers temporaires
const cleanupTemp = await use_mcp_tool({
  server_name: "win-cli",
  tool_name: "execute_command",
  arguments: {
    shell: "powershell",
    command: "Remove-Item -Path $env:TEMP\\* -Recurse -Force -ErrorAction SilentlyContinue"
  }
});

// 4. Vérification des mises à jour Windows
const windowsUpdates = await use_mcp_tool({
  server_name: "win-cli",
  tool_name: "execute_command",
  arguments: {
    shell: "powershell",
    command: "Get-WindowsUpdate"
  }
});

// 5. Génération d'un rapport de maintenance
const maintenanceReport = generateMaintenanceReport(diskSpace, largeFiles, cleanupTemp, windowsUpdates);
```

### Fonctionnalités avancées

- **Surveillance des performances**:
  ```javascript
  // Collecte de métriques de performance
  const performanceMetrics = await use_mcp_tool({
    server_name: "win-cli",
    tool_name: "execute_command",
    arguments: {
      shell: "powershell",
      command: `
        $cpu = (Get-Counter '\\Processor(_Total)\\% Processor Time').CounterSamples.CookedValue
        $memory = (Get-Counter '\\Memory\\Available MBytes').CounterSamples.CookedValue
        $disk = (Get-Counter '\\PhysicalDisk(_Total)\\% Disk Time').CounterSamples.CookedValue
        $network = (Get-Counter '\\Network Interface(*)\\Bytes Total/sec').CounterSamples | Where-Object {$_.InstanceName -notlike '*isatap*'} | Measure-Object -Property CookedValue -Sum
        
        [PSCustomObject]@{
            CPU = $cpu
            MemoryAvailableMB = $memory
            DiskUsage = $disk
            NetworkBytesPerSec = $network.Sum
        } | ConvertTo-Json
      `
    }
  });
  ```

- **Gestion des services**:
  ```javascript
  // Vérification et redémarrage des services problématiques
  const services = await use_mcp_tool({
    server_name: "win-cli",
    tool_name: "execute_command",
    arguments: {
      shell: "powershell",
      command: "Get-Service | Where-Object {$_.Status -eq 'Stopped' -and $_.StartType -eq 'Automatic'}"
    }
  });
  
  for (const service of parseServices(services)) {
    await use_mcp_tool({
      server_name: "win-cli",
      tool_name: "execute_command",
      arguments: {
        shell: "powershell",
        command: `Start-Service -Name "${service.Name}" -ErrorAction SilentlyContinue`
      }
    });
  }
  ```

## 3. Recherche et synthèse avec SearXNG et JinaNavigator

### Cas d'usage: Veille technologique automatisée

Cet exemple montre comment utiliser Roo pour effectuer une veille technologique automatisée en combinant SearXNG pour la recherche et JinaNavigator pour l'extraction de contenu.

### Configuration des serveurs MCP

```bash
# Installation du serveur MCP SearXNG (externe)
# Depuis la racine du dépôt principal
cd mcps/external/searxng
node ./dist/index.js

# Installation du serveur MCP JinaNavigator (interne)
# Depuis la racine du dépôt principal
cd mcps/internal/jinavigator-server
node ./dist/index.js
```

### Exemple: Veille sur une technologie émergente

```javascript
// Exemple de workflow de veille technologique

// 1. Recherche d'informations récentes
const searchResults = await use_mcp_tool({
  server_name: "searxng",
  tool_name: "searxng_web_search",
  arguments: {
    query: "\"edge computing\" \"nouvelles applications\" site:techcrunch.com OR site:zdnet.fr",
    time_range: "month",
    language: "fr"
  }
});

// 2. Extraction et conversion des articles pertinents
const articles = [];
for (const result of searchResults.results.slice(0, 5)) {
  const article = await use_mcp_tool({
    server_name: "jinavigator",
    tool_name: "convert_web_to_markdown",
    arguments: {
      url: result.url
    }
  });
  
  articles.push({
    title: result.title,
    url: result.url,
    content: article.markdown
  });
}

// 3. Extraction des structures des articles
const outlines = await use_mcp_tool({
  server_name: "jinavigator",
  tool_name: "extract_markdown_outline",
  arguments: {
    urls: articles.map(a => ({ url: a.url })),
    max_depth: 2
  }
});

// 4. Génération d'une synthèse
const techReport = generateTechnologyReport(articles, outlines);
```

### Fonctionnalités avancées

- **Analyse de sentiment et tendances**:
  ```javascript
  // Analyse des tendances et du sentiment
  function analyzeTrends(articles) {
    // Extraction des termes fréquents
    const terms = extractFrequentTerms(articles);
    
    // Analyse du sentiment par sujet
    const sentiments = analyzeTopicSentiment(articles, terms);
    
    // Identification des tendances émergentes
    const emergingTrends = identifyEmergingTrends(terms, sentiments);
    
    return {
      topTerms: terms.slice(0, 10),
      sentimentAnalysis: sentiments,
      emergingTrends: emergingTrends
    };
  }
  ```

- **Suivi temporel des évolutions**:
  ```javascript
  // Comparaison avec les données historiques
  async function compareWithHistoricalData(currentReport) {
    // Récupération des rapports précédents
    const previousReports = await loadPreviousReports();
    
    // Analyse des évolutions
    const evolution = {
      newTopics: findNewTopics(currentReport, previousReports),
      growingTopics: findGrowingTopics(currentReport, previousReports),
      decliningTopics: findDecliningTopics(currentReport, previousReports)
    };
    
    return evolution;
  }
  ```

## 4. Analyse de données avec Jupyter

### Cas d'usage: Analyse automatisée de données

Cet exemple montre comment utiliser Roo pour automatiser l'analyse de données avec Jupyter.

### Configuration du serveur MCP

```bash
# Installation du serveur MCP Jupyter (interne)
# Depuis la racine du dépôt principal
cd mcps/internal/jupyter-mcp-server
node ./dist/index.js
```

### Exemple: Analyse de données de ventes

```javascript
// Exemple de workflow d'analyse de données

// 1. Création d'un nouveau notebook
const notebook = await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "create_notebook",
  arguments: {
    path: "./analyse_ventes.ipynb",
    kernel: "python3"
  }
});

// 2. Démarrage d'un kernel
const kernel = await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "start_kernel",
  arguments: {
    kernel_name: "python3"
  }
});

// 3. Ajout des cellules d'importation et chargement de données
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "add_cell",
  arguments: {
    path: "./analyse_ventes.ipynb",
    cell_type: "code",
    source: `
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
from datetime import datetime

# Configuration
plt.style.use('ggplot')
sns.set(style="whitegrid")
%matplotlib inline
    `
  }
});

await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "add_cell",
  arguments: {
    path: "./analyse_ventes.ipynb",
    cell_type: "code",
    source: `
# Chargement des données
sales_data = pd.read_csv('ventes_2025.csv')

# Affichage des premières lignes
sales_data.head()
    `
  }
});

// 4. Ajout de cellules d'analyse
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "add_cell",
  arguments: {
    path: "./analyse_ventes.ipynb",
    cell_type: "code",
    source: `
# Analyse temporelle
sales_data['date'] = pd.to_datetime(sales_data['date'])
sales_data['month'] = sales_data['date'].dt.month
sales_data['day_of_week'] = sales_data['date'].dt.dayofweek

# Ventes mensuelles
monthly_sales = sales_data.groupby('month')['amount'].sum().reset_index()

plt.figure(figsize=(12, 6))
sns.barplot(x='month', y='amount', data=monthly_sales)
plt.title('Ventes mensuelles')
plt.xlabel('Mois')
plt.ylabel('Montant total des ventes')
plt.xticks(range(12), ['Jan', 'Fév', 'Mar', 'Avr', 'Mai', 'Juin', 'Juil', 'Août', 'Sep', 'Oct', 'Nov', 'Déc'])
plt.show()
    `
  }
});

// 5. Exécution du notebook
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "execute_notebook",
  arguments: {
    path: "./analyse_ventes.ipynb",
    kernel_id: kernel.id
  }
});

// 6. Arrêt du kernel
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "stop_kernel",
  arguments: {
    kernel_id: kernel.id
  }
});
```

### Fonctionnalités avancées

- **Analyse prédictive**:
  ```javascript
  // Ajout d'une cellule pour l'analyse prédictive
  await use_mcp_tool({
    server_name: "jupyter",
    tool_name: "add_cell",
    arguments: {
      path: "./analyse_ventes.ipynb",
      cell_type: "code",
      source: `
  # Préparation des données pour la prédiction
  from sklearn.model_selection import train_test_split
  from sklearn.ensemble import RandomForestRegressor
  from sklearn.metrics import mean_absolute_error, r2_score
  
  # Création de features
  features = sales_data[['month', 'day_of_week', 'product_category', 'store_id']]
  features = pd.get_dummies(features, columns=['product_category', 'store_id'])
  target = sales_data['amount']
  
  # Split des données
  X_train, X_test, y_train, y_test = train_test_split(features, target, test_size=0.2, random_state=42)
  
  # Entraînement du modèle
  model = RandomForestRegressor(n_estimators=100, random_state=42)
  model.fit(X_train, y_train)
  
  # Évaluation
  predictions = model.predict(X_test)
  mae = mean_absolute_error(y_test, predictions)
  r2 = r2_score(y_test, predictions)
  
  print(f"MAE: {mae:.2f}")
  print(f"R²: {r2:.2f}")
  
  # Importance des features
  feature_importance = pd.DataFrame({
      'feature': features.columns,
      'importance': model.feature_importances_
  }).sort_values('importance', ascending=False)
  
  plt.figure(figsize=(10, 6))
  sns.barplot(x='importance', y='feature', data=feature_importance.head(10))
  plt.title('Importance des features')
  plt.tight_layout()
  plt.show()
      `
    }
  });
  ```

- **Génération de rapport automatique**:
  ```javascript
  // Ajout d'une cellule pour générer un rapport
  await use_mcp_tool({
    server_name: "jupyter",
    tool_name: "add_cell",
    arguments: {
      path: "./analyse_ventes.ipynb",
      cell_type: "code",
      source: `
  # Génération d'un rapport automatique
  from IPython.display import Markdown
  
  def generate_sales_report(data, predictions, mae, r2):
      total_sales = data['amount'].sum()
      avg_sales = data['amount'].mean()
      top_category = data.groupby('product_category')['amount'].sum().idxmax()
      top_store = data.groupby('store_id')['amount'].sum().idxmax()
      
      report = f"""
  # Rapport d'analyse des ventes
  
  ## Résumé
  
  - **Total des ventes**: {total_sales:,.2f} €
  - **Vente moyenne**: {avg_sales:.2f} €
  - **Catégorie la plus vendue**: {top_category}
  - **Magasin le plus performant**: {top_store}
  
  ## Performance du modèle prédictif
  
  - **Erreur absolue moyenne**: {mae:.2f} €
  - **Coefficient de détermination (R²)**: {r2:.2f}
  
  ## Recommandations
  
  1. Concentrer les efforts marketing sur la catégorie {top_category}
  2. Analyser les pratiques du magasin {top_store} pour les répliquer
  3. Optimiser les stocks en fonction des prévisions mensuelles
  """
      
      return Markdown(report)
  
  # Affichage du rapport
  generate_sales_report(sales_data, predictions, mae, r2)
      `
    }
  });
  ```

## 5. Traitement de fichiers avec QuickFiles

### Cas d'usage: Traitement par lots de documents

Cet exemple montre comment utiliser Roo pour automatiser le traitement par lots de documents avec QuickFiles.

### Configuration du serveur MCP

```bash
# Installation du serveur MCP QuickFiles (interne)
# Depuis la racine du dépôt principal
cd mcps/internal/quickfiles-server
node ./build/index.js
```

### Exemple: Analyse et transformation de logs

```javascript
// Exemple de workflow de traitement de fichiers

// 1. Recherche des fichiers de logs
const logFiles = await use_mcp_tool({
  server_name: "quickfiles",
  tool_name: "list_directory_contents",
  arguments: {
    paths: [{
      path: "./logs",
      recursive: true,
      file_pattern: "*.log"
    }]
  }
});

// 2. Lecture du contenu des logs
const logsContent = await use_mcp_tool({
  server_name: "quickfiles",
  tool_name: "read_multiple_files",
  arguments: {
    paths: logFiles.files.map(file => file.path)
  }
});

// 3. Recherche de patterns d'erreurs
const errorPatterns = await use_mcp_tool({
  server_name: "quickfiles",
  tool_name: "search_in_files",
  arguments: {
    paths: logFiles.files.map(file => file.path),
    pattern: "ERROR|CRITICAL|EXCEPTION",
    use_regex: true,
    context_lines: 3
  }
});

// 4. Extraction de la structure des logs
const logStructure = await use_mcp_tool({
  server_name: "quickfiles",
  tool_name: "extract_markdown_structure",
  arguments: {
    paths: logsContent.files.map(file => file.path)
  }
});

// 5. Génération d'un rapport d'analyse
const logAnalysisReport = generateLogAnalysisReport(logsContent, errorPatterns, logStructure);

// 6. Transformation des logs (normalisation)
await use_mcp_tool({
  server_name: "quickfiles",
  tool_name: "search_and_replace",
  arguments: {
    files: logsContent.files.map(file => ({
      path: file.path,
      search: "\\[(\\d{4}-\\d{2}-\\d{2} \\d{2}:\\d{2}:\\d{2})\\]",
      replace: "[TIMESTAMP: $1]",
      use_regex: true
    }))
  }
});
```

### Fonctionnalités avancées

- **Agrégation et analyse statistique**:
  ```javascript
  // Fonction d'analyse statistique des logs
  function analyzeLogStatistics(logsContent, errorPatterns) {
    // Extraction des timestamps
    const timestamps = extractTimestamps(logsContent);
    
    // Analyse de la distribution temporelle
    const timeDistribution = analyzeTimeDistribution(timestamps);
    
    // Corrélation entre erreurs
    const errorCorrelations = findErrorCorrelations(errorPatterns);
    
    // Identification des périodes problématiques
    const problematicPeriods = identifyProblematicPeriods(timestamps, errorPatterns);
    
    return {
      timeDistribution,
      errorCorrelations,
      problematicPeriods
    };
  }
  ```

- **Transformation avancée de fichiers**:
  ```javascript
  // Transformation avancée avec édition multiple
  await use_mcp_tool({
    server_name: "quickfiles",
    tool_name: "edit_multiple_files",
    arguments: {
      files: logsContent.files.map(file => ({
        path: file.path,
        diffs: [
          {
            search: "user=(\\w+)",
            replace: "user=[REDACTED]",
            start_line: 1
          },
          {
            search: "password=(\\w+)",
            replace: "password=[REDACTED]",
            start_line: 1
          },
          {
            search: "ip=(\\d+\\.\\d+\\.\\d+\\.\\d+)",
            replace: "ip=[REDACTED]",
            start_line: 1
          }
        ]
      }))
    }
  });
  ```

## 6. Intégration multi-services

### Cas d'usage: Pipeline de traitement de données complet

Cet exemple montre comment combiner plusieurs serveurs MCP pour créer un pipeline de traitement de données complet.

### Exemple: Collecte, analyse et visualisation de données

```javascript
// Exemple de workflow multi-services

// 1. Collecte de données via API (win-cli)
const rawData = await use_mcp_tool({
  server_name: "win-cli",
  tool_name: "execute_command",
  arguments: {
    shell: "powershell",
    command: "Invoke-RestMethod -Uri 'https://api.example.com/data' -Headers @{'Authorization'='Bearer $env:API_KEY'} | ConvertTo-Json -Depth 10"
  }
});

// 2. Sauvegarde des données brutes (filesystem)
await use_mcp_tool({
  server_name: "filesystem",
  tool_name: "write_file",
  arguments: {
    path: "./data/raw_data.json",
    content: rawData
  }
});

// 3. Enrichissement avec des données web (searxng + jinavigator)
const searchResults = await use_mcp_tool({
  server_name: "searxng",
  tool_name: "searxng_web_search",
  arguments: {
    query: "latest statistics " + extractKeywords(rawData)
  }
});

const enrichmentData = await use_mcp_tool({
  server_name: "jinavigator",
  tool_name: "convert_web_to_markdown",
  arguments: {
    url: searchResults.results[0].url
  }
});

// 4. Analyse des données avec Jupyter
// 4.1 Création du notebook
const notebook = await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "create_notebook",
  arguments: {
    path: "./analysis/data_analysis.ipynb"
  }
});

// 4.2 Démarrage du kernel
const kernel = await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "start_kernel",
  arguments: {}
});

// 4.3 Ajout des cellules d'analyse
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "add_cell",
  arguments: {
    path: "./analysis/data_analysis.ipynb",
    cell_type: "code",
    source: `
import pandas as pd
import json
import matplotlib.pyplot as plt
import seaborn as sns

# Chargement des données
with open('../data/raw_data.json', 'r') as f:
    data = json.load(f)
    
# Conversion en DataFrame
df = pd.json_normalize(data)

# Analyse exploratoire
print(df.info())
print(df.describe())

# Visualisation
plt.figure(figsize=(12, 8))
sns.heatmap(df.corr(), annot=True, cmap='coolwarm')
plt.title('Matrice de corrélation')
plt.tight_layout()
plt.savefig('../reports/correlation_matrix.png')
plt.show()
    `
  }
});

// 4.4 Exécution du notebook
await use_mcp_tool({
  server_name: "jupyter",
  tool_name: "execute_notebook",
  arguments: {
    path: "./analysis/data_analysis.ipynb",
    kernel_id: kernel.id
  }
});

// 5. Génération du rapport final (GitHub)
const reportContent = generateFinalReport(rawData, enrichmentData, "./reports/correlation_matrix.png");

await use_mcp_tool({
  server_name: "github",
  tool_name: "create_or_update_file",
  arguments: {
    owner: "votre-organisation",
    repo: "votre-projet",
    path: "reports/data_analysis_report.md",
    content: reportContent,
    message: "Ajout du rapport d'analyse de données",
    branch: "main"
  }
});
```

### Fonctionnalités avancées

- **Orchestration conditionnelle**:
  ```javascript
  // Fonction d'orchestration conditionnelle
  async function conditionalWorkflow(data) {
    // Analyse préliminaire
    const preliminaryAnalysis = analyzeData(data);
    
    // Décision basée sur l'analyse
    if (preliminaryAnalysis.anomalyDetected) {
      // Flux de travail pour les anomalies
      await anomalyWorkflow(data, preliminaryAnalysis);
    } else if (preliminaryAnalysis.qualityIssues) {
      // Flux de travail pour les problèmes de qualité
      await qualityIssueWorkflow(data, preliminaryAnalysis);
    } else {
      // Flux de travail standard
      await standardWorkflow(data);
    }
  }
  ```

- **Pipeline de traitement parallèle**:
  ```javascript
  // Fonction de traitement parallèle
  async function parallelProcessing(data) {
    // Division des données en segments
    const segments = splitDataIntoSegments(data, 4);
    
    // Traitement parallèle
    const processingPromises = segments.map(async (segment, index) => {
      // Sauvegarde du segment
      await use_mcp_tool({
        server_name: "filesystem",
        tool_name: "write_file",
        arguments: {
          path: `./data/segment_${index}.json`,
          content: JSON.stringify(segment)
        }
      });
      
      // Traitement du segment
      return processSegment(segment, index);
    });
    
    // Attente de tous les traitements
    const results = await Promise.all(processingPromises);
    
    // Fusion des résultats
    return mergeResults(results);
  }
  ```

---

Ces exemples illustrent comment intégrer Roo avec différents services via MCP pour créer des workflows d'automatisation puissants et flexibles. Vous pouvez adapter ces exemples à vos besoins spécifiques et les combiner pour créer des solutions personnalisées.

Pour des conseils sur l'implémentation optimale de ces intégrations, consultez le guide des [Bonnes pratiques](./bonnes-pratiques.md).