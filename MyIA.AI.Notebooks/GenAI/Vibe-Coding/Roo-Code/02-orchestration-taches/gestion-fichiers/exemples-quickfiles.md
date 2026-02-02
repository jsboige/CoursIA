# 📋 Exemples d'utilisation de Quickfiles

Ce document présente des exemples concrets d'utilisation du MCP Quickfiles pour différents scénarios de gestion de fichiers. Chaque exemple est accompagné d'explications et de bonnes pratiques.

## Lecture multiple de fichiers

### Exemple 1 : Lecture de plusieurs fichiers de configuration

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>read_multiple_files</tool_name>
<arguments>
{
  "paths": [
    "config/database.json",
    "config/app.json",
    "config/logging.json"
  ],
  "show_line_numbers": true
}
</arguments>
</use_mcp_tool>
```

Cette commande lit simultanément trois fichiers de configuration, affichant leur contenu avec des numéros de ligne pour faciliter la référence.

### Exemple 2 : Lecture d'extraits spécifiques de fichiers volumineux

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>read_multiple_files</tool_name>
<arguments>
{
  "paths": [
    {
      "path": "logs/application.log",
      "excerpts": [
        {"start": 100, "end": 120},
        {"start": 500, "end": 520}
      ]
    },
    {
      "path": "src/main.js",
      "excerpts": [
        {"start": 50, "end": 100}
      ]
    }
  ],
  "show_line_numbers": true
}
</arguments>
</use_mcp_tool>
```

Cette commande lit des sections spécifiques de deux fichiers différents, ce qui est particulièrement utile pour les fichiers volumineux comme les logs.

## Listage de répertoires

### Exemple 1 : Listage récursif avec filtrage par extension

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>list_directory_contents</tool_name>
<arguments>
{
  "paths": [
    {
      "path": "src",
      "recursive": true,
      "file_pattern": "*.js",
      "sort_by": "modified",
      "sort_order": "desc"
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande liste récursivement tous les fichiers JavaScript dans le répertoire `src`, triés par date de modification (du plus récent au plus ancien).

### Exemple 2 : Listage de plusieurs répertoires avec différentes options

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>list_directory_contents</tool_name>
<arguments>
{
  "paths": [
    {
      "path": "src/components",
      "recursive": true,
      "max_depth": 2
    },
    {
      "path": "src/utils",
      "file_pattern": "*.{js,ts}"
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande liste les fichiers dans deux répertoires différents avec des options spécifiques pour chacun.

## Recherche dans les fichiers

### Exemple 1 : Recherche d'un motif avec contexte

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_in_files</tool_name>
<arguments>
{
  "paths": ["src"],
  "pattern": "function\\s+handleError",
  "use_regex": true,
  "context_lines": 3,
  "file_pattern": "*.js"
}
</arguments>
</use_mcp_tool>
```

Cette commande recherche toutes les fonctions `handleError` dans les fichiers JavaScript du répertoire `src`, affichant 3 lignes de contexte avant et après chaque correspondance.

### Exemple 2 : Recherche de TODO dans plusieurs répertoires

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_in_files</tool_name>
<arguments>
{
  "paths": ["src", "tests", "docs"],
  "pattern": "TODO|FIXME",
  "use_regex": true,
  "case_sensitive": false,
  "context_lines": 1
}
</arguments>
</use_mcp_tool>
```

Cette commande recherche tous les commentaires TODO ou FIXME dans trois répertoires différents, sans distinction de casse.

## Édition multiple de fichiers

### Exemple 1 : Mise à jour des en-têtes de licence

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>edit_multiple_files</tool_name>
<arguments>
{
  "files": [
    {
      "path": "src/app.js",
      "diffs": [
        {
          "search": "// Copyright (c) 2024 Company",
          "replace": "// Copyright (c) 2025 Company"
        }
      ]
    },
    {
      "path": "src/utils.js",
      "diffs": [
        {
          "search": "// Copyright (c) 2024 Company",
          "replace": "// Copyright (c) 2025 Company"
        }
      ]
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande met à jour l'année de copyright dans les en-têtes de deux fichiers.

### Exemple 2 : Refactorisation d'une API

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>edit_multiple_files</tool_name>
<arguments>
{
  "files": [
    {
      "path": "src/api.js",
      "diffs": [
        {
          "search": "function fetchData(url, callback) {",
          "replace": "async function fetchData(url) {"
        },
        {
          "search": "  xhr.onload = function() {\n    callback(null, xhr.responseText);\n  };",
          "replace": "  try {\n    const response = await fetch(url);\n    return await response.json();\n  } catch (error) {\n    throw error;\n  }"
        }
      ]
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande refactorise une fonction d'API basée sur callbacks en une version utilisant async/await.

## Recherche et remplacement

### Exemple 1 : Mise à jour des imports dans plusieurs fichiers

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_and_replace</tool_name>
<arguments>
{
  "paths": ["src"],
  "search": "import { Component } from 'react';",
  "replace": "import React, { Component } from 'react';",
  "file_pattern": "*.jsx",
  "recursive": true,
  "preview": true
}
</arguments>
</use_mcp_tool>
```

Cette commande recherche et remplace les imports React dans tous les fichiers JSX, avec une prévisualisation des changements avant application.

### Exemple 2 : Correction d'un motif récurrent avec regex

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_and_replace</tool_name>
<arguments>
{
  "files": [
    {
      "path": "src/utils/validation.js",
      "search": "function validate([a-zA-Z]+)\\(([^)]+)\\) \\{\\s+if\\(!\\2\\) return false;",
      "replace": "function validate$1($2) {\n  if ($2 === undefined || $2 === null) return false;",
      "use_regex": true
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande utilise une expression régulière pour améliorer les vérifications de validation dans un fichier JavaScript.

## Extraction de structure Markdown

### Exemple 1 : Analyse de la documentation

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>extract_markdown_structure</tool_name>
<arguments>
{
  "paths": [
    "docs/api.md",
    "docs/getting-started.md"
  ],
  "max_depth": 3,
  "include_context": true,
  "context_lines": 1
}
</arguments>
</use_mcp_tool>
```

Cette commande extrait la structure des titres jusqu'au niveau 3 de deux fichiers de documentation, avec une ligne de contexte pour chaque titre.

### Exemple 2 : Analyse d'un README

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>extract_markdown_structure</tool_name>
<arguments>
{
  "paths": ["README.md"],
  "max_depth": 2
}
</arguments>
</use_mcp_tool>
```

Cette commande extrait uniquement les titres de niveau 1 et 2 du fichier README.md.

## Suppression de fichiers

### Exemple : Nettoyage de fichiers temporaires

```
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>delete_files</tool_name>
<arguments>
{
  "paths": [
    "temp/cache.json",
    "temp/debug.log",
    "build/temp.js"
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande supprime trois fichiers temporaires en une seule opération.

## Scénarios d'orchestration avancés

### Scénario 1 : Analyse et refactorisation d'un projet

```
# Étape 1 : Explorer la structure du projet
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>list_directory_contents</tool_name>
<arguments>
{
  "paths": [{"path": "src", "recursive": true}]
}
</arguments>
</use_mcp_tool>

# Étape 2 : Rechercher les fonctions obsolètes
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_in_files</tool_name>
<arguments>
{
  "paths": ["src"],
  "pattern": "deprecated",
  "context_lines": 5
}
</arguments>
</use_mcp_tool>

# Étape 3 : Remplacer les fonctions obsolètes
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_and_replace</tool_name>
<arguments>
{
  "paths": ["src"],
  "search": "oldFunction\\(([^)]*)\\)",
  "replace": "newFunction($1)",
  "use_regex": true
}
</arguments>
</use_mcp_tool>

# Étape 4 : Vérifier les modifications
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>read_multiple_files</tool_name>
<arguments>
{
  "paths": ["src/main.js", "src/utils.js"]
}
</arguments>
</use_mcp_tool>
```

### Scénario 2 : Migration de configuration

```
# Étape 1 : Lire les fichiers de configuration actuels
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>read_multiple_files</tool_name>
<arguments>
{
  "paths": ["config/old-format/*.json"]
}
</arguments>
</use_mcp_tool>

# Étape 2 : Rechercher les clés à migrer
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_in_files</tool_name>
<arguments>
{
  "paths": ["config/old-format"],
  "pattern": "\"apiVersion\":\\s*\"v1\"",
  "file_pattern": "*.json"
}
</arguments>
</use_mcp_tool>

# Étape 3 : Mettre à jour le format de configuration
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_and_replace</tool_name>
<arguments>
{
  "paths": ["config/old-format"],
  "search": "\"apiVersion\":\\s*\"v1\"",
  "replace": "\"apiVersion\": \"v2\"",
  "use_regex": true,
  "file_pattern": "*.json"
}
</arguments>
</use_mcp_tool>
```

### Scénario 3 : Analyse de documentation et mise à jour

```
# Étape 1 : Extraire la structure de la documentation
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>extract_markdown_structure</tool_name>
<arguments>
{
  "paths": ["docs/*.md"],
  "max_depth": 3
}
</arguments>
</use_mcp_tool>

# Étape 2 : Rechercher les références obsolètes
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_in_files</tool_name>
<arguments>
{
  "paths": ["docs"],
  "pattern": "version 1\\.x",
  "file_pattern": "*.md"
}
</arguments>
</use_mcp_tool>

# Étape 3 : Mettre à jour les références
<use_mcp_tool>
<server_name>quickfiles</server_name>
<tool_name>search_and_replace</tool_name>
<arguments>
{
  "paths": ["docs"],
  "search": "version 1\\.x",
  "replace": "version 2.0",
  "use_regex": true,
  "file_pattern": "*.md"
}
</arguments>
</use_mcp_tool>
```

## Bonnes pratiques pour l'utilisation de Quickfiles

1. **Planifiez vos opérations** : Avant de modifier des fichiers, planifiez les étapes avec des recherches et des analyses
2. **Utilisez la prévisualisation** : Activez l'option `preview` pour voir les changements avant de les appliquer
3. **Sauvegardez avant les modifications massives** : Créez des copies de sauvegarde avant d'appliquer des modifications à grande échelle
4. **Commencez petit** : Testez vos opérations sur un petit ensemble de fichiers avant de les appliquer à tout le projet
5. **Combinez les outils** : Utilisez les différents outils de Quickfiles ensemble pour créer des workflows efficaces
6. **Vérifiez après modification** : Utilisez `read_multiple_files` pour vérifier les fichiers après les avoir modifiés
7. **Utilisez des expressions régulières précises** : Pour les opérations de recherche et remplacement, utilisez des regex bien ciblées
8. **Limitez la portée** : Utilisez `file_pattern` et des chemins spécifiques pour limiter la portée des opérations

## Conclusion

Quickfiles est un outil puissant qui, lorsqu'il est utilisé correctement dans le cadre du mode Orchestrator, peut considérablement améliorer votre productivité dans la gestion de fichiers. Les exemples présentés dans ce document ne sont qu'un aperçu des possibilités offertes par cet outil.