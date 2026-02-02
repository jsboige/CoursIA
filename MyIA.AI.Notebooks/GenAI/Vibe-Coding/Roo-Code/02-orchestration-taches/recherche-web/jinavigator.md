# 📄 Utilisation de Jinavigator pour les Contenus Web

## Introduction

Jinavigator est un MCP (Model Context Protocol) spécialisé qui permet à Roo de convertir des pages web en format Markdown structuré. Cette fonctionnalité est particulièrement utile pour l'analyse de contenus web volumineux, comme des articles techniques, des documentations ou des publications scientifiques.

## Avantages de Jinavigator

- **Extraction efficace du contenu** : Élimine les éléments non essentiels (publicités, menus, etc.)
- **Format structuré** : Convertit le contenu HTML en Markdown bien organisé
- **Préservation de la hiérarchie** : Maintient la structure des titres et sous-titres
- **Traitement de pages volumineuses** : Gère efficacement les articles longs
- **Extraction de plans** : Peut extraire uniquement la structure des titres d'une page

## Outils disponibles dans Jinavigator

Jinavigator propose plusieurs outils accessibles via le MCP :

### 1. convert_web_to_markdown

Convertit une page web complète en Markdown.

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>convert_web_to_markdown</tool_name>
<arguments>
{
  "url": "https://exemple.com/article",
  "start_line": 0,
  "end_line": 0
}
</arguments>
</use_mcp_tool>
```

Les paramètres `start_line` et `end_line` sont optionnels et permettent d'extraire seulement une partie spécifique du contenu.

### 2. access_jina_resource

Accède au contenu Markdown d'une page web via un URI au format jina://{url}.

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>access_jina_resource</tool_name>
<arguments>
{
  "uri": "jina://https://exemple.com/article",
  "start_line": 0,
  "end_line": 0
}
</arguments>
</use_mcp_tool>
```

### 3. multi_convert

Convertit plusieurs pages web en Markdown en une seule requête.

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>multi_convert</tool_name>
<arguments>
{
  "urls": [
    {
      "url": "https://exemple.com/article1",
      "start_line": 0,
      "end_line": 0
    },
    {
      "url": "https://exemple.com/article2"
    }
  ]
}
</arguments>
</use_mcp_tool>
```

### 4. extract_markdown_outline

Extrait uniquement la structure hiérarchique des titres d'une page web avec leurs numéros de ligne.

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>extract_markdown_outline</tool_name>
<arguments>
{
  "urls": [
    {
      "url": "https://exemple.com/documentation"
    }
  ],
  "max_depth": 3
}
</arguments>
</use_mcp_tool>
```

Le paramètre `max_depth` contrôle la profondeur maximale des titres à extraire (1=h1, 2=h1+h2, etc.).

## Exemples d'utilisation

### Exemple 1 : Analyse d'un article technique

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>convert_web_to_markdown</tool_name>
<arguments>
{
  "url": "https://martinfowler.com/articles/practical-test-pyramid.html"
}
</arguments>
</use_mcp_tool>
```

Cette commande convertira l'article complet sur la pyramide de tests en Markdown structuré, permettant à Roo d'analyser en profondeur son contenu.

### Exemple 2 : Extraction du plan d'une documentation

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>extract_markdown_outline</tool_name>
<arguments>
{
  "urls": [
    {
      "url": "https://docs.python.org/fr/3/tutorial/index.html"
    }
  ],
  "max_depth": 2
}
</arguments>
</use_mcp_tool>
```

Cette commande extraira uniquement les titres de niveau 1 et 2 de la documentation Python, offrant une vue d'ensemble de sa structure.

### Exemple 3 : Comparaison de plusieurs articles

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>multi_convert</tool_name>
<arguments>
{
  "urls": [
    {
      "url": "https://www.infoq.com/articles/microservices-design-ideals/"
    },
    {
      "url": "https://martinfowler.com/articles/microservices.html"
    }
  ]
}
</arguments>
</use_mcp_tool>
```

Cette commande convertira deux articles sur les microservices en Markdown, permettant à Roo de comparer leurs approches et perspectives.

## Bonnes pratiques

### Quand utiliser Jinavigator

- **Documentation technique** : Pour analyser des guides, tutoriels ou références
- **Articles longs** : Pour traiter des publications détaillées
- **Contenu académique** : Pour extraire l'information de papers ou études
- **Comparaison de sources** : Pour analyser plusieurs perspectives sur un sujet

### Optimisation des requêtes

1. **Ciblage précis** : Utilisez des URLs directes vers le contenu pertinent
2. **Limitation de portée** : Utilisez `start_line` et `end_line` pour les très longs documents
3. **Extraction de plan** : Commencez par `extract_markdown_outline` pour comprendre la structure avant d'extraire tout le contenu
4. **Requêtes multiples** : Utilisez `multi_convert` pour traiter plusieurs sources en une seule requête

### Limitations

- Ne peut pas interagir avec des éléments dynamiques (contrairement au navigateur intégré)
- Certains sites peuvent bloquer l'extraction de contenu
- Le rendu peut différer légèrement de l'original, surtout pour les mises en page complexes
- Les contenus générés dynamiquement par JavaScript peuvent être manquants

## Intégration avec le mode Orchestrator

Le mode Orchestrator peut utiliser Jinavigator dans un workflow complet :

1. Identifier des sources pertinentes avec SearXNG
2. Extraire les plans des documents avec `extract_markdown_outline`
3. Convertir les sections les plus pertinentes en Markdown avec `convert_web_to_markdown`
4. Analyser le contenu et synthétiser l'information
5. Vérifier visuellement certains éléments avec le navigateur intégré si nécessaire

## Cas d'usage avancés

### Veille technologique

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>multi_convert</tool_name>
<arguments>
{
  "urls": [
    {"url": "https://blog.jetbrains.com/idea/category/releases/"},
    {"url": "https://blog.golang.org/"},
    {"url": "https://devblogs.microsoft.com/typescript/"}
  ]
}
</arguments>
</use_mcp_tool>
```

### Analyse de documentation API

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>convert_web_to_markdown</tool_name>
<arguments>
{
  "url": "https://docs.github.com/en/rest/reference"
}
</arguments>
</use_mcp_tool>
```

### Extraction de tutoriels techniques

```
<use_mcp_tool>
<server_name>jinavigator</server_name>
<tool_name>convert_web_to_markdown</tool_name>
<arguments>
{
  "url": "https://www.tensorflow.org/tutorials/keras/classification"
}
</arguments>
</use_mcp_tool>