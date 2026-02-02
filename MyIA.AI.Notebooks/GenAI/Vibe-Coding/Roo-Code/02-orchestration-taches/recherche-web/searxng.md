# 🔎 Utilisation de SearXNG pour les Recherches Web

## Introduction

SearXNG est un moteur de recherche méta privé et open-source qui agrège les résultats de plusieurs moteurs de recherche tout en respectant la vie privée des utilisateurs. Dans Roo, SearXNG est disponible comme MCP (Model Context Protocol) et permet d'effectuer des recherches web pour obtenir des informations actualisées.

## Fonctionnalités principales

- **Agrégation de résultats** : Combine les résultats de plusieurs moteurs de recherche
- **Respect de la vie privée** : Ne stocke pas d'informations personnelles
- **Filtrage temporel** : Permet de limiter les résultats à une période spécifique
- **Recherche multilingue** : Supporte les requêtes dans différentes langues
- **Personnalisation** : Options pour affiner les recherches

## Utilisation de base

L'outil principal de SearXNG dans Roo est `searxng_web_search`, accessible via le MCP :

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "votre requête de recherche",
  "pageno": 1,
  "time_range": "",
  "language": "all",
  "safesearch": "0"
}
</arguments>
</use_mcp_tool>
```

### Paramètres disponibles

| Paramètre | Description | Valeurs possibles | Défaut |
|-----------|-------------|-------------------|--------|
| `query` | Texte de la recherche | Chaîne de caractères | (Requis) |
| `pageno` | Numéro de page des résultats | Nombre entier ≥ 1 | 1 |
| `time_range` | Période de recherche | "", "day", "month", "year" | "" (tous) |
| `language` | Langue des résultats | Code de langue ("fr", "en", etc.) ou "all" | "all" |
| `safesearch` | Niveau de filtrage du contenu | "0" (aucun), "1" (modéré), "2" (strict) | "0" |

## Lecture du contenu des URLs

En complément de la recherche, SearXNG propose l'outil `web_url_read` pour extraire le contenu d'une URL spécifique :

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>web_url_read</tool_name>
<arguments>
{
  "url": "https://exemple.com/page"
}
</arguments>
</use_mcp_tool>
```

Cet outil est utile pour approfondir l'analyse d'une page web identifiée lors d'une recherche.

## Exemples d'utilisation

### Exemple 1 : Recherche d'actualités récentes

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "dernières avancées intelligence artificielle",
  "time_range": "month",
  "language": "fr"
}
</arguments>
</use_mcp_tool>
```

Cette requête recherchera les informations sur les avancées en IA publiées au cours du dernier mois, en français.

### Exemple 2 : Recherche technique avec lecture approfondie

```
# Étape 1 : Recherche initiale
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "python asyncio tutorial best practices"
}
</arguments>
</use_mcp_tool>

# Étape 2 : Lecture d'une page pertinente identifiée dans les résultats
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>web_url_read</tool_name>
<arguments>
{
  "url": "https://realpython.com/async-io-python/"
}
</arguments>
</use_mcp_tool>
```

### Exemple 3 : Recherche multilingue avec pagination

```
# Page 1 des résultats
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "frameworks javascript comparaison",
  "pageno": 1,
  "language": "fr"
}
</arguments>
</use_mcp_tool>

# Page 2 des résultats (si nécessaire)
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "frameworks javascript comparaison",
  "pageno": 2,
  "language": "fr"
}
</arguments>
</use_mcp_tool>
```

## Bonnes pratiques

### Formulation des requêtes

1. **Soyez précis** : Utilisez des termes spécifiques plutôt que génériques
   - ✅ "React hooks useEffect dépendances"
   - ❌ "React tutoriel"

2. **Utilisez des opérateurs** : Affinez vos recherches avec des opérateurs
   - `"phrase exacte"` : Recherche une expression exacte
   - `site:exemple.com` : Limite la recherche à un site spécifique
   - `filetype:pdf` : Recherche un type de fichier spécifique

3. **Limitez la période** : Utilisez `time_range` pour des informations récentes
   - Particulièrement utile pour les technologies qui évoluent rapidement

### Optimisation des performances

- Commencez par des requêtes générales, puis affinez progressivement
- Utilisez la pagination (`pageno`) pour explorer plus de résultats
- Combinez `searxng_web_search` et `web_url_read` pour une analyse approfondie

### Limitations

- Les résultats peuvent varier selon la disponibilité des moteurs de recherche
- Certains sites peuvent bloquer l'accès à SearXNG
- Le contenu dynamique peut ne pas être correctement extrait par `web_url_read`
- Les résultats sont limités en nombre par requête

## Intégration avec le mode Orchestrator

Le mode Orchestrator peut utiliser SearXNG comme première étape d'un workflow de recherche :

1. Effectuer une recherche générale avec SearXNG pour identifier des sources pertinentes
2. Extraire le contenu détaillé des pages les plus prometteuses avec `web_url_read` ou Jinavigator
3. Vérifier visuellement certaines informations avec le navigateur intégré si nécessaire
4. Synthétiser les informations recueillies pour répondre à la question initiale

## Cas d'usage avancés

### Veille technologique

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "site:github.com new framework javascript 2025",
  "time_range": "month"
}
</arguments>
</use_mcp_tool>
```

### Recherche académique

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "filetype:pdf \"machine learning\" \"computer vision\" 2024 research",
  "language": "en"
}
</arguments>
</use_mcp_tool>
```

### Résolution de problèmes techniques

```
<use_mcp_tool>
<server_name>searxng</server_name>
<tool_name>searxng_web_search</tool_name>
<arguments>
{
  "query": "site:stackoverflow.com \"TypeError: Cannot read property of undefined\" React useEffect",
  "language": "en"
}
</arguments>
</use_mcp_tool>
```

## Comparaison avec les autres outils de recherche

| Fonctionnalité | SearXNG | Navigateur intégré | Jinavigator |
|----------------|---------|-------------------|-------------|
| Vitesse | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| Diversité des sources | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| Analyse approfondie | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| Interaction | ❌ | ⭐⭐⭐⭐⭐ | ❌ |
| Extraction structurée | ⭐⭐ | ❌ | ⭐⭐⭐⭐⭐ |

SearXNG est idéal pour la phase initiale de recherche, tandis que les autres outils sont plus adaptés pour l'analyse approfondie de sources spécifiques.