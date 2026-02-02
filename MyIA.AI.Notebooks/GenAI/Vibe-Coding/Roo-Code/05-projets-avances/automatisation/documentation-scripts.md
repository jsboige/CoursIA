# 📚 Documentation des Scripts d'Automatisation

Cette documentation détaille le fonctionnement des scripts d'automatisation fournis dans ce module. Ces scripts sont conçus pour démontrer des techniques avancées d'automatisation avec Roo et peuvent être adaptés à vos besoins spécifiques.

## Table des matières

1. [Vue d'ensemble](#vue-densemble)
2. [Architecture des scripts](#architecture-des-scripts)
3. [Script PowerShell (Windows)](#script-powershell-windows)
4. [Script Bash (macOS/Linux)](#script-bash-macoslinux)
5. [Fonctionnalités communes](#fonctionnalités-communes)
6. [Personnalisation et extension](#personnalisation-et-extension)
7. [Bonnes pratiques](#bonnes-pratiques)
8. [Dépannage](#dépannage)

## Vue d'ensemble

Les scripts d'automatisation fournis (`automatisation-windows.ps1` et `automatisation-mac.sh`) implémentent un pipeline de traitement de fichiers complet avec les fonctionnalités suivantes:

- Analyse de différents types de fichiers (TXT, CSV, JSON, XML)
- Transformation et enrichissement des données
- Intégration avec des APIs externes
- Génération de rapports HTML et JSON
- Traitement parallèle pour optimiser les performances
- Logging avancé et gestion des erreurs
- Notifications d'événements

Ces scripts sont conçus pour être modulaires, extensibles et robustes, avec une gestion appropriée des erreurs et des cas limites.

## Architecture des scripts

Les deux scripts partagent une architecture commune organisée en modules fonctionnels:

```
┌─────────────────────┐     ┌─────────────────────┐     ┌─────────────────────┐
│  Configuration      │     │  Traitement         │     │  Rapports           │
│  et initialisation  │ ──> │  de fichiers        │ ──> │  et notifications   │
└─────────────────────┘     └─────────────────────┘     └─────────────────────┘
         │                           │                           │
         │                           │                           │
         ▼                           ▼                           ▼
┌─────────────────────┐     ┌─────────────────────┐     ┌─────────────────────┐
│  Logging et         │     │  Intégration        │     │  Traitement         │
│  gestion d'erreurs  │     │  API externe        │     │  parallèle          │
└─────────────────────┘     └─────────────────────┘     └─────────────────────┘
```

Chaque module est implémenté comme un ensemble de fonctions connexes, ce qui facilite la maintenance et l'extension du code.

## Script PowerShell (Windows)

### Prérequis

- PowerShell 5.1 ou supérieur
- Droits d'administrateur (selon les opérations effectuées)
- Modules optionnels: `ImportExcel` (pour le traitement avancé des fichiers Excel)

### Paramètres

| Paramètre | Type | Description | Obligatoire |
|-----------|------|-------------|-------------|
| ProjectPath | String | Chemin vers le répertoire du projet à traiter | Oui |
| OutputPath | String | Chemin où les résultats seront générés | Oui |
| ApiKey | String | Clé API pour les services externes | Non |
| LogLevel | String | Niveau de détail des logs (Verbose, Info, Warning, Error) | Non |
| MaxThreads | Int | Nombre maximum de threads parallèles à utiliser | Non |
| SendNotifications | Switch | Active l'envoi de notifications par email | Non |

### Utilisation

```powershell
# Utilisation basique
.\automatisation-windows.ps1 -ProjectPath "C:\Projets\MonProjet" -OutputPath "C:\Rapports"

# Utilisation avancée avec tous les paramètres
.\automatisation-windows.ps1 -ProjectPath "C:\Projets\MonProjet" `
                           -OutputPath "C:\Rapports" `
                           -ApiKey "votre-clé-api" `
                           -LogLevel "Verbose" `
                           -MaxThreads 8 `
                           -SendNotifications
```

### Fonctionnalités spécifiques à PowerShell

- Utilisation des runspaces pour le traitement parallèle
- Intégration avec les cmdlets PowerShell pour la manipulation de fichiers
- Support des types de données .NET
- Gestion avancée des erreurs avec try/catch/finally

## Script Bash (macOS/Linux)

### Prérequis

- Bash 4.0 ou supérieur
- Utilitaires standard Unix: `find`, `grep`, `awk`, `sed`
- Dépendances: `jq` (pour le traitement JSON), `bc` (pour les calculs), `curl` (pour les appels API)
- Optionnel: `GNU Parallel` (pour le traitement parallèle optimisé)

### Paramètres

| Paramètre | Description | Obligatoire |
|-----------|-------------|-------------|
| --project-path | Chemin vers le répertoire du projet à traiter | Oui |
| --output-path | Chemin où les résultats seront générés | Oui |
| --api-key | Clé API pour les services externes | Non |
| --log-level | Niveau de détail des logs (verbose, info, warning, error) | Non |
| --max-threads | Nombre maximum de threads parallèles à utiliser | Non |
| --send-notifications | Active l'envoi de notifications | Non |
| --help | Affiche l'aide et quitte | Non |

### Utilisation

```bash
# Utilisation basique
./automatisation-mac.sh --project-path "/Projets/MonProjet" --output-path "/Rapports"

# Utilisation avancée avec tous les paramètres
./automatisation-mac.sh --project-path "/Projets/MonProjet" \
                      --output-path "/Rapports" \
                      --api-key "votre-clé-api" \
                      --log-level "verbose" \
                      --max-threads 8 \
                      --send-notifications
```

### Fonctionnalités spécifiques à Bash

- Utilisation de GNU Parallel pour le traitement parallèle efficace
- Traitement basé sur les flux (pipes) pour une meilleure efficacité
- Compatibilité avec les environnements macOS et Linux
- Verrouillage de fichiers pour les opérations concurrentes

## Fonctionnalités communes

### Pipeline de traitement de fichiers

Les deux scripts implémentent un pipeline de traitement en trois étapes:

1. **Analyse**: Extraction des métadonnées et du contenu des fichiers
   - Détection du type de fichier
   - Extraction des métriques (nombre de lignes, mots, objets)
   - Détection de mots-clés et tagging

2. **Transformation**: Modification du contenu selon des règles configurables
   - Conversion de casse
   - Ajout d'horodatage
   - Calculs sur les données (pour CSV)

3. **Enrichissement**: Ajout d'informations supplémentaires
   - Métadonnées système (utilisateur, machine, environnement)
   - Données externes via API (simulé dans les exemples)

### Intégration API

Les scripts incluent une infrastructure pour l'intégration avec des APIs externes:

- Gestion des en-têtes d'authentification
- Sérialisation/désérialisation JSON
- Mécanisme de retry avec backoff exponentiel
- Gestion des erreurs HTTP

### Génération de rapports

Deux types de rapports sont générés:

1. **Rapport HTML**: Interface utilisateur conviviale
   - Résumé des opérations
   - Tableau détaillé des fichiers traités
   - Mise en forme conditionnelle selon le statut
   - Emplacement pour des graphiques (à implémenter)

2. **Rapport JSON**: Format structuré pour l'intégration
   - Données complètes sur les fichiers traités
   - Métriques d'exécution
   - Configuration utilisée
   - Facilement parsable par d'autres systèmes

### Logging et notifications

Système de logging avancé avec:

- Niveaux de log configurables (Verbose, Info, Warning, Error)
- Horodatage des entrées
- Sortie console colorée
- Fichier de log persistant

Système de notifications (simulé dans les exemples):
- Notifications de début et fin de traitement
- Alertes en cas d'erreurs
- Résumé des opérations effectuées

## Personnalisation et extension

### Ajout de nouveaux types de fichiers

Pour ajouter le support d'un nouveau type de fichier:

1. Modifiez la fonction `Analyze-File` (PowerShell) ou `analyze_file` (Bash)
2. Ajoutez un nouveau cas dans la structure switch/case
3. Implémentez la logique d'extraction des métadonnées et du contenu
4. Ajoutez la transformation correspondante dans `Transform-File`/`transform_file`

Exemple (PowerShell):
```powershell
".yaml" {
    $content = Get-Content -Path $File.FullName -Raw
    $yamlObject = ConvertFrom-Yaml -Yaml $content  # Nécessite le module PowerShell-Yaml
    $result.Metrics.DocumentCount = ($yamlObject | Measure-Object).Count
    $result.Status = "Processed"
}
```

### Intégration avec d'autres services

Pour intégrer un nouveau service API:

1. Utilisez les fonctions `Invoke-ApiRequest` (PowerShell) ou `invoke_api_request` (Bash)
2. Créez une nouvelle fonction wrapper pour votre service
3. Gérez l'authentification et la sérialisation spécifiques au service

Exemple (Bash):
```bash
# Fonction pour appeler l'API OpenWeather
get_weather_data() {
    local city="$1"
    local api_result=$(invoke_api_request "weather?q=$city&units=metric" "GET" "" "true")
    echo "$api_result"
}
```

### Personnalisation des rapports

Pour personnaliser les rapports HTML:

1. Modifiez la fonction `Generate-HtmlReport` (PowerShell) ou `generate_html_report` (Bash)
2. Ajoutez des styles CSS supplémentaires
3. Intégrez des bibliothèques JavaScript pour des visualisations (comme Chart.js)
4. Ajoutez des sections supplémentaires selon vos besoins

## Bonnes pratiques

### Sécurité

- Ne stockez jamais les clés API en dur dans le code
- Utilisez des variables d'environnement ou des coffres-forts sécurisés
- Validez toutes les entrées utilisateur
- Limitez les permissions au minimum nécessaire

### Performance

- Utilisez le traitement parallèle pour les opérations intensives
- Implémentez un mécanisme de cache pour les appels API fréquents
- Limitez la taille des fichiers traités en mémoire
- Utilisez des flux (streams) pour les fichiers volumineux

### Maintenance

- Commentez le code de manière claire et concise
- Utilisez des noms de variables et fonctions descriptifs
- Séparez la logique métier de l'infrastructure
- Implémentez des tests unitaires pour les fonctions critiques

## Dépannage

### Problèmes courants

| Problème | Cause possible | Solution |
|----------|----------------|----------|
| Erreur "Permission denied" | Droits insuffisants | Exécutez le script avec des privilèges élevés |
| Erreur "Command not found" (Bash) | Dépendance manquante | Installez les utilitaires requis (`jq`, `curl`, etc.) |
| Traitement lent | Fichiers volumineux | Augmentez `MaxThreads` ou réduisez la taille des fichiers |
| Erreurs API | Clé API invalide | Vérifiez la validité et les permissions de votre clé API |
| Rapport HTML vide | Erreur de traitement | Vérifiez les logs pour identifier les erreurs |

### Logs de débogage

Pour obtenir des logs détaillés:

- PowerShell: Utilisez `-LogLevel "Verbose"`
- Bash: Utilisez `--log-level "verbose"`

Les logs sont stockés dans le répertoire spécifié par `OutputPath` et peuvent être analysés pour identifier les problèmes.

---

## Conclusion

Ces scripts d'automatisation démontrent des techniques avancées pour le traitement de fichiers, l'intégration API et la génération de rapports. Ils peuvent servir de base pour développer des solutions d'automatisation personnalisées adaptées à vos besoins spécifiques.

Pour toute question ou assistance supplémentaire, consultez la documentation de Roo ou contactez l'équipe de support.