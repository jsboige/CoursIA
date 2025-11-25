# Analyse et Catégorisation des Scripts `genai-auth`

Ce document présente une analyse détaillée et une catégorisation des scripts situés dans `scripts/genai-auth/` et ses sous-répertoires. L'objectif est de préparer la consolidation de ces scripts dans une structure plus maintenable.

## 1. Scripts à la Racine (`scripts/genai-auth/`)

| Nom du Fichier                       | Type        | Catégorie      | Description                                                                                             | Proposition de Cible        |
| ------------------------------------ | ----------- | -------------- | ------------------------------------------------------------------------------------------------------- | --------------------------- |
| `validate_genai_ecosystem.py`        | Python      | **Validation** | Script principal de validation de l'écosystème (structure, config, API, etc.).                          | `core/validate_ecosystem.py`  |
| `install_comfyui_with_auth.py`       | Python      | **Installation** | Orchestre l'installation complète de ComfyUI avec authentification.                                     | `core/install_comfyui.py`     |
| `diagnose_comfyui_auth.py`           | Python      | **Diagnostic**   | Script de diagnostic complet pour les problèmes d'authentification de ComfyUI.                            | `core/diagnose_auth.py`       |
| `setup-comfyui-auth.ps1`             | PowerShell  | **Lanceur**      | Wrapper PowerShell qui appelle d'autres scripts pour configurer et valider l'authentification.          | `setup_auth.ps1` (à la racine) |
| `sync_comfyui_credentials.py`        | Python      | **Utilitaire**   | Synchronise les identifiants du `.env` vers le conteneur ComfyUI. Tâche atomique et réutilisable.       | `utils/credentials_manager.py` |
| `benchmark.py`                       | Python      | **Performance**  | Mesure les performances de génération d'images et monitore le GPU.                                      | `benchmarks/image_generation.py` |
| `benchmark_container_test.py`        | Python      | **Performance**  | Probablement un test ou une variante du benchmark principal. À analyser.                                | `benchmarks/` ou à fusionner    |
| `benchmark_no_auth.py`               | Python      | **Performance**  | Variante du benchmark sans authentification. À fusionner avec le script principal.                      | Fusionner dans `benchmarks/`    |
| `validate_comfyui_auth_final.py`     | Python      | **Validation**   | Script de validation final, probablement appelé par des lanceurs. À fusionner/intégrer.                   | Fusionner dans `core/`          |
| `run-comfyui-auth-diagnostic.ps1`    | PowerShell  | **Lanceur**      | Lance le script de diagnostic. À conserver comme point d'entrée simple.                               | `run_diagnostic.ps1` (à la racine) |
| `monitor_comfyui_qwen.ps1`           | PowerShell  | **Monitoring**   | Script pour surveiller le service ComfyUI.                                                              | `utils/monitor_service.ps1`   |
| `comfyui-auth-resolution-summary.ps1`| PowerShell  | **Rapport**      | Probablement un script pour générer un résumé. À analyser.                                              | `utils/` ou `reports/`        |
| **Fichiers de données/logs**         | JSON, LOG   | **Données**      | `*.json`, `*.log`. Ne sont pas des scripts.                                                             | À ignorer ou nettoyer         |

## 2. Scripts de Test (`scripts/genai-auth/tests/genai-improvements/`)

Ce répertoire contient des tests, des scripts de débogage et des correctifs ponctuels.

| Nom du Fichier                    | Type     | Catégorie         | Description                                                                    | Proposition de Cible                     |
| --------------------------------- | -------- | ----------------- | ------------------------------------------------------------------------------ | ---------------------------------------- |
| `test_comfyui_client.py`          | Python   | **Test**          | Tests unitaires et d'intégration pour le client ComfyUI.                       | `tests/test_client.py`                   |
| `test_minimal_workflow.py`        | Python   | **Test**          | Test d'intégration d'un workflow minimal pour isoler des bugs.                 | `tests/test_workflow_minimal.py`         |
| `test_qwen_workflow.py`           | Python   | **Test**          | Test d'un workflow Qwen plus complet.                                          | `tests/test_workflow_qwen.py`            |
| `test_simple_connection.py`       | Python   | **Test**          | Test de connexion basique au service ComfyUI.                                  | `tests/test_connection.py`               |
| `inspect_workflow_detailed.py`    | Python   | **Débogage**      | Analyse les connexions d'un workflow pour le débogage.                         | `utils/workflow_inspector.py`            |
| `inspect_nodes_authenticated.py`  | Python   | **Débogage**      | Inspecte les nœuds ComfyUI avec authentification.                              | Fusionner dans `utils/workflow_inspector.py` |
| `inspect_nodes_simple.py`         | Python   | **Débogage**      | Inspecte les nœuds ComfyUI sans authentification.                              | Fusionner dans `utils/workflow_inspector.py` |
| `debug_workflow_error.py`         | Python   | **Débogage**      | Script de débogage pour une erreur de workflow spécifique.                     | `tests/` ou à archiver                 |
| **Scripts Datés**                 | Python   | **Correctif/Dev** | `2025-*.py`. Scripts de développement ou correctifs ponctuels.                 | À archiver (`archive/dev_scripts/`)    |
| `PHASE2_IMPLEMENTATION_REPORT.json`| JSON    | **Données**       | Rapport de données.                                                            | À archiver ou ignorer                    |

## 3. Synthèse et Prochaines Étapes

- **`core/`** : contiendra les points d'entrée principaux : `install`, `validate`, `diagnose`.
- **`utils/`** : contiendra la logique réutilisable : `credentials_manager`, `workflow_inspector`, `comfyui_client`, etc.
- **`benchmarks/`** : contiendra les scripts de mesure de performance.
- **`tests/`** : contiendra tous les scripts de test (`pytest` ou autres).
- **`launchers/` (ou à la racine)** : contiendra les wrappers PowerShell (`.ps1`) pour faciliter l'exécution.
- **`archive/`** : contiendra les scripts de développement datés et les correctifs qui ne sont plus pertinents.

La prochaine étape est de valider cette catégorisation et de passer à la phase de recherche documentaire pour s'assurer que notre plan est cohérent avec l'historique du projet.