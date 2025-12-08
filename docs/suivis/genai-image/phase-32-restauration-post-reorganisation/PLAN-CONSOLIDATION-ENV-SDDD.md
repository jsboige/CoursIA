# Plan de Consolidation des Fichiers `.env` (SDDD)

## 1. Analyse de la Situation

Actuellement, l'environnement souffre d'une fragmentation des fichiers de configuration `.env`, entraînant des risques d'incohérence des secrets (tokens) et des difficultés de maintenance.

### Fichiers Identifiés
1.  `docker-configurations/services/comfyui-qwen/.env` (Cible Maître)
2.  `docker-configurations/services/comfyui-qwen/.env` (Satellite)
3.  `scripts/docker-configurations/services/comfyui-qwen/.env` (Satellite)
4.  `scripts/docker-configurations/services/comfyui-qwen/.env` (Copie récente du Maître)
5.  `scripts/.env` (Satellite)
6.  `.env` (Racine - Satellite)

### Problèmes Détectés
*   **Duplication** : Les mêmes clés (`COMFYUI_API_TOKEN`, `COMFYUI_BEARER_TOKEN`) existent avec des valeurs potentiellement différentes.
*   **Nomenclature** : Utilisation incohérente des noms de variables (`COMFYUI_API_TOKEN` vs `COMFYUI_BEARER_TOKEN`).
*   **Dépendances Hardcodées** : De nombreux scripts pointent vers des chemins spécifiques, rendant la suppression simple risquée.

## 2. Stratégie de Consolidation

L'objectif est d'avoir **une seule source de vérité** tout en maintenant la compatibilité avec les scripts existants via des liens symboliques.

### 2.1. Définition du Maître
Le fichier **`docker-configurations/services/comfyui-qwen/.env`** est désigné comme le **Fichier Maître**.
Il doit contenir l'union de toutes les clés nécessaires.

**Actions :**
*   Fusionner les clés uniques des satellites vers le Maître.
*   Standardiser les noms : `COMFYUI_API_TOKEN` sera un alias de `COMFYUI_BEARER_TOKEN` si nécessaire pour la compatibilité.

### 2.2. Gestion des Satellites (Symlinks)
Pour éviter de casser les scripts existants, les fichiers satellites seront remplacés par des **liens symboliques** (symlinks) pointant vers le Maître.

*   `.env` (Racine) -> `docker-configurations/services/comfyui-qwen/.env`
*   `scripts/.env` -> `../docker-configurations/services/comfyui-qwen/.env`
*   `docker-configurations/services/comfyui-qwen/.env` -> `../services/comfyui-qwen/.env`

*Note : Sous Windows, les symlinks nécessitent des privilèges ou le mode développeur. Si impossible, une copie synchronisée par script sera utilisée comme fallback, mais le symlink est privilégié.*

### 2.3. Mise à jour des Scripts Critiques
Les scripts suivants doivent être audités et potentiellement corrigés pour suivre les symlinks ou pointer directement vers le Maître :
*   `scripts/genai-auth/setup-comfyui-auth.ps1`
*   `scripts/genai-auth/utils/token_synchronizer.py`
*   `scripts/genai-auth/utils/reconstruct_env.py`

## 3. Plan d'Exécution (Mode Code)

1.  **Sauvegarde** : Créer une archive de tous les `.env` actuels.
2.  **Unification** :
    *   Lire le contenu du Maître actuel.
    *   Ajouter les clés manquantes (`COMFYUI_RAW_TOKEN`, etc.) provenant des satellites.
    *   Écrire le nouveau contenu dans le Maître.
3.  **Bascule** :
    *   Supprimer les fichiers satellites.
    *   Créer les liens symboliques.
4.  **Validation** :
    *   Vérifier que les scripts critiques accèdent bien aux variables.
    *   Vérifier que Docker compose charge bien le fichier.

## 4. Critères de Succès
*   Un seul fichier `.env` physique existe.
*   Tous les emplacements précédents sont des symlinks valides.
*   Les scripts de démarrage et d'authentification fonctionnent sans erreur.
*   Aucune perte de clé API ou de configuration.