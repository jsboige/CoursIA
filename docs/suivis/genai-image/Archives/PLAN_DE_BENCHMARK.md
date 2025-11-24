# Plan de Benchmark pour la Performance de Génération Qwen

Ce document décrit le protocole pour mesurer et valider la performance de génération d'images du système ComfyUI + Qwen.

## 1. Objectif

L'objectif est de mesurer de manière fiable le temps de génération "end-to-end" pour un workflow texte-vers-image de base, afin d'établir une performance de référence ("baseline") et de valider l'impact des optimisations futures.

## 2. Workflow de Test

Le benchmark utilisera un workflow ComfyUI standardisé pour assurer la reproductibilité des tests. Le contenu de ce workflow, qui sera sauvegardé dans `scripts/genai-auth/workflow_benchmark.json`, est le suivant :

```json
{
  "prompt": {
    "3": {
      "class_type": "CheckpointLoaderSimple",
      "inputs": {
        "ckpt_name": "Qwen-Image-Edit-2509-FP8/diffusion_pytorch_model.safetensors"
      }
    },
    "6": {
      "class_type": "QwenT2IWrapper",
      "inputs": {
        "model": [
          "3",
          0
        ],
        "prompt": "a beautiful landscape",
        "width": 512,
        "height": 512,
        "steps": 25,
        "cfg_scale": 7.5,
        "negative_prompt": "ugly, blurry, low quality",
        "seed": 42
      }
    },
    "9": {
      "class_type": "SaveImage",
      "inputs": {
        "images": [
          "6",
          0
        ],
        "filename_prefix": "benchmark_qwen"
      }
    }
  }
}
```

**Note importante :** Le chemin `ckpt_name` est une estimation et devra peut-être être ajusté en fonction de la structure exacte du modèle sur le disque.

## 3. Script de Mesure

Un script Python, `scripts/genai-auth/benchmark.py`, sera créé pour automatiser le processus. Sa logique sera la suivante :

1.  **Charger** le fichier `workflow_benchmark.json`.
2.  **Se connecter** à l'API ComfyUI via WebSocket.
3.  **Envoyer** la requête de génération (prompt).
4.  **Démarrer un chronomètre** au moment de l'envoi.
5.  **Attendre** la réception du message "executed" qui contient l'image générée.
6.  **Arrêter le chronomètre**.
7.  **Afficher** le temps écoulé.
8.  **Répéter** l'opération 5 fois et calculer le temps moyen.

## 4. Monitoring

Pendant l'exécution du benchmark, les métriques suivantes seront observées :

*   **Utilisation VRAM** : Pour confirmer que le modèle est entièrement chargé.
*   **Utilisation GPU (%)** : Pour s'assurer que le GPU est pleinement sollicité.
*   **Logs du conteneur** : Pour identifier toute erreur ou étape lente.

## 5. Prochaines Étapes

La prochaine étape consistera à passer en mode "Code" pour :
1.  Créer le fichier `scripts/genai-auth/workflow_benchmark.json`.
2.  Créer le script `scripts/genai-auth/benchmark.py`.
3.  Exécuter le benchmark pour établir la performance de référence.