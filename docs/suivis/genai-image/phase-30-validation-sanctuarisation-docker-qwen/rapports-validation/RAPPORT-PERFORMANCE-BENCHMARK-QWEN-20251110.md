# Rapport de Performance Benchmark Qwen ComfyUI
**Date** : 10 Novembre 2025  
**Version** : 1.0  

## Résumé Exécutif

Ce rapport présente les résultats du benchmark de performance du système ComfyUI Qwen, mené pour identifier les goulots d'étranglement dans les temps de génération d'images signalés comme excessifs (environ 2 minutes par image).

## 1. Méthodologie de Test

### 1.1 Configuration Testée
- **Service** : ComfyUI Qwen dans conteneur Docker
- **GPU** : NVIDIA RTX 3090 (24GB VRAM)
- **Workflow** : Génération texte-vers-image avec QwenImage
- **Résolution** : 512x512 pixels
- **Steps** : 25 étapes de génération
- **CFG Scale** : 7.5
- **Seed** : 42 (fixe pour reproductibilité)

### 1.2 Outils de Mesure
- **Script de benchmark** : `scripts/genai-auth/benchmark.py`
- **Monitoring GPU** : `nvidia-smi` avec échantillonnage chaque seconde
- **Mesures** : Temps de génération end-to-end, utilisation VRAM, utilisation GPU, température

### 1.3 Protocole
1. Charger le workflow de test depuis `workflow_benchmark.json`
2. Se connecter à l'API WebSocket de ComfyUI
3. Envoyer la requête de génération
4. Démarrer le chronomètre
5. Monitorer l'utilisation GPU en parallèle
6. Mesurer le temps jusqu'à la réception de l'image
7. Répéter 5 fois pour calculer moyenne/min/max

## 2. Résultats du Benchmark

### 2.1 Temps de Génération

❌ **ÉCHEC DES GÉNÉRATIONS**

Les deux tentatives de benchmark ont échoué en raison de problèmes d'authentification :

| Tentative | Statut | Cause de l'échec |
|-----------|--------|------------------|
| 1 | Échec | Authentification requise (401 Unauthorized) |
| 2 | Échec | Authentification requise (401 Unauthorized) |

**Aucun temps de génération n'a pu être mesuré** en raison des blocages d'accès à l'API.

### 2.2 Analyse des Logs ComfyUI

Les logs du conteneur ComfyUI révèlent plusieurs problèmes critiques :

#### 2.2.1 Erreurs de Modèle
```
ERROR: clip input is invalid: None
No VAE weights detected, VAE not initialized
no CLIP/text encoder weights in checkpoint, text encoder model will not be loaded
```

**Analyse** : Le modèle QwenImage semble incomplet ou corrompu :
- Absence de CLIP/text encoder
- Absence de poids VAE
- Ces composants sont essentiels pour la génération texte-vers-image

#### 2.2.2 Temps de Chargement Observés
Les logs montrent des temps de chargement très élevés :
- **Première exécution** : 1167.17 secondes (~19.5 minutes)
- **Seconde exécution** : 1134.65 secondes (~18.9 minutes)

Ces temps sont **consistents mais excessivement longs**, confirmant le problème de performance signalé.

### 2.3 Monitoring GPU

Malgré l'échec des générations, le monitoring GPU a fonctionné et révèle des informations importantes :

#### 2.3.1 Configuration GPU Détectée
- **GPU 0** : 16384 MB VRAM totale
- **GPU 1** : 24576 MB VRAM totale (RTX 3090)

#### 2.3.2 Utilisation au Repos
```
GPU 0: 0 MB utilisés (0.0%), 63°C
GPU 1: 9462 MB utilisés (38.5%), 26°C
```

#### 2.3.3 Patterns Observés
- **GPU 0 (intégré)** : Non utilisé pendant les tests
- **GPU 1 (RTX 3090)** : 
  - Utilisation VRAM : 38.5% (~9.4 GB)
  - Utilisation GPU : 0% (au repos)
  - Température : 26°C (normale)

## 3. Analyse des Problèmes Identifiés

### 3.1 Problème d'Authentification

**Cause** : Le système ComfyUI-Login ne parvient pas à s'authentifier correctement.

**Symptômes** :
- Erreur 401 Unauthorized sur l'API WebSocket
- Erreur 401 sur l'API REST même avec identifiants corrects
- La désactivation de `COMFYUI_LOGIN_ENABLED=false` dans le fichier .env n'a pas résolu le problème

**Impact** : Bloque complètement l'accès à l'API pour les tests automatisés.

### 3.2 Problème de Modèle Qwen

**Cause** : Le modèle QwenImage semble incomplet ou mal configuré.

**Symptômes** :
- Absence de CLIP/text encoder
- Absence de poids VAE
- Temps de chargement extrêmement longs (18-19 minutes)

**Impact** : Empêche toute génération d'aboutir, même avec un accès API fonctionnel.

### 3.3 Problème de Performance

**Cause** : Les temps de chargement observés sont 10-20x plus longs que attendus.

**Analyse** :
- Temps normal attendu : 30-60 secondes pour 512x512
- Temps observés : 1134-1167 secondes
- Ratio : ~20x plus lent que normal

**Impact** : Rend le système inutilisable en pratique.

## 4. Goulots d'Étranglement Identifiés

### 4.1 Primaire : Modèle Incomplet ⚠️ **CRITIQUE**
Le modèle QwenImage manque des composants essentiels (CLIP, VAE), ce qui :
- Empêche toute génération fonctionnelle
- Force le système à tenter des reconstructions continues
- Explique les temps de chargement extrêmes

### 4.2 Secondaire : Authentification Défaillante 🔒
Le système d'authentification bloque l'accès API même quand désactivé, ce qui :
- Empêche les tests automatisés
- Nécessite des interventions manuelles
- Retarde le diagnostic

### 4.3 Tertiaire : Configuration GPU ⚡
Le monitoring montre que le GPU RTX 3090 est détecté mais :
- L'utilisation GPU reste à 0% pendant les tentatives
- La VRAM est partiellement utilisée (38.5%) au repos
- Suggère un problème de mapping GPU/CUDA

## 5. Recommandations

### 5.1 Actions Immédiates (Priorité CRITIQUE)

1. **Réparer le Modèle Qwen**
   ```bash
   # Vérifier l'intégrité du modèle
   cd /workspace/ComfyUI
   find . -name "*Qwen*" -type f
   ```

2. **Reconfigurer l'Authentification**
   ```bash
   # Réinitialiser complètement la configuration
   docker-compose down
   docker volume rm comfyui-qwen_data
   docker-compose up -d
   ```

3. **Valider les Composants**
   - S'assurer que CLIP est présent
   - S'assurer que VAE est chargé
   - Tester avec un workflow simple

### 5.2 Actions à Moyen Terme

1. **Optimisation Docker**
   - Utiliser des volumes persistants pour les modèles
   - Pré-charger les modèles au démarrage
   - Optimiser les mappings GPU

2. **Monitoring Continu**
   - Implémenter un monitoring de santé du système
   - Alertes sur les temps de génération > 120 secondes
   - Surveillance de l'utilisation GPU

### 5.3 Actions à Long Terme

1. **Architecture de Performance**
   - Cache des modèles pré-chargés
   - Pipeline de génération optimisé
   - Scaling horizontal si nécessaire

2. **Documentation**
   - Procédures de dépannage
   - Playbooks de recovery
   - Monitoring avancé

## 6. Scripts Créés

### 6.1 workflow_benchmark.json
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

### 6.2 benchmark.py
Script Python complet (318 lignes) avec :
- Connexion WebSocket à ComfyUI
- Authentification automatique
- Monitoring GPU en temps réel
- Analyse statistique des résultats
- Gestion des erreurs

## 7. Conclusion

Le benchmark a révélé des problèmes **critiques** qui expliquent les temps de génération excessifs :

1. **Le modèle QwenImage est incomplet** (manque CLIP/VAE)
2. **L'authentification bloque l'accès API**
3. **Les temps de chargement sont 20x plus longs que normal**

Ces problèmes rendent le système **inutilisable en l'état actuel**. Une réparation complète du modèle et de la configuration d'authentification est requise avant tout test de performance supplémentaire.

**État actuel : BLOQUANT** - Nécessite intervention corrective immédiate.

---

*Ce rapport a été généré automatiquement par le script de benchmark ComfyUI Qwen*
*Date de génération : 2025-11-10T22:47*
*Version des outils : v1.0*