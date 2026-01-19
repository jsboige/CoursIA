# 🔐 GenAI Auth & Management Scripts

Ce répertoire contient les outils centralisés pour gérer l'infrastructure GenAI (ComfyUI, Forge, Qwen) avec une authentification sécurisée et une validation rigoureuse.

## 📁 Structure Simplifiée

La structure a été rationalisée pour plus de clarté et de maintenabilité.

```
scripts/genai-auth/
├── manage-genai.ps1        # 🚀 Point d'entrée unique (CLI PowerShell)
├── docker_manager.py       # 🐳 Gestionnaire central Docker (Cycle de vie, Maintenance)
├── validation_suite.py     # ✅ Suite de validation unifiée (Auth, Nodes, Génération)
├── core/                   # 🧱 Librairies Core
│   ├── auth_manager.py     # Gestion de l'authentification (Tokens, Hashing)
│   └── comfyui_client.py   # Client API ComfyUI unifié
├── config/                 # ⚙️ Configuration (Modèles, Nodes, Tokens)
├── utils/                  # 🛠️ Utilitaires divers et legacy
└── archive/                # 📦 Scripts obsolètes ou archivés
```

## 🚀 Utilisation Rapide (`manage-genai.ps1`)

Le script `manage-genai.ps1` est le point d'entrée recommandé. Il encapsule toutes les commandes Python complexes.

### Commandes Principales

| Commande | Description |
| :--- | :--- |
| **`Setup`** | Initialise l'environnement : installe les dépendances, télécharge les modèles, configure les secrets. |
| **`Start`** | Démarre les services Docker (ComfyUI, Forge). |
| **`Stop`** | Arrête les services proprement. |
| **`Restart`** | Redémarre les services. |
| **`Validate`** | Lance la suite de validation complète (Santé, Auth, Nodes, Test Génération). |
| **`Sync`** | Synchronise les credentials entre l'hôte et les conteneurs. |
| **`Logs`** | Affiche les logs des conteneurs. |
| **`Status`** | Affiche l'état des services et l'utilisation GPU. |

### Exemples

```powershell
# Démarrer l'environnement
./manage-genai.ps1 Start

# Valider que tout fonctionne (Auth + Nodes + Test Image)
./manage-genai.ps1 Validate

# Réinstaller les dépendances et modèles manquants
./manage-genai.ps1 Setup

# Voir les logs en temps réel
./manage-genai.ps1 Logs -Tail 100
```

## 🛠️ Scripts Python Core

Si vous devez utiliser les scripts Python directement (débuggage avancé) :

### `docker_manager.py`
Gestionnaire d'infrastructure.
```bash
python docker_manager.py status
python docker_manager.py setup comfyui-qwen
python docker_manager.py validate
```

### `validation_suite.py`
Suite de tests.
```bash
python validation_suite.py --full       # Tout tester
python validation_suite.py --auth-only  # Tester seulement l'auth
python validation_suite.py --nodes-only # Tester seulement les custom nodes
```

## 📦 Archivage (Consolidation 2025-12-12)

Les anciens scripts dispersés (`diagnostic_manager.py`, `validate_all_models.py`, `verify_image_content.py`, etc.) ont été consolidés ou déplacés dans `archive/consolidated_20251212/` pour garder la racine propre.

---
*Dernière mise à jour : 2025-12-13*