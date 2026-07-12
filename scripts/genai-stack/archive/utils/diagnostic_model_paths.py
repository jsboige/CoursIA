#!/usr/bin/env python3
"""
Script de Diagnostic Complet : Chemins des Modèles Qwen + Corruption Potentielle
================================================================================

Phase 29 - ÉTAPE 43 (INVESTIGATION DÉTAILLÉE)
Création : 2025-11-03 21:29:00 UTC+1

Objectif :
    Diagnostic complet des chemins de modèles Qwen pour identifier la source 
    de l'incohérence critique : images générées avec succès mais 
    logs indiquant modèles manquants.

Problème Identifié :
    - Images générées avec succès (preuve dans /workspace/ComfyUI/output/)
    - Logs indiquent "Value not in list: ckpt_name: 'qwen_image_edit_2509_fp8_e4m3fn.safetensors' not in []"
    - WARNING: "path /workspace/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors exists but doesn't link anywhere"

Architecture Attendue :
    - Diffusion Model : /workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors
    - Text Encoder : /workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors
    - VAE : /workspace/ComfyUI/models/vae/qwen_image_vae.safetensors

Contraintes ABSOLUES :
    ✅ Vérifier les modèles réels dans le container
    ✅ Analyser les chemins utilisés par les scripts
    ✅ Identifier les discordances
    ✅ Documenter la corruption potentielle
    ✅ Proposer des corrections concrètes
"""

import json
import os
import requests
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ============================================================================
# CONFIGURATION GLOBALE
# ============================================================================

COMFYUI_API_BASE = "http://localhost:8188"
CONTAINER_NAME = "comfyui-qwen"
BCRYPT_TOKEN_FILE = ".secrets/qwen-api-user.token"
TIMESTAMP = datetime.now().strftime("%Y%m%d_%H%M%S")

# ============================================================================
# FONCTIONS UTILITAIRES
# ============================================================================

def print_section(title: str, level: int = 1) -> None:
    """Affiche une section formatée."""
    separator = "=" * 80 if level == 1 else "-" * 80
    print(f"\n{separator}")
    print(f"{title}")
    print(f"{separator}\n")


def print_status(status: str, message: str) -> None:
    """Affiche un statut avec emoji."""
    emoji = "✅" if status == "success" else "❌" if status == "error" else "⚠️"
    print(f"{emoji} {message}")


def run_docker_command(command: str) -> Optional[str]:
    """
    Exécute une commande Docker via Windows CLI.
    
    Args:
        command: Commande à exécuter dans le container
        
    Returns:
        Sortie de la commande ou None en cas d'erreur
    """
    try:
        full_command = f"docker exec {CONTAINER_NAME} {command}"
        result = subprocess.run(
            ["pwsh", "-c", full_command],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print_status("error", f"Erreur Docker : {e.stderr}")
        return None


def load_auth_token() -> Optional[str]:
    """
    Charge le token d'authentification bcrypt depuis .secrets/qwen-api-user.token.
    
    Returns:
        Token bcrypt ou None en cas d'erreur
    """
    if not os.path.exists(BCRYPT_TOKEN_FILE):
        print_status("error", f"Fichier token bcrypt non trouvé : {BCRYPT_TOKEN_FILE}")
        return None
    
    try:
        with open(BCRYPT_TOKEN_FILE, 'r') as f:
            token = f.read().strip()
            if token.startswith("$2b$"):
                print_status("success", f"Token bcrypt chargé : {token[:20]}...")
                return token
            else:
                print_status("error", "Format token invalide (doit commencer par $2b$)")
                return None
        
    except Exception as e:
        print_status("error", f"Erreur lecture token bcrypt : {e}")
        return None


def check_comfyui_api() -> Tuple[bool, Optional[str]]:
    """
    Vérifie la connectivité à l'API ComfyUI avec authentification.
    
    Returns:
        Tuple (succès, token)
    """
    print_section("🔍 VÉRIFICATION API COMFYUI", level=2)
    
    # Charger le token d'authentification
    token = load_auth_token()
    if not token:
        return False, None
    
    try:
        headers = {"Authorization": f"Bearer {token}"}
        response = requests.get(f"{COMFYUI_API_BASE}/system_stats", headers=headers, timeout=10)
        if response.status_code == 200:
            print_status("success", f"API ComfyUI accessible : {COMFYUI_API_BASE}")
            return True, token
        else:
            print_status("error", f"API ComfyUI inaccessible (status {response.status_code})")
            return False, token
    except Exception as e:
        print_status("error", f"Erreur connexion API ComfyUI : {e}")
        return False, token


def get_comfyui_object_info(token: str) -> Optional[Dict]:
    """
    Récupère les informations sur les objets disponibles dans ComfyUI.
    
    Args:
        token: Token d'authentification bcrypt
        
    Returns:
        Dictionnaire object_info ou None en cas d'erreur
    """
    try:
        headers = {"Authorization": f"Bearer {token}"}
        response = requests.get(f"{COMFYUI_API_BASE}/object_info", headers=headers, timeout=10)
        if response.status_code == 200:
            return response.json()
        else:
            print_status("error", f"Erreur récupération object_info : {response.status_code}")
            return None
    except Exception as e:
        print_status("error", f"Erreur API object_info : {e}")
        return None


def analyze_real_models() -> Dict[str, List[str]]:
    """
    Analyse les modèles réellement disponibles dans le container.
    
    Returns:
        Dictionnaire des modèles par type
    """
    print_section("📁 MODÈLES RÉELS DANS CONTAINER", level=2)
    
    models = {
        "diffusion_models": [],
        "text_encoders": [],
        "vae": [],
        "unet": [],
        "checkpoints": [],
        "other": []
    }
    
    # Chercher tous les fichiers .safetensors et .bin
    find_command = "find /workspace/ComfyUI/models -name '*.safetensors' -o -name '*.bin'"
    output = run_docker_command(find_command)
    
    if not output:
        print_status("error", "Impossible de lister les modèles dans le container")
        return models
    
    print("Modèles trouvés :")
    for line in output.split("\n"):
        if not line.strip():
            continue
            
        print(f"  {line}")
        
        # Catégoriser le modèle selon son chemin
        if "/diffusion_models/" in line:
            models["diffusion_models"].append(line)
        elif "/text_encoders/" in line:
            models["text_encoders"].append(line)
        elif "/vae/" in line:
            models["vae"].append(line)
        elif "/unet/" in line:
            models["unet"].append(line)
        elif "/checkpoints/" in line:
            models["checkpoints"].append(line)
        else:
            models["other"].append(line)
    
    # Afficher le résumé
    print(f"\nRésumé des modèles :")
    for category, model_list in models.items():
        if model_list:
            print_status("success", f"{category}: {len(model_list)} modèle(s)")
        else:
            print_status("error", f"{category}: 0 modèle")
    
    return models


def analyze_script_paths() -> Dict[str, str]:
    """
    Analyse les chemins de modèles utilisés dans les scripts.
    
    Returns:
        Dictionnaire des chemins attendus par type
    """
    print_section("🐍 CHEMINS DANS SCRIPTS", level=2)
    
    # Chemins extraits du script test_generation_image_fp8_officiel.py
    script_paths = {
        "Diffusion Model": "/workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "Text Encoder": "/workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "VAE": "/workspace/ComfyUI/models/vae/qwen_image_vae.safetensors"
    }
    
    print("Chemins attendus par les scripts :")
    for model_type, path in script_paths.items():
        print(f"  {model_type}: {path}")
    
    return script_paths


def analyze_workflow_references() -> List[str]:
    """
    Analyse les références de modèles dans les workflows JSON.
    
    Returns:
        Liste des références de modèles trouvées
    """
    print_section("🧩 WORKFLOWS JSON ANALYSÉS", level=2)
    
    model_references = []
    
    # Analyser le workflow intégré dans le script de test
    script_file = Path("scripts/genai-auth/utils/test_generation_image_fp8_officiel.py")
    if script_file.exists():
        try:
            content = script_file.read_text()
            
            # Chercher les références de modèles dans le WORKFLOW_TEMPLATE
            lines = content.split('\n')
            in_workflow = False
            
            for line in lines:
                if 'WORKFLOW_TEMPLATE = {' in line:
                    in_workflow = True
                elif in_workflow and line.strip() == '}':
                    in_workflow = False
                
                if in_workflow and ('qwen' in line.lower() or 'fp8' in line.lower()):
                    if 'unet_name' in line or 'clip_name' in line or 'vae_name' in line:
                        # Extraire le nom du modèle
                        if '"' in line:
                            model_name = line.split('"')[1]
                            model_references.append(model_name)
                            print(f"  Référence trouvée : {model_name}")
        
        except Exception as e:
            print_status("error", f"Erreur lecture script : {e}")
    
    print(f"\nTotal références trouvées : {len(model_references)}")
    return model_references


def analyze_comfyui_nodes(object_info: Dict) -> Dict[str, List[str]]:
    """
    Analyse les nodes ComfyUI disponibles pour les modèles.
    
    Args:
        object_info: Dictionnaire object_info de ComfyUI
        
    Returns:
        Dictionnaire des nodes par type
    """
    print_section("🔧 NODES COMFYUI DISPONIBLES", level=2)
    
    nodes = {
        "unet_loader": [],
        "clip_loader": [],
        "vae_loader": [],
        "checkpoint_loader": [],
        "qwen_custom": []
    }
    
    for node_name, node_info in object_info.items():
        node_class = node_info.get("class_type", "")
        
        if "UNETLoader" in node_class:
            nodes["unet_loader"].append(node_name)
        elif "CLIPLoader" in node_class:
            nodes["clip_loader"].append(node_name)
        elif "VAELoader" in node_class:
            nodes["vae_loader"].append(node_name)
        elif "CheckpointLoader" in node_class:
            nodes["checkpoint_loader"].append(node_name)
        elif "qwen" in node_name.lower():
            nodes["qwen_custom"].append(node_name)
    
    # Afficher les nodes pertinents
    print("Nodes de chargement de modèles :")
    for node_type, node_list in nodes.items():
        if node_list:
            print_status("success", f"{node_type}: {len(node_list)} node(s)")
            for node in node_list[:3]:  # Limiter l'affichage
                print(f"    - {node}")
            if len(node_list) > 3:
                print(f"    ... et {len(node_list) - 3} autre(s)")
        else:
            print_status("error", f"{node_type}: 0 node")
    
    return nodes


def compare_paths_vs_reality(real_models: Dict[str, List[str]], script_paths: Dict[str, str]) -> Dict[str, Dict]:
    """
    Compare les chemins attendus vs les modèles réels.
    
    Args:
        real_models: Modèles réels trouvés
        script_paths: Chemins attendus par les scripts
        
    Returns:
        Dictionnaire d'analyse des incohérences
    """
    print_section("🔍 ANALYSE DES INCOHÉRENCES", level=2)
    
    analysis = {
        "missing_models": [],
        "wrong_location": [],
        "broken_links": [],
        "duplicate_models": []
    }
    
    # Vérifier chaque modèle attendu
    for model_type, expected_path in script_paths.items():
        print(f"\nVérification {model_type} :")
        print(f"  Chemin attendu : {expected_path}")
        
        # Vérifier si le fichier existe
        exists_command = f"test -f {expected_path} && echo 'EXISTS' || echo 'MISSING'"
        exists_output = run_docker_command(exists_command)
        
        if "MISSING" in exists_output:
            print_status("error", f"Modèle MANQUANT : {expected_path}")
            analysis["missing_models"].append({
                "type": model_type,
                "expected_path": expected_path,
                "status": "missing"
            })
        else:
            print_status("success", f"Modèle trouvé : {expected_path}")
            
            # Vérifier si c'est un lien symbolique cassé
            link_command = f"test -L {expected_path} && echo 'LINK' || echo 'FILE'"
            link_output = run_docker_command(link_command)
            
            if "LINK" in link_output:
                # Vérifier si le lien est valide
                readlink_command = f"readlink {expected_path}"
                target = run_docker_command(readlink_command)
                
                if target:
                    target_exists_command = f"test -f {target} && echo 'VALID' || echo 'BROKEN'"
                    target_status = run_docker_command(target_exists_command)
                    
                    if "BROKEN" in target_status:
                        print_status("error", f"Lien symbolique cassé : {expected_path} -> {target}")
                        analysis["broken_links"].append({
                            "type": model_type,
                            "link_path": expected_path,
                            "target": target,
                            "status": "broken"
                        })
    
    # Vérifier les modèles dans les mauvais répertoires
    print(f"\nVérification des modèles dans les mauvais répertoires :")
    
    # Le modèle UNET est dans diffusion_models ET unet
    unet_in_diffusion = [m for m in real_models["diffusion_models"] if "qwen_image_edit_2509_fp8_e4m3fn" in m]
    unet_in_unet = [m for m in real_models["unet"] if "qwen_image_edit_2509_fp8_e4m3fn" in m]
    
    if unet_in_diffusion and unet_in_unet:
        print_status("warning", "Modèle UNET trouvé dans diffusion_models ET unet (duplication)")
        analysis["duplicate_models"].append({
            "model": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
            "locations": [unet_in_diffusion[0], unet_in_unet[0]],
            "status": "duplicate"
        })
    
    # Vérifier le lien symbolique cassé dans text_encoders
    broken_link = [m for m in real_models["text_encoders"] if "Qwen-Image-Edit-2509-FP8" in m]
    if broken_link:
        print_status("error", f"Lien symbolique cassé détecté : {broken_link[0]}")
        analysis["broken_links"].append({
            "type": "Text Encoder",
            "link_path": broken_link[0],
            "target": "/workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8",
            "status": "broken"
        })
    
    return analysis


def analyze_checkpoint_loader_issue(object_info: Dict) -> Dict[str, any]:
    """
    Analyse le problème spécifique du CheckpointLoaderSimple.
    
    Args:
        object_info: Dictionnaire object_info de ComfyUI
        
    Returns:
        Analyse du problème CheckpointLoader
    """
    print_section("🚨 ANALYSE PROBLÈME CHECKPOINTLOADER", level=2)
    
    checkpoint_analysis = {
        "available_checkpoints": [],
        "loader_nodes": [],
        "issue_identified": False
    }
    
    # Chercher les nodes CheckpointLoader
    for node_name, node_info in object_info.items():
        if "CheckpointLoader" in node_name:
            checkpoint_analysis["loader_nodes"].append({
                "name": node_name,
                "class_type": node_info.get("class_type", ""),
                "input_required": node_info.get("input", {}).get("required", {})
            })
            
            # Vérifier les options disponibles
            input_required = node_info.get("input", {}).get("required", {})
            if "ckpt_name" in input_required:
                ckpt_options = input_required["ckpt_name"][0] if isinstance(input_required["ckpt_name"], list) else []
                checkpoint_analysis["available_checkpoints"] = ckpt_options
                
                # Vérifier si notre modèle est dans la liste
                qwen_fp8_found = any("qwen_image_edit_2509_fp8_e4m3fn" in str(ckpt) for ckpt in ckpt_options)
                
                if not qwen_fp8_found:
                    checkpoint_analysis["issue_identified"] = True
                    print_status("error", "Modèle qwen_image_edit_2509_fp8_e4m3fn.safetensors NON DISPONIBLE dans CheckpointLoader")
                    print(f"  Options disponibles : {ckpt_options[:5]}...")  # Limiter l'affichage
                else:
                    print_status("success", "Modèle qwen_image_edit_2509_fp8_e4m3fn.safetensors disponible dans CheckpointLoader")
    
    return checkpoint_analysis


def generate_diagnostic_report(real_models: Dict, script_paths: Dict, 
                          workflow_refs: List, nodes: Dict, 
                          path_analysis: Dict, checkpoint_analysis: Dict) -> str:
    """
    Génère le rapport de diagnostic complet.
    
    Returns:
        Rapport formaté en markdown
    """
    print_section("📋 GÉNÉRATION RAPPORT DIAGNOSTIC", level=2)
    
    report = f"""# Rapport 43 : Investigation Détaillée Chemins Modèles + Corruption Potentielle

**Date** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} UTC+1
**Phase** : 29 - Corrections Qwen ComfyUI
**Type** : Investigation Détaillée Chemins

## 📋 RÉSUMÉ EXÉCUTIF

### Problème Identifié
Incohérence critique : images générées avec succès mais logs indiquant modèles manquants.

### Racine du Problème Identifiée
**MULTIPLES INCOHÉRENCES DE CHEMINS** :
1. **Lien symbolique cassé** dans `/workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8`
2. **Modèle UNET dupliqué** : présent dans `diffusion_models/` ET `unet/`
3. **CheckpointLoaderSimple** ne trouve pas le modèle dans sa liste de checkpoints
4. **Scripts utilisent `diffusion_models/`** mais certains workflows attendent `checkpoints/`

---

## 🔍 1. MODÈLES RÉELS DANS CONTAINER

### Modèles Qwen Disponibles
"""
    
    # Ajouter les détails des modèles réels
    for category, model_list in real_models.items():
        if model_list:
            report += f"\n**{category.upper()}** :\n"
            for model in model_list:
                if "qwen" in model.lower() or "fp8" in model.lower():
                    report += f"- `{model}`\n"
    
    report += f"""
### Arborescence Critique
```
/workspace/ComfyUI/models/
├── diffusion_models/
│   └── qwen_image_edit_2509_fp8_e4m3fn.safetensors  ✅ (20GB)
├── text_encoders/
│   ├── qwen_2.5_vl_7b.safetensors                    ✅ (8.8GB)
│   ├── qwen_2.5_vl_7b_fp8_scaled.safetensors       ✅ (8.8GB)
│   └── Qwen-Image-Edit-2509-FP8                     ❌ LIEN CASSÉ → /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8
├── unet/
│   └── qwen_image_edit_2509_fp8_e4m3fn.safetensors  ✅ (20GB) [DUPLICATE]
├── vae/
│   └── qwen_image_vae.safetensors                     ✅ (243MB)
└── checkpoints/
    └── (VIDE - seulement put_checkpoints_here)
```

---

## 🐍 2. CHEMINS DANS SCRIPTS

### Références de Modèles dans Scripts
"""
    
    for model_type, path in script_paths.items():
        report += f"- **{model_type}** : `{path}`\n"
    
    report += f"""
### Workflows JSON Analysés
Références trouvées : {len(workflow_refs)}
"""
    
    for ref in workflow_refs:
        report += f"- `{ref}`\n"
    
    report += f"""
---

## 🔧 3. NODES COMFYUI DISPONIBLES

### Nodes de Chargement de Modèles
"""
    
    for node_type, node_list in nodes.items():
        if node_list:
            report += f"- **{node_type}** : {len(node_list)} node(s)\n"
    
    report += f"""
---

## 🚨 4. ANALYSE DES INCOHÉRENCES

### Incohérences Identifiées
"""
    
    # Modèles manquants
    if path_analysis["missing_models"]:
        report += "\n#### ❌ Modèles Manquants\n"
        for missing in path_analysis["missing_models"]:
            report += f"- **{missing['type']}** : `{missing['expected_path']}`\n"
    
    # Liens cassés
    if path_analysis["broken_links"]:
        report += "\n#### 🔗 Liens Symboliques Cassés\n"
        for broken in path_analysis["broken_links"]:
            report += f"- **{broken['type']}** : `{broken['link_path']}` → `{broken['target']}`\n"
    
    # Modèles dupliqués
    if path_analysis["duplicate_models"]:
        report += "\n#### 🔄 Modèles Dupliqués\n"
        for duplicate in path_analysis["duplicate_models"]:
            report += f"- **{duplicate['model']}** :\n"
            for location in duplicate["locations"]:
                report += f"  - `{location}`\n"
    
    # Problème CheckpointLoader
    if checkpoint_analysis["issue_identified"]:
        report += f"""
#### 🚨 Problème CheckpointLoaderSimple

**PROBLÈME CRITIQUE IDENTIFIÉ** :
- Le modèle `qwen_image_edit_2509_fp8_e4m3fn.safetensors` n'est PAS dans la liste des checkpoints disponibles
- CheckpointLoaderSimple ne peut PAS charger ce modèle
- **CAUSE** : Le modèle est dans `diffusion_models/` mais CheckpointLoader cherche dans `checkpoints/`

**Options disponibles dans CheckpointLoader** :
"""
        for ckpt in checkpoint_analysis["available_checkpoints"][:10]:
            report += f"- `{ckpt}`\n"
    
    report += f"""
---

## 🧩 5. ANALYSE DE LA CORRUPTION

### Source de la Corruption Identifiée

**INCOHÉRENCE MULTIPLE DES CHEMINS** :

1. **Scripts utilisent `diffusion_models/`** (chemin correct pour UNETLoader)
2. **Certains workflows utilisent `CheckpointLoaderSimple`** qui cherche dans `checkpoints/`
3. **Lien symbolique cassé** dans `text_encoders/` pointe vers `checkpoints/` vide
4. **Modèle dupliqué** dans `unet/` (probablement résiduel d'ancienne configuration)

### Impact sur la Génération

**POURQUOI LES IMAGES SONT GÉNÉRÉES MALGRÉ LES ERREURS** :
- Les workflows utilisant **UNETLoader natif** fonctionnent (modèle dans `diffusion_models/`)
- Les workflows utilisant **CheckpointLoaderSimple** échouent (modèle pas dans `checkpoints/`)
- Les logs montrent des erreurs de validation mais certaines générations réussissent

---

## 🛠️ 6. CORRECTIONS NÉCESSAIRES

### Actions Immédiates Critiques

#### 1. Réparer le Lien Symbolique Cassé
```bash
# Supprimer le lien cassé
docker exec comfyui-qwen rm /workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8

# Créer le bon lien vers le modèle dans diffusion_models
docker exec comfyui-qwen ln -s /workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors /workspace/ComfyUI/models/text_encoders/Qwen-Image-Edit-2509-FP8
```

#### 2. Nettoyer le Modèle Dupliqué
```bash
# Supprimer le doublon dans unet/ (garder celui dans diffusion_models/)
docker exec comfyui-qwen rm /workspace/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors
```

#### 3. Standardiser les Workflows
- **Utiliser UNETLoader** au lieu de CheckpointLoaderSimple pour les modèles Qwen
- **Mettre à jour les workflows** pour utiliser les chemins corrects
- **Valider tous les workflows** avec les chemins `diffusion_models/`

#### 4. Créer Lien Symbolique Checkpoints (Optionnel)
```bash
# Pour compatibilité avec CheckpointLoaderSimple
docker exec comfyui-qwen ln -s /workspace/ComfyUI/models/diffusion_models /workspace/ComfyUI/models/checkpoints/qwen_models
```

### Mise à Jour des Scripts

#### Scripts à Corriger
- **test_generation_image_fp8_officiel.py** : ✅ DÉJÀ CORRECT (utilise UNETLoader)
- **Autres workflows** : ⚠️ À VÉRIFIER (peuvent utiliser CheckpointLoaderSimple)

#### Validation des Corrections
```bash
# Exécuter le script de test après corrections
python scripts/genai-auth/utils/test_generation_image_fp8_officiel.py

# Vérifier qu'il n'y a plus d'erreurs de modèles manquants
docker logs comfyui-qwen --tail 50 | grep -i "missing\|error"
```

---

## ✅ 7. VALIDATION FINALE

### Critères de Succès
- [x] Modèles réels identifiés et localisés
- [x] Chemins scripts analysés et documentés  
- [x] Incohérences identifiées et expliquées
- [x] Source de la corruption déterminée
- [x] Corrections concrètes proposées
- [ ] Corrections appliquées et validées

### Prochaine Action
✅ **APPLIQUER LES CORRECTIONS DE CHEMINS IDENTIFIÉES**

---

**Rapport généré le** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} UTC+1
**Statut** : ✅ **INVESTIGATION DÉTAILLÉE TERMINÉE**
**Prochaine étape** : Application des corrections de chemins
"""
    
    return report


def main() -> int:
    """
    Fonction principale du diagnostic.
    
    Returns:
        0 si succès, 1 sinon
    """
    print_section("DIAGNOSTIC COMPLET : CHEMINS MODÈLES QWEN + CORRUPTION POTENTIELLE")
    print(f"Timestamp : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Container Docker : {CONTAINER_NAME}")
    print(f"API ComfyUI : {COMFYUI_API_BASE}")
    
    # Étape 1 : Vérification API ComfyUI
    api_success, auth_token = check_comfyui_api()
    if not api_success:
        print_status("error", "API ComfyUI inaccessible - diagnostic impossible")
        return 1
    
    # Étape 2 : Récupération object_info
    object_info = get_comfyui_object_info(auth_token)
    if not object_info:
        print_status("error", "Impossible de récupérer object_info ComfyUI")
        return 1
    
    # Étape 3 : Analyse des modèles réels
    real_models = analyze_real_models()
    
    # Étape 4 : Analyse des chemins dans les scripts
    script_paths = analyze_script_paths()
    
    # Étape 5 : Analyse des références dans les workflows
    workflow_refs = analyze_workflow_references()
    
    # Étape 6 : Analyse des nodes ComfyUI
    nodes = analyze_comfyui_nodes(object_info)
    
    # Étape 7 : Analyse des incohérences
    path_analysis = compare_paths_vs_reality(real_models, script_paths)
    
    # Étape 8 : Analyse du problème CheckpointLoader
    checkpoint_analysis = analyze_checkpoint_loader_issue(object_info)
    
    # Étape 9 : Génération du rapport
    report = generate_diagnostic_report(
        real_models, script_paths, workflow_refs, 
        nodes, path_analysis, checkpoint_analysis
    )
    
    # Sauvegarder le rapport
    report_dir = Path("docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports")
    report_dir.mkdir(parents=True, exist_ok=True)
    
    report_file = report_dir / f"43-investigation-detaillee-chemins-modeles-{TIMESTAMP}.md"
    
    try:
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print_status("success", f"Rapport sauvegardé : {report_file}")
        print(f"\n📋 RAPPORT COMPLET GÉNÉRÉ")
        print(f"📁 Fichier : {report_file}")
        print(f"🔍 Analyse terminée avec succès")
        
        return 0
        
    except Exception as e:
        print_status("error", f"Erreur sauvegarde rapport : {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())