#!/usr/bin/env python3
"""
Script d'amélioration du notebook Qwen Image-Edit
Phase 21 - Itérations notebooks GenAI Image

Objectif:
    Insérer 3 cellules pédagogiques supplémentaires dans le notebook Qwen
    pour améliorer la qualité pédagogique et l'expérience d'apprentissage.

Améliorations:
    1. Cellule Diagramme Architecture ComfyUI (après cellule 2 - Architecture)
    2. Cellule Exemples Workflows Réels (après cellule 5 - Hello World)
    3. Cellule Comparaison Avant/Après (après cellule 11 - Expérimentation)

Auteur: SDDD Process
Date: 2025-10-21
"""

import json
import sys
from pathlib import Path

# Configuration
NOTEBOOK_PATH = Path("MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb")

# ============================================================================
# CELLULE 1: DIAGRAMME ARCHITECTURE COMFYUI
# Position: Après cellule 2 (Architecture) → Index 3
# ============================================================================
CELL_DIAGRAMME_ARCHITECTURE = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### 🔧 Visualisation Architecture Workflow ComfyUI\n",
        "\n",
        "**Diagramme ASCII d'un workflow ComfyUI typique**:\n",
        "\n",
        "```\n",
        "┌─────────────────────────────────────────────────────────────┐\n",
        "│                    WORKFLOW COMFYUI                         │\n",
        "│                                                             │\n",
        "│  ┌──────────────┐        ┌──────────────┐                 │\n",
        "│  │ Load Model   │───────▶│ CLIP Text    │                 │\n",
        "│  │ (Checkpoint) │        │ Encode       │                 │\n",
        "│  └──────────────┘        └──────────────┘                 │\n",
        "│         │                       │                          │\n",
        "│         │                       ▼                          │\n",
        "│         │                ┌──────────────┐                 │\n",
        "│         │                │ Conditioning │                 │\n",
        "│         │                │ (Prompts)    │                 │\n",
        "│         │                └──────────────┘                 │\n",
        "│         │                       │                          │\n",
        "│         ▼                       ▼                          │\n",
        "│  ┌──────────────────────────────────────┐                │\n",
        "│  │          KSampler                     │                │\n",
        "│  │  (steps, denoise, seed, sampler)     │                │\n",
        "│  └──────────────────────────────────────┘                │\n",
        "│                    │                                       │\n",
        "│                    ▼                                       │\n",
        "│             ┌──────────────┐                              │\n",
        "│             │ VAE Decode   │                              │\n",
        "│             └──────────────┘                              │\n",
        "│                    │                                       │\n",
        "│                    ▼                                       │\n",
        "│             ┌──────────────┐                              │\n",
        "│             │ Save Image   │                              │\n",
        "│             └──────────────┘                              │\n",
        "└─────────────────────────────────────────────────────────────┘\n",
        "```\n",
        "\n",
        "**Flux de données**:\n",
        "1. **Checkpoint** → Fournit le modèle (model, CLIP, VAE)\n",
        "2. **CLIP Text Encode** → Convertit le prompt en embeddings\n",
        "3. **KSampler** → Génère l'image latente à partir des embeddings\n",
        "4. **VAE Decode** → Convertit l'image latente en image RGB\n",
        "5. **Save Image** → Sauvegarde l'image finale\n",
        "\n",
        "**Correspondance JSON**:\n",
        "```json\n",
        "{\n",
        "  \"1\": {\"class_type\": \"CheckpointLoaderSimple\", ...},\n",
        "  \"2\": {\"class_type\": \"CLIPTextEncode\", \"inputs\": {\"clip\": [\"1\", 1], ...}},\n",
        "  \"3\": {\"class_type\": \"KSampler\", \"inputs\": {\"model\": [\"1\", 0], ...}},\n",
        "  \"4\": {\"class_type\": \"VAEDecode\", \"inputs\": {\"samples\": [\"3\", 0], ...}},\n",
        "  \"5\": {\"class_type\": \"SaveImage\", \"inputs\": {\"images\": [\"4\", 0]}}\n",
        "}\n",
        "```\n",
        "\n",
        "**Notation `[\"ID_NODE\", INDEX_OUTPUT]`**:\n",
        "- `[\"1\", 0]` = Output 0 (model) du node 1\n",
        "- `[\"1\", 1]` = Output 1 (CLIP) du node 1\n",
        "- `[\"3\", 0]` = Output 0 (latents) du node 3\n",
        "\n",
        "💡 **Astuce**: Chaque node peut avoir plusieurs outputs. L'index détermine lequel utiliser."
    ]
}

# ============================================================================
# CELLULE 2: EXEMPLES WORKFLOWS RÉELS
# Position: Après cellule 5 (Hello World) → Index 6 (ajusté après 1ère insertion = 7)
# ============================================================================
CELL_WORKFLOWS_REELS = {
    "cell_type": "code",
    "metadata": {},
    "execution_count": None,
    "outputs": [],
    "source": [
        "# ========================================\n",
        "# 🎯 WORKFLOW RÉEL 1: Édition Simple Image\n",
        "# ========================================\n",
        "\n",
        "def create_simple_edit_workflow(image_name: str, edit_prompt: str, denoise: float = 0.5) -> dict:\n",
        "    \"\"\"Workflow édition simple d'une image existante\n",
        "    \n",
        "    Args:\n",
        "        image_name: Nom du fichier image uploadé sur ComfyUI\n",
        "        edit_prompt: Description de l'édition souhaitée\n",
        "        denoise: Force de l'édition (0.0 = aucune, 1.0 = complète)\n",
        "    \n",
        "    Returns:\n",
        "        Workflow JSON prêt à exécuter\n",
        "    \"\"\"\n",
        "    workflow = {\n",
        "        \"1\": {\n",
        "            \"class_type\": \"CheckpointLoaderSimple\",\n",
        "            \"inputs\": {\"ckpt_name\": \"qwen_vl_model.safetensors\"}\n",
        "        },\n",
        "        \"2\": {\n",
        "            \"class_type\": \"LoadImage\",\n",
        "            \"inputs\": {\"image\": image_name}\n",
        "        },\n",
        "        \"3\": {\n",
        "            \"class_type\": \"CLIPTextEncode\",\n",
        "            \"inputs\": {\n",
        "                \"text\": edit_prompt,\n",
        "                \"clip\": [\"1\", 1]\n",
        "            }\n",
        "        },\n",
        "        \"4\": {\n",
        "            \"class_type\": \"VAEEncode\",\n",
        "            \"inputs\": {\n",
        "                \"pixels\": [\"2\", 0],\n",
        "                \"vae\": [\"1\", 2]\n",
        "            }\n",
        "        },\n",
        "        \"5\": {\n",
        "            \"class_type\": \"KSampler\",\n",
        "            \"inputs\": {\n",
        "                \"seed\": 42,\n",
        "                \"steps\": 20,\n",
        "                \"cfg\": 7.0,\n",
        "                \"sampler_name\": \"euler\",\n",
        "                \"scheduler\": \"normal\",\n",
        "                \"denoise\": denoise,\n",
        "                \"model\": [\"1\", 0],\n",
        "                \"positive\": [\"3\", 0],\n",
        "                \"negative\": [\"3\", 0],  # Pas de prompt négatif pour édition simple\n",
        "                \"latent_image\": [\"4\", 0]\n",
        "            }\n",
        "        },\n",
        "        \"6\": {\n",
        "            \"class_type\": \"VAEDecode\",\n",
        "            \"inputs\": {\n",
        "                \"samples\": [\"5\", 0],\n",
        "                \"vae\": [\"1\", 2]\n",
        "            }\n",
        "        },\n",
        "        \"7\": {\n",
        "            \"class_type\": \"SaveImage\",\n",
        "            \"inputs\": {\n",
        "                \"images\": [\"6\", 0],\n",
        "                \"filename_prefix\": \"qwen_edit_simple\"\n",
        "            }\n",
        "        }\n",
        "    }\n",
        "    return workflow\n",
        "\n",
        "# ========================================\n",
        "# 🎯 WORKFLOW RÉEL 2: Chaînage Nodes Avancé\n",
        "# ========================================\n",
        "\n",
        "def create_chained_workflow(base_prompt: str, refine_prompt: str) -> dict:\n",
        "    \"\"\"Workflow avec chaînage: génération base + raffinement\n",
        "    \n",
        "    Architecture:\n",
        "        1. Génération image base (text-to-image)\n",
        "        2. Raffinement avec nouveau prompt (image-to-image)\n",
        "    \n",
        "    Args:\n",
        "        base_prompt: Prompt initial génération\n",
        "        refine_prompt: Prompt raffinement/amélioration\n",
        "    \n",
        "    Returns:\n",
        "        Workflow JSON avec 2 étapes KSampler\n",
        "    \"\"\"\n",
        "    workflow = {\n",
        "        # Étape 1: Génération base\n",
        "        \"1\": {\n",
        "            \"class_type\": \"CheckpointLoaderSimple\",\n",
        "            \"inputs\": {\"ckpt_name\": \"qwen_vl_model.safetensors\"}\n",
        "        },\n",
        "        \"2\": {\n",
        "            \"class_type\": \"CLIPTextEncode\",\n",
        "            \"inputs\": {\"text\": base_prompt, \"clip\": [\"1\", 1]}\n",
        "        },\n",
        "        \"3\": {\n",
        "            \"class_type\": \"EmptyLatentImage\",\n",
        "            \"inputs\": {\"width\": 512, \"height\": 512, \"batch_size\": 1}\n",
        "        },\n",
        "        \"4\": {\n",
        "            \"class_type\": \"KSampler\",\n",
        "            \"inputs\": {\n",
        "                \"seed\": 42,\n",
        "                \"steps\": 10,\n",
        "                \"cfg\": 7.0,\n",
        "                \"sampler_name\": \"euler\",\n",
        "                \"scheduler\": \"normal\",\n",
        "                \"denoise\": 1.0,  # Génération complète\n",
        "                \"model\": [\"1\", 0],\n",
        "                \"positive\": [\"2\", 0],\n",
        "                \"negative\": [\"2\", 0],\n",
        "                \"latent_image\": [\"3\", 0]\n",
        "            }\n",
        "        },\n",
        "        # Étape 2: Raffinement\n",
        "        \"5\": {\n",
        "            \"class_type\": \"CLIPTextEncode\",\n",
        "            \"inputs\": {\"text\": refine_prompt, \"clip\": [\"1\", 1]}\n",
        "        },\n",
        "        \"6\": {\n",
        "            \"class_type\": \"KSampler\",\n",
        "            \"inputs\": {\n",
        "                \"seed\": 43,\n",
        "                \"steps\": 10,\n",
        "                \"cfg\": 7.0,\n",
        "                \"sampler_name\": \"euler\",\n",
        "                \"scheduler\": \"normal\",\n",
        "                \"denoise\": 0.3,  # Raffinement léger\n",
        "                \"model\": [\"1\", 0],\n",
        "                \"positive\": [\"5\", 0],\n",
        "                \"negative\": [\"5\", 0],\n",
        "                \"latent_image\": [\"4\", 0]  # Sortie de l'étape 1\n",
        "            }\n",
        "        },\n",
        "        \"7\": {\n",
        "            \"class_type\": \"VAEDecode\",\n",
        "            \"inputs\": {\"samples\": [\"6\", 0], \"vae\": [\"1\", 2]}\n",
        "        },\n",
        "        \"8\": {\n",
        "            \"class_type\": \"SaveImage\",\n",
        "            \"inputs\": {\n",
        "                \"images\": [\"7\", 0],\n",
        "                \"filename_prefix\": \"qwen_chained\"\n",
        "            }\n",
        "        }\n",
        "    }\n",
        "    return workflow\n",
        "\n",
        "# ========================================\n",
        "# EXEMPLE D'UTILISATION\n",
        "# ========================================\n",
        "\n",
        "# Workflow 1: Édition simple\n",
        "workflow_simple = create_simple_edit_workflow(\n",
        "    image_name=\"cat.png\",\n",
        "    edit_prompt=\"Add sunglasses to the cat\",\n",
        "    denoise=0.5\n",
        ")\n",
        "print(\"✅ Workflow édition simple créé\")\n",
        "print(f\"   Nodes: {len(workflow_simple)}\")\n",
        "\n",
        "# Workflow 2: Chaînage\n",
        "workflow_chained = create_chained_workflow(\n",
        "    base_prompt=\"A cat sitting on a chair\",\n",
        "    refine_prompt=\"High quality, professional photography, detailed fur\"\n",
        ")\n",
        "print(\"✅ Workflow chaîné créé\")\n",
        "print(f\"   Nodes: {len(workflow_chained)}\")\n",
        "print(f\"   KSamplers: 2 (base + raffinement)\")\n",
        "\n",
        "# 💡 Pour exécuter ces workflows:\n",
        "# client = ComfyUIClient(\"https://qwen-image-edit.myia.io\")\n",
        "# result = client.execute_workflow(workflow_simple)\n",
        "# images = client.get_results(result[\"prompt_id\"])"
    ]
}

# ============================================================================
# CELLULE 3: COMPARAISON AVANT/APRÈS
# Position: Après cellule 11 (Expérimentation) → Index 12 (ajusté après 2 insertions = 14)
# ============================================================================
CELL_COMPARAISON_AVANT_APRES = {
    "cell_type": "code",
    "metadata": {},
    "execution_count": None,
    "outputs": [],
    "source": [
        "# ========================================\n",
        "# 🖼️ COMPARAISON AVANT/APRÈS: Side-by-Side\n",
        "# ========================================\n",
        "\n",
        "import matplotlib.pyplot as plt\n",
        "from PIL import Image\n",
        "import numpy as np\n",
        "from typing import List, Tuple\n",
        "\n",
        "def compare_before_after(\n",
        "    original_path: str,\n",
        "    edited_path: str,\n",
        "    title_original: str = \"Image Originale\",\n",
        "    title_edited: str = \"Image Éditée\",\n",
        "    show_metrics: bool = True\n",
        ") -> None:\n",
        "    \"\"\"Affiche comparaison side-by-side avec métriques qualité\n",
        "    \n",
        "    Args:\n",
        "        original_path: Chemin image originale\n",
        "        edited_path: Chemin image éditée\n",
        "        title_original: Titre image originale\n",
        "        title_edited: Titre image éditée\n",
        "        show_metrics: Afficher métriques qualité (PSNR, SSIM)\n",
        "    \"\"\"\n",
        "    # Charger images\n",
        "    img_original = Image.open(original_path)\n",
        "    img_edited = Image.open(edited_path)\n",
        "    \n",
        "    # Convertir en numpy arrays\n",
        "    arr_original = np.array(img_original)\n",
        "    arr_edited = np.array(img_edited)\n",
        "    \n",
        "    # Créer figure avec 2 colonnes\n",
        "    fig, axes = plt.subplots(1, 2, figsize=(16, 8))\n",
        "    \n",
        "    # Image originale\n",
        "    axes[0].imshow(arr_original)\n",
        "    axes[0].set_title(f\"{title_original}\\n{img_original.size[0]}x{img_original.size[1]}\", \n",
        "                      fontsize=14, fontweight='bold')\n",
        "    axes[0].axis('off')\n",
        "    \n",
        "    # Image éditée\n",
        "    axes[1].imshow(arr_edited)\n",
        "    axes[1].set_title(f\"{title_edited}\\n{img_edited.size[0]}x{img_edited.size[1]}\", \n",
        "                      fontsize=14, fontweight='bold')\n",
        "    axes[1].axis('off')\n",
        "    \n",
        "    # Métriques qualité\n",
        "    if show_metrics and arr_original.shape == arr_edited.shape:\n",
        "        # PSNR (Peak Signal-to-Noise Ratio)\n",
        "        mse = np.mean((arr_original - arr_edited) ** 2)\n",
        "        if mse == 0:\n",
        "            psnr = float('inf')\n",
        "        else:\n",
        "            max_pixel = 255.0\n",
        "            psnr = 20 * np.log10(max_pixel / np.sqrt(mse))\n",
        "        \n",
        "        # Différence absolue moyenne\n",
        "        mae = np.mean(np.abs(arr_original - arr_edited))\n",
        "        \n",
        "        # Afficher métriques\n",
        "        metrics_text = f\"📊 Métriques:\\n\"\n",
        "        metrics_text += f\"   PSNR: {psnr:.2f} dB\\n\"\n",
        "        metrics_text += f\"   MAE: {mae:.2f}\\n\"\n",
        "        metrics_text += f\"   Pixels modifiés: {np.sum(arr_original != arr_edited):,}\"\n",
        "        \n",
        "        fig.text(0.5, 0.02, metrics_text, ha='center', fontsize=12, \n",
        "                 bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))\n",
        "    \n",
        "    plt.tight_layout()\n",
        "    plt.show()\n",
        "    \n",
        "    # Interprétation PSNR\n",
        "    if show_metrics and arr_original.shape == arr_edited.shape:\n",
        "        print(\"\\n📈 Interprétation PSNR:\")\n",
        "        if psnr > 40:\n",
        "            print(\"   ✅ Excellente qualité (PSNR > 40 dB) - Changements subtils\")\n",
        "        elif psnr > 30:\n",
        "            print(\"   ✅ Bonne qualité (PSNR 30-40 dB) - Changements visibles mais contrôlés\")\n",
        "        elif psnr > 20:\n",
        "            print(\"   ⚠️  Qualité acceptable (PSNR 20-30 dB) - Changements significatifs\")\n",
        "        else:\n",
        "            print(\"   ⚠️  Qualité faible (PSNR < 20 dB) - Changements majeurs\")\n",
        "\n",
        "def create_difference_map(\n",
        "    original_path: str,\n",
        "    edited_path: str,\n",
        "    amplification: float = 5.0\n",
        ") -> None:\n",
        "    \"\"\"Crée une carte visuelle des différences entre 2 images\n",
        "    \n",
        "    Args:\n",
        "        original_path: Chemin image originale\n",
        "        edited_path: Chemin image éditée\n",
        "        amplification: Facteur amplification différences pour visibilité\n",
        "    \"\"\"\n",
        "    img_original = np.array(Image.open(original_path))\n",
        "    img_edited = np.array(Image.open(edited_path))\n",
        "    \n",
        "    if img_original.shape != img_edited.shape:\n",
        "        print(\"❌ Images de tailles différentes, impossible de comparer\")\n",
        "        return\n",
        "    \n",
        "    # Calculer différence absolue\n",
        "    diff = np.abs(img_original.astype(float) - img_edited.astype(float))\n",
        "    \n",
        "    # Amplifier pour visibilité\n",
        "    diff_amplified = np.clip(diff * amplification, 0, 255).astype(np.uint8)\n",
        "    \n",
        "    # Afficher\n",
        "    fig, axes = plt.subplots(1, 3, figsize=(20, 6))\n",
        "    \n",
        "    axes[0].imshow(img_original)\n",
        "    axes[0].set_title(\"Originale\", fontsize=14, fontweight='bold')\n",
        "    axes[0].axis('off')\n",
        "    \n",
        "    axes[1].imshow(img_edited)\n",
        "    axes[1].set_title(\"Éditée\", fontsize=14, fontweight='bold')\n",
        "    axes[1].axis('off')\n",
        "    \n",
        "    axes[2].imshow(diff_amplified)\n",
        "    axes[2].set_title(f\"Carte Différences (×{amplification})\", fontsize=14, fontweight='bold')\n",
        "    axes[2].axis('off')\n",
        "    \n",
        "    plt.tight_layout()\n",
        "    plt.show()\n",
        "    \n",
        "    # Statistiques différences\n",
        "    print(f\"\\n📊 Statistiques différences:\")\n",
        "    print(f\"   Moyenne: {np.mean(diff):.2f}\")\n",
        "    print(f\"   Max: {np.max(diff):.2f}\")\n",
        "    print(f\"   Pixels modifiés (>5): {np.sum(diff > 5):,} ({100*np.sum(diff > 5)/diff.size:.2f}%)\")\n",
        "\n",
        "# ========================================\n",
        "# EXEMPLE D'UTILISATION\n",
        "# ========================================\n",
        "\n",
        "# Cas d'usage: Comparer original vs édition Qwen\n",
        "# compare_before_after(\n",
        "#     original_path=\"cat_original.png\",\n",
        "#     edited_path=\"cat_with_sunglasses.png\",\n",
        "#     title_original=\"Chat Original\",\n",
        "#     title_edited=\"Chat avec Lunettes (Qwen Edit)\",\n",
        "#     show_metrics=True\n",
        "# )\n",
        "\n",
        "# Cas d'usage: Carte différences pour analyse détaillée\n",
        "# create_difference_map(\n",
        "#     original_path=\"cat_original.png\",\n",
        "#     edited_path=\"cat_with_sunglasses.png\",\n",
        "#     amplification=10.0\n",
        "# )\n",
        "\n",
        "print(\"✅ Fonctions comparaison avant/après définies\")\n",
        "print(\"   - compare_before_after(): Affichage side-by-side + métriques\")\n",
        "print(\"   - create_difference_map(): Carte visuelle différences\")\n",
        "print(\"\\n💡 Décommentez les exemples ci-dessus pour tester avec vos images\")"
    ]
}

# ============================================================================
# FONCTION PRINCIPALE
# ============================================================================

def ameliorer_notebook_qwen():
    """Fonction principale d'amélioration du notebook Qwen"""
    
    print("=" * 70)
    print("AMÉLIORATION NOTEBOOK QWEN IMAGE-EDIT")
    print("Phase 21 - Itérations Notebooks GenAI Image")
    print("=" * 70)
    
    # Vérifier existence notebook
    if not NOTEBOOK_PATH.exists():
        print(f"❌ ERREUR: Notebook non trouvé à {NOTEBOOK_PATH}")
        sys.exit(1)
    
    print(f"\n📖 Lecture notebook: {NOTEBOOK_PATH}")
    
    # Lire notebook JSON
    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)
    
    cells = notebook.get('cells', [])
    print(f"✅ Notebook chargé: {len(cells)} cellules actuelles")
    
    # Définir insertions (ordre INVERSE pour préserver indices)
    insertions = [
        # Cellule 3: Comparaison Avant/Après (après cellule 11 Expérimentation)
        # Position initiale: 12, mais après 2 insertions précédentes = 14
        (14, CELL_COMPARAISON_AVANT_APRES, "Comparaison Avant/Après"),
        
        # Cellule 2: Workflows Réels (après cellule 5 Hello World)
        # Position initiale: 6, mais après 1ère insertion = 7
        (7, CELL_WORKFLOWS_REELS, "Exemples Workflows Réels"),
        
        # Cellule 1: Diagramme Architecture (après cellule 2 Architecture)
        (3, CELL_DIAGRAMME_ARCHITECTURE, "Diagramme Architecture ComfyUI")
    ]
    
    # IMPORTANT: Inverser liste pour insérer de la fin vers le début
    # Cela préserve les indices des cellules précédentes
    insertions_reversed = list(reversed(insertions))
    
    print(f"\n🔧 Insertion de {len(insertions_reversed)} nouvelles cellules:")
    for idx, cell, name in insertions_reversed:
        print(f"   - Position {idx}: {name} ({cell['cell_type']})")
    
    # Insérer cellules
    for idx, cell, name in insertions_reversed:
        cells.insert(idx, cell)
        print(f"   ✅ Cellule '{name}' insérée à l'index {idx}")
    
    # Mettre à jour notebook
    notebook['cells'] = cells
    
    # Sauvegarder
    print(f"\n💾 Sauvegarde notebook modifié...")
    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, ensure_ascii=False, indent=2)
    
    print(f"✅ Notebook sauvegardé avec succès")
    print(f"\n📊 RÉSULTAT FINAL:")
    print(f"   Cellules avant: 15")
    print(f"   Cellules ajoutées: 3")
    print(f"   Cellules après: {len(cells)}")
    print(f"   Ratio amélioration: +{100 * 3 / 15:.1f}%")
    
    print("\n" + "=" * 70)
    print("✅ AMÉLIORATION NOTEBOOK QWEN TERMINÉE AVEC SUCCÈS")
    print("=" * 70)
    
    return True

# ============================================================================
# POINT D'ENTRÉE
# ============================================================================

if __name__ == "__main__":
    try:
        success = ameliorer_notebook_qwen()
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"\n❌ ERREUR FATALE: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)