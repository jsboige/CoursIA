#!/usr/bin/env python3
"""
Script d'amélioration du notebook Forge SD XL Turbo
Phase 21 - Itérations notebooks

Ajoute 3 cellules pédagogiques à des positions spécifiques:
1. Introduction Visuelle (index 2)
2. Exemples Avancés (index 10 après modification)
3. Tips & Troubleshooting (index 12 après modification)
"""

import json
import sys
from pathlib import Path
from typing import Dict, Any, List

# Chemin notebook relatif au script
NOTEBOOK_PATH = Path(__file__).parent.parent / "MyIA.AI.Notebooks" / "GenAI" / "01-Images-Foundation" / "01-4-Forge-SD-XL-Turbo.ipynb"

def create_code_cell(source: List[str]) -> Dict[str, Any]:
    """Crée une cellule code avec métadonnées standards"""
    return {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": source
    }

def create_markdown_cell(source: List[str]) -> Dict[str, Any]:
    """Crée une cellule markdown avec métadonnées standards"""
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": source
    }

# --- CELLULE 1: Introduction Visuelle (index 2) ---
CELL_INTRO_VISUELLE = create_code_cell([
    '"""\n',
    'Vérification du statut de l\'API et affichage d\'une bannière visuelle\n',
    '"""\n',
    '\n',
    '# Test de connectivité API\n',
    'try:\n',
    '    response = requests.get(f"{API_BASE_URL}/sdapi/v1/options", timeout=10)\n',
    '    response.raise_for_status()\n',
    '    \n',
    '    # Bannière de succès\n',
    '    from IPython.display import display, HTML\n',
    '    \n',
    '    banner_html = """\n',
    '    <div style="background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);\n',
    '                padding: 20px;\n',
    '                border-radius: 10px;\n',
    '                text-align: center;\n',
    '                color: white;\n',
    '                font-family: Arial, sans-serif;\n',
    '                box-shadow: 0 4px 6px rgba(0,0,0,0.1);">\n',
    '        <h1 style="margin: 0; font-size: 28px;">🎨 Stable Diffusion Forge</h1>\n',
    '        <h2 style="margin: 10px 0 0 0; font-weight: normal; font-size: 18px;">SD XL Turbo API</h2>\n',
    '        <p style="margin: 15px 0 0 0; font-size: 14px; opacity: 0.9;">✅ API Connectée et Opérationnelle</p>\n',
    '        <p style="margin: 5px 0 0 0; font-size: 12px; opacity: 0.7;">Génération rapide 4-steps • Performance ~18s</p>\n',
    '    </div>\n',
    '    """\n',
    '    \n',
    '    display(HTML(banner_html))\n',
    '    print("\\n✅ API Forge accessible et prête à l\'utilisation")\n',
    '    \n',
    'except requests.exceptions.RequestException as e:\n',
    '    print(f"⚠️ Avertissement: Impossible de contacter l\'API Forge")\n',
    '    print(f"   Erreur: {e}")\n',
    '    print(f"   Vérifiez que l\'API est accessible à {API_BASE_URL}")\n'
])

# --- CELLULE 2: Exemples Avancés (index 10 après ajout cellule 1) ---
CELL_EXEMPLES_AVANCES = create_code_cell([
    '"""\n',
    'Techniques Avancées de Génération\n',
    '\n',
    'Ce bloc explore des techniques avancées pour améliorer vos générations:\n',
    '1. Reproductibilité avec seed fixe\n',
    '2. Exploration créative avec seeds aléatoires\n',
    '3. Génération batch optimisée\n',
    '"""\n',
    '\n',
    'import time\n',
    'import random\n',
    '\n',
    '# --- Technique 1: Reproductibilité avec Seed Fixe ---\n',
    'print("🎯 Technique 1: Génération Reproductible (seed fixe)\\n")\n',
    '\n',
    'def generate_with_seed(prompt: str, seed: int):\n',
    '    """Génère une image avec seed fixe pour reproductibilité"""\n',
    '    payload = {\n',
    '        "prompt": prompt,\n',
    '        "steps": 4,\n',
    '        "cfg_scale": 2.0,\n',
    '        "width": 512,\n',
    '        "height": 512,\n',
    '        "seed": seed,\n',
    '        "sampler_name": "DPM++ 2M"\n',
    '    }\n',
    '    \n',
    '    try:\n',
    '        response = requests.post(\n',
    '            f"{API_BASE_URL}/sdapi/v1/txt2img",\n',
    '            json=payload,\n',
    '            timeout=TIMEOUT\n',
    '        )\n',
    '        response.raise_for_status()\n',
    '        result = response.json()\n',
    '        \n',
    '        if "images" in result and len(result["images"]) > 0:\n',
    '            image_data = base64.b64decode(result["images"][0])\n',
    '            return Image.open(BytesIO(image_data))\n',
    '    except Exception as e:\n',
    '        print(f"❌ Erreur: {e}")\n',
    '    return None\n',
    '\n',
    '# Test avec seed fixe (42)\n',
    'prompt_seed = "a mystical forest with glowing mushrooms"\n',
    'print(f"Prompt: \\"{prompt_seed}\\"\\nSeed: 42\\n")\n',
    '\n',
    'img_seed = generate_with_seed(prompt_seed, seed=42)\n',
    'if img_seed:\n',
    '    plt.figure(figsize=(6, 6))\n',
    '    plt.imshow(img_seed)\n',
    '    plt.axis(\'off\')\n',
    '    plt.title("Génération Reproductible (seed=42)", fontsize=11)\n',
    '    plt.tight_layout()\n',
    '    plt.show()\n',
    '    print("💡 Astuce: Réexécutez cette cellule → même résultat garanti\\n")\n',
    '\n',
    '# --- Technique 2: Exploration Créative (seeds aléatoires) ---\n',
    'print("\\n🎲 Technique 2: Exploration Créative (seeds aléatoires)\\n")\n',
    '\n',
    'prompt_creative = "a steampunk airship in the clouds"\n',
    'seeds_random = [random.randint(1, 999999) for _ in range(3)]\n',
    '\n',
    'print(f"Génération de 3 variations avec seeds aléatoires...\\n")\n',
    'images_seeds = []\n',
    '\n',
    'for i, seed in enumerate(seeds_random, 1):\n',
    '    print(f"{i}. Seed: {seed}")\n',
    '    img = generate_with_seed(prompt_creative, seed)\n',
    '    if img:\n',
    '        images_seeds.append((img, seed))\n',
    '\n',
    '# Affichage grille\n',
    'if len(images_seeds) == 3:\n',
    '    fig, axes = plt.subplots(1, 3, figsize=(15, 5))\n',
    '    for ax, (img, seed) in zip(axes, images_seeds):\n',
    '        ax.imshow(img)\n',
    '        ax.axis(\'off\')\n',
    '        ax.set_title(f"Seed: {seed}", fontsize=9)\n',
    '    plt.suptitle("Exploration Créative: Même Prompt, Seeds Différents", fontsize=12)\n',
    '    plt.tight_layout()\n',
    '    plt.show()\n',
    '    print("\\n💡 Observation: Même prompt → résultats visuels différents\\n")\n',
    '\n',
    '# --- Technique 3: Batch Generation Optimisé ---\n',
    'print("\\n⚡ Technique 3: Génération Batch Optimisée\\n")\n',
    '\n',
    'def generer_batch_optimise(prompts_list: List[str]):\n',
    '    """Génère plusieurs images en batch avec gestion erreurs"""\n',
    '    results = []\n',
    '    start_time = time.time()\n',
    '    \n',
    '    for i, prompt in enumerate(prompts_list, 1):\n',
    '        print(f"[{i}/{len(prompts_list)}] {prompt[:50]}...")\n',
    '        img = generate_image_forge(\n',
    '            prompt=prompt,\n',
    '            steps=4,\n',
    '            cfg_scale=2.0,\n',
    '            width=512,\n',
    '            height=512\n',
    '        )\n',
    '        if img:\n',
    '            results.append((prompt, img))\n',
    '    \n',
    '    elapsed = time.time() - start_time\n',
    '    print(f"\\n✅ Batch terminé: {len(results)}/{len(prompts_list)} succès en {elapsed:.1f}s")\n',
    '    return results\n',
    '\n',
    '# Batch de 3 prompts thématiques\n',
    'batch_prompts = [\n',
    '    "a futuristic city at sunset, cyberpunk style",\n',
    '    "a peaceful zen garden with cherry blossoms",\n',
    '    "an underwater scene with colorful coral reefs"\n',
    ']\n',
    '\n',
    'resultats_batch = generer_batch_optimise(batch_prompts)\n',
    '\n',
    '# Affichage résultats batch\n',
    'if len(resultats_batch) >= 2:\n',
    '    n_cols = len(resultats_batch)\n',
    '    fig, axes = plt.subplots(1, n_cols, figsize=(5*n_cols, 5))\n',
    '    if n_cols == 1:\n',
    '        axes = [axes]\n',
    '    \n',
    '    for ax, (prompt, img) in zip(axes, resultats_batch):\n',
    '        ax.imshow(img)\n',
    '        ax.axis(\'off\')\n',
    '        title = prompt if len(prompt) <= 35 else prompt[:32] + "..."\n',
    '        ax.set_title(title, fontsize=9)\n',
    '    \n',
    '    plt.suptitle("Génération Batch Thématique", fontsize=12, y=1.02)\n',
    '    plt.tight_layout()\n',
    '    plt.show()\n',
    '    \n',
    '    print("\\n💡 Usage: Idéal pour prototypage rapide de concepts multiples")\n'
])

# --- CELLULE 3: Tips & Troubleshooting (index 12 après ajout cellules 1+2) ---
CELL_TIPS_TROUBLESHOOTING = create_markdown_cell([
    '## 💡 Tips & Troubleshooting\n',
    '\n',
    '### Erreurs Courantes et Solutions\n',
    '\n',
    '#### 1. ⏱️ Timeout Error (`requests.exceptions.Timeout`)\n',
    '\n',
    '**Symptôme**: La requête échoue après 60 secondes\n',
    '\n',
    '**Causes possibles**:\n',
    '- Charge serveur élevée\n',
    '- Paramètres non-optimaux (steps > 4)\n',
    '- Résolution trop élevée (>768×768)\n',
    '\n',
    '**Solutions**:\n',
    '```python\n',
    '# Augmenter timeout si nécessaire\n',
    'TIMEOUT = 90  # au lieu de 60\n',
    '\n',
    '# Vérifier paramètres Turbo\n',
    'steps = 4       # ✅ Optimal\n',
    'cfg_scale = 2.0 # ✅ Optimal\n',
    'width = 512     # ✅ Optimal\n',
    '```\n',
    '\n',
    '#### 2. ❌ Bad Request Error (HTTP 400)\n',
    '\n',
    '**Symptôme**: `response.status_code == 400`\n',
    '\n',
    '**Causes possibles**:\n',
    '- Payload JSON mal formé\n',
    '- Paramètres invalides (sampler inconnu, résolution impaire)\n',
    '- Prompt trop long (>77 tokens)\n',
    '\n',
    '**Solutions**:\n',
    '```python\n',
    '# Valider payload avant envoi\n',
    'import json\n',
    'try:\n',
    '    json.dumps(payload)  # Test sérialisation\n',
    'except TypeError as e:\n',
    '    print(f"Payload invalide: {e}")\n',
    '\n',
    '# Vérifier résolution (multiple de 64)\n',
    'width = (width // 64) * 64\n',
    'height = (height // 64) * 64\n',
    '```\n',
    '\n',
    '#### 3. 🖼️ Image Non Générée (payload vide)\n',
    '\n',
    '**Symptôme**: `result["images"]` est vide ou absent\n',
    '\n',
    '**Causes possibles**:\n',
    '- Prompt contient mots-clés bloqués (NSFW filter)\n',
    '- Modèle non chargé côté serveur\n',
    '\n',
    '**Solutions**:\n',
    '```python\n',
    '# Vérifier réponse complète\n',
    'if "images" not in result:\n',
    '    print(f"Réponse API: {result}")\n',
    '    \n',
    '# Tester avec prompt simple\n',
    'prompt_test = "a landscape"  # Minimal, neutre\n',
    '```\n',
    '\n',
    '### 🚀 Tips Performance\n',
    '\n',
    '#### Optimisation Vitesse\n',
    '\n',
    '| Action | Gain | Trade-off |\n',
    '|--------|------|----------|\n',
    '| `steps=4` (vs 20) | **~4× plus rapide** | Légère réduction qualité |\n',
    '| `512×512` (vs 768×768) | **~2× plus rapide** | Résolution inférieure |\n',
    '| `cfg_scale=2.0` (vs 7.0) | **~1.5× plus rapide** | Moins de guidage |\n',
    '\n',
    '#### Optimisation Qualité\n',
    '\n',
    '```python\n',
    '# Pour génération finale haute qualité\n',
    'image_hq = generate_image_forge(\n',
    '    prompt=prompt,\n',
    '    steps=6,          # ⚠️ Compromis: +50% temps\n',
    '    cfg_scale=2.5,    # Guidage légèrement renforcé\n',
    '    width=768,\n',
    '    height=768\n',
    ')\n',
    '```\n',
    '\n',
    '### 📚 Ressources Complémentaires\n',
    '\n',
    '- **Guide Prompts Efficaces**: [Lexica.art](https://lexica.art) (exemples visuels)\n',
    '- **Samplers Comparés**: [Stable Diffusion Wiki](https://github.com/AUTOMATIC1111/stable-diffusion-webui/wiki/Features#sampling-method-selection)\n',
    '- **Negative Prompts Templates**: [PromptHero](https://prompthero.com/stable-diffusion-negative-prompts)\n',
    '\n',
    '### 🔗 Liens Utiles\n',
    '\n',
    '- **Documentation API Complète**: [`GUIDE-APIS-ETUDIANTS.md`](../../../docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md)\n',
    '- **Notebook Qwen (Édition Images)**: [`01-5-Qwen-Image-Edit.ipynb`](01-5-Qwen-Image-Edit.ipynb)\n',
    '- **Status API Temps Réel**: `https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/progress`\n'
])

def main():
    """Fonction principale d'amélioration du notebook"""
    
    print("🔧 Amélioration Notebook Forge SD XL Turbo - Phase 21")
    print("=" * 60)
    
    # Lecture notebook
    print(f"\n📖 Lecture: {NOTEBOOK_PATH}")
    try:
        with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
            notebook = json.load(f)
    except FileNotFoundError:
        print(f"❌ Erreur: Fichier introuvable: {NOTEBOOK_PATH}")
        return 1
    except json.JSONDecodeError as e:
        print(f"❌ Erreur parsing JSON: {e}")
        return 1
    
    cells = notebook.get('cells', [])
    initial_count = len(cells)
    print(f"   Cellules initiales: {initial_count}")
    
    # Insertion cellules aux positions spécifiées
    insertions = [
        (2, CELL_INTRO_VISUELLE, "Introduction Visuelle"),
        (10 + 1, CELL_EXEMPLES_AVANCES, "Exemples Avancés"),  # +1 car cellule 1 déjà insérée
        (12 + 2, CELL_TIPS_TROUBLESHOOTING, "Tips & Troubleshooting")  # +2 car cellules 1+2 déjà insérées
    ]
    
    print("\n🔨 Insertion cellules:")
    for idx, cell, name in insertions:
        cells.insert(idx, cell)
        print(f"   ✅ [{idx:2d}] {name} ({cell['cell_type']})")
    
    notebook['cells'] = cells
    final_count = len(cells)
    print(f"\n📊 Résultat: {initial_count} → {final_count} cellules (+{final_count - initial_count})")
    
    # Sauvegarde
    print(f"\n💾 Sauvegarde: {NOTEBOOK_PATH}")
    try:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, ensure_ascii=False, indent=1)
        print("   ✅ Notebook sauvegardé avec succès")
    except Exception as e:
        print(f"   ❌ Erreur sauvegarde: {e}")
        return 1
    
    print("\n✅ Amélioration terminée avec succès!")
    print("\n📝 Modifications appliquées:")
    print("   • [Index 2]  Introduction Visuelle + Vérification API")
    print("   • [Index 11] Techniques Avancées (seed, batch, exploration)")
    print("   • [Index 14] Tips & Troubleshooting complets")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())