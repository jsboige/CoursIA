"""Apply robust .env loading pattern to all GenAI notebooks

Pattern robuste avec env_loaded:
- Recherche .env dans TOUS les parents (pas juste GenAI_ROOT)
- Vérifie existence AVANT de charger
- Variable env_loaded pour confirmation
- WARNING si pas trouvé
"""
import json
from pathlib import Path

# Vrai pattern robuste (comme dans Audio notebooks)
ROBUST_PATTERN = '''# Chargement robuste de la configuration .env
from dotenv import load_dotenv
import os

# Recherche du .env dans tous les parents (pour Papermill qui change le cwd)
current_path = Path.cwd()
env_loaded = False
while current_path.name != "GenAI" and len(current_path.parts) > 1:
    env_path = current_path / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f".env charge depuis: {env_path}")
        env_loaded = True
        break
    current_path = current_path.parent

if not env_loaded:
    print("WARNING: .env non trouve, utilisation variables environnement")'''

def has_env_loading(source):
    """Check if cell contains .env loading code"""
    return any(keyword in source for keyword in ['load_dotenv', '.env', 'GENAI_ROOT'])

def needs_fix(source):
    """Check if cell has old pattern that needs fixing"""
    # Needs fix if has .env code but NOT robust pattern
    if not has_env_loading(source):
        return False
    return 'env_loaded' not in source

def fix_notebook(nb_path):
    """Apply robust pattern to a single notebook"""
    print(f"Processing {nb_path}...")

    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    modified = False
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell.get('source', []))

        if needs_fix(source):
            # Remove old .env loading code and insert robust pattern
            lines = cell.get('source', [])
            new_lines = []
            skipped_env_code = False

            for line in lines:
                # Skip old .env loading lines
                if any(keyword in line for keyword in [
                    'GENAI_ROOT = Path.cwd()',
                    'while GENAI_ROOT.name',
                    'while current_path.name',
                    'load_dotenv(',
                    'env_path =',
                    '.env"'
                ]):
                    if not skipped_env_code:
                        # Insert robust pattern at first removal
                        new_lines.extend(ROBUST_PATTERN.split('\n'))
                        skipped_env_code = True
                        new_lines.append('')  # blank line after
                    # Skip this line
                else:
                    new_lines.append(line)

            if skipped_env_code:
                cell['source'] = new_lines
                modified = True
                print(f"  Fixed cell {i}")

    if modified:
        with open(nb_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
        print(f"  -> Saved")
        return True
    else:
        print(f"  -> No changes (already robust or no .env code)")
        return False

def main():
    base = Path('MyIA.AI.Notebooks/GenAI')

    # Notebooks to fix (those with .env loading but not robust)
    categories = {
        'Image': [
            'Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb',
            'Image/01-Foundation/01-2-GPT-5-Image-Generation.ipynb',
            'Image/01-Foundation/01-3-Basic-Image-Operations.ipynb',
            'Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb',
            'Image/01-Foundation/01-5-Qwen-Image-Edit.ipynb',
            'Image/02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb',
            'Image/02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb',
            'Image/02-Advanced/02-3-Stable-Diffusion-3-5.ipynb',
            'Image/02-Advanced/02-4-Z-Image-Lumina2.ipynb',
            'Image/03-Orchestration/03-1-Multi-Model-Comparison.ipynb',
            'Image/03-Orchestration/03-2-Workflow-Orchestration.ipynb',
            'Image/03-Orchestration/03-3-Performance-Optimization.ipynb',
            'Image/04-Applications/04-1-Educational-Content-Generation.ipynb',
            'Image/04-Applications/04-2-Creative-Workflows.ipynb',
            'Image/04-Applications/04-3-Production-Integration.ipynb',
            'Image/04-Applications/04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb',
            'Image/examples/history-geography.ipynb',
            'Image/examples/literature-visual.ipynb',
            'Image/examples/science-diagrams.ipynb',
        ],
        'Video': [
            'Video/01-Foundation/01-1-Video-Operations-Basics.ipynb',
            'Video/01-Foundation/01-2-GPT-5-Video-Understanding.ipynb',
            'Video/01-Foundation/01-3-Qwen-VL-Video-Analysis.ipynb',
            'Video/01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb',
            'Video/01-Foundation/01-5-AnimateDiff-Introduction.ipynb',
            'Video/02-Advanced/02-1-HunyuanVideo-Generation.ipynb',
            'Video/02-Advanced/02-2-LTX-Video-Lightweight.ipynb',
            'Video/02-Advanced/02-3-Wan-Video-Generation.ipynb',
            'Video/02-Advanced/02-4-SVD-Image-to-Video.ipynb',
            'Video/03-Orchestration/03-1-Multi-Model-Video-Comparison.ipynb',
            'Video/03-Orchestration/03-2-Video-Workflow-Orchestration.ipynb',
            'Video/03-Orchestration/03-3-ComfyUI-Video-Workflows.ipynb',
            'Video/04-Applications/04-1-Educational-Video-Generation.ipynb',
            'Video/04-Applications/04-2-Creative-Video-Workflows.ipynb',
            'Video/04-Applications/04-3-Sora-API-Cloud-Video.ipynb',
            'Video/04-Applications/04-4-Production-Video-Pipeline.ipynb',
        ],
        'Texte': [
            'Texte/1_OpenAI_Intro.ipynb',
            'Texte/2_PromptEngineering.ipynb',
            'Texte/3_Structured_Outputs.ipynb',
            'Texte/4_Function_Calling.ipynb',
            'Texte/5_RAG_Modern.ipynb',
            'Texte/6_PDF_Web_Search.ipynb',
            'Texte/7_Code_Interpreter.ipynb',
            'Texte/8_Reasoning_Models.ipynb',
            'Texte/9_Production_Patterns.ipynb',
            'Texte/10_LocalLlama.ipynb',
            'Texte/11_Quantization.ipynb',
        ]
    }

    results = {'Image': [], 'Video': [], 'Texte': []}

    for category, notebooks in categories.items():
        print(f"\n{'='*60}")
        print(f"Processing {category} ({len(notebooks)} notebooks)")
        print('='*60)

        for nb_rel in notebooks:
            nb_path = base / nb_rel
            if not nb_path.exists():
                print(f"  NOT FOUND: {nb_rel}")
                continue

            if fix_notebook(nb_path):
                results[category].append(nb_rel)

    print(f"\n{'='*60}")
    print("SUMMARY")
    print('='*60)
    for cat, fixed in results.items():
        print(f"{cat}: {len(fixed)} fixed")
    print(f"Total: {sum(len(v) for v in results.values())} notebooks fixed")

if __name__ == '__main__':
    main()
