"""Fix .env loading with relative paths in notebooks"""
import json

notebooks_to_fix = [
    'MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb',
    'MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-3-Stable-Diffusion-3-5.ipynb',
    'MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-4-Z-Image-Lumina2.ipynb'
]

new_pattern = '''# Chargement variables d'environnement
from dotenv import load_dotenv

# Recherche du .env en remontant l'arborescence (robuste pour Papermill)
current_path = Path.cwd()
while current_path.name != 'GenAI' and len(current_path.parts) > 1:
    current_path = current_path.parent
env_path = current_path / '.env'
if env_path.exists():
    load_dotenv(env_path)
    print(f"Fichier .env charge depuis: {env_path}")
else:
    print("Aucun fichier .env trouve dans l'arborescence")'''

for nb_path in notebooks_to_fix:
    print(f'Processing {nb_path.split("/")[-1]}...')
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    modified = False
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'code':
            source = ''.join(cell.get('source', []))
            # Check if this cell has load_dotenv with relative paths
            if 'load_dotenv' in source and ('../' in source):
                # Check if already robust
                if 'Path.cwd()' in source and 'while current_path.name' in source:
                    print(f'  Cell {i}: Already has robust pattern, skipping')
                    continue

                # Replace load_dotenv lines with new pattern
                lines = cell.get('source', [])
                new_lines = []
                skipped_load_dotenv = False
                for line in lines:
                    if 'load_dotenv' in line and '../' in line:
                        if not skipped_load_dotenv:
                            new_lines.extend(new_pattern.splitlines(keepends=True))
                            skipped_load_dotenv = True
                        # Skip the old load_dotenv line
                    else:
                        new_lines.append(line)

                if skipped_load_dotenv:
                    cell['source'] = new_lines
                    modified = True
                    print(f'  Cell {i}: Fixed load_dotenv pattern')

    if modified:
        with open(nb_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
        print(f'  -> Saved')
    else:
        print(f'  -> No changes needed')

print('\nDone!')
