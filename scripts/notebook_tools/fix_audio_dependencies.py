#!/usr/bin/env python3
"""
Fix Audio GPU notebooks - Add graceful dependency detection

This script adds a dependency detection cell to GPU notebooks that:
1. Checks if required packages are installed
2. Displays clear messages for missing dependencies
3. Sets flags to skip functionality gracefully
4. Provides installation instructions
"""

import json
from pathlib import Path
from typing import List, Dict

# Notebook-specific dependency configurations
GPU_DEPENDENCIES = {
    'Audio/01-Foundation/01-5-Kokoro-TTS-Local.ipynb': {
        'packages': ['kokoro-onnx', 'kokoro'],
        'primary': 'kokoro-onnx',
        'fallback': 'kokoro',
        'install': 'pip install kokoro-onnx',
        'optional': True,
        'description': 'Kokoro TTS local (82M params, MIT license)',
    },
    'Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb': {
        'packages': ['chatterbox-tts'],
        'primary': 'chatterbox-tts',
        'install': 'pip install chatterbox-tts',
        'optional': True,
        'description': 'Chatterbox TTS (expressive speech, ~8 GB VRAM)',
    },
    'Audio/02-Advanced/02-2-XTTS-Voice-Cloning.ipynb': {
        'packages': ['TTS'],
        'primary': 'TTS',
        'install': 'pip install TTS',
        'optional': True,
        'description': 'Coqui TTS (XTTS v2 voice cloning, ~6 GB VRAM)',
    },
    'Audio/02-Advanced/02-3-MusicGen-Generation.ipynb': {
        'packages': ['audiocraft'],
        'primary': 'audiocraft',
        'install': 'pip install audiocraft',
        'optional': True,
        'description': 'AudioCraft (MusicGen, ~10 GB VRAM)',
    },
    'Audio/02-Advanced/02-4-Demucs-Source-Separation.ipynb': {
        'packages': ['demucs', 'torchaudio'],
        'primary': 'demucs',
        'secondary': ['torchaudio'],
        'install': 'pip install demucs torchaudio',
        'optional': True,
        'description': 'Demucs v4 (source separation, ~4 GB VRAM)',
    },
}


def create_dependency_cell(config: Dict) -> Dict:
    """Create a dependency detection cell for a notebook."""
    packages = config['packages']
    primary = config.get('primary', packages[0])
    fallback = config.get('fallback')
    secondary = config.get('secondary', [])
    install_cmd = config['install']
    description = config['description']
    optional = config['optional']

    # Build the import checks
    import_checks = []
    for pkg in packages:
        import_name = pkg.replace('-', '_') if '-' in pkg else pkg
        import_checks.append(f"""
try:
    import {import_name}
    {pkg.replace('-', '_').replace('.', '_')}_available = True
    print("  {pkg}: INSTALLE")
except ImportError:
    {pkg.replace('-', '_').replace('.', '_')}_available = False
    print("  {pkg}: NON INSTALLE")""")

    import_code = "".join(import_checks)

    # Build the availability logic
    availability_logic = f"""
# Verifier la disponibilite des modeles
if {' or '.join([f"{p.replace('-', '_').replace('.', '_')}_available" for p in packages])}:
    print(f"\\nStatut: Les modeles GPU sont disponibles pour ce notebook.")
    print(f"Description: {description}")
else:
    print(f"\\nStatut: Les dependances GPU ne sont pas installees.")
    print(f"\\nATTENTION: Ce notebook necessite des dependances GPU optionnelles.")
    print(f"Description: {description}")
    print(f"\\nInstallation requise:")
    print(f"  {install_cmd}")
    print(f"\\nSans ces dependances, ce notebook s'exécutera en mode limite (API uniquement).")
"""

    if fallback:
        availability_logic += f"""
# Fallback: essayer le package secondaire
if not {primary.replace('-', '_').replace('.', '_')}_available and {fallback.replace('-', '_').replace('.', '_')}_available:
    print(f"\\nNote: Utilisation du fallback {fallback} au lieu de {primary}")
"""

    cell_code = f'''# Detection des dependances GPU
print("VERIFICATION DES DEPENDANCES GPU")
print("=" * 50)
print(f"Notebook: {description}")
print(f"Packages requis: {', '.join(packages)}")
print()
{import_code}
{availability_logic}
print("=" * 50)
'''

    return {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": cell_code.strip().split('\n')
    }


def find_insert_position(cells: List[Dict]) -> int:
    """Find the position to insert the dependency cell (after setup, before first section)."""
    for i, cell in enumerate(cells):
        if cell.get('cell_type') == 'markdown':
            content = ''.join(cell.get('source', []))
            # Look for first section header (## Section X)
            if content.strip().startswith('## Section'):
                return i
    # Fallback: insert after the params cell (usually index 2)
    return min(3, len(cells) - 1)


def fix_notebook(notebook_path: Path, config: Dict) -> bool:
    """Add dependency detection to a notebook."""
    print(f"Processing: {notebook_path.relative_to(notebook_path.parents[3])}")

    # Read notebook
    with open(notebook_path, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    # Check if dependency cell already exists
    for cell in notebook.get('cells', []):
        if 'VERIFICATION DES DEPENDANCES GPU' in ''.join(cell.get('source', [])):
            print(f"  Skip: Dependency cell already exists")
            return False

    # Create the dependency cell
    dep_cell = create_dependency_cell(config)

    # Find insert position
    insert_pos = find_insert_position(notebook.get('cells', []))

    # Insert the cell
    notebook['cells'].insert(insert_pos, dep_cell)

    # Write back
    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)

    print(f"  Done: Dependency cell inserted at position {insert_pos}")
    return True


def main():
    """Main function to fix all GPU notebooks."""
    root = Path(__file__).parents[2] / 'MyIA.AI.Notebooks' / 'GenAI'

    print("=" * 60)
    print("Fix Audio GPU Notebooks - Dependency Detection")
    print("=" * 60)
    print(f"Root: {root}")
    print()

    fixed_count = 0
    skipped_count = 0

    for rel_path, config in GPU_DEPENDENCIES.items():
        notebook_path = root / rel_path
        if not notebook_path.exists():
            print(f"Skip: {rel_path} (not found)")
            skipped_count += 1
            continue

        if fix_notebook(notebook_path, config):
            fixed_count += 1
        else:
            skipped_count += 1
        print()

    print("=" * 60)
    print(f"Summary: {fixed_count} fixed, {skipped_count} skipped")
    print("=" * 60)


if __name__ == '__main__':
    main()
