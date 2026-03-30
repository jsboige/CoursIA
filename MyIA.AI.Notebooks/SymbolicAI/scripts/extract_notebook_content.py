#!/usr/bin/env python3
"""
Extrait les débuts de cellules de tous les notebooks du répertoire SymbolicAI.
Utile pour générer un README complet.
"""

import json
import os
from pathlib import Path

def extract_cell_preview(cell, max_lines=3, max_chars=200):
    """Extrait un aperçu d'une cellule."""
    source = cell.get('source', [])
    if isinstance(source, str):
        lines = source.split('\n')
    else:
        lines = source

    # Nettoyer et prendre les premières lignes
    clean_lines = []
    for line in lines[:max_lines]:
        line = line.strip()
        if line and not line.startswith('#!'):  # Ignorer les magics .NET
            clean_lines.append(line)

    preview = ' '.join(clean_lines)[:max_chars]
    return preview

def analyze_notebook(notebook_path):
    """Analyse un notebook et retourne ses informations."""
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except Exception as e:
        return {'error': str(e)}

    cells = nb.get('cells', [])

    # Extraire le kernel
    kernel = nb.get('metadata', {}).get('kernelspec', {}).get('display_name', 'Unknown')

    # Compter les types de cellules
    markdown_cells = [c for c in cells if c.get('cell_type') == 'markdown']
    code_cells = [c for c in cells if c.get('cell_type') == 'code']

    # Extraire le titre (premier markdown qui commence par #)
    title = None
    for cell in markdown_cells:
        source = ''.join(cell.get('source', []))
        for line in source.split('\n'):
            if line.startswith('# '):
                title = line[2:].strip()
                break
        if title:
            break

    # Extraire les sections (## headers)
    sections = []
    for cell in markdown_cells:
        source = ''.join(cell.get('source', []))
        for line in source.split('\n'):
            if line.startswith('## '):
                sections.append(line[3:].strip())

    # Extraire les sous-sections (### headers) pour plus de détail
    subsections = []
    for cell in markdown_cells:
        source = ''.join(cell.get('source', []))
        for line in source.split('\n'):
            if line.startswith('### '):
                subsections.append(line[4:].strip())

    return {
        'path': str(notebook_path),
        'name': notebook_path.stem,
        'kernel': kernel,
        'title': title,
        'total_cells': len(cells),
        'markdown_cells': len(markdown_cells),
        'code_cells': len(code_cells),
        'sections': sections,
        'subsections': subsections[:20],  # Limiter
    }

def scan_directory(base_dir):
    """Scanne récursivement un répertoire pour les notebooks."""
    base_path = Path(base_dir)
    notebooks = []

    for notebook_path in sorted(base_path.rglob('*.ipynb')):
        # Ignorer les checkpoints
        if '.ipynb_checkpoints' in str(notebook_path):
            continue
        # Ignorer archive
        if 'archive' in str(notebook_path).lower():
            continue

        rel_path = notebook_path.relative_to(base_path)
        info = analyze_notebook(notebook_path)
        info['relative_path'] = str(rel_path)
        info['directory'] = str(rel_path.parent) if rel_path.parent != Path('.') else 'root'
        notebooks.append(info)

    return notebooks

def generate_report(notebooks):
    """Génère un rapport formaté."""
    # Grouper par répertoire
    by_dir = {}
    for nb in notebooks:
        d = nb.get('directory', 'root')
        if d not in by_dir:
            by_dir[d] = []
        by_dir[d].append(nb)

    print("=" * 80)
    print("RAPPORT DES NOTEBOOKS - SymbolicAI")
    print("=" * 80)
    print(f"\nTotal: {len(notebooks)} notebooks\n")

    for directory, nbs in sorted(by_dir.items()):
        print(f"\n{'='*60}")
        print(f"📁 {directory.upper()}")
        print(f"{'='*60}")

        for nb in nbs:
            print(f"\n--- {nb.get('name', 'Unknown')} ---")
            print(f"  Kernel: {nb.get('kernel', 'Unknown')}")
            print(f"  Titre: {nb.get('title', 'Sans titre')}")
            print(f"  Cellules: {nb.get('total_cells', 0)} (md:{nb.get('markdown_cells',0)}, code:{nb.get('code_cells',0)})")

            sections = nb.get('sections', [])
            if sections:
                print(f"  Sections ({len(sections)}):")
                for s in sections[:10]:
                    print(f"    - {s}")
                if len(sections) > 10:
                    print(f"    ... et {len(sections)-10} autres")

            subsections = nb.get('subsections', [])
            if subsections and len(subsections) > len(sections):
                print(f"  Sous-sections notables:")
                for s in subsections[:8]:
                    print(f"    · {s}")

def generate_markdown_table(notebooks):
    """Génère des tableaux markdown pour le README."""
    by_dir = {}
    for nb in notebooks:
        d = nb.get('directory', 'root')
        if d not in by_dir:
            by_dir[d] = []
        by_dir[d].append(nb)

    print("\n" + "="*80)
    print("TABLEAUX MARKDOWN POUR README")
    print("="*80)

    for directory, nbs in sorted(by_dir.items()):
        print(f"\n### {directory}\n")
        print("| Notebook | Cellules | Sections principales |")
        print("|----------|----------|---------------------|")
        for nb in nbs:
            name = nb.get('name', 'Unknown')
            cells = nb.get('total_cells', 0)
            sections = nb.get('sections', [])[:3]
            sections_str = ', '.join(sections) if sections else '-'
            if len(sections_str) > 50:
                sections_str = sections_str[:47] + '...'
            print(f"| {name} | {cells} | {sections_str} |")

if __name__ == '__main__':
    base_dir = Path(__file__).parent.parent  # SymbolicAI/
    print(f"Scanning: {base_dir}\n")

    notebooks = scan_directory(base_dir)
    generate_report(notebooks)
    generate_markdown_table(notebooks)
