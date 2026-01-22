#!/usr/bin/env python3
"""
Script de réorganisation des notebooks Tweety
Sépare Tweety-5 en deux notebooks :
- Tweety-5 : Argumentation Abstraite (Dung uniquement)
- Tweety-6 : Argumentation Structurée (ASPIC+, DeLP, ABA, etc.)
Et renomme l'ancien Tweety-6 en Tweety-7
"""

import json
import shutil
from pathlib import Path

def read_notebook(path):
    """Lit un notebook et retourne son contenu JSON"""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def write_notebook(path, nb):
    """Écrit un notebook au format JSON"""
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f"✓ Écrit: {path}")

def create_notebook_from_cells(cells, metadata=None):
    """Crée un nouveau notebook à partir d'une liste de cellules"""
    if metadata is None:
        metadata = {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            },
            "language_info": {
                "name": "python",
                "version": "3.10.0"
            }
        }

    return {
        "cells": cells,
        "metadata": metadata,
        "nbformat": 4,
        "nbformat_minor": 5
    }

def main():
    base_dir = Path(".")

    # 1. Lire Tweety-5 actuel
    tweety5_path = base_dir / "Tweety-5-Abstract-Argumentation.ipynb"
    print(f"\nLecture de {tweety5_path}...")
    tweety5 = read_notebook(tweety5_path)

    # Sauvegarder une copie de backup
    backup_path = base_dir / "Tweety-5-Abstract-Argumentation.ipynb.backup"
    shutil.copy(tweety5_path, backup_path)
    print(f"✓ Backup créé: {backup_path}")

    cells = tweety5['cells']
    metadata = tweety5['metadata']

    # 2. Séparer les cellules
    # Cellules 0-1: Header + Init
    # Cellules 2-10: Section 4.1 Dung
    # Cellules 11-20: Sections 4.2-4.6 Structured
    # Cellule 21: Navigation

    init_cells = cells[0:2]  # Header + Init
    dung_cells = cells[2:11]  # Section 4.1 complète
    structured_cells = cells[11:21]  # Sections 4.2-4.6

    print(f"\n✓ Séparation des cellules:")
    print(f"  - Init: {len(init_cells)} cellules")
    print(f"  - Dung (4.1): {len(dung_cells)} cellules")
    print(f"  - Structured (4.2-4.6): {len(structured_cells)} cellules")

    # 3. Créer nouveau Tweety-5 (Dung uniquement)
    new_tweety5_cells = init_cells + dung_cells

    # Ajouter cellule de navigation pour Tweety-5
    nav_tweety5 = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "---\n",
            "\n",
            "## Navigation\n",
            "\n",
            "- **Precedent**: [Tweety-4-Belief-Revision.ipynb](Tweety-4-Belief-Revision.ipynb)\n",
            "- **Suivant**: [Tweety-6-Structured-Argumentation.ipynb](Tweety-6-Structured-Argumentation.ipynb)\n",
            "- **Index**: [Tweety-1-Setup.ipynb](Tweety-1-Setup.ipynb)\n"
        ]
    }
    new_tweety5_cells.append(nav_tweety5)

    new_tweety5 = create_notebook_from_cells(new_tweety5_cells, metadata)

    # Mettre à jour le titre du notebook
    if new_tweety5_cells[0]['cell_type'] == 'markdown':
        new_tweety5_cells[0]['source'] = [
            "# Argumentation Abstraite (Dung)\n",
            "\n",
            "Ce notebook couvre les cadres d'argumentation abstraits de Dung.\n",
            "\n",
            "**Pre-requis**: Executez d'abord [Tweety-1-Setup.ipynb](Tweety-1-Setup.ipynb) pour configurer l'environnement.\n",
            "\n",
            "**Navigation**: [Precedent](Tweety-4-Belief-Revision.ipynb) | [Suivant](Tweety-6-Structured-Argumentation.ipynb)\n"
        ]

    write_notebook(tweety5_path, new_tweety5)

    # 4. Créer Tweety-6 (Argumentation Structurée)
    tweety6_cells = init_cells.copy()

    # Modifier le header pour Tweety-6
    header_tweety6 = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "# Argumentation Structuree\n",
            "\n",
            "Ce notebook couvre les frameworks d'argumentation structuree : ASPIC+, DeLP, ABA, Argumentation Deductive et ASP.\n",
            "\n",
            "**Pre-requis**: Executez d'abord [Tweety-1-Setup.ipynb](Tweety-1-Setup.ipynb) pour configurer l'environnement.\n",
            "\n",
            "**Navigation**: [Precedent](Tweety-5-Abstract-Argumentation.ipynb) | [Suivant](Tweety-7-Advanced-Argumentation.ipynb)\n"
        ]
    }

    tweety6_cells[0] = header_tweety6
    tweety6_cells.extend(structured_cells)

    # Ajouter navigation pour Tweety-6
    nav_tweety6 = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "---\n",
            "\n",
            "## Navigation\n",
            "\n",
            "- **Precedent**: [Tweety-5-Abstract-Argumentation.ipynb](Tweety-5-Abstract-Argumentation.ipynb)\n",
            "- **Suivant**: [Tweety-7-Advanced-Argumentation.ipynb](Tweety-7-Advanced-Argumentation.ipynb)\n",
            "- **Index**: [Tweety-1-Setup.ipynb](Tweety-1-Setup.ipynb)\n"
        ]
    }
    tweety6_cells.append(nav_tweety6)

    new_tweety6 = create_notebook_from_cells(tweety6_cells, metadata)
    tweety6_path = base_dir / "Tweety-6-Structured-Argumentation.ipynb"
    write_notebook(tweety6_path, new_tweety6)

    # 5. Renommer ancien Tweety-6 en Tweety-7
    old_tweety6_path = base_dir / "Tweety-6-Advanced-Argumentation.ipynb"
    tweety7_path = base_dir / "Tweety-7-Advanced-Argumentation.ipynb"

    if old_tweety6_path.exists():
        print(f"\nRenommage {old_tweety6_path} → {tweety7_path}...")

        # Lire et mettre à jour les liens de navigation
        tweety7 = read_notebook(old_tweety6_path)

        # Mettre à jour le header si c'est du markdown
        if tweety7['cells'][0]['cell_type'] == 'markdown':
            tweety7['cells'][0]['source'] = [
                line.replace('Tweety-5-Abstract-Argumentation', 'Tweety-6-Structured-Argumentation')
                for line in tweety7['cells'][0]['source']
            ]

        # Mettre à jour la navigation footer
        for cell in tweety7['cells']:
            if cell['cell_type'] == 'markdown' and '## Navigation' in ''.join(cell['source']):
                cell['source'] = [
                    line.replace('Tweety-5-Abstract-Argumentation', 'Tweety-6-Structured-Argumentation')
                    for line in cell['source']
                ]

        write_notebook(tweety7_path, tweety7)

        # Supprimer l'ancien fichier
        old_tweety6_path.unlink()
        print(f"✓ Supprimé: {old_tweety6_path}")

    print("\n" + "="*60)
    print("✓ Réorganisation terminée avec succès !")
    print("="*60)
    print(f"\nNouvelle structure :")
    print(f"  - Tweety-5-Abstract-Argumentation.ipynb (Dung uniquement)")
    print(f"  - Tweety-6-Structured-Argumentation.ipynb (ASPIC+, DeLP, ABA, etc.)")
    print(f"  - Tweety-7-Advanced-Argumentation.ipynb (ancien Tweety-6)")
    print(f"\nBackup conservé : {backup_path}")

if __name__ == "__main__":
    main()
