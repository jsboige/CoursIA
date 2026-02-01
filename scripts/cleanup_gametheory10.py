#!/usr/bin/env python3
"""
Script pour nettoyer GameTheory-10-ForwardInduction-SPE.ipynb
Reorganise les cellules markdown pedagogiques au bon endroit.
"""

import json
import sys
from pathlib import Path

def find_cell_by_content(cells, start_text, cell_type='markdown'):
    """Trouve une cellule par le debut de son contenu."""
    for idx, cell in enumerate(cells):
        if cell['cell_type'] != cell_type:
            continue
        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
        if source.startswith(start_text):
            return idx
    return -1

def move_cell(cells, from_idx, to_idx):
    """Deplace une cellule de from_idx vers to_idx."""
    if from_idx < 0 or from_idx >= len(cells):
        print(f"  WARNING: from_idx {from_idx} invalide")
        return cells
    if to_idx < 0 or to_idx > len(cells):
        print(f"  WARNING: to_idx {to_idx} invalide")
        return cells

    cell = cells.pop(from_idx)
    # Ajuster to_idx si necessaire
    if from_idx < to_idx:
        to_idx -= 1
    cells.insert(to_idx, cell)
    return cells

def main():
    notebook_path = Path("MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE.ipynb")

    if not notebook_path.exists():
        print(f"ERROR: Notebook non trouve: {notebook_path}")
        sys.exit(1)

    # Charger le notebook
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    print(f"Notebook charge: {len(cells)} cellules\n")

    # IMPORTANT: Travailler du BAS vers le HAUT pour eviter les decalages d'indices

    # 1. Cell 27 (Applications) -> avant cell 40 (Resume)
    print("1. Deplacement cell 27 (Applications) vers avant Resume...")
    idx_app = find_cell_by_content(cells, "### Applications des concepts")
    idx_resume = find_cell_by_content(cells, "## 8. Resume")
    if idx_app >= 0 and idx_resume >= 0:
        cells = move_cell(cells, idx_app, idx_resume)
        print(f"   {idx_app} -> {idx_resume}")

    # 2. Cell 26 (Structure solutions) -> apres cell 39 (espace solutions)
    print("2. Deplacement cell 26 (Structure solutions) apres espace solutions...")
    idx_struct = find_cell_by_content(cells, "### Structure pour vos solutions")
    idx_espace = find_cell_by_content(cells, "# Espace pour vos solutions", cell_type='code')
    if idx_struct >= 0 and idx_espace >= 0:
        cells = move_cell(cells, idx_struct, idx_espace + 1)
        print(f"   {idx_struct} -> {idx_espace + 1}")

    # 3. Cell 25 (Guide exercices) -> apres cell 38 (Exercices)
    print("3. Deplacement cell 25 (Guide exercices) apres Exercices...")
    idx_guide = find_cell_by_content(cells, "### Guide pour résoudre")
    idx_exo = find_cell_by_content(cells, "## 7. Exercices")
    if idx_guide >= 0 and idx_exo >= 0:
        # Trouver la fin de la section Exercices (prochaine cell markdown apres)
        next_md = idx_exo + 1
        while next_md < len(cells) and cells[next_md]['cell_type'] != 'code':
            next_md += 1
        cells = move_cell(cells, idx_guide, next_md)
        print(f"   {idx_guide} -> {next_md}")

    # 4. Cell 24 (Interpretation diagramme) -> apres cell 37 (visualisation)
    print("4. Deplacement cell 24 (Interpretation diagramme) apres visualisation...")
    idx_interp_diag = find_cell_by_content(cells, "### Interprétation du diagramme")
    idx_vis_hier = find_cell_by_content(cells, "def visualize_refinement_hierarchy", cell_type='code')
    if idx_interp_diag >= 0 and idx_vis_hier >= 0:
        cells = move_cell(cells, idx_interp_diag, idx_vis_hier + 1)
        print(f"   {idx_interp_diag} -> {idx_vis_hier + 1}")

    # 5. Cell 23 (Interpretation exemples) -> apres cell 36 (comparison)
    print("5. Deplacement cell 23 (Interpretation exemples) apres comparison...")
    idx_interp_ex = find_cell_by_content(cells, "### Interprétation des exemples comparatifs")
    idx_comp = find_cell_by_content(cells, "def comparison_summary", cell_type='code')
    if idx_interp_ex >= 0 and idx_comp >= 0:
        cells = move_cell(cells, idx_interp_ex, idx_comp + 1)
        print(f"   {idx_interp_ex} -> {idx_comp + 1}")

    # 6. Cell 22 (Relation raffinements) -> avant cell 35 (tableau)
    print("6. Deplacement cell 22 (Relation raffinements) avant tableau...")
    idx_rel = find_cell_by_content(cells, "### Relation entre les raffinements")
    idx_tab = find_cell_by_content(cells, "## 6. Comparaison des Raffinements")
    if idx_rel >= 0 and idx_tab >= 0:
        cells = move_cell(cells, idx_rel, idx_tab)
        print(f"   {idx_rel} -> {idx_tab}")

    # 7. Cell 20 (Modelisation Burn Money) -> avant cell 33 (code)
    print("7. Deplacement cell 20 (Modelisation Burn Money) avant code...")
    idx_mod_burn = find_cell_by_content(cells, "### Modélisation du Burn Money Game")
    idx_analyze_burn = find_cell_by_content(cells, "def analyze_burn_money_game", cell_type='code')
    if idx_mod_burn >= 0 and idx_analyze_burn >= 0:
        cells = move_cell(cells, idx_mod_burn, idx_analyze_burn)
        print(f"   {idx_mod_burn} -> {idx_analyze_burn}")

    # 8. Cell 17 (Verification numerique) -> avant cell 30 (code)
    print("8. Deplacement cell 17 (Verification numerique) avant code...")
    idx_verif = find_cell_by_content(cells, "### Vérification numérique du trembling")
    idx_perturbed = find_cell_by_content(cells, "def perturbed_best_response", cell_type='code')
    if idx_verif >= 0 and idx_perturbed >= 0:
        cells = move_cell(cells, idx_verif, idx_perturbed)
        print(f"   {idx_verif} -> {idx_perturbed}")

    # 9. Cell 16 (Modele tremblement) -> avant cell 29 (code)
    print("9. Deplacement cell 16 (Modele tremblement) avant code...")
    idx_mod_tremb = find_cell_by_content(cells, "### Le modèle de tremblement")
    idx_demo_tremb = find_cell_by_content(cells, "def demonstrate_trembling_hand", cell_type='code')
    if idx_mod_tremb >= 0 and idx_demo_tremb >= 0:
        cells = move_cell(cells, idx_mod_tremb, idx_demo_tremb)
        print(f"   {idx_mod_tremb} -> {idx_demo_tremb}")

    # 10. Cell 14 (Interpretation visualisation) -> apres cell 21 (visualisation)
    print("10. Deplacement cell 14 (Interpretation visualisation) apres visualisation...")
    idx_interp_vis = find_cell_by_content(cells, "### Interprétation de la visualisation")
    idx_vis_fi = find_cell_by_content(cells, "def visualize_forward_induction", cell_type='code')
    if idx_interp_vis >= 0 and idx_vis_fi >= 0:
        cells = move_cell(cells, idx_interp_vis, idx_vis_fi + 1)
        print(f"   {idx_interp_vis} -> {idx_vis_fi + 1}")

    # 11. Cell 12 (Construction Stag Hunt) -> avant cell 18 (code)
    print("11. Deplacement cell 12 (Construction Stag Hunt) avant code...")
    idx_const_stag = find_cell_by_content(cells, "### Construction du modèle Stag Hunt")
    idx_create_stag = find_cell_by_content(cells, "def create_stag_hunt_with_outside", cell_type='code')
    if idx_const_stag >= 0 and idx_create_stag >= 0:
        cells = move_cell(cells, idx_const_stag, idx_create_stag)
        print(f"   {idx_const_stag} -> {idx_create_stag}")

    # 12. Cell 8 (Engagement prealable) -> avant cell 13 (code)
    print("12. Deplacement cell 8 (Engagement prealable) avant code...")
    idx_eng = find_cell_by_content(cells, "### Illustration : Le jeu de l'engagement")
    idx_create_eng = find_cell_by_content(cells, "def create_entry_game_with_commitment", cell_type='code')
    if idx_eng >= 0 and idx_create_eng >= 0:
        cells = move_cell(cells, idx_eng, idx_create_eng)
        print(f"   {idx_eng} -> {idx_create_eng}")

    # 13. Cell 5 (Algorithmes detection) -> avant cell 6 (code)
    print("13. Deplacement cell 5 (Algorithmes detection) avant code...")
    idx_algo = find_cell_by_content(cells, "### Algorithmes de détection et vérification")
    idx_identify = find_cell_by_content(cells, "def identify_subgames", cell_type='code')
    if idx_algo >= 0 and idx_identify >= 0:
        cells = move_cell(cells, idx_algo, idx_identify)
        print(f"   {idx_algo} -> {idx_identify}")

    # 14. Cell 3 (Structure donnees) -> avant cell 2 (code)
    print("14. Deplacement cell 3 (Structure donnees) avant code...")
    idx_struct_data = find_cell_by_content(cells, "### Structure de données pour les jeux")
    idx_classes = find_cell_by_content(cells, "# Classes de base", cell_type='code')
    if idx_struct_data >= 0 and idx_classes >= 0:
        cells = move_cell(cells, idx_struct_data, idx_classes)
        print(f"   {idx_struct_data} -> {idx_classes}")

    # Sauvegarder le notebook modifie
    nb['cells'] = cells

    print(f"\nEcriture du notebook nettoye ({len(cells)} cellules)...")
    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print("✓ Nettoyage termine!")
    print(f"\nNotebook sauvegarde: {notebook_path}")

if __name__ == '__main__':
    main()
