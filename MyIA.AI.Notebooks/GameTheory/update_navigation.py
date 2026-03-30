#!/usr/bin/env python3
"""Update navigation links in all GameTheory notebooks after reorganization."""

import json
import os
import re

# Define the new structure
STRUCTURE = {
    # (number, name, side_tracks)
    1: ("Setup", []),
    2: ("NormalForm", ["2b-Lean-Definitions"]),
    3: ("Topology2x2", []),
    4: ("NashEquilibrium", ["4b-Lean-NashExistence", "4c-NashExistence-Python"]),
    5: ("ZeroSum-Minimax", []),
    6: ("EvolutionTrust", []),
    7: ("ExtensiveForm", []),
    8: ("CombinatorialGames", ["8b-Lean-CombinatorialGames", "8c-CombinatorialGames-Python"]),
    9: ("BackwardInduction", []),
    10: ("ForwardInduction-SPE", []),
    11: ("BayesianGames", []),
    12: ("ReputationGames", []),
    13: ("ImperfectInfo-CFR", []),
    14: ("DifferentialGames", []),
    15: ("CooperativeGames", ["15b-Lean-CooperativeGames", "15c-CooperativeGames-Python"]),
    16: ("MechanismDesign", ["16b-Lean-SocialChoice", "16c-SocialChoice-Python"]),
    17: ("MultiAgent-RL", []),
}

# Side tracks mapping: side_track_id -> (parent_num, description)
SIDE_TRACKS = {
    "2b": (2, "Formalisation Lean des jeux en forme normale"),
    "4b": (4, "Preuve Lean de l'existence de Nash"),
    "4c": (4, "Illustrations numeriques du point fixe"),
    "8b": (8, "Formalisation Lean des jeux combinatoires"),
    "8c": (8, "Approfondissement Python des jeux combinatoires"),
    "15b": (15, "Formalisation Lean des jeux cooperatifs"),
    "15c": (15, "Exemples avances de jeux cooperatifs"),
    "16b": (16, "Formalisation Lean du choix social"),
    "16c": (16, "Simulations Python du choix social"),
}

def get_notebook_filename(num, name):
    return f"GameTheory-{num}-{name}.ipynb"

def get_side_track_filename(track_id):
    return f"GameTheory-{track_id}.ipynb"

def create_main_navigation(num, name, side_tracks):
    """Create navigation markdown for a main notebook."""
    lines = []

    # Previous/Next navigation
    prev_link = ""
    next_link = ""

    if num > 1:
        prev_num = num - 1
        prev_name = STRUCTURE[prev_num][0]
        prev_link = f"[<< {prev_num}-{prev_name}](GameTheory-{prev_num}-{prev_name}.ipynb)"

    if num < 17:
        next_num = num + 1
        next_name = STRUCTURE[next_num][0]
        next_link = f"[{next_num}-{next_name} >>](GameTheory-{next_num}-{next_name}.ipynb)"

    nav_line = " | ".join(filter(None, [prev_link, "[Index](README.md)", next_link]))
    lines.append(f"**Navigation** : {nav_line}")

    # Side tracks
    if side_tracks:
        track_links = []
        for track in side_tracks:
            track_links.append(f"[{track}](GameTheory-{track}.ipynb)")
        lines.append(f"\n**Side tracks** : {' | '.join(track_links)}")

    return "\n".join(lines)

def create_side_track_navigation(track_id):
    """Create navigation markdown for a side track notebook."""
    parent_num, desc = SIDE_TRACKS[track_id]
    parent_name = STRUCTURE[parent_num][0]
    parent_link = f"[{parent_num}-{parent_name}](GameTheory-{parent_num}-{parent_name}.ipynb)"

    # Find sibling side tracks
    siblings = STRUCTURE[parent_num][1]
    sibling_links = []
    for s in siblings:
        s_id = s.split("-")[0]
        if s_id != track_id:
            sibling_links.append(f"[{s}](GameTheory-{s}.ipynb)")

    lines = [f"**Navigation** : [<< {parent_num}-{parent_name} (track principal)]({parent_link}) | [Index](README.md)"]
    if sibling_links:
        lines.append(f"\n**Autres side tracks** : {' | '.join(sibling_links)}")

    return "\n".join(lines)

def update_notebook_navigation(filepath, is_side_track=False, track_id=None, num=None, name=None, side_tracks=None):
    """Update navigation in a notebook's first markdown cell."""
    with open(filepath, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Find the first markdown cell after any initial code cells
    nav_cell_idx = None
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'markdown':
            source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
            # Check if this looks like a navigation or title cell
            if '**Navigation**' in source or source.startswith('# ') or 'GameTheory' in source:
                nav_cell_idx = i
                break

    if nav_cell_idx is None:
        # Add navigation cell at the beginning
        nav_cell_idx = 0

    # Generate new navigation
    if is_side_track:
        nav_content = create_side_track_navigation(track_id)
    else:
        nav_content = create_main_navigation(num, name, side_tracks)

    # Get existing cell content and update navigation
    cell = nb['cells'][nav_cell_idx]
    source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

    # Remove old navigation lines
    lines = source.split('\n')
    new_lines = []
    skip_until_blank = False
    for line in lines:
        if line.startswith('**Navigation**') or line.startswith('**Side tracks**') or line.startswith('**Autres side tracks**'):
            skip_until_blank = True
            continue
        if skip_until_blank and line.strip() == '':
            skip_until_blank = False
            continue
        if not skip_until_blank:
            new_lines.append(line)

    # Find where to insert navigation (after title if present)
    insert_idx = 0
    for i, line in enumerate(new_lines):
        if line.startswith('# '):
            insert_idx = i + 1
            break

    # Ensure blank line before navigation
    if insert_idx > 0 and insert_idx < len(new_lines) and new_lines[insert_idx - 1].strip():
        new_lines.insert(insert_idx, '')
        insert_idx += 1

    # Insert navigation
    new_lines.insert(insert_idx, nav_content)

    # Update cell
    nb['cells'][nav_cell_idx]['source'] = '\n'.join(new_lines)

    # Write back
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    return True

def update_internal_references(filepath, old_to_new_map):
    """Update internal references to old notebook names."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    modified = False
    for old_name, new_name in old_to_new_map.items():
        if old_name in content:
            content = content.replace(old_name, new_name)
            modified = True

    if modified:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)

    return modified

def main():
    base_dir = os.path.dirname(os.path.abspath(__file__))

    # Mapping of old names to new names for reference updates
    old_to_new = {
        "GameTheory-8-BackwardInduction": "GameTheory-9-BackwardInduction",
        "GameTheory-9-ForwardInduction-SPE": "GameTheory-10-ForwardInduction-SPE",
        "GameTheory-10-BayesianGames": "GameTheory-11-BayesianGames",
        "GameTheory-11-ReputationGames": "GameTheory-12-ReputationGames",
        "GameTheory-12-ImperfectInfo-CFR": "GameTheory-13-ImperfectInfo-CFR",
        "GameTheory-13-DifferentialGames": "GameTheory-14-DifferentialGames",
        "GameTheory-14-CooperativeGames": "GameTheory-15-CooperativeGames",
        "GameTheory-15-MechanismDesign": "GameTheory-16-MechanismDesign",
        "GameTheory-16-MultiAgent-RL": "GameTheory-17-MultiAgent-RL",
        "GameTheory-17-Lean-Definitions": "GameTheory-2b-Lean-Definitions",
        "GameTheory-18-Lean-NashExistence": "GameTheory-4b-Lean-NashExistence",
        "GameTheory-18b-NashExistence-Python": "GameTheory-4c-NashExistence-Python",
        "GameTheory-19-Lean-CombinatorialGames": "GameTheory-8b-Lean-CombinatorialGames",
        "GameTheory-19b-CombinatorialGames-Python": "GameTheory-8c-CombinatorialGames-Python",
        "GameTheory-20-Lean-SocialChoice": "GameTheory-16b-Lean-SocialChoice",
        "GameTheory-20b-SocialChoice-Python": "GameTheory-16c-SocialChoice-Python",
        "GameTheory-21-Lean-CooperativeGames": "GameTheory-15b-Lean-CooperativeGames",
        "GameTheory-21b-CooperativeGames-Python": "GameTheory-15c-CooperativeGames-Python",
    }

    # Update all notebooks
    print("Updating navigation links...")

    # Main notebooks
    for num, (name, side_tracks) in STRUCTURE.items():
        filename = get_notebook_filename(num, name)
        filepath = os.path.join(base_dir, filename)
        if os.path.exists(filepath):
            try:
                update_notebook_navigation(filepath, is_side_track=False, num=num, name=name, side_tracks=side_tracks)
                print(f"  Updated: {filename}")
            except Exception as e:
                print(f"  Error updating {filename}: {e}")
        else:
            print(f"  Missing: {filename}")

    # Side track notebooks
    for track_id in SIDE_TRACKS:
        # Find full track name
        for num, (name, tracks) in STRUCTURE.items():
            for t in tracks:
                if t.startswith(track_id):
                    filename = f"GameTheory-{t}.ipynb"
                    filepath = os.path.join(base_dir, filename)
                    if os.path.exists(filepath):
                        try:
                            update_notebook_navigation(filepath, is_side_track=True, track_id=track_id)
                            print(f"  Updated: {filename}")
                        except Exception as e:
                            print(f"  Error updating {filename}: {e}")
                    else:
                        print(f"  Missing: {filename}")
                    break

    # Update internal references in all notebooks
    print("\nUpdating internal references...")
    for filename in os.listdir(base_dir):
        if filename.startswith("GameTheory-") and filename.endswith(".ipynb"):
            filepath = os.path.join(base_dir, filename)
            if update_internal_references(filepath, old_to_new):
                print(f"  Updated refs in: {filename}")

    print("\nDone!")

if __name__ == "__main__":
    main()
