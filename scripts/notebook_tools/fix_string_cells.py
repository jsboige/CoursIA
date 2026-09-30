#!/usr/bin/env python3
"""
Convert STRING source cells to LIST format in Jupyter notebooks.

Jupyter notebooks store cell source as either:
- STRING: "code line 1\ncode line 2"
- LIST: ["code line 1", "code line 2"]

This script converts all STRING cells to LIST format for consistency.

Le volet LIST ne reecrit que les frontieres REELLEMENT collees (cf
``fix_list_newlines``) : la forme globale, qui ajoutait '\\n' a tout element
non-dernier des qu'un seul en manquait, doublait les sauts deja rendus par la
liste (issue #17550). C'est le meme correctif que celui deja applique a
``notebook_tools._fix_source_newlines`` (#5094, cause #5005).
"""

import json
from pathlib import Path
from typing import List

_WS = (' ', '\t')

#: En dessous de ce nombre d'elements, une liste de lignes d'un seul caractere
#: reste plausible ecrite a la main ; au-dessus, c'est une cellule deserialisee
#: caractere par caractere (mesure repo du 2026-09-23 : 820 elements sur 1384
#: notebooks balayes, issue #17550).
EXPLODED_MIN_ELEMENTS = 20


def convert_string_to_list(source) -> List[str]:
    """Convert STRING source to LIST format.

    nbformat convention: each line except the last ends with '\\n'.
    Example: "a\\nb\\nc" -> ["a\\n", "b\\n", "c"]
    """
    if isinstance(source, list):
        return source
    lines = source.split('\n')
    # Add '\n' to each line except the last (nbformat convention)
    return [line + '\n' for line in lines[:-1]] + [lines[-1]] if lines else []


def _genuinely_glued(source: List[str]) -> List[int]:
    """Indices k ou ``''.join`` colle ``source[k]`` et ``source[k+1]`` sans separateur.

    Predicat de ``notebook_tools._fix_source_newlines`` (#5094) : une frontiere
    n'est fautive que si ``source[k]`` ne finit ni par '\\n' ni par une espace,
    ET si ``source[k+1]`` ne commence ni par '\\n' ni par une espace. Un '\\n'
    d'un cote ou une espace de l'autre rend la frontiere correcte a
    l'affichage : y ajouter '\\n' double le saut (issue #17550).

    Ajout mesure ici : le saut se materialise comme terminateur de la ligne de
    GAUCHE, donc un element vide n'est jamais un terminateur. Sans cette
    condition, ``''`` se change en '\\n' et fabrique une ligne blanche qui
    n'existait pas au rendu (4 cellules du depot, +7 blanches ; la cellule
    76 elements ``06-3-AudioDiffusion-Comparison-A-vs-B`` passait de 0 a 7
    blanches entre des lignes de code).
    """
    return [
        k for k in range(len(source) - 1)
        if source[k] and not source[k].endswith('\n') and not source[k].endswith(_WS)
        and not source[k + 1].startswith('\n') and not source[k + 1].startswith(_WS)
    ]


def is_exploded_character_list(source) -> bool:
    """Vrai si la liste n'est PAS structuree en lignes : toutes <= 1 caractere.

    Mesure repo (2026-09-23, 1384 notebooks) : un seul cas, 820 elements
    ``['#', ' ', 'P', 'a', 'r', ...]`` -- cellule deserialisee caractere par
    caractere. Y ajouter '\\n' ecrit une ligne par caractere, et aucun predicat
    de frontiere ne le repare (623 des 820 elements restent modifies meme avec
    le predicat chirurgical). Un tel motif n'est pas reecrit.
    """
    if not isinstance(source, list) or len(source) <= EXPLODED_MIN_ELEMENTS:
        return False
    return all(len(e.rstrip('\n')) <= 1 for e in source[:-1])


def fix_list_newlines(source: List[str]) -> List[str]:
    """Fix LIST cells missing trailing '\\n' on genuinely-glued boundaries only.

    Retablit le '\\n' de convention nbformat sur les seules frontieres ou
    ``''.join`` colle deux lignes sans aucun separateur. Deux motifs sont laisses
    INTACTS plutot que reecrits (issue #17550) :

    - une frontiere qui rend deja correctement (espace d'un cote, '\\n' de
      l'autre) : y ajouter '\\n' double le saut ;
    - une cellule deserialisee caractere par caractere.
    """
    if not source or len(source) <= 1:
        return source
    if is_exploded_character_list(source):
        return source
    glued = _genuinely_glued(source)
    if not glued:
        return source
    fixed = list(source)
    for k in glued:
        fixed[k] = fixed[k] + '\n'
    return fixed


def fix_notebook(notebook_path: Path, dry_run: bool = False) -> bool:
    """Fix STRING cells and LIST cells with missing newlines. Returns True if changes were made."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    modified = False
    for cell in data.get('cells', []):
        source = cell.get('source')
        if source and isinstance(source, str):
            cell['source'] = convert_string_to_list(source)
            modified = True
        elif source and isinstance(source, list) and len(source) > 1:
            if is_exploded_character_list(source):
                # Non reecrite : y ajouter '\n' ecrirait une ligne par caractere.
                # Signale plutot que silencieux -- c'est un defaut a traiter a la main.
                print(f'  [REFUS] {notebook_path} : cellule deserialisee caractere '
                      f'par caractere ({len(source)} elements) -- non reecrite')
                continue
            fixed = fix_list_newlines(source)
            if fixed != source:
                cell['source'] = fixed
                modified = True

    if modified and not dry_run:
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=1, ensure_ascii=False)
            # Add trailing newline
            f.write('\n')

    return modified


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Fix STRING cells in Jupyter notebooks')
    parser.add_argument('path', help='Notebook file or directory')
    parser.add_argument('--dry-run', action='store_true', help='Show changes without modifying')
    parser.add_argument('--genai-only', action='store_true', help='Only process GenAI notebooks')
    args = parser.parse_args()

    path = Path(args.path)
    notebooks = []

    if path.is_file() and path.suffix == '.ipynb':
        notebooks = [path]
    elif path.is_dir():
        for nb in path.rglob('*.ipynb'):
            if '_output' in str(nb):
                continue
            if args.genai_only and 'GenAI' not in str(nb):
                continue
            notebooks.append(nb)

    fixed_count = 0
    for nb in notebooks:
        if fix_notebook(nb, dry_run=args.dry_run):
            print(f'  [FIXED] {nb}')
            fixed_count += 1
        elif args.dry_run:
            # Show all notebooks even if no changes
            print(f'  [OK] {nb}')

    print(f'\nTotal: {fixed_count}/{len(notebooks)} notebooks fixed')
    if args.dry_run:
        print('(Dry run - no files modified)')


if __name__ == '__main__':
    main()
