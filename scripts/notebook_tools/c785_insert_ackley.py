#!/usr/bin/env python3
"""
c.785 — Insere 2 cellules (markdown + code) dans MGS-7b-LandscapeMultidim.ipynb
entre la cellule Schwefel (56b11c2f) et la cellule Exercices (688c4c68).
Met egalement a jour la TOC de la cellule 22e8527a pour mentionner l'etape 5 = Ackley
et decaler l'exercice en etape 6.

Approche : manipulation JSON sur le fichier .ipynb brut (L772-L1 ★★ :
TOUJOURS Edit raw sur JSON, JAMAIS NotebookEdit replace/insert qui ecrase outputs+execution_count).
Apres ce script, le notebook sera reexecute localement via .NET Interactive
pour re-inscrire execution_count + outputs sur la cellule code fraichement ajoutee.
"""

import json
import os
import sys

NB_PATH = 'C:/dev/CoursIA-2-c785/MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-7b-LandscapeMultidim.ipynb'

ACKLEY_MARKDOWN = [
    "## Ackley en $n = 2$ et $n = 30$ : la \"bassine\" de minima locaux au bord\n",
    "\n",
    "Ackley est la 4e fonction canonique de `KnownFunctions.cs` et complete le panorama\n",
    "MGS-7b sur une geometrie tres differente de Rastrigin et Schwefel. Sa formule est\n",
    "\n",
    "$$f(\\vec x) = -a \\exp\\left(-b \\sqrt{\\tfrac{1}{n} \\sum_i x_i^2}\\right) - \\exp\\left(\\tfrac{1}{n} \\sum_i \\cos(c x_i)\\right) + a + e$$\n",
    "\n",
    "avec les parametres canoniques $a = 20$, $b = 0.2$, $c = 2\\pi$. La **bassine centrale**\n",
    "est quasi-plate : un enorme plateau legerement ondule entoure l'origine, et un **anneau\n",
    "de minima locaux** (`cos`) ceint cette bassine. **En dimension superieure, ces minima\n",
    "se demultiplient exponentiellement** (~ $e^{n-1}$ cuvettes) — Ackley est repute parmi\n",
    "les paysages les plus trompeurs pour les metaheuristiques en haute dimension.\n",
    "\n",
    "**Effet attendu de la projection N-D** : en 2-D, on voit nettement la bassine centrale\n",
    "(rouge profond sature = haut fitness = l'optimum global) cernee par un anneau ondule\n",
    "(vert/jaune = minima locaux `cos`). En 30-D, la projection MAX capture les innombrables\n",
    "coordonnees cachees qui peuvent atteindre des valeurs loin du centre → depuis presque\n",
    "chaque pixel visible, il existe un point cache qui grimpe tres haut sur la modulation\n",
    "`cos`. La heatmap **se rapproche d'une saturation rouge uniforme** (le praticien lit\n",
    "cela comme : \"le paysage est devenu si multimodal qu'aucune direction n'est fiable,\n",
    "il faut des redemarrages massifs\").\n",
    "\n",
    "C'est precisement la **lecon de la projection MAX** qu'on cherche a transmettre a travers\n",
    "MGS-7b : Ackley-n en 2-D rassure (bol central visible), Ackley-n en N-D inquiete (le\n",
    "bol n'existe presque plus a l'ecran). Le contraste entre les deux heatmaps ci-dessous\n",
    "est l'illustration la plus parlante du **pourquoi** les redemarrages et le seeding\n",
    "aleatoire sont indispensables au-dela de la dimension 5.\n",
]

ACKLEY_CODE = [
    "using System.IO;\n",
    "var rngAck = new Random(777);\n",
    "\n",
    "foreach (int dim in new[] { 2, 30 })\n",
    "{\n",
    "    using var h = KnownFunctionLandscape.RenderHeatmap(\n",
    "        new AckleyFitness(), dimension: dim, nbSamples: 30, rng: rngAck,\n",
    "        width: 120, height: 120);\n",
    "\n",
    "    var path = $@\"assets\\landscape_multidim_ackley_d{dim}.png\";\n",
    "    File.WriteAllBytes(path, h.ToPngGdi());\n",
    "\n",
    "    var (px, py) = h.ToPixel(0.0, 0.0);\n",
    "    Console.WriteLine($\"Ackley dim={dim,2} — pixel (0,0) = {h.Bitmap.GetPixel(px, py)} (PNG: {path}).\");\n",
    "}\n",
]


def main():
    with open(NB_PATH, encoding='utf-8') as f:
        nb = json.load(f)

    # --- 1. Insertion des 2 cellules ---
    schwefel_idx = next(i for i, c in enumerate(nb['cells']) if c.get('id') == '56b11c2f')
    assert nb['cells'][schwefel_idx + 1].get('id') == '688c4c68', \
        f"gap inattendu apres schwefel: cellule suivante = {nb['cells'][schwefel_idx + 1].get('id')}"

    markdown_cell = {
        'cell_type': 'markdown',
        'id': 'df8e3a90',
        'metadata': {},
        'source': ACKLEY_MARKDOWN,
    }
    code_cell = {
        'cell_type': 'code',
        'execution_count': None,
        'id': 'ab9c4d12',
        'metadata': {},
        'outputs': [],
        'source': ACKLEY_CODE,
    }
    # Insertion en ordre : markdown puis code (sinon ordre inverse)
    nb['cells'].insert(schwefel_idx + 1, markdown_cell)
    nb['cells'].insert(schwefel_idx + 2, code_cell)
    print(f'INSERE 2 cellules (markdown df8e3a90 + code ab9c4d12) a index {schwefel_idx + 1} et {schwefel_idx + 2}')

    # --- 2. Mise a jour de la TOC dans la cellule 22e8527a ---
    toc_cell = next(c for c in nb['cells'] if c.get('id') == '22e8527a')
    new_toc = []
    for line in toc_cell['source']:
        # Etape 4 (Schwefel) reste inchangee
        if line.startswith('4. **Schwefel en $n = 5, 30$**'):
            new_toc.append(line)
            # Inserer l'etape 5 Ackley entre Schwefel et Exercice
            new_toc.append('5. **Ackley en $n = 2, 30$** : voir comment la bassine centrale de minima locaux se degrade en projection N-D.\n')
            # L'etape Exercice devient 6
        elif line.startswith('5. **Exercice**'):
            new_toc.append('6. **Exercice** : explorer la convergence de la projection en fonction de `nbSamples`.\n')
        else:
            new_toc.append(line)

    # Verifier qu'on a bien insere 1 ligne et remplace 1 ligne (sinon suspect)
    before = toc_cell['source']
    after = new_toc
    inserted = [l for l in after if l not in before]
    removed = [l for l in before if l not in after]
    print(f'TOC: {len(inserted)} inseree, {len(removed)} remplacee')
    if '5. **Ackley en' not in ''.join(inserted):
        print('WARN: Ackley pas dans inserted!')
        sys.exit(1)
    if '6. **Exercice' not in ''.join(inserted):
        print('WARN: exercice pas renum!')
        sys.exit(1)

    toc_cell['source'] = new_toc

    # --- 3. Ecriture du fichier ---
    # Garder l'indentation / format le plus proche de l'original (4 espaces)
    with open(NB_PATH, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        f.write('\n')  # newline final comme les .ipynb nbformat
    print(f'ECRIT: {NB_PATH} ({os.path.getsize(NB_PATH)} bytes)')


if __name__ == '__main__':
    main()
