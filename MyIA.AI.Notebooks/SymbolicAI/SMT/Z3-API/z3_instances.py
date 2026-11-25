"""Corpus d'instances Z3 exporte par la serie Z3-API.

Objet
-----
Les carnets de la serie portent l'encodage de leurs instances dans des
**cellules** : une cellule n'est pas importable, donc aucun instrument
externe ne peut mesurer la meme chose qu'eux sans **reecrire** l'encodage
— et une reecriture diverge en silence.

Ce module est l'**export** de ces encodages (question 3 de la regle
organ-first) : il rend les instances **programmatiquement** et devient la
**source unique** de ces encodages. L'instrument qui les mesure
(`scripts/notebook_tools/z3_tactics_invariance.py`) l'importe au lieu de
porter une copie.

Provenance, cellule par cellule
-------------------------------
- `petersen(k)` : `Z3-11-Graph-Coloring-Python.ipynb`, cellules « Graphe de
  Petersen », « Modele Z3 : une variable de couleur par sommet » et
  « Recherche lineaire du nombre chromatique » ;
- `chromatic_number()` : le meme carnet, la boucle `k = 1..N` de la cellule
  « Recherche lineaire du nombre chromatique » ;
- `send_more_money()` : `Z3-10-Cryptarithmetic-Python.ipynb`, cellule
  « Cryptarithme classique : SEND + MORE = MONEY » ;
- `cryptarithm_solutions()` : le meme carnet, la cellule « Exercice 2 :
  prouver l'unicite de SEND + MORE = MONEY » (enumeration par blocage de la
  solution trouvee).

Fidelite — elle est **verifiee**, pas promise
---------------------------------------------
La parite entre cet export et les **sorties committes** des carnets est
verifiee par `scripts/notebook_tools/tests/test_z3_instances_parity.py` : si
un carnet change d'encodage et que l'export n'est pas mis a jour, la parite
tombe en rouge. C'est le seul garde-fou : un export non verifie divergerait
en silence, exactement comme une copie.
"""

from __future__ import annotations

import z3

#: Aretes du graphe de Petersen : pentagone externe, rayons, pentagramme interne.
PETERSEN_EDGES: tuple[tuple[int, int], ...] = (
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
)

#: Lettres du cryptarithme SEND + MORE = MONEY.
SEND_MORE_LETTERS: tuple[str, ...] = ("S", "E", "N", "D", "M", "O", "R", "Y")

#: Un encodage : les contraintes et les variables de l'enonce.
Instance = tuple[list[z3.ExprRef], list[z3.ArithRef]]


def petersen(k: int) -> Instance:
    """Coloration du graphe de Petersen avec `k` couleurs (carnet Z3-11).

    Encodage fidele a la cellule « Recherche lineaire du nombre chromatique » :
    domaine `0 <= Cv < k`, aretes de couleurs differentes, et **brisure de
    symetrie** `C0 == 0` — sans elle, le modele n'est pas unique et la
    comparaison de modeles entre configurations n'aurait pas de sens.

    Returns:
        Les contraintes de l'enonce et ses variables de couleur.
    """
    couleurs = [z3.Int(f"C{v}") for v in range(10)]
    contraintes: list[z3.ExprRef] = [
        z3.And(couleur >= 0, couleur < k) for couleur in couleurs
    ]
    contraintes.append(couleurs[0] == 0)
    contraintes += [couleurs[a] != couleurs[b] for a, b in PETERSEN_EDGES]
    return contraintes, couleurs


def send_more_money() -> Instance:
    """Cryptarithme SEND + MORE = MONEY (carnet Z3-10).

    Encodage fidele a la cellule « Cryptarithme classique » : domaine `0..9`,
    lettres deux a deux distinctes, **tetes non nulles** (`S > 0`, `M > 0`) et
    equation positionnelle.

    Returns:
        Les contraintes de l'enonce et ses variables.
    """
    chiffres = {lettre: z3.Int(lettre) for lettre in SEND_MORE_LETTERS}
    variables = [chiffres[lettre] for lettre in SEND_MORE_LETTERS]
    contraintes: list[z3.ExprRef] = [
        z3.Distinct(*variables),
        # Chiffres de tete : ni SEND ni MORE ne commence par un zero.
        chiffres["S"] > 0,
        chiffres["M"] > 0,
    ]
    contraintes += [
        z3.And(chiffres[lettre] >= 0, chiffres[lettre] <= 9)
        for lettre in SEND_MORE_LETTERS
    ]
    gauche = 1000 * chiffres["S"] + 100 * chiffres["E"] + 10 * chiffres["N"] + chiffres["D"]
    droite = 1000 * chiffres["M"] + 100 * chiffres["O"] + 10 * chiffres["R"] + chiffres["E"]
    resultat = (
        10000 * chiffres["M"] + 1000 * chiffres["O"] + 100 * chiffres["N"]
        + 10 * chiffres["E"] + chiffres["Y"]
    )
    contraintes.append(gauche + droite == resultat)
    return contraintes, variables


def chromatic_number(max_colors: int = 10) -> int:
    """Nombre chromatique du graphe de Petersen (carnet Z3-11).

    La boucle lineaire du carnet : pour `k` croissant, on resout l'enonce ;
    la premiere valeur satisfaite est le nombre chromatique.

    Returns:
        `chi(Petersen)`, ou -1 si aucune coloration n'est trouvee.
    """
    for k in range(1, max_colors + 1):
        contraintes, _variables = petersen(k)
        solveur = z3.Solver()
        solveur.add(*contraintes)
        if solveur.check() == z3.sat:
            return k
    return -1


def cryptarithm_solutions() -> list[dict[str, int]]:
    """Toutes les solutions du cryptarithme (carnet Z3-10).

    Enumeration par blocage : on resout, on note la solution, on **interdit**
    cette solution, on redemande — jusqu'a `unsat`, qui prouve l'exhaustivite
    de l'enumeration. La cellule du carnet fait de meme.

    Returns:
        Une solution par affectation des huit lettres.
    """
    contraintes, variables = send_more_money()
    solveur = z3.Solver()
    solveur.add(*contraintes)
    solutions: list[dict[str, int]] = []
    while solveur.check() == z3.sat:
        modele = solveur.model()
        valeurs = {
            variable.decl().name(): modele.eval(variable, model_completion=False).as_long()
            for variable in variables
        }
        solutions.append(valeurs)
        solveur.add(
            z3.Or(*[variable != valeurs[variable.decl().name()] for variable in variables])
        )
    return solutions
