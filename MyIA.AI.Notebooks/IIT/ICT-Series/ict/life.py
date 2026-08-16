"""Substrat Jeu de la Vie (Conway) — trajectoires calibrees sur patterns canoniques.

Outille la phase-zero « Life as certified calibration substrate » de la serie
ICT (issue #5726, Epic #4588). Le substrat est le **Jeu de la Vie** de Conway
(M. Gardner, *Mathematical Games*, Scientific American 1970 ; E. R. Berlekamp,
J. H. Conway & R. K. Guy, *Winning Ways for Your Mathematical Plays*, 1982),
regle **B3/S23** sur grille 2-D a bords periodiques :

* une cellule morte ayant exactement 3 voisines vivantes naît (B3) ;
* une cellule vivante ayant 2 ou 3 voisines vivantes survit (S23) ;
* toute autre cellule meurt (sous-population ou etouffement).

Le role de ce substrat dans la batterie ICT (cf. :mod:`ict.agency`,
:mod:`ict.stake`, :mod:`ict.causal_emergence`) : contrairement au tri (1-D) ou
au bistable (0-D), le Jeu de la Vie offre une **morphodynamique 2-D avec
propagation d'information localisee** — les gliders y jouent le role de
« particules » transportant une information sur de grands horizons temporels,
ce qui en fait un banc discriminant pour l'emergence causale multi-echelle.

**Pont preuve <-> mesure** : le calcul de trajectoire implemente ici (simulation
naive pas-a-pas, toroidale) est l'exact pendant Python de la branche « naive »
du theoreme ``hashlife_correct`` formalise en Lean dans la track ``conway_lean``
(``MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeCorrectness.lean``).
Ce theoreme — desormais **prouve sans sorry** sur ``main`` (chaine P4
``p4_succ_membership`` + pont de localite BR1-BR3 + BR4a ``one_jump_toGrid_correct``
(PR #10919) + ``p5_large_n_jumpN`` decharge par induction sur le fuel et
re-signature trajectoire b3' (PR #11007), ``hashlife_correctN`` re-signee) —
garantit que l'evaluation **Hashlife** (quadtree memoise, sauts temporels
``2^k``) calcule la *meme chose* que la simulation naive pas-a-pas. Les longues
trajectoires exportees depuis ce module heritent donc d'une garantie de
correction : l'acceleration Hashlife, si on l'employait, ne changerait rien au
film produit (c'est precisement ce que dit le theoreme), et la calibration
ci-dessous verifie que la dynamique Python respecte les constantes canoniques
des patterns (periodes et deplacements).

Numpy uniquement (voisinage vectorise via ``numpy.roll``, bords periodiques),
comme le reste du package leger ``ict``.

Reference : ICT-0 (cadrage de la serie), issue #5726, tracker Lean #6724.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import numpy as np


# --------------------------------------------------------------- dynamique B3/S23
def next_generation(grid: np.ndarray) -> np.ndarray:
    """Un pas de la regle B3/S23 sur grille toroidale (vectorise via ``roll``).

    Voisinage de Moore 8 points, bords periodiques : chaque cellule voit le
    cote oppose de la grille. Retourne une nouvelle grille 0/1 (uint8).
    """
    g = (np.asarray(grid) != 0).astype(np.uint8)
    neighbors = np.zeros_like(g, dtype=np.int16)
    for dr in (-1, 0, 1):
        for dc in (-1, 0, 1):
            if (dr, dc) == (0, 0):
                continue
            neighbors += np.roll(np.roll(g, dr, axis=0), dc, axis=1)
    birth = (g == 0) & (neighbors == 3)
    survive = (g == 1) & ((neighbors == 2) | (neighbors == 3))
    return (birth | survive).astype(np.uint8)


def trajectory(grid: np.ndarray, steps: int) -> List[np.ndarray]:
    """Film causal : la suite des ``steps`` grilles succesives (incluant t=0).

    Chaque element est une grille 0/1 ; ``traj[0]`` est la condition initiale
    fournie, ``traj[t]`` l'etat apres ``t`` generations.
    """
    g = (np.asarray(grid) != 0).astype(np.uint8)
    film = [g.copy()]
    for _ in range(int(steps)):
        g = next_generation(g)
        film.append(g.copy())
    return film


def live_cells(grid: np.ndarray) -> List[Tuple[int, int]]:
    """Coordonnees ``(ligne, colonne)`` des cellules vivantes — format d'export.

    C'est la representation compacte de chaque image du film pour les
    consommateurs de la batterie ICT (etats discrets, comparaison entre
    instants, export JSON).
    """
    rows, cols = np.nonzero(grid)
    return [(int(r), int(c)) for r, c in zip(rows, cols)]


# --------------------------------------------------------------- patterns canoniques
_PATTERNS: Dict[str, List[str]] = {
    # Glider (Gosper 1970) : period 4, deplacement diagonal (1, 1) par periode.
    "glider": [
        ".O.",
        "..O",
        "OOO",
    ],
    # Blinker (oscillateur minimal) : period 2, stationnaire.
    "blinker": [
        "OOO",
    ],
    # Pulsar (oscillateur period 3 le plus connu) : stationnaire.
    "pulsar": [
        "..OOO...OOO..",
        ".............",
        "O....O.O....O",
        "O....O.O....O",
        "O....O.O....O",
        "..OOO...OOO..",
        ".............",
        "..OOO...OOO..",
        "O....O.O....O",
        "O....O.O....O",
        "O....O.O....O",
        ".............",
        "..OOO...OOO..",
    ],
    # Lightweight spaceship : period 4, deplacement orthogonal (0, 2) par periode
    # (c/2 vers l'est sous cette orientation). Forme verifiee empiriquement en
    # faisant evoluer la synthese officielle a 3 gliders (Catagolue xq4_6frc)
    # et en extrayant la phase a 9 cellules.
    "lwss": [
        ".OOOO",
        "O...O",
        "....O",
        "O..O.",
    ],
    # Bloc (structure stable canonique) : period 1, stationnaire.
    "block": [
        "OO",
        "OO",
    ],
}


def canonical_pattern(name: str) -> np.ndarray:
    """Grille du pattern canonique ``name`` (glider, blinker, pulsar, lwss, block)."""
    rows = _PATTERNS[name]
    return np.array([[1 if ch == "O" else 0 for ch in row] for row in rows], dtype=np.uint8)


def embed(pattern: np.ndarray, size: int, top: int = 0, left: int = 0) -> np.ndarray:
    """Place ``pattern`` dans une grille toroidale ``size x size`` en ``(top, left)``."""
    p = (np.asarray(pattern) != 0).astype(np.uint8)
    if p.shape[0] > size or p.shape[1] > size:
        raise ValueError("pattern plus grand que la grille cible")
    grid = np.zeros((size, size), dtype=np.uint8)
    h, w = p.shape
    grid[top:top + h, left:left + w] = p
    return grid


def canonical_patterns() -> Dict[str, np.ndarray]:
    """Tous les patterns canoniques (calibration, notebooks ICT)."""
    return {name: canonical_pattern(name) for name in _PATTERNS}


# --------------------------------------------------------------- calibration
#: Constantes canoniques des patterns (LifeWiki / Catagolue, Berlekamp-Conway-Guy
#: 1982) : nom -> (periode, deplacement (dl, dc) par periode). Le deplacement du
#: glider et du LWSS depend de l'orientation encodee ci-dessus ; la calibration
#: verifie la norme et l'orthogonalite/diagonalite pour rester valable si on
#: change d'orientation.
CALIBRATION: Dict[str, Dict[str, object]] = {
    "glider": {"period": 4, "displacement": (1, 1), "kind": "diagonal"},
    "blinker": {"period": 2, "displacement": (0, 0), "kind": "stationary"},
    "pulsar": {"period": 3, "displacement": (0, 0), "kind": "stationary"},
    "lwss": {"period": 4, "displacement": (0, 2), "kind": "orthogonal"},
    "block": {"period": 1, "displacement": (0, 0), "kind": "stationary"},
}


def _bounding_box(grid: np.ndarray) -> Optional[Tuple[np.ndarray, Tuple[int, int]]]:
    """Contenu canonique (translate a l'origine) et coin superieur gauche."""
    rows, cols = np.nonzero(grid)
    if rows.size == 0:
        return None
    r0, c0 = int(rows.min()), int(cols.min())
    return grid[r0:rows.max() + 1, c0:cols.max() + 1], (r0, c0)


def period_and_displacement(grid: np.ndarray, max_steps: int = 64) -> Tuple[Optional[int], Optional[Tuple[int, int]]]:
    """Periode spatiale et deplacement net du pattern de ``grid``.

    Detection par retour du contenu canonique (translation-invariant) : la
    periode ``p`` est le plus petit nombre de generations apres lequel le
    pattern, translate a l'origine, redevient identique a lui-meme ; le
    deplacement est le decalage du coin de la boite englobante sur une periode.
    Retourne ``(None, None)`` si rien n'est retrouve en ``max_steps`` (pattern
    mourant sans etat final stable, ou grille trop petite / wrap toroidal
    intervenu).
    """
    g = (np.asarray(grid) != 0).astype(np.uint8)
    box0 = _bounding_box(g)
    if box0 is None:
        return 0, (0, 0)
    canon0, origin0 = box0
    for p in range(1, int(max_steps) + 1):
        g = next_generation(g)
        box = _bounding_box(g)
        if box is None:
            return None, None
        canon, origin = box
        if canon.shape == canon0.shape and bool((canon == canon0).all()):
            return p, (origin[0] - origin0[0], origin[1] - origin0[1])
    return None, None


def calibrate(name: str, size: int = 32) -> Tuple[bool, Dict[str, object]]:
    """Verifie que le pattern canonique ``name`` reproduit ses constantes.

    C'est le **certificat de calibration** du substrat : le moteur B3/S23
    implemente ici doit reproduire les periodes et deplacements documentes des
    patterns canoniques. Un echec ici invalide toute mesure ICT construite sur
    ce substrat (la garantie Lean couvre l'egalite Hashlife/naif, pas la
    correctesse de l'implementation Python — qui se prouve par cette
    calibration contre les constantes connues).
    """
    ref = CALIBRATION[name]
    period, displacement = period_and_displacement(embed(canonical_pattern(name), size), max_steps=2 * size)
    if period != ref["period"] or displacement is None:
        return False, {"name": name, "period": period, "displacement": displacement, **ref}
    dr, dc = displacement
    if ref["kind"] == "stationary":
        ok = (dr, dc) == (0, 0)
    elif ref["kind"] == "diagonal":
        ok = abs(dr) == abs(dc) == 1
    else:  # orthogonal
        ok = (abs(dr) == 0 and abs(dc) == 2) or (abs(dr) == 2 and abs(dc) == 0)
    return ok, {"name": name, "period": period, "displacement": displacement,
                "expected": ref, "kind": ref["kind"]}


def calibrate_all() -> Dict[str, bool]:
    """Calibration de tous les patterns canoniques (utilisee par les tests)."""
    return {name: calibrate(name)[0] for name in _PATTERNS}


def trajectory_symbols(traj: List[np.ndarray]) -> Tuple[List[str], Dict[str, np.ndarray]]:
    """Encode une trajectoire de grilles en labels d'etats discrets.

    Chaque grille est identifiee par son **contenu** (octets) : deux grilles de
    meme disposition portent le meme label, independamment de leur instant
    d'observation. Les labels (``"e0"``, ``"e1"``, ...) suivent l'ordre de
    PREMIERE apparition, ce qui rend l'encodage reproductible et lisible.

    C'est le pont vers la batterie de mesures ICT : la suite de labels est
    directement consommable par :func:`ict.tpm_estimation.tpm_from_trajectory`
    (etats hashables), qui en tire la chaine de Markov empirique dont
    :mod:`ict.causal_emergence` mesure le profil causal. Sur une dynamique
    deterministe comme B3/S23, le nombre d'etats distincts d'une trajectoire
    fermee est la **longueur du cycle** (ex. glider sur tore 16x16 : 64).

    Retourne ``(symbols, states)`` ou ``states[label]`` redonne la grille
    representative de chaque etat (pour inspection apres mesure).
    """
    symbols: List[str] = []
    canon: Dict[bytes, str] = {}
    states: Dict[str, np.ndarray] = {}
    for g in traj:
        key = g.tobytes()
        if key not in canon:
            label = f"e{len(canon)}"
            canon[key] = label
            states[label] = g
        symbols.append(canon[key])
    return symbols, states
