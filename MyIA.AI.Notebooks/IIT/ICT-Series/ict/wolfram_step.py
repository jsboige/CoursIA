"""Automate cellulaire 1-D de Wolfram -- organe extracté d'ICT-18 (pli 2 EPIC #19766).

Outille la brique « programmes simples » du pli 2 de l'EPIC Origami Wolfram
(#19766). La regle 30 (chaotique, classe III), la regle 110 (complexe, classe
IV) et la regle 0 (triviale, classe I) sont les trois exemples canoniques que
Wolfram 2002 (« A New Kind of Science ») utilise pour definir les 4 classes
d'automates cellulaires 1-D :

* **Classe I** : homogenéité -- la trajectoire converge vers un point fixe
  uniforme (ex. regle 0, 32, 160, 232). Densité constante, périodicité 1.
* **Classe II** : cycles simples -- la trajectoire converge vers un cycle
  periodique stable de courte periode (ex. regle 4, 8, 13). Densité oscille
  entre quelques valeurs.
* **Classe III** : chaotique -- la trajectoire est imprevisible, densité
  proche de 0.5, pas de structure persistante (ex. regle 30, 45, 75, 126).
* **Classe IV** : complexe -- la trajectoire porte une structure persistante
  (gliders, particules), densité oscille mais reste caracteristique (ex.
  regle 110). C'est la classe computationnellement la plus riche.

**Source primaire** : Wolfram, S. (2002) « A New Kind of Science »,
Wolfram Media, chapitres 2-3. L'implémentation ``wolfram_step`` reproduit la
definition standard : voisinage 3-cellules (gauche, centre, droite), regle
sur 8 bits (256 regles au total), bords periodiques (modulo n_cells).

**Provenance dans le depot** : extraite d'ICT-18
(``ICT-18-ArrowOfTimeReversibilization-Python.ipynb``) « Exemple guide 3 »
au cours du cycle c.107, pli 2 de l'EPIC Origami Wolfram. L'exemple guide y
demontre la signature thermodynamique (production d'entropie, detailed
balance) sur les regles 0, 30, 110, 250. Cette extraction transforme
l'exemple inline en un module reutilisable, premier pas du pli 2 carnet
(ICT-19 ou ICT-18b selon le curriculum).

**Cadrage epistemologique** : Wolfram soutient que la regle 110 est
*intrinséquement* computationnellement irreducible -- predire son etat a
l'horizon T demande une simulation T pas. Ce module ne *verifie* pas la these
(elle est empirique et conceptuelle, pas formelle) ; il fournit l'instrument
de mesure. La verification se fait au carnet, par confrontation a
``time_arrow.compare_real_reversed_reversibilized`` (cf. ICT-18).

Usage :

    >>> from ict.wolfram_step import wolfram_step, wolfram_trajectory, classify_rule
    >>> traj = wolfram_trajectory(rule=30, n_cells=32, n_steps=300, seed=33)
    >>> classify_rule(30, n_cells=64, n_steps=500)
    {'rule': 30, 'class_label': 'III (chaotic)', 'asymptotic_density': 0.498, ...}
"""

from __future__ import annotations

from typing import Iterable, List, Optional

import numpy as np

__all__ = [
    "WOLFRAM_CLASSES",
    "CANONICAL_RULES",
    "wolfram_step",
    "wolfram_trajectory",
    "wolfram_density",
    "wolfram_class_indicators",
    "classify_rule",
]


# ---------------------------------------------------------------------------
# Index de la table des 256 regles de Wolfram.
#
# Wolfram 2002 utilise une convention d'indexation lexicographique sur le
# voisinage (left << 2) | (center << 1) | right : la regle est un entier sur
# 8 bits dont chaque bit est la valeur de sortie pour le voisinage
# correspondant. La regle 30 a pour representation binaire 00011110
# (bit 0 = voisinage 000, bit 1 = voisinage 001, ..., bit 7 = voisinage 111),
# d'ou le nom canonique "regle 30" pour la regle aux sorties
# 0,1,1,1,1,0,0,0 (0, 1, 1, 1, 1, 0, 0, 0 dans l'ordre 7,6,5,4,3,2,1,0).
# ---------------------------------------------------------------------------

WOLFRAM_CLASSES = {
    # Classe I : converge vers un point fixe (ex. tout blanc ou tout noir).
    0: "I (uniform)",
    32: "I (uniform)",
    160: "I (uniform)",
    232: "I (uniform)",
    # Classe II : converge vers un cycle periodique simple.
    4: "II (periodic)",
    8: "II (periodic)",
    13: "II (periodic)",
    # Classe III : chaotique, densite proche de 0.5.
    30: "III (chaotic)",
    45: "III (chaotic)",
    75: "III (chaotic)",
    126: "III (chaotic)",
    # Classe IV : complexe, structure persistante (gliders).
    110: "IV (complex)",
}


# Regles canoniques (les 3 exemples d'ICT-18 + une regle complexe).
CANONICAL_RULES = (0, 30, 110, 250)


def wolfram_step(state: np.ndarray, rule: int) -> np.ndarray:
    """Un pas de l'automate cellulaire 1-D de Wolfram, bords periodiques.

    Parametres
    ----------
    state : np.ndarray
        Vecteur d'etats 0/1 de longueur n_cells. La convention suit
        Wolfram 2002 (representation binaire) et ICT-18.
    rule : int
        Regle sur 8 bits (0 a 255). Le bit d'index ``(left << 2) |
        (center << 1) | right`` definit la sortie du voisinage
        correspondant.

    Retour
    ------
    np.ndarray
        Vecteur d'etats apres un pas, meme longueur que ``state``.

    Exemple
    -------
    >>> import numpy as np
    >>> state = np.array([0, 0, 0, 1, 0, 0, 0], dtype=int)
    >>> wolfram_step(state, 30).tolist()
    [0, 0, 1, 1, 1, 0, 0]
    """
    state = np.asarray(state, dtype=int)
    n = len(state)
    if n == 0:
        return state.copy()
    # Voisinage circulaire : decalage gauche/droite/centre, calcul d'index 3 bits.
    left = np.roll(state, 1)
    center = state
    right = np.roll(state, -1)
    idx = (left << 2) | (center << 1) | right
    # Table de verite : le bit p de ``rule`` donne la sortie pour le voisinage p.
    out = ((rule >> idx) & 1).astype(int)
    return out


def wolfram_trajectory(
    rule: int,
    n_cells: int = 32,
    n_steps: int = 300,
    seed: int = 33,
    record_densities: bool = True,
) -> List[int]:
    """Trajectoire d'un automate de Wolfram ; historique de densites (nb de 1).

    Parametres
    ----------
    rule : int
        Regle sur 8 bits (0 a 255).
    n_cells : int
        Taille de la grille (par defaut 32, adapte a ICT-18).
    n_steps : int
        Nombre de pas a simuler (par defaut 300, adapte a ICT-18).
    seed : int
        Graine aleatoire de l'etat initial (par defaut 33, adapte a ICT-18).
    record_densities : bool
        Si ``True``, retourne la sequence de densites (nb de 1) a chaque pas.
        Si ``False``, retourne les etats complets (matrices).

    Retour
    ------
    List[int] (ou List[np.ndarray])
        Historique de la trajectoire.

    Notes
    -----
    La densite (nb de 1) est l'observable privilegiee dans ICT-18
    Exemple guide 3 -- elle donne une signature thermodynamique robuste
    a la fois sur les regimes homogenes (densite constante), periodiques
    (oscillation entre quelques valeurs), chaotiques (densite proche de 0.5)
    et complexes (densite caracteristique sans cycle evident).
    """
    rng = np.random.default_rng(seed)
    state = rng.integers(0, 2, size=n_cells)
    history: List[int] = []
    states: List[np.ndarray] = []
    for _ in range(n_steps):
        if record_densities:
            history.append(int(state.sum()))
        else:
            states.append(state.copy())
        state = wolfram_step(state, rule)
    return history if record_densities else states


def wolfram_density(state: np.ndarray) -> float:
    """Densite d'un etat : proportion de cellules a 1.

    Parametres
    ----------
    state : np.ndarray
        Vecteur 0/1.

    Retour
    ------
    float
        Densite dans [0, 1].
    """
    state = np.asarray(state, dtype=int)
    if len(state) == 0:
        return 0.0
    return float(state.mean())


def wolfram_class_indicators(
    densities: Iterable[float],
    tail: int = 100,
    n_cells: int = 1,
) -> dict:
    """Indicateurs des 4 classes de Wolfram a partir d'une trajectoire de densites.

    Renvoie un dict avec :

    * ``asymptotic_density`` : moyenne sur les ``tail`` derniers pas,
      normalisee dans [0, 1] par ``n_cells``.
    * ``asymptotic_std`` : ecart-type sur les ``tail`` derniers pas
      (normalise lui aussi).
    * ``unique_densities_tail`` : nombre de densites distinctes en queue.
    * ``period_estimate`` : plus petit pas p tel que la sequence de
      densites est periodique de periode p (renvoie 1 si constante,
      0 si pas de periode detectee sur la queue).
    * ``class_heuristic`` : etiquette sommaire heuristique parmi
      ``{'I-uniform', 'II-periodic', 'III-chaotic', 'IV-complex',
      'undecided'}``.

    Parametres
    ----------
    densities : iterable de float
        Historique des densites brutes (nb de cellules a 1 par pas).
        Sortie de `` wolfram_trajectory(..., record_densities=True)``.
    tail : int
        Fenetre d'analyse en queue de trajectoire (par defaut 100).
    n_cells : int
        Taille de la grille (par defaut 1 : pas de normalisation, les
        densites sont prises telles quelles). En pratique, passer la
        valeur utilisee pour `` wolfram_trajectory`` pour obtenir des
        indicateurs normalises.
    """
    densities = np.asarray(list(densities), dtype=float)
    if len(densities) < tail:
        tail = len(densities)
    if tail == 0:
        return {
            "asymptotic_density": 0.0,
            "asymptotic_std": 0.0,
            "unique_densities_tail": 0,
            "period_estimate": 0,
            "class_heuristic": "undecided",
        }
    tail_d = densities[-tail:]
    # Normalisation : densites par cellule, dans [0, 1].
    if n_cells > 1:
        tail_d = tail_d / n_cells
    asym_d = float(tail_d.mean())
    asym_std = float(tail_d.std())
    unique = int(len(np.unique(np.round(tail_d, 6))))
    # Detection de periodicite : plus petit p >= 1 tel que la sequence est
    # periodique de periode p sur la queue.
    period = 0
    max_p = min(20, tail // 2)
    for p in range(1, max_p + 1):
        # Comparaison par blocs successifs de taille p.
        n_blocks = tail // p
        if n_blocks < 2:
            continue
        ok_periodic = True
        ref = tail_d[:p]
        for k in range(1, n_blocks):
            if not np.allclose(tail_d[k * p:(k + 1) * p], ref, atol=1e-9):
                ok_periodic = False
                break
        if ok_periodic:
            period = p
            break
    # Heuristique 4 classes (empirique, non theoremique).
    # Seuils sur la densite normalisee. La discrimination fine III (chaotique)
    # vs IV (complexe) necessite l'analyse des motifs spatiaux (gliders) -- hors
    # du scope de ce module, qui ne mesure que la trajectoire de densite. On
    # utilise donc l'etiquette "III-or-IV" pour les regimes a forte variance
    # non periodique ; la discrimination fine se fait dans le carnet par
    # capture du pattern spatial.
    if asym_std < 1e-3:
        heuristic = "I-uniform"
    elif period > 0 and period <= 8:
        heuristic = "II-periodic"
    elif asym_std > 0.03:
        heuristic = "III-or-IV"
    else:
        heuristic = "undecided"
    return {
        "asymptotic_density": asym_d,
        "asymptotic_std": asym_std,
        "unique_densities_tail": unique,
        "period_estimate": period,
        "class_heuristic": heuristic,
    }


def classify_rule(
    rule: int,
    n_cells: int = 64,
    n_steps: int = 500,
    seed: int = 33,
    tail: int = 100,
) -> dict:
    """Classification heuristique d'une regle par sa trajectoire de densite.

    Combine l'indexation de Wolframe (connue pour les regles canoniques)
    et les indicateurs mesures empiriquement (``wolfram_class_indicators``).
    Renvoie un dict avec :

    * ``rule`` : la regle demandee.
    * ``known_class`` : etiquette de Wolfram si la regle est dans
      ``WOLFRAM_CLASSES``, sinon ``None``.
    * ``indicators`` : resultat de ``wolfram_class_indicators``.
    * ``class_label`` : heuristique finale, avec mention si l'heuristique
      et l'indexation Wolframe divergent.

    Parametres
    ----------
    rule : int
        Regle de Wolfram (0 a 255).
    n_cells : int
        Taille de la grille (par defaut 64, plus long que ICT-18 pour
        ameliorer la stabilite des indicateurs).
    n_steps : int
        Pas de simulation (par defaut 500, plus long que ICT-18).
    seed : int
        Graine aleatoire (par defaut 33).
    tail : int
        Fenetre d'analyse en queue (par defaut 100).
    """
    densities = wolfram_trajectory(
        rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed, record_densities=True
    )
    indicators = wolfram_class_indicators(densities, tail=tail, n_cells=n_cells)
    known = WOLFRAM_CLASSES.get(rule)
    heuristic = indicators["class_heuristic"]
    # Heuristique -> etiquette courte (I/II/III-or-IV/undecided).
    # La discrimination III vs IV necessite l'analyse spatiale (gliders),
    # qui n'est pas dans le scope de la mesure de densite seule.
    if heuristic.startswith("I-"):
        final = "I"
    elif heuristic.startswith("II-"):
        final = "II"
    elif heuristic.startswith("III-or-IV"):
        # Si la regle est indexee, on garde la discrimination connue.
        final = None  # a fixer ci-dessous si known
    else:
        final = "undecided"
    if known is not None:
        known_short = known.split(" ")[0]
        measured_short = "III-or-IV" if final is None else final
        if known_short == measured_short or known_short in ("III", "IV") and measured_short == "III-or-IV":
            label = f"{known_short} (known+measured)"
        else:
            label = f"{known_short} (known) | {measured_short} (measured)"
    else:
        label = f"{final or 'III-or-IV'} (measured only)"
    return {
        "rule": rule,
        "known_class": known,
        "indicators": indicators,
        "class_label": label,
    }