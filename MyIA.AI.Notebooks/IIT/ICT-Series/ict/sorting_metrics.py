"""Metriques de morphogenese minimale pour les self-sorting arrays.

Ces mesures reprennent le vocabulaire de Zhang, Goldstein & Levin (2025)
et le rendent calculable sur une trajectoire enregistree par ``Probe`` :
sortedness, monotonicity error, comptage d'inversions, deplacement restant,
delai de gratification, agregation par algotype, temps de recuperation.

Toutes les fonctions ne dependent que de la bibliotheque standard.
"""

from __future__ import annotations

from collections import Counter
from typing import Optional


# --------------------------------------------------------------------- ordre
def inversion_count(values: list) -> int:
    """Nombre de paires (i < j) telles que values[i] > values[j]."""
    n = len(values)
    c = 0
    for i in range(n):
        vi = values[i]
        for j in range(i + 1, n):
            if vi > values[j]:
                c += 1
    return c


def max_inversions(n: int) -> int:
    return n * (n - 1) // 2


def sortedness(values: list) -> float:
    """Degre de tri dans [0, 1] : 1.0 = parfaitement trie (ordre croissant)."""
    n = len(values)
    if n < 2:
        return 1.0
    return 1.0 - inversion_count(values) / max_inversions(n)


def monotonicity_error(values: list) -> float:
    """Fraction de paires adjacentes en descente (erreur de monotonie locale).

    Contrairement aux inversions (mesure globale), cette mesure est *locale* :
    elle peut augmenter transitoirement meme quand les inversions diminuent,
    signature d'un sacrifice local au service du progres global.
    """
    n = len(values)
    if n < 2:
        return 0.0
    desc = sum(1 for i in range(n - 1) if values[i] > values[i + 1])
    return desc / (n - 1)


def distance_to_target(values: list, target: Optional[list] = None) -> int:
    """Deplacement total restant : somme des |rang_actuel - rang_cible|.

    Mesure 'combien de chemin reste a parcourir' pour atteindre le tri.
    Gere les doublons via un appariement stable des rangs.
    """
    if target is None:
        target = sorted(values)
    # rang cible de chaque valeur (stable pour les doublons)
    target_slots: dict = {}
    for idx, v in enumerate(target):
        target_slots.setdefault(v, []).append(idx)
    used: dict = {v: 0 for v in target_slots}
    total = 0
    for cur_idx, v in enumerate(values):
        slot_list = target_slots[v]
        tgt_idx = slot_list[used[v]]
        used[v] += 1
        total += abs(cur_idx - tgt_idx)
    return total


# ---------------------------------------------------------- trajectoire / dynamique
def sortedness_curve(values_trajectory: list) -> list:
    return [sortedness(v) for v in values_trajectory]


def monotonicity_curve(values_trajectory: list) -> list:
    return [monotonicity_error(v) for v in values_trajectory]


def inversions_curve(values_trajectory: list) -> list:
    return [inversion_count(v) for v in values_trajectory]


def delayed_gratification_events(curve: list) -> int:
    """Nombre de pas ou la metrique s'est *degradee* (a augmente).

    Applique a la courbe d'erreur de monotonie, mesure les episodes ou le
    systeme s'eloigne localement du but tout en progressant globalement :
    une forme structurelle de 'delai de gratification'.
    """
    return sum(1 for a, b in zip(curve, curve[1:]) if b > a)


def aggregation_index(algotypes: list) -> float:
    """Indice d'agregation par algotype (clustering du 'kin').

    Compare la fraction de paires adjacentes de meme algotype a celle attendue
    sous un arrangement aleatoire. > 0 => les memes algotypes se regroupent ;
    ~ 0 => arrangement indiscernable de l'aleatoire ; < 0 => repulsion.
    """
    n = len(algotypes)
    if n < 2:
        return 0.0
    observed = sum(1 for i in range(n - 1) if algotypes[i] == algotypes[i + 1]) / (n - 1)
    counts = Counter(algotypes)
    expected = sum(c * (c - 1) for c in counts.values()) / (n * (n - 1))
    if 1.0 - expected == 0:
        return 0.0
    return (observed - expected) / (1.0 - expected)


def aggregation_curve(algotypes_trajectory: list) -> list:
    return [aggregation_index(a) for a in algotypes_trajectory]


def recovery_time(curve: list, perturbation_step: int, tol: float = 1e-9) -> Optional[int]:
    """Nombre de pas pour revenir au niveau d'avant perturbation (ou mieux).

    Retourne None si le niveau anterieur n'est jamais retrouve dans la courbe.
    """
    if perturbation_step <= 0 or perturbation_step >= len(curve):
        return None
    baseline = curve[perturbation_step - 1]
    for t in range(perturbation_step, len(curve)):
        if curve[t] >= baseline - tol:
            return t - perturbation_step
    return None
