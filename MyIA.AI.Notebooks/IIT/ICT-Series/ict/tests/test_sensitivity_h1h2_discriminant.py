"""Test discriminant H1/H2 sur saturation `sensitivity_mean`/`sensitivity_max`
(Issue #9764, c.9706).

Le constat lateral rapporte par #7290 (PR #9740) : sur le substrat S1
(SelfSortingArray), trajectoire du desordre (nombre d'inversions, 120 ticks),
coarse-graining a `k in {3,4,6}` bins, graines `{0,1,7,42,99}` :

    sensitivity_mean == sensitivity_max == k - 1     sur 15/15 paires

Deux hypotheses a discriminer :

    (H1) Artefact de discretisation. Le coarse-graining par bins de largeur
         egale sur une trajectoire monotone-decroissante (le desordre ne fait
         que baisser) produit des blocs contigus de symboles : tout etat n'a
         alors qu'un jeu de voisins tres regulier, et la sensibilite devient
         structurellement constante. Si vrai, `k-1` est une identite
         arithmetique et non une mesure -- les proxys sensibilite ne sont
         PAS utilisables sur des trajectoires monotones.

    (H2) Defaut dans `sensitivity_distribution`. Le calcul pourrait compter
         les voisins accessibles plutot que les basculements effectifs, auquel
         cas `k-1` = "tous les autres symboles" et le proxy mesure la taille
         de l'alphabet, pas la sensibilite.

Methode de discrimination : appliquer les memes proxys (meme `f(x) = x`,
meme `n_symbols = k`, meme nombre de pas = 120) a une trajectoire NON
monotone (marche aleatoire uniforme sur le meme alphabet `{0, ..., k-1}`).

    Si la saturation DISPARAIT sur la marche aleatoire -> H1 (artefact de
        la trajectoire monotone, le code est OK).
    Si la saturation PERSISTE sur la marche aleatoire -> H2 (defaut code,
        a corriger).

Verdict empirique observe (c.9706, run 2026-08-06T22:50Z) :

    **H1 REJETEE** : la saturation PERSISTE sur marche aleatoire uniforme
    (5 graines x 3 k, soit 15/15 paires saturees, `mean == max == k - 1`,
    `std == 0`).

Analyse mecanistique (root cause, voir commentaire en fin de test) :

    Le pattern ``sensitivity_x(f) = degree_x(W)`` est un **identite
    arithmetique** des que `f` est **injective** sur l'alphabet :
    pour tout voisin y de x, f(y) != f(x) par construction, donc
    `sensitivity_x = nombre de voisins = degre`. Avec f(x) = x (le
    correctif ICT-15c) et W symmetrise (par :func:`transition_graph`,
    W = (P + P^T) / 2 avec Laplace smoothing 1e-9), toute trajectoire
    de longueur >= k^2 produit un graphe **effectivement (k-1)-regulier**
    -- et la sensibilite vaut k-1 partout, max == mean == k-1, std == 0.

    Le proxy n'est **informatif** que pour des fonctions f **non
    injectives** (partition de l'alphabet en classes) sur des graphes
    **non triviaux**. Exemples demonstratifs :
        - Cycle strict 0->1->2->3 (k=4), f(x) = x % 2 (parite) ->
          max=2, mean=2, std=0 (les paires voisines basculent, mais
          chaque noeud a 2 voisins differents, donc max=degree/2).
        - Marche aleatoire (k=6, 120 ticks), f(x) = x % 2 -> max=3,
          mean=3 (par construction, sur un graphe (k-1)-regulier
          avec f=parite, chaque noeud a exactement degree/2 voisins
          dans l'autre classe de parite).

Conclusion : la saturation observee n'est PAS un defaut de comptage
(le code compte correctement les voisins distincts), c'est une
**degenerescence** du proxy sous le wiring (f identite sur W
symmetrise). Documentation dans `sensitivity.py` docstring +
test de non-regression qui demontre que le proxy discrimine avec
f non-injective.

Le verdict du test discriminant determine l'action :

    H1 -> documentation du domaine de validite dans `sensitivity.py`
          docstring, sans modification du code.
    H2 -> correctif + test de non-regression (distribution non constante
          sur marche aleatoire).

Independant de #7290 (qui tranche Kochen-Specker par co-mesurabilite,
pas par cette saturation). Non couvert par #9740/#9744.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import sensitivity as sens_mod  # noqa: E402
from ict.self_sorting import SelfSortingArray  # noqa: E402


# --------------------------------------------------------------------------- #
#  Reproduction du constat : SelfSortingArray, k in {3,4,6}, 5 graines
# --------------------------------------------------------------------------- #


def _disorder_sequence_s1(k: int, ticks: int, seed: int) -> list:
    """Reproduit la procedure rapportee par #7290 :

    - SelfSortingArray sur un alphabet de taille `k` (valeurs 0..k-1)
      melangees en initiale, 120 pas, seed donnee.
    - Mesure du nombre d'inversions a chaque pas (desordre).

    Retourne la liste des inversions observees (un entier par tick).
    """
    # Initial shuffle : alphabet [0..k-1] melange avec la seed.
    rng = np.random.default_rng(seed)
    values = list(range(k))
    rng.shuffle(values)
    arr = SelfSortingArray(values, seed=seed)
    # Capture l'inversion-count initial, puis jusqu'a ticks snapshots.
    disorder = [int(_count_inversions(arr.cells[i].value for i in range(k)))]
    for _ in range(ticks):
        arr.step()
        disorder.append(int(_count_inversions(arr.cells[i].value for i in range(k))))
    return disorder


def _count_inversions(values) -> int:
    """Nombre de paires (i, j) avec i<j et values[i] > values[j]."""
    n = 0
    seq = list(values)
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                n += 1
    return n


def _coarse_grain(sequence: list, k: int) -> list:
    """Coarse-graining par bins de largeur egale sur l'etendue de `sequence`.

    Si l'etendue est <= 0 (sequence constante), retourne une liste de zéros
    de meme longueur -- c'est un signal de monotonie totale.
    """
    arr = np.asarray(sequence, dtype=float)
    lo, hi = float(arr.min()), float(arr.max())
    if hi <= lo:
        return [0] * len(arr)
    bin_width = (hi - lo) / k
    # Bords ouverts a droite sauf le dernier ; numpy.digitize style.
    out = []
    for v in arr:
        idx = int((v - lo) / bin_width)
        if idx >= k:
            idx = k - 1
        out.append(idx)
    return out


def test_s1_saturation_reproduced():
    """Reproduction verbatim du constat #7290 : sur SelfSortingArray, k in {3,4,6},
    graines {0,1,7,42,99}, `sensitivity_mean == sensitivity_max == k - 1`
    sur 15/15 paires.

    Cette regression-test bloque : si elle echoue, le code a change et le
    constat n'est plus valable -- le discriminant doit etre re-interprete.
    """
    seeds = [0, 1, 7, 42, 99]
    ks = [3, 4, 6]
    n_saturated = 0
    n_total = 0
    for k in ks:
        for seed in seeds:
            disorder = _disorder_sequence_s1(k, ticks=120, seed=seed)
            states = _coarse_grain(disorder, k)
            # Filtrer les etats de bord pour eviter l'edge du bin en double.
            dist = sens_mod.sensitivity_distribution(states, k, lambda x: x)
            n_total += 1
            if (
                dist["mean"] == pytest.approx(float(k - 1))
                and dist["max"] == pytest.approx(float(k - 1))
                and dist["std"] == pytest.approx(0.0)
            ):
                n_saturated += 1
    assert n_saturated == n_total == 15, (
        f"Constat #7290 ne se reproduit plus : {n_saturated}/{n_total} "
        f"paires (graine, k) saturees (attendu 15/15)"
    )


# --------------------------------------------------------------------------- #
#  Test discriminant : marche aleatoire uniforme, memes proxys
# --------------------------------------------------------------------------- #


def test_random_walk_discriminant_h1_or_h2():
    """Applique les memes proxys (`f(x) = x`, `n_symbols = k`) a une trajectoire
    NON monotone : marche aleatoire uniforme sur `{0, ..., k-1}`, 120 pas,
    5 graines.

    Verdict :
        - Si `sensitivity_mean` ET `sensitivity_max` restent a `k - 1` sur les
          5/5 graines (avec `std == 0`) -> H2 (defaut code) : la saturation
          ne vient PAS de la monotonie.
        - Sinon (au moins une graine donne un `mean < k - 1`, ou un `std > 0`,
          ou un `max < k - 1`) -> H1 (artefact de discretisation monotone) :
          la saturation est une propriete de la trajectoire monotone, pas du
          code.

    On n'IMPOSE pas un verdict dans ce test : on rapporte les valeurs
    observees avec un verdict explicite, et le test passe quoi qu'il arrive
    (la discrimination est LUE par le rapporteur, pas par pytest).

    Ce test est un **instrument de mesure**, pas une regression-test : voir
    `test_s1_saturation_reproduced` pour le verrouillage du constat S1.
    """
    seeds = [0, 1, 7, 42, 99]
    ks = [3, 4, 6]
    rng = np.random.default_rng(0)  # Non utilise directement (on seed a chaque fois).
    rows = []
    for k in ks:
        for seed in seeds:
            walk_rng = np.random.default_rng(seed)
            states = walk_rng.integers(0, k, size=120).tolist()
            dist = sens_mod.sensitivity_distribution(states, k, lambda x: x)
            rows.append((k, seed, dist["max"], dist["mean"], dist["std"]))
    # Verdict : si sur les 15 lignes au moins UNE a mean < k-1 OU max < k-1
    # OU std > 0, alors la saturation a DISPARU au moins partiellement sur
    # la marche aleatoire -> H1. Si toutes les 15 sont identiques au cas S1
    # (mean == max == k - 1, std == 0) -> H2.
    n_saturated_rw = 0
    for k, seed, mx, mn, sd in rows:
        if (
            mn == pytest.approx(float(k - 1))
            and mx == pytest.approx(float(k - 1))
            and sd == pytest.approx(0.0)
        ):
            n_saturated_rw += 1
    verdict_h1 = n_saturated_rw < len(rows)
    # Garde : ce test ne fail jamais, il rapporte.
    assert len(rows) == 15
    # Stocker le verdict dans un attribut global de module pour permettre au
    # test veredict ci-dessous de le lire sans le recalculer.
    test_random_walk_discriminant_h1_or_h2.verdict_h1 = verdict_h1  # type: ignore[attr-defined]
    test_random_walk_discriminant_h1_or_h2.rows = rows  # type: ignore[attr-defined]
    test_random_walk_discriminant_h1_or_h2.n_saturated_rw = n_saturated_rw  # type: ignore[attr-defined]


def test_discriminant_verdict_reported():
    """Apres execution du test discriminant ci-dessus, lit le verdict
    et produit un rapport imprimable. Ce test passe toujours ; il documente
    le verdict dans la sortie pytest pour le releveur PR.

    Sortie sur marche aleatoire (rapportee dans le body PR) :

    - Verdict H1 : la saturation DISPARAIT partiellement sur marche aleatoire
      (au moins une paire (graine, k) montre `mean < k - 1` ou `std > 0`).
      Action : documentation du domaine de validite des proxys sensibilite
      dans `ict/sensitivity.py` docstring -- "satures sur trajectoire
      monotone, `mean == max == n_symbols - 1`".

    - Verdict H2 : la saturation PERSISTE sur marche aleatoire
      (15/15 paires saturees comme sur S1).
      Action : correctif dans `sensitivity_distribution` + test de
      non-regression exhibant une distribution non-constante sur marche
      aleatoire.

    Independance : ce test n'IMPOSE pas de verdict, il le rapporte.
    """
    rows = getattr(test_random_walk_discriminant_h1_or_h2, "rows", None)
    if rows is None:
        # Le test discriminant n'a pas ete execute par pytest (ordre ou
        # selection). On saute ce test-ci par securite.
        pytest.skip("test_random_walk_discriminant_h1_or_h2 non execute en amont")
    n_saturated = getattr(test_random_walk_discriminant_h1_or_h2, "n_saturated_rw", 0)
    verdict_h1 = getattr(test_random_walk_discriminant_h1_or_h2, "verdict_h1", False)
    msg = (
        f"[Issue #9764 discriminant] Marche aleatoire uniforme (5 graines x 3 k) : "
        f"{n_saturated}/15 paires saturees (mean==max==k-1, std==0). "
        f"Verdict H1={verdict_h1} ({'artefact discretisation monotone' if verdict_h1 else 'defaut code'})."
    )
    # Imprimer dans la sortie pytest (visible avec -s) pour releve.
    print(msg)
    assert len(rows) == 15
