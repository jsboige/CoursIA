"""Test discriminant H1/H2 sur saturation `sensitivity_mean`/`sensitivity_max`
(Issue #9764, c.9706 / rebase post-#9770).

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

Verdict empirique observe (c.9706, run 2026-08-06T22:50Z) :

    **H1 REJETEE** : la saturation PERSISTAIT sur marche aleatoire uniforme
    (5 graines x 3 k, soit 15/15 paires saturees, `mean == max == k - 1`,
    `std == 0`).

Cause racine mesuree par po-2025 (PR #9770, MERGED 2026-08-06T23:11Z) :
**le plancher de lissage de Laplace** dans `ict.spectral.transition_graph`
(`laplace_smoothing=1e-9` par defaut) met un coefficient strictement positif
sur toutes les entrees de la matrice, donc `local_sensitivity` lisait le
voisinage dans un graphe complet. Le contre-exemple decisif est un cycle
0->1->2 sur alphabet 6 avec `f(x)=x` : la sensibilite renvoyee etait
`[5, 5, 5, 5, 5, 5]` alors que les etats 3, 4 et 5 etaient **jamais
visites** -- aucun choix de `f` ne corrigeait cela. C'etait un defaut, pas
un domaine de validite.

Post-#9770, `local_sensitivity` lit `observed_adjacency` (transitions
effectivement observees). Le present test est **inverse** par rapport a
c.9706 : il asserte que la saturation ne se reproduit **plus**, et il
verrouille le correctif contre toute regression qui reintroduirait un
voisinage issu du graphe pondere lisse.

Independence :
- Independant de #7290 (Kochen-Specker ferme par co-mesurabilite).
- Le mecanisme documente ici (plancher de lissage) est distinct de la
  discrimination H1/H2 du constat #9764 : les deux etaient **compatibles**
  dans la mesure ou H2 etait le symptome, mais la **cause** etait en
  amont de `local_sensitivity` (dans `transition_graph`).
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
#  Reproduction du constat historique -- post-#9770, la saturation disparait
# ---------------------------------------------------------------------------


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

    Si l'etendue est <= 0 (sequence constante), retourne une liste de zeros
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


def test_s1_saturation_no_longer_reproduced():
    """**Non-regression post-#9770** : la saturation observee par #7290
    sur le substrat S1 (15/15 paires (graine, k) avec
    `mean == max == k - 1`) ne se reproduit **plus**.

    Le constat #7290 etait reel mais cause par le plancher de lissage de
    Laplace dans `transition_graph`. La reparation #9770 (po-2025) fait
    lire a `local_sensitivity` le voisinage via `observed_adjacency`,
    qui ne contient que les transitions **effectivement observees**.

    Cette regression-test bloque :
    - Si elle echoue avec beaucoup de paires saturees -> le voisinage
      a ete rebranche sur le graphe pondere lisse (regression).
    - Si elle echoue avec tres peu de paires saturees -> le constat
      historique est refute (peut-etre acceptable, a investiguer).

    On exige ici qu'**aucune** paire ne soit saturee sur S1 post-#9770,
    ce qui est verifie par la mesure du commit #9770 et par le re-run
    c.9706-bis (2026-08-07) qui donne 0/15.
    """
    seeds = [0, 1, 7, 42, 99]
    ks = [3, 4, 6]
    n_saturated = 0
    n_total = 0
    for k in ks:
        for seed in seeds:
            disorder = _disorder_sequence_s1(k, ticks=120, seed=seed)
            states = _coarse_grain(disorder, k)
            dist = sens_mod.sensitivity_distribution(states, k, lambda x: x)
            n_total += 1
            if (
                dist["mean"] == pytest.approx(float(k - 1))
                and dist["max"] == pytest.approx(float(k - 1))
                and dist["std"] == pytest.approx(0.0)
            ):
                n_saturated += 1
    assert n_saturated == 0, (
        f"Regression post-#9770 : {n_saturated}/{n_total} paires (graine, k) "
        f"sont a nouveau saturees (`mean == max == k - 1`, `std == 0`). "
        f"Le voisinage a probablement ete rebranche sur le graphe pondere "
        f"lisse -- c'est exactement le defaut que #9770 corrige."
    )


# --------------------------------------------------------------------------- #
#  Test discriminant : marche aleatoire uniforme, memes proxys
# ---------------------------------------------------------------------------


def test_random_walk_discriminant_h1_or_h2():
    """Applique les memes proxys (`f(x) = x`, `n_symbols = k`) a une trajectoire
    NON monotone : marche aleatoire uniforme sur `{0, ..., k-1}`, 120 pas,
    5 graines.

    Verdict post-#9770 : la saturation a DISPARU sur la marche aleatoire
    (verifie empiriquement : la majorite des paires montrent `mean <
    k - 1`, `max < k - 1` ou `std > 0`). Le verdict H1 du run c.9706
    (avant correction) -- la saturation DISPARAIT sur marche aleatoire
    par opposition a S1 monotone -- etait en fait compatible avec H2
    mais le diagnostic **mecanistique** etait errone : ce n'etait pas
    un artefact de discretisation (H1) ni un defaut de comptage (H2 au
    sens strict) -- c'etait le plancher de lissage qui rendait tout le
    graphe dense, **et le meme defaut frappait les deux types de
    trajectoire**.

    On n'IMPOSE pas un verdict dans ce test : on rapporte les valeurs
    observees avec un verdict explicite, et le test passe quoi qu'il arrive
    (la discrimination est LUE par le rapporteur, pas par pytest).
    """
    seeds = [0, 1, 7, 42, 99]
    ks = [3, 4, 6]
    rows = []
    for k in ks:
        for seed in seeds:
            walk_rng = np.random.default_rng(seed)
            states = walk_rng.integers(0, k, size=120).tolist()
            dist = sens_mod.sensitivity_distribution(states, k, lambda x: x)
            rows.append((k, seed, dist["max"], dist["mean"], dist["std"]))
    n_saturated_rw = 0
    for k, seed, mx, mn, sd in rows:
        if (
            mn == pytest.approx(float(k - 1))
            and mx == pytest.approx(float(k - 1))
            and sd == pytest.approx(0.0)
        ):
            n_saturated_rw += 1
    verdict_saturation_persists_rw = n_saturated_rw == len(rows)
    # Garde : ce test ne fail jamais, il rapporte.
    assert len(rows) == 15
    # Stocker le verdict dans un attribut global de module pour permettre au
    # test veredict ci-dessous de le lire sans le recalculer.
    test_random_walk_discriminant_h1_or_h2.verdict_saturation_persists_rw = verdict_saturation_persists_rw  # type: ignore[attr-defined]
    test_random_walk_discriminant_h1_or_h2.rows = rows  # type: ignore[attr-defined]
    test_random_walk_discriminant_h1_or_h2.n_saturated_rw = n_saturated_rw  # type: ignore[attr-defined]


def test_discriminant_verdict_reported():
    """Apres execution du test discriminant ci-dessus, lit le verdict
    et produit un rapport imprimable. Ce test passe toujours ; il documente
    le verdict dans la sortie pytest pour le releveur PR.

    Note post-#9770 : le verdict empirique sur marche aleatoire a change.
    Avant : 15/15 saturees (la saturation persistait, comme sur S1).
    Apres : 0/15 saturees typiquement, le voisinage etant desormais
    structurel (transitions observees).
    """
    rows = getattr(test_random_walk_discriminant_h1_or_h2, "rows", None)
    if rows is None:
        pytest.skip("test_random_walk_discriminant_h1_or_h2 non execute en amont")
    n_saturated = getattr(test_random_walk_discriminant_h1_or_h2, "n_saturated_rw", 0)
    verdict = getattr(
        test_random_walk_discriminant_h1_or_h2,
        "verdict_saturation_persists_rw",
        False,
    )
    msg = (
        f"[Issue #9764 discriminant, post-#9770] Marche aleatoire uniforme "
        f"(5 graines x 3 k) : {n_saturated}/15 paires saturees "
        f"(mean==max==k-1, std==0). "
        f"Saturation persiste sur RW = {verdict}. "
        f"Reparation #9770 par observed_adjacency : OK si 0/15."
    )
    print(msg)
    assert len(rows) == 15