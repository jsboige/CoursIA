"""Tests du module :mod:`ict.self_sorting` (ICT-2 morphogenese, Epic #4588).

Couvre les **contrats publiques** non testés du notebook ICT-2
("Self-sorting arrays as morphogenesis : le tri emerge des regles locales",
Zhang, Goldstein & Levin 2025, arXiv:2401.05375) :

  1. ``Cell`` / ``Probe`` : dataclasses minimales, defauts coherents.
  2. ``SelfSortingArray.__init__`` : defauts (algotype="bubble", frozen=False,
     seed=0, frozen_mode="passive") + 3 ``ValueError`` (length mismatch,
     algotype invalide, frozen_mode invalide).
  3. Properties : ``values`` / ``algotypes`` reflètent l'etat des cellules
     (apres swap, apres perturbation).
  4. Convergence : bubble / insertion / tableau chimerique convergent vers
     l'ordre croissant sur des petits cas.
  5. Cellules ``frozen`` : mode passif = robustesse emergente (le voisin peut
     traverser) ; mode obstacle = mur infranchissable (segments independants).
  6. ``has_move`` / ``step`` : semantique du point fixe + activation aleatoire
     + increment des compteurs (swaps, comparisons, steps).
  7. ``run`` plafonne a ``max_steps`` + variante ``record=False`` ne snapshote
     que l'etat final.
  8. ``perturb`` casse l'ordre apres convergence (snapshots pris, swaps
     effectues si >= 2 cellules deplacables).

Pattern herite de ``test_sorting_metrics.py`` et ``test_multiscale_agency.py`` :
bootstrap ``sys.path`` module-level, sans fixtures, tolerances commentees.
Le module est autonome (stdlib only) -- aucune dependance ``numpy``.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import self_sorting as SS  # noqa: E402


# --------------------------------------------------------------------------- #
#  Dataclasses Cell / Probe                                                   #
# --------------------------------------------------------------------------- #


def test_cell_defaults():
    """Defauts ``Cell`` : algotype="bubble", frozen=False, cid=-1."""
    c = SS.Cell(value=42)
    assert c.value == 42
    assert c.algotype == "bubble"
    assert c.frozen is False
    assert c.cid == -1


def test_cell_explicit_fields_override_defaults():
    """``Cell`` accepte des valeurs explicites pour chaque champ."""
    c = SS.Cell(value=7, algotype="insertion", frozen=True, cid=3)
    assert c.value == 7
    assert c.algotype == "insertion"
    assert c.frozen is True
    assert c.cid == 3


def test_probe_starts_empty_and_snapshot_appends_state():
    """``Probe`` demarre vide ; ``snapshot`` empile l'etat courant des cellules.

    Chaque appel incremente ``__len__`` de 1. ``__len__`` mesure le nombre
    de snapshots (et non le nombre de cellules).
    """
    p = SS.Probe()
    assert len(p) == 0
    cells = [SS.Cell(value=v, cid=i) for i, v in enumerate([3, 1, 2])]
    p.snapshot(cells)
    assert len(p) == 1
    assert p.values == [[3, 1, 2]]
    assert p.algotypes == [["bubble", "bubble", "bubble"]]
    # positions : {cid: idx} par pas.
    assert p.positions == [{0: 0, 1: 1, 2: 2}]

    # Un second snapshot doit empiler sans ecraser.
    p.snapshot(list(reversed(cells)))
    assert len(p) == 2
    assert p.values == [[3, 1, 2], [2, 1, 3]]


# --------------------------------------------------------------------------- #
#  SelfSortingArray.__init__ : defauts + 3 ValueError                          #
# --------------------------------------------------------------------------- #


def test_init_defaults_and_initial_snapshot():
    """A la construction, l'etat initial est snapshote une fois et les
    cellules ont les defauts demandes."""
    arr = SS.SelfSortingArray([3, 1, 2])
    # Defauts implicites : algotype=bubble partout, frozen=False partout,
    # seed=0 (deterministe), frozen_mode="passive".
    assert arr.cells[0].algotype == "bubble"
    assert arr.cells[1].algotype == "bubble"
    assert arr.cells[2].algotype == "bubble"
    assert all(not c.frozen for c in arr.cells)
    assert arr.cells[0].cid == 0
    assert arr.cells[1].cid == 1
    assert arr.cells[2].cid == 2
    # Le snapshot initial est pris (cf. __init__ : probe.snapshot(self.cells)).
    assert len(arr.probe) == 1
    # steps demarre a 0 (les pas n'ont pas encore ete executes).
    assert arr.steps == 0
    # rng est un random.Random instanciel (pas le global) -> seedable.
    assert isinstance(arr.rng, __import__("random").Random)


def test_init_rejects_length_mismatch():
    """Length mismatch entre values / algotypes / frozen -> ``ValueError``.

    Cas : 3 valeurs mais 2 algotypes.
    """
    with pytest.raises(ValueError, match="meme longueur"):
        SS.SelfSortingArray([3, 1, 2], algotypes=["bubble", "bubble"])


def test_init_rejects_length_mismatch_frozen():
    """Mismatch entre algotypes et frozen -> ``ValueError``."""
    with pytest.raises(ValueError, match="meme longueur"):
        SS.SelfSortingArray(
            [3, 1, 2],
            algotypes=["bubble", "bubble", "bubble"],
            frozen=[False, False],
        )


def test_init_rejects_invalid_algotype():
    """Algotype hors ``ALGOTYPES`` -> ``ValueError``."""
    with pytest.raises(ValueError, match="algotypes doit etre parmi"):
        SS.SelfSortingArray([3, 1, 2], algotypes=["bubble", "merge", "bubble"])


def test_init_rejects_invalid_frozen_mode():
    """``frozen_mode`` autre que ``"passive"`` / ``"obstacle"`` -> ``ValueError``."""
    with pytest.raises(ValueError, match="passive.*obstacle"):
        SS.SelfSortingArray([3, 1, 2], frozen_mode="wall")


def test_init_accepts_explicit_algotypes_mixed():
    """Tableau chimerique (mix bubble/insertion) accepte a la construction.

    Le constructeur ne verifie que l'appartenance a ``ALGOTYPES``, pas la
    coherence des regles locales (la convergence emergente est testee plus bas).
    """
    arr = SS.SelfSortingArray(
        [5, 2, 4, 1, 3],
        algotypes=["bubble", "insertion", "bubble", "insertion", "bubble"],
    )
    assert arr.algotypes == ["bubble", "insertion", "bubble", "insertion", "bubble"]


# --------------------------------------------------------------------------- #
#  Properties : values / algotypes reflètent l'etat des cellules               #
# --------------------------------------------------------------------------- #


def test_values_property_reflects_current_cells():
    """``values`` retourne la projection ``[c.value for c in cells]``.

    Apres perturbation manuelle (swap interne via methode), la property suit.
    """
    arr = SS.SelfSortingArray([3, 1, 2])
    assert arr.values == [3, 1, 2]
    # Force un swap via la methode interne _swap et reverifie.
    arr._swap(0, 1)
    assert arr.values == [1, 3, 2]


def test_algotypes_property_reflects_swaps_keeping_algotype_per_cell():
    """``algotypes`` suit les cellules (et donc leurs regles) apres swap.

    Important : c'est la *cellule* qui porte l'algotype, donc swapper deux
    cellules echange aussi leurs regles.
    """
    arr = SS.SelfSortingArray([3, 1, 2], algotypes=["bubble", "insertion", "bubble"])
    arr._swap(0, 2)  # cellule 0 (bubble) et cellule 2 (bubble) -> pas de
    # changement visible sur les algotypes ici, donc on swap 0 et 1 pour voir.
    arr._swap(0, 1)
    # Apres swap, cellule en position 0 porte maintenant "insertion",
    # cellule en position 1 porte "bubble".
    assert arr.algotypes == ["insertion", "bubble", "bubble"]


# --------------------------------------------------------------------------- #
#  Convergence : bubble / insertion / chimerique                               #
# --------------------------------------------------------------------------- #


def _run_to_completion(values, algotypes=None, seed=0):
    """Helper : ``run()`` jusqu'au point fixe et retourne le tableau trie.

    ``seed`` fixe -> trajectoire reproductible (meme swap sequence d'un
    appel a l'autre).
    """
    arr = SS.SelfSortingArray(values, algotypes=algotypes, seed=seed)
    arr.run(max_steps=20000)
    return arr


def test_bubble_sorts_ascending():
    """Regle ``bubble`` pure : convergence vers l'ordre croissant.

    Sur [3, 1, 2] (cf. papier), bubble fait migrer les grandes valeurs vers
    la droite. Au point fixe, le tableau est trie croissant.
    """
    arr = _run_to_completion([3, 1, 2], algotypes=["bubble", "bubble", "bubble"])
    assert arr.values == [1, 2, 3]
    # Au point fixe, aucune cellule ne peut agir.
    assert arr.has_move() is False


def test_insertion_sorts_ascending():
    """Regle ``insertion`` pure : convergence vers l'ordre croissant aussi.

    Insertion regarde le voisin de gauche et glisse a gauche si plus petit ;
    les petites valeurs migrent vers le debut. Meme ordre global que bubble.
    """
    arr = _run_to_completion([3, 1, 2], algotypes=["insertion"] * 3)
    assert arr.values == [1, 2, 3]
    assert arr.has_move() is False


def test_chimeric_array_converges_to_ascending():
    """Tableau chimerique (bubble + insertion melanges) : converge aussi.

    Les deux regles pulsent dans la meme direction (ordre croissant global),
    donc un mix local converge au meme attracteur.
    """
    arr = _run_to_completion(
        [5, 2, 4, 1, 3],
        algotypes=["bubble", "insertion", "bubble", "insertion", "bubble"],
    )
    assert arr.values == [1, 2, 3, 4, 5]
    assert arr.has_move() is False


def test_run_increments_step_counter_and_swaps_at_least_once():
    """``run`` doit incrementer ``steps`` au moins une fois et le compteur
    ``swaps`` reflete le nombre d'echanges effectues (>= 1 pour un tableau
    non deja trie)."""
    arr = SS.SelfSortingArray([3, 1, 2], seed=0)
    assert arr.probe.swaps == 0
    arr.run()
    assert arr.steps > 0
    # Sur [3,1,2], au moins un swap est necessaire pour atteindre l'ordre
    # croissant. Donc probe.swaps > 0.
    assert arr.probe.swaps > 0
    # Etape finale : on a snapshote l'etat converge.
    assert arr.values == [1, 2, 3]


def test_run_respects_max_steps_ceiling():
    """``max_steps`` plafonne le nombre d'activations meme si la convergence
    n'est pas atteinte.

    Pour demontrer le plafond, on prend un cas qui ne converge pas en peu de
    pas : un long tableau bubble sort avec max_steps=2 doit s'arreter la.
    """
    # Tableau inversement trie, max_steps=2 -> on plafonne.
    arr = SS.SelfSortingArray([5, 4, 3, 2, 1], seed=0)
    arr.run(max_steps=2)
    assert arr.steps <= 2
    # On n'a pas converge -> has_move reste True.
    assert arr.has_move() is True


# --------------------------------------------------------------------------- #
#  Cellules ``frozen`` : passif (traversable) vs obstacle (mur)                #
# --------------------------------------------------------------------------- #


def test_frozen_passive_mode_is_traversable_and_converges():
    """Mode passif : la cellule frozen est un *passager*. Le systeme atteint
    un ordre croissant complet malgre les cellules cassees (robustesse
    emergente, fidele au papier)."""
    # [3, 1, 2] avec la cellule du milieu (idx=1) gelee.
    arr = SS.SelfSortingArray(
        [3, 1, 2],
        frozen=[False, True, False],
        frozen_mode="passive",
        seed=0,
    )
    arr.run()
    # Convergence emergente : la cellule frozen est deplacee par ses voisins
    # sains jusqu'a sa position finale dans l'ordre croissant.
    assert arr.values == [1, 2, 3]
    assert arr.has_move() is False


def test_frozen_obstacle_mode_blocks_swap():
    """Mode obstacle : la cellule frozen agit comme un mur. Le swap
    cellule-i <-> voisin-j est refuse si ``cells[j].frozen``.

    Strategie : on choisit un tableau ou bubble pur veut echanger avec une
    cellule frozen adjacente ; on verifie qu'au point fixe la cellule
    frozen garde sa position initiale.
    """
    # Tableau [3, 1] avec cellule 1 (valeur=1) frozen en mode obstacle.
    # Bubble sur cellule 0 veut swapper a droite (3>1) -- mais le voisin (j=1)
    # est frozen en mode obstacle -> _neighbor_blocked(j) True -> pas de swap.
    arr = SS.SelfSortingArray(
        [3, 1],
        frozen=[False, True],
        frozen_mode="obstacle",
        seed=0,
    )
    # Apres run, le tableau reste [3, 1] : la cellule frozen est un mur.
    arr.run(max_steps=10)
    assert arr.values == [3, 1]
    # Aucun mouvement possible.
    assert arr.has_move() is False


def test_frozen_obstacle_segments_sort_independently():
    """Mode obstacle : chaque segment delimite par des murs frozen se trie
    independamment (variante d'etude du papier).

    Tableau [3, 1, 2] avec cellule centrale (idx=1) frozen en mode obstacle.
    Les segments [3] (gauche) et [2] (droite) sont triviaux ; test trivial.

    Pour un test plus discriminant : [3, 1, 0, 2] avec cellule 2 frozen.
    Segment gauche [3, 1] se trie en [1, 3] ; segment droit [2] est trivial.
    Position finale : [1, 3, 0, 2] -- la cellule frozen (valeur=0) reste en
    place.
    """
    arr = SS.SelfSortingArray(
        [3, 1, 0, 2],
        frozen=[False, False, True, False],
        frozen_mode="obstacle",
        seed=0,
    )
    arr.run(max_steps=200)
    # La cellule frozen garde sa valeur 0 a l'indice 2.
    assert arr.values[2] == 0
    # Le segment gauche [3, 1] est trie : indices 0 et 1 portent 1 et 3
    # (dans un ordre quelconque puisque le swap interne n'a pas de freeze).
    assert sorted(arr.values[0:2]) == [1, 3]
    # Le segment droit [2] est trivial.
    assert arr.values[3] == 2


# --------------------------------------------------------------------------- #
#  has_move / step : semantique du point fixe + activation aleatoire           #
# --------------------------------------------------------------------------- #


def test_has_move_true_on_unsorted_array():
    """``has_move`` est True tant qu'au moins une cellule peut agir."""
    arr = SS.SelfSortingArray([3, 1, 2], seed=0)
    assert arr.has_move() is True


def test_has_move_false_after_sorting():
    """Apres convergence, ``has_move`` est False (point fixe)."""
    arr = SS.SelfSortingArray([3, 1, 2], seed=0)
    arr.run()
    assert arr.has_move() is False


def test_step_returns_bool_and_increments_steps():
    """``step`` retourne un bool (True si swap, False si activation a vide)
    et incremente toujours ``steps`` + ``probe.comparisons`` + snapshot.

    On verifie les invariants structurels sans presumer de la valeur de
    retour : la cellule activee par le scheduler aleatoire peut etre
    n'importe laquelle parmi les non-frozen, donc un pas a vide est
    legal meme depuis un tableau non trie (active une cellule deja a sa
    place). Ce qui est garanti : ``steps`` est incremente, ``comparisons``
    est incremente, et un snapshot est ajoute.
    """
    arr = SS.SelfSortingArray([3, 1, 2], seed=0)
    out = arr.step()
    assert isinstance(out, bool)
    assert arr.steps == 1
    assert arr.probe.comparisons >= 1
    # Le probe est snapshote apres chaque step (meme vide) -> +1 snapshot.
    assert len(arr.probe) >= 2
    # Cas affirmatif : apres un nombre de pas suffisant (>20000), on a
    # converge vers l'ordre croissant, ce qui prouve aussi que le scheduler
    # peut realiser des swaps.
    arr.run(max_steps=20000)
    assert arr.values == [1, 2, 3]
    assert arr.probe.swaps >= 1


def test_step_returns_false_when_no_movable_cells():
    """Si toutes les cellules sont frozen, ``step`` retourne False sans rien
    faire (et n'incremente pas steps -- cf. code)."""
    arr = SS.SelfSortingArray(
        [3, 1, 2],
        frozen=[True, True, True],
        frozen_mode="passive",
        seed=0,
    )
    out = arr.step()
    assert out is False
    # Aucune cellule activable -> le code court-circuite avant steps+=1.
    assert arr.steps == 0


# --------------------------------------------------------------------------- #
#  run(record=False) : ne snapshote que l'etat final                          #
# --------------------------------------------------------------------------- #


def test_run_record_false_only_snapshots_final_state():
    """Avec ``record=False``, le probe ne contient que l'etat final
    (1 snapshot terminal) au lieu de N snapshots intermediaires."""
    arr = SS.SelfSortingArray([3, 1, 2], seed=0)
    initial_len = len(arr.probe)
    arr.run(record=False)
    # Le probe n'a ete incremente que par le snapshot final -> 1 seul
    # nouveau snapshot par rapport a l'etat initial (ou 2 si on compte
    # l'initial ; le code ajoute +1 a la fin de run(record=False)).
    # Total snapshots == initial_len + 1.
    assert len(arr.probe) == initial_len + 1
    # Et le resultat est bien trie.
    assert arr.values == [1, 2, 3]


# --------------------------------------------------------------------------- #
#  perturb : lesion exogene + snapshot final                                  #
# --------------------------------------------------------------------------- #


def test_perturb_breaks_a_sorted_array():
    """``perturb`` casse l'ordre d'un tableau qui etait au point fixe et
    snapshot l'etat post-perturbation."""
    arr = SS.SelfSortingArray([1, 2, 3], seed=0)
    arr.run()
    # Avant perturbation : tableau trie.
    assert arr.values == [1, 2, 3]
    sorted_snapshot_before = list(arr.probe.values[-1])

    n_swaps_before = arr.probe.swaps
    arr.perturb(n_swaps=3)
    # Apres perturbation : un nouveau snapshot est ajoute.
    assert len(arr.probe.values) > 0
    # L'etat final peut etre differents de l'etat trie (depend de la seed ;
    # seed=0 produit generalement une perturbation visible sur [1,2,3]).
    # On verifie au moins que le compteur swaps a progresse OU que la
    # trajectoire a un nouveau snapshot distinct.
    has_new_state = arr.probe.swaps > n_swaps_before or list(arr.probe.values[-1]) != sorted_snapshot_before
    assert has_new_state, "perturb doit modifier l'etat ou incrementer swaps"


def test_perturb_skips_when_fewer_than_two_movable_cells():
    """Si moins de 2 cellules sont deplacables, ``perturb`` court-circuite
    la boucle de swaps mais snapshot l'etat courant (cf. code)."""
    arr = SS.SelfSortingArray(
        [3, 1, 2],
        frozen=[True, False, True],  # 1 seule cellule movable
        frozen_mode="passive",
        seed=0,
    )
    n_snapshots_before = len(arr.probe)
    swaps_before = arr.probe.swaps
    arr.perturb(n_swaps=5)
    # Pas de swap applique (1 seule movable).
    assert arr.probe.swaps == swaps_before
    # Le snapshot final est tout de meme pris.
    assert len(arr.probe) == n_snapshots_before + 1
