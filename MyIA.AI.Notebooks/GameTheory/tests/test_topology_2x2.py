"""
Tests pour le module `topology_2x2_periodic_table.py` (notebook GameTheory-3).

Le module implemente la classification de Robinson-Goforth des jeux 2x2
strictement ordinaux : etant donne deux matrices de gains (A pour le joueur
ligne, B pour le joueur colonne), il determine les equilibres de Nash purs,
les strategies dominantes, et le type canonique (Prisoner's Dilemma, Stag Hunt,
Chicken/Hawk-Dove, Matching Pennies, etc.).

Les tests assertent des INVARIANTS et des resultats theoriques connus, pas
seulement l'absence de crash :

  - **find_pure_nash** : chaque equilibre renvoye est verifie comme un vrai
    best-response croise (invariant de definition), sur des bimatrices
    canoniques (PD, Stag Hunt, Chicken, Matching Pennies) auxquelles on connait
    la structure d'equilibre par construction.
  - **find_dominant_strategy** : detection de la dominance stricte (row 0/1,
    column 0/1) sur des matrices construites, et absence de dominance (-1)
    sur les jeux de coordination.
  - **classify_game** : sur des bimatrices canoniques CONSTRUITES DIRECTEMENT
    (pas via l'encodeur ordinal), chaque type canonique est reconnu correctement.
    C'est le contrat essentiel du module.
  - **Enumeration exhaustive des 576 jeux ordinaux stricts** (24 x 24 permutations
    de {1,2,3,4}) : aucun crash, le classifieur partitionne l'espace tout entier
    de maniere deterministe, et les comptes par type sont stables.
  - **Incoherence documentee (xfail)** : les modeles NAMED_GAMES du module ne
    font PAS de aller-retour via son propre encodeur create_ordinal_game
    (seul Matching Pennies passe). L'encodage de la matrice B (joueur colonne)
    est incoherent avec l'ordre des tuples des modeles. Surfacage honest d'un
    bug reel, sans le consecrer : les assertions expriment le comportement
    CORRECT attendu, et echouent (xfail) tant que le bug n'est pas corrige.

Run with: pytest tests/test_topology_2x2.py -v
"""

import sys
from pathlib import Path
from itertools import permutations

import numpy as np
import pytest

# Ajoute GameTheory/examples/ au path pour importer le module.
sys.path.insert(0, str(Path(__file__).parent.parent / "examples"))

import topology_2x2_periodic_table as topo  # noqa: E402


# ----------------------------------------------------------------------------
# Jeux canoniques construits directement (semantique maitrisee).
#
# Convention : A[i, j] = gain du joueur ligne (P1) quand P1 joue i, P2 joue j.
#              B[i, j] = gain du joueur colonne (P2) dans la meme situation.
#              Indice 0 = Cooperate (C), indice 1 = Defect (D).
#
# Ces bimatrices contournent volontairement create_ordinal_game (dont l'encodage
# P2 est incoherent - voir TestCreateOrdinalGameInconsistency) afin de tester
# classify_game / find_pure_nash sur leurs propres termes.
# ----------------------------------------------------------------------------

# Prisoner's Dilemma canonique : T > R > P > S, (C,C)=(R,R)=(3,3),
# (D,D)=(P,P)=(2,2). Unique equilibre de Nash en strategies dominantes : (D,D).
PD_A = np.array([[3, 1], [4, 2]])   # P1: CC=3(R), CD=1(S), DC=4(T), DD=2(P)
PD_B = np.array([[3, 4], [1, 2]])   # P2: CC=3(R), CD=4(T), DC=1(S), DD=2(P)

# Stag Hunt : deux equilibres purs diagonaux (C,C) payoff-dominant et (D,D)
# risk-dominant. Pas de strategie dominante.
SH_A = np.array([[4, 1], [3, 2]])
SH_B = np.array([[4, 3], [1, 2]])

# Chicken / Hawk-Dove : deux equilibres purs anti-diagonaux (C,D) et (D,C).
CH_A = np.array([[3, 2], [4, 1]])
CH_B = np.array([[3, 4], [2, 1]])

# Matching Pennies : somme nulle, aucun equilibre pur.
MP_A = np.array([[1, -1], [-1, 1]])
MP_B = np.array([[-1, 1], [1, -1]])

# Pure coordination : deux equilibres diagonaux a somme egale.
COORD_A = np.array([[1, 0], [0, 1]])
COORD_B = np.array([[1, 0], [0, 1]])


# ----------------------------------------------------------------------------
# create_ordinal_game : contrat structurel.
# ----------------------------------------------------------------------------

class TestCreateOrdinalGame:
    """create_ordinal_game : forme et formule d'encodage documentee."""

    def test_returns_two_matrices(self):
        A, B = topo.create_ordinal_game((1, 2, 3, 4), (4, 3, 2, 1))
        assert isinstance(A, np.ndarray)
        assert isinstance(B, np.ndarray)

    def test_shape_2x2(self):
        A, B = topo.create_ordinal_game((1, 2, 3, 4), (4, 3, 2, 1))
        assert A.shape == (2, 2)
        assert B.shape == (2, 2)

    def test_A_row_major_encoding(self):
        """A est construite en row-major : A = [[p1[0],p1[1]],[p1[2],p1[3]]]."""
        A, _ = topo.create_ordinal_game((3, 1, 4, 2), (1, 2, 3, 4))
        np.testing.assert_array_equal(A, np.array([[3, 1], [4, 2]]))

    def test_B_column_major_encoding(self):
        """B utilise la formule documentee B = [[p2[0],p2[2]],[p2[1],p2[3]]].

        C'est le comportement REEL du module (que l'on fige ici). Cette formule
        est la source de l'incoherence avec NAMED_GAMES (voir TestNamedGamesRoundTrip).
        """
        _, B = topo.create_ordinal_game((1, 2, 3, 4), (3, 1, 4, 2))
        np.testing.assert_array_equal(B, np.array([[3, 4], [1, 2]]))

    def test_deterministic(self):
        a = topo.create_ordinal_game((1, 2, 3, 4), (4, 3, 2, 1))
        b = topo.create_ordinal_game((1, 2, 3, 4), (4, 3, 2, 1))
        np.testing.assert_array_equal(a[0], b[0])
        np.testing.assert_array_equal(a[1], b[1])


# ----------------------------------------------------------------------------
# find_pure_nash : equilibres de Nash purs, verifies par invariant.
# ----------------------------------------------------------------------------

class TestFindPureNash:
    """find_pure_nash : invariant de best-response croise sur cas connus."""

    def test_nash_is_best_response_for_both_players(self):
        """INVARIANT DE DEFINITION : tout (i,j) renvoye est un best-response.

        Pour chaque equilibre (i,j) : A[i,j] >= A[1-i,j] (P1 best-response)
        ET B[i,j] >= B[i,1-j] (P2 best-response). Verifie sur un ensemble de
        jeux : si cette propriete echoue, find_pure_nash est casse.
        """
        games = [(PD_A, PD_B), (SH_A, SH_B), (CH_A, CH_B), (MP_A, MP_B), (COORD_A, COORD_B)]
        for A, B in games:
            for (i, j) in topo.find_pure_nash(A, B):
                assert A[i, j] >= A[1 - i, j], f"P1 pas best-response en {(i,j)}"
                assert B[i, j] >= B[i, 1 - j], f"P2 pas best-response en {(i,j)}"

    def test_prisoners_dilemma_single_nash_DD(self):
        """PD : unique equilibre pur (D,D) = (1,1)."""
        nash = topo.find_pure_nash(PD_A, PD_B)
        assert nash == [(1, 1)]

    def test_stag_hunt_two_diagonal_nash(self):
        """Stag Hunt : deux equilibres diagonaux (C,C) et (D,D)."""
        nash = set(map(tuple, topo.find_pure_nash(SH_A, SH_B)))
        assert nash == {(0, 0), (1, 1)}

    def test_chicken_two_anti_diagonal_nash(self):
        """Chicken : deux equilibres anti-diagonaux (C,D) et (D,C)."""
        nash = set(map(tuple, topo.find_pure_nash(CH_A, CH_B)))
        assert nash == {(0, 1), (1, 0)}

    def test_matching_pennies_no_pure_nash(self):
        """Matching Pennies : aucun equilibre pur."""
        assert topo.find_pure_nash(MP_A, MP_B) == []

    def test_coordination_two_diagonal_nash(self):
        nash = set(map(tuple, topo.find_pure_nash(COORD_A, COORD_B)))
        assert nash == {(0, 0), (1, 1)}

    def test_nash_completeness_hand_verified(self):
        """Jeu a unique equilibre non-diagonal (1,0)=(D,C), construit a la main.

        A = [[1,3],[5,4]], B = [[1,3],[6,2]] : (1,0) seul equilibre pur.
          - (0,0): A[0,0]=1 < A[1,0]=5 -> P1 prefere D, pas Nash.
          - (0,1): A[0,1]=3 < A[1,1]=4 -> P1 prefere D, pas Nash.
          - (1,0): A[1,0]=5 >= A[0,0]=1 ET B[1,0]=6 >= B[1,1]=2 -> Nash.
          - (1,1): B[1,1]=2 < B[1,0]=6 -> P2 prefere C, pas Nash.
        """
        A = np.array([[1, 3], [5, 4]])
        B = np.array([[1, 3], [6, 2]])
        nash = [tuple(x) for x in topo.find_pure_nash(A, B)]
        assert nash == [(1, 0)]


# ----------------------------------------------------------------------------
# find_dominant_strategy : dominance stricte.
# ----------------------------------------------------------------------------

class TestFindDominantStrategy:
    """find_dominant_strategy : detection de la dominance stricte (0/1/-1)."""

    def test_pd_row_dominant_is_defect(self):
        """PD : le joueur ligne a une strategie dominante Defect (1)."""
        assert topo.find_dominant_strategy(PD_A, is_row=True) == 1

    def test_pd_col_dominant_is_defect(self):
        """PD : le joueur colonne a une strategie dominante Defect (1)."""
        assert topo.find_dominant_strategy(PD_B, is_row=False) == 1

    def test_row0_dominant(self):
        """Matrice ou row 0 domine strictement row 1."""
        A = np.array([[5, 6], [1, 2]])  # 5>1 et 6>2
        assert topo.find_dominant_strategy(A, is_row=True) == 0

    def test_col0_dominant(self):
        """Matrice ou col 0 domine strictement col 1."""
        B = np.array([[5, 1], [6, 2]])  # 5>1 et 6>2
        assert topo.find_dominant_strategy(B, is_row=False) == 0

    def test_stag_hunt_no_dominant(self):
        """Stag Hunt : aucune strategie dominante (-1) pour les deux joueurs."""
        assert topo.find_dominant_strategy(SH_A, is_row=True) == -1
        assert topo.find_dominant_strategy(SH_B, is_row=False) == -1

    def test_chicken_no_dominant(self):
        """Chicken : aucune strategie dominante (-1)."""
        assert topo.find_dominant_strategy(CH_A, is_row=True) == -1
        assert topo.find_dominant_strategy(CH_B, is_row=False) == -1

    def test_no_dominant_when_indifferent(self):
        """Pas de dominance stricte si egalite sur une colonne (strict >)."""
        A = np.array([[3, 5], [3, 1]])  # 3 == 3 sur col 0 -> pas strict
        assert topo.find_dominant_strategy(A, is_row=True) == -1


# ----------------------------------------------------------------------------
# classify_game : LE contrat essentiel, sur bimatrices canoniques directes.
# ----------------------------------------------------------------------------

class TestClassifyGameCanonical:
    """classify_game reconnait les types canoniques sur bimatrices directes.

    Ces tests contournent create_ordinal_game (incoherent) en fournissant A et B
    directement. C'est le contrat de classification qui compte.
    """

    def test_prisoners_dilemma(self):
        assert topo.classify_game(PD_A, PD_B) == "Prisoner's Dilemma"

    def test_stag_hunt(self):
        assert topo.classify_game(SH_A, SH_B) == "Stag Hunt"

    def test_chicken_hawk_dove(self):
        assert topo.classify_game(CH_A, CH_B) == "Chicken/Hawk-Dove"

    def test_matching_pennies(self):
        assert topo.classify_game(MP_A, MP_B) == "Matching Pennies"

    def test_pure_coordination(self):
        """Coordination pure (sommes egales sur les deux Nash diagonaux)."""
        assert topo.classify_game(COORD_A, COORD_B) == "Coordination Game"

    def test_dominant_strategy_not_pd(self):
        """Deux strategies dominantes mais (C,C) n'est pas Pareto-superieur :
        classify renvoie 'Dominant Strategy' (pas PD)."""
        # (D,D)=(3,3) et (C,C)=(1,1) : (C,C) n'est PAS Pareto-superieur a (D,D).
        A = np.array([[1, 2], [3, 4]])
        B = np.array([[1, 3], [2, 4]])
        assert topo.classify_game(A, B) == "Dominant Strategy"

    def test_deterministic(self):
        """classify est une fonction pure : meme bimatrice -> meme classe."""
        for A, B in [(PD_A, PD_B), (SH_A, SH_B), (CH_A, CH_B)]:
            c1 = topo.classify_game(A, B)
            c2 = topo.classify_game(A, B)
            assert c1 == c2


# ----------------------------------------------------------------------------
# Enumeration exhaustive des 576 jeux ordinaux stricts.
#
# Un jeu ordinal strict 2x2 : chaque joueur a un classement strict (sans ex aequo)
# des 4 issues, soit une permutation de {1,2,3,4}. Il y a 4! = 24 permutations
# par joueur, donc 24 x 24 = 576 jeux au total (avant reduction par symetrie).
# ----------------------------------------------------------------------------

CLASSIFICATION_COUNTS = {
    # Comptes observes par execution directe du classifieur sur les 576 jeux.
    # Figes ici comme invariant de regression deterministe : si le classifieur
    # change, ces comptes changent et le test alerte.
    "Other": 288,
    "Dominant Strategy": 140,
    "Matching Pennies": 72,
    "Chicken/Hawk-Dove": 36,
    "Stag Hunt": 26,
    "Coordination Game": 10,
    "Prisoner's Dilemma": 4,
}

VALID_TYPES = {
    "Prisoner's Dilemma", "Stag Hunt", "Chicken/Hawk-Dove",
    "Battle of the Sexes", "Matching Pennies", "Coordination Game",
    "Dominant Strategy", "Other",
}


@pytest.fixture(scope="module")
def exhaustive_counts():
    """Classifie les 576 jeux ordinaux stricts et renvoie le decompte par type."""
    counts = {}
    for p1 in permutations([1, 2, 3, 4]):
        for p2 in permutations([1, 2, 3, 4]):
            A, B = topo.create_ordinal_game(p1, p2)
            cls = topo.classify_game(A, B)
            counts[cls] = counts.get(cls, 0) + 1
    return counts


class TestExhaustiveEnumeration:
    """Le classifieur partitionne l'espace des 576 jeux ordinaux stricts."""

    def test_all_576_classified(self, exhaustive_counts):
        """Aucun crash : la somme des comptes fait 576 (partition complete)."""
        assert sum(exhaustive_counts.values()) == 576

    def test_only_valid_types_returned(self, exhaustive_counts):
        """Toutes les classes renvoyees sont dans l'ensemble documente (8 types)."""
        for cls in exhaustive_counts:
            assert cls in VALID_TYPES, f"Type inattendu : {cls!r}"

    def test_counts_match_reference_partition(self, exhaustive_counts):
        """Les comptes par type correspondent a la partition de reference.

        Ces valeurs sont determinees par execution directe et figent le
        comportement du classifieur (invariant de regression deterministe).
        """
        for cls, expected in CLASSIFICATION_COUNTS.items():
            assert exhaustive_counts.get(cls, 0) == expected, (
                f"Comptage de {cls!r} : attendu {expected}, "
                f"obtenu {exhaustive_counts.get(cls, 0)}"
            )

    def test_prisoners_dilemma_rare_strict_ordinal(self, exhaustive_counts):
        """INVARIANT THEORIQUE : exactement 4 jeux ordinaux stricts sont des PD.

        Un PD ordinal strict demande T>R>P>S (un seul ordre parmi les 24) pour
        chaque joueur AVEC la structure (C,C) Pareto-superieure a (D,D). Peu de
        permutations satisfont cela -> compte faible. La valeur exacte (4) est
        celle produite par le classifieur ; on verifie qu'elle est petite et
        non nulle (le PD existe dans l'espace ordinal strict).
        """
        n_pd = exhaustive_counts.get("Prisoner's Dilemma", 0)
        assert 0 < n_pd < 20, f"Compte PD inattendu : {n_pd}"
        assert n_pd == 4

    def test_matching_pennies_count(self, exhaustive_counts):
        """Matching Pennies (0 Nash pur) : compte non nul."""
        assert exhaustive_counts.get("Matching Pennies", 0) > 0


# ----------------------------------------------------------------------------
# NAMED_GAMES round-trip : INCOHERENCE DOCUMENTEE (xfail honest).
#
# Les modeles NAMED_GAMES du module ne font PAS l'aller-retour via son propre
# encodeur create_ordinal_game : seul Matching Pennies est correctement
# reconnu. Les autres modeles (PD, Stag Hunt, Chicken, BoS) sont mal classes
# parce que l'encodage de la matrice B (B = [[p2[0],p2[2]],[p2[1],p2[3]]]) est
# incoherent avec l'ordre des tuples des modeles (qui semblent lister les gains
# P2 en ordre row-major (CC,CD,DC,DD), comme P1, alors que la formule B les
    # consomme en ordre column-major).
#
# Ces tests xfail expriment le COMPORTEMENT CORRECT attendu (le modele PD doit
# etre classifie "Prisoner's Dilemma"). Ils echouent aujourd'hui (bug) et
# passeront (xpass) quand l'encodage sera corrige dans une PR dediee (un sujet
# par PR ; ce fichier est test-only). strict=False pour ne pas casser CI quand
# le bug sera corrige.
# ----------------------------------------------------------------------------

@pytest.mark.xfail(
    reason="create_ordinal_game B-encoding incoherent avec NAMED_GAMES: "
           "le modele PD est classe 'Dominant Strategy' au lieu de "
           "'Prisoner's Dilemma'. Bug a corriger dans une PR dediee.",
    strict=False,
)
def test_named_prisoners_dilemma_round_trips():
    A, B = topo.create_ordinal_game(**{k: topo.NAMED_GAMES["Prisoner's Dilemma"][k]
                                       for k in ("p1", "p2")})
    assert topo.classify_game(A, B) == "Prisoner's Dilemma"


@pytest.mark.xfail(
    reason="create_ordinal_game B-encoding incoherent : le modele Stag Hunt "
           "est classe 'Other' au lieu de 'Stag Hunt'. Bug a corriger dans une "
           "PR dediee.",
    strict=False,
)
def test_named_stag_hunt_round_trips():
    data = topo.NAMED_GAMES["Stag Hunt"]
    A, B = topo.create_ordinal_game(data["p1"], data["p2"])
    assert topo.classify_game(A, B) == "Stag Hunt"


@pytest.mark.xfail(
    reason="create_ordinal_game B-encoding incoherent : le modele Chicken "
           "est classe 'Other' au lieu de 'Chicken/Hawk-Dove'. Bug a corriger "
           "dans une PR dediee.",
    strict=False,
)
def test_named_chicken_round_trips():
    data = topo.NAMED_GAMES["Chicken"]
    A, B = topo.create_ordinal_game(data["p1"], data["p2"])
    assert topo.classify_game(A, B) in ("Chicken/Hawk-Dove", "Chicken")


@pytest.mark.xfail(
    reason="create_ordinal_game B-encoding incoherent : le modele Battle of "
           "the Sexes est classe 'Coordination Game'. Bug a corriger dans une "
           "PR dediee.",
    strict=False,
)
def test_named_battle_of_the_sexes_round_trips():
    data = topo.NAMED_GAMES["Battle of the Sexes"]
    A, B = topo.create_ordinal_game(data["p1"], data["p2"])
    assert topo.classify_game(A, B) == "Battle of the Sexes"


def test_named_matching_pennies_round_trips():
    """Matching Pennies est le SEUL modele qui fait correctement l'aller-retour.

    (Aucune dominance, 0 Nash pur -> la classification est robuste a l'encodage
    B car elle ne depend que de l'existence de Nash/dominance, pas de leur
    position precisement.) Ce test (non xfail) verifie que ce cas fonctionne.
    """
    data = topo.NAMED_GAMES["Matching Pennies"]
    A, B = topo.create_ordinal_game(data["p1"], data["p2"])
    assert topo.classify_game(A, B) == "Matching Pennies"


# ----------------------------------------------------------------------------
# print_game_analysis : fonction d'affichage (smoke test, capture stdout).
# ----------------------------------------------------------------------------

class TestPrintGameAnalysis:
    """print_game_analysis : affichage lisible sans erreur (smoke test)."""

    def test_runs_without_error(self, capsys):
        topo.print_game_analysis("Test", PD_A, PD_B)
        out = capsys.readouterr().out
        assert "Test" in out
        assert "Prisoner's Dilemma" in out

    def test_shows_nash(self, capsys):
        topo.print_game_analysis("PD", PD_A, PD_B)
        out = capsys.readouterr().out
        assert "Nash" in out
