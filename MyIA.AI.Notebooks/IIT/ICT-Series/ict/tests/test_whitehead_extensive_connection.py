"""Tests du banc de la case 28 (connexion extensive, Whitehead 1929).

Le banc execute un scelle : `docs/ict/whitehead-extensive-connection-pre-enregistrement.md`
fixe les hypotheses, les lectures (K1-K5), les substrats, les predictions et la
regle de verdict ; `ict/whitehead_extensive_connection.py` ne fait que les
executer. Ces tests gardent trois choses distinctes :

1. **les scalaires du scelle** contre la derive entre le doc et le module
   (graines, seuils, listes de lemmes, taille de la grille) ;
2. **les primitives** dont dependent les verdicts (normalisation fermee vs
   litterale, chaine non tangentielle et chaine naive rejetee par D10(i),
   temoin scelle present en S2 et absent en S1, alignement position/identifiant
   des masques de `prepare`) ;
3. **les mesures** : determinisme byte-a-byte, invariants de la matrice, et
   egalite avec l'artefact committe `ict/results/whitehead_extensive_connection_results.json`.

Aucun test ne recalibre une bande : le verdict est borne par le scelle, pas par
ces tests.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

import pytest

from ict import whitehead_extensive_connection as wec

ICT_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = ICT_DIR.parent.parent.parent.parent
SEALED_DOC = REPO_ROOT / "docs" / "ict" / "whitehead-extensive-connection-pre-enregistrement.md"
RESULTS = ICT_DIR / "results" / "whitehead_extensive_connection_results.json"


@pytest.fixture(scope="module")
def sealed_text():
    assert SEALED_DOC.is_file(), f"scelle introuvable : {SEALED_DOC}"
    return SEALED_DOC.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def substrates():
    return {substrate.key: substrate for substrate in wec.build_substrates(0)}


@pytest.fixture(scope="module")
def light_report():
    """Run complet sans recensement ni balayage (les seuls champs lents)."""
    return wec.run_all(with_census=False, with_sweep=False)


# --------------------------------------------------------------------------- #
# 1. Scalaires du scelle
# --------------------------------------------------------------------------- #


def test_assumption_set_is_tronc_without_13_and_14():
    """La numerotation imprimee saute 13 et 14 : 24 hypotheses, pas 26."""
    assert len(wec.ASSUMPTIONS) == 24
    assert set(wec.ASSUMPTIONS) == set(range(1, 13)) | set(range(15, 27))
    assert 13 not in wec.ASSUMPTIONS and 14 not in wec.ASSUMPTIONS


def test_lemma_lists_partition_the_assumptions():
    """L7 annonce 13 non violables et 11 violables, sans recouvrement."""
    never = set(wec.NEVER_VIOLABLE)
    violable = set(wec.VIOLABLE)
    assert not never & violable
    assert never | violable == set(wec.ASSUMPTIONS)
    assert len(never) == 13 and len(violable) == 11


@pytest.mark.parametrize(
    "scalar, value",
    [
        ("NULL_SIZE", 8),
        ("P6_MIN_VIOLATIONS", 12),
        ("CONTROL_MIN_VIOLATIONS", 14),
        ("MIN_NECESSARY", 15),
        ("MIN_EPOCHAL", 3),
        ("CHAIN_LENGTH", 40),
        ("MANY", 2),
    ],
)
def test_sealed_scalars(scalar, value):
    """Chaque seuil du compte final est celui du scelle, pas un ajustement posterieur."""
    assert getattr(wec, scalar) == value


def test_seeds_are_the_family_convention():
    """Graines de test 0/1/7/42/99, graines de controle disjointes 11/22/33."""
    assert wec.TEST_SEEDS == (0, 1, 7, 42, 99)
    assert wec.CONTROL_SEEDS == (11, 22, 33)
    assert not set(wec.TEST_SEEDS) & set(wec.CONTROL_SEEDS)


def test_grid_is_thirteen_points_including_the_thirds():
    points = wec._pts(wec.GRID)
    assert len(wec.GRID) == 13 == len(points)
    assert F(1, 3) in points and F(2, 3) in points
    assert [F(1, 6), F(1, 3), F(1, 2), F(2, 3), F(5, 6)] == list(points[1:6])


def test_sealed_doc_carries_the_readings_and_the_verdict_rule(sealed_text):
    """Le doc est la source normative : les cinq lectures et la regle y sont ecrites."""
    for marker in ("K1", "K2", "K3", "K4", "K5", "REFUTÉ", "SUPPORTED",
                   "NON_CONCLUSIF", "PARTIEL"):
        assert marker in sealed_text, f"le scelle ne nomme pas {marker}"
    assert "S2r" in sealed_text
    # Les seuils du compte final se lisent dans le doc, pas seulement dans le module.
    for number in (str(wec.P6_MIN_VIOLATIONS), str(wec.CONTROL_MIN_VIOLATIONS),
                   str(wec.MIN_NECESSARY), str(wec.MIN_EPOCHAL)):
        assert number in sealed_text


# --------------------------------------------------------------------------- #
# 2. Primitives dont dependent les verdicts
# --------------------------------------------------------------------------- #


def test_closed_and_literal_normalizations_differ_on_touching_pieces(substrates):
    """S1 recolle les morceaux qui se touchent, S2 les garde distincts ; meme adherence."""
    closed, literal = substrates["S1_closed"], substrates["S2_open"]
    pieces = ((F(0), F(1, 3)), (F(1, 3), F(2, 3)), (F(2, 3), F(1)))
    assert len(closed.normalize(pieces)) == 1
    assert len(literal.normalize(pieces)) == 3
    # csp = adherence : les deux formes se rejoignent, sinon R1 de S1 serait faux.
    assert closed.csp(closed.normalize(pieces)) == literal.csp(literal.normalize(pieces))


def test_naive_chain_is_rejected_by_d10_i_in_regular_families(substrates):
    """D10(i) : une chaine a plus petit membre est tangentielle, donc ecartee.

    Valable la ou D8 n'est pas vide, c'est-a-dire dans les familles regulieres
    (S1, S2r, S4). En S2, l'irregularite vide D8 : voir le test suivant.
    """
    for key in ("S1_closed", "S2r_open_regularized", "S4_d1"):
        statuses = wec.chain_statuses(substrates[key])
        assert statuses["non_tangentielle"] is True, key
        assert statuses["chaine_naive_rejetee_par_D10_i"] is True, key


def test_irregular_open_family_empties_d8(substrates):
    """En S2 aucune intersection n'est exterieure, donc D8 est vide et D9 vaut l'inclusion.

    C'est la lecture declaree de la famille ouverte ; elle explique que la chaine
    naive n'y soit pas ecartee par D10(i) tout en etant tangentielle en S1.
    """
    literal = substrates["S2_open"]
    statuses = wec.chain_statuses(literal)
    assert statuses["chaine_naive_rejetee_par_D10_i"] is False
    naive = literal.naive_chain()
    assert literal.includes(naive.member(1), naive.member(2)) is True
    assert literal.tang(naive.member(1), naive.member(2)) is False
    # Memes deux regions, famille fermee : la tangence reapparait.
    assert substrates["S1_closed"].tang(
        substrates["S1_closed"].naive_chain().member(1),
        substrates["S1_closed"].naive_chain().member(2)) is True


def test_sealed_witness_is_present_in_open_and_absent_in_closed(substrates):
    """Le temoin scelle dissecte (0,1) et (0,1)\\{1/3,2/3} en S2 ; en S1 les deux coincident."""
    open_witness = substrates["S2_open"].sealed_witness()
    assert open_witness["regions_distinctes"] is True
    assert open_witness["dans_la_batterie"] is True
    assert open_witness["dissection_de_0_1"] is True
    assert open_witness["dissection_de_la_seconde"] is True

    closed_witness = substrates["S1_closed"].sealed_witness()
    assert closed_witness["regions_distinctes"] is False
    assert closed_witness["temoins"][0] == closed_witness["temoins"][1]


@pytest.mark.parametrize("key", ["S1_closed", "S2_open", "S2r_open_regularized",
                                 "S3_atomic", "S4_d1", "S5_tree"])
def test_prepare_masks_are_read_by_battery_position(key, substrates):
    """Garde de l'aliasing position/identifiant : `inc[i]` doit designer la ligne i.

    C'est la cause racine d'un run avorte : une batterie triee par `repr` donnait
    `battery[position] != position` pour les familles indexees par un entier, et
    les masques lus par identifiant designaient une autre region (A20 faux).
    """
    substrate = substrates[key]
    substrate.prepare()
    battery = substrate.battery()
    for position in range(len(battery)):
        assert substrate.index_of(battery[position]) == position, (key, position)
        for other in range(len(battery)):
            bit = bool((substrate.inc[position] >> other) & 1)
            assert bit == substrate.includes(battery[position], battery[other]), (
                key, position, other)


def test_connection_is_irreflexive_by_convention(substrates):
    """K1 : A4 est une convention de nomenclature, donc `par_definition` partout."""
    for key, substrate in substrates.items():
        substrate.prepare()
        battery = substrate.battery()
        for region in battery:
            assert substrate.conn(region, region) is False, key


# --------------------------------------------------------------------------- #
# 3. Mesures
# --------------------------------------------------------------------------- #


def test_substrate_sizes_are_stable(substrates):
    """Tailles mesurees, gardees contre une derive de construction de batterie."""
    sizes = {key: len(substrate.battery()) for key, substrate in substrates.items()}
    assert sizes == {
        "S1_closed": 89,
        "S2_open": 92,
        "S2r_open_regularized": 89,
        "S3_atomic": 63,
        "S4_d1": 29,
        "S4_d2": 30,
        "S4_d3": 30,
        "S4_d4": 30,
        "S5_tree": 14,
    }


def test_run_is_byte_for_byte_deterministic():
    """Aucun horodatage, aucune iteration sur un ensemble non ordonne."""
    first = json.dumps(wec.run_all(with_census=False, with_sweep=False),
                       sort_keys=True, default=wec._json_default)
    second = json.dumps(wec.run_all(with_census=False, with_sweep=False),
                        sort_keys=True, default=wec._json_default)
    assert first == second


def test_matrix_has_no_seed_divergence(light_report):
    """Un statut `instable` signerait une mesure dependante de la graine, non du substrat."""
    for key, state in light_report["substrates"].items():
        assert state["graines_divergentes"] == [], key


def test_invariants_of_the_matrix(light_report):
    """Ce que la mesure etablit dans **tous** les substrats, sans exception."""
    matrix = light_report["matrice"]
    for key, row in matrix.items():
        assert row["1"] == "true", key          # A1 symetrie de la connexion
        assert row["20"] == "true", key         # A20 : faux a l'epoque de l'aliasing
        assert row["4"] == "par_definition", key
        assert row["7"] == "par_definition", key
        assert row["21"] == "par_definition", key
        assert row["26"] == "par_definition", key


def test_open_regularized_family_has_no_false_cell(light_report):
    """Controle de L8 : les echecs de S2 tiennent a l'irregularite, pas a l'ouverture."""
    row = light_report["matrice"]["S2r_open_regularized"]
    assert wec._failures(row) == []


def test_p1_holds_and_partials_are_declared(light_report):
    """P1 : aucune case `false` en S1 ; A15/A16 y restent `partiel` (scelle 6.3)."""
    p1 = light_report["predictions"]["P1"]
    assert p1["tenue"] is True
    assert p1["cases_false"] == []
    assert p1["cases_partiel"] == [15, 16]


def test_verdict_is_bounded_by_the_sealed_rule(light_report):
    """Le verdict appartient a l'echelle du scelle, et son alternative est nommee."""
    assert light_report["verdict"] in {
        "REFUTE", "SUPPORTED", "PARTIEL", "NON_CONCLUSIF", "NON_CONCLUSIF_INSTRUMENT"}
    assert light_report["verdict_hors_instrument"] in {
        "REFUTE", "SUPPORTED", "PARTIEL", "NON_CONCLUSIF"}
    assert light_report["verdict_hors_instrument"] != "NON_CONCLUSIF_INSTRUMENT"


def test_committed_results_match_a_fresh_run(light_report):
    """L'artefact committe est reproductible : meme matrice, meme partition, meme verdict."""
    if not RESULTS.is_file():
        pytest.skip(f"artefact non encore genere : {RESULTS}")
    committed = json.loads(RESULTS.read_text(encoding="utf-8"))
    for field in ("matrice", "partition", "verdict", "verdict_hors_instrument"):
        assert committed[field] == light_report[field], field
    for name in ("P1", "P2", "P3", "P4", "P5", "P6"):
        assert committed["predictions"][name]["tenue"] == light_report["predictions"][name]["tenue"], name
    for key, state in light_report["substrates"].items():
        assert committed["substrates"][key]["regions"] == state["regions"], key
