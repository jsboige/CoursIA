"""Tests du banc de la case 28b (portee exacte et null calibre, Whitehead 1929).

Le scelle `docs/ict/whitehead-calibrated-null-pre-enregistrement.md` fixe, avant
toute mesure : la portee attendue `R`, les theoremes de lecture T1-T4, le null
exact sur les 32 768 relations a n = 6, la courbe de densite en fractions, les
graines de transfert et de balayage, et la regle de verdict borne.
`ict/whitehead_calibrated_null.py` ne fait que les executer, en invoquant
l'organe de la case 28 par import (`ict/whitehead_extensive_connection.py`).

Ces tests gardent trois choses distinctes :

1. **les scalaires du scelle** contre la derive entre le doc et le module
   (portee, plafond, grilles, graines, decoupage des clauses par verdict) ;
2. **les primitives** dont dependent les verdicts : le recensement a n = 5
   reproduit la portee publiee de la case 28 et n'y viole jamais A17 — le fait
   nouveau est a n = 6 ; les temoins W et G evalues par leur nom ; K6 ; la
   partition de L7 (treize hypotheses non violables, onze violables) ;
3. **les mesures** : determinisme byte-a-byte, invariants du recensement, et
   egalite avec l'artefact committe `ict/results/whitehead_calibrated_null_results.json`.

Aucun test ne recalibre une bande : la clause tombee (Q5c, A18 a 7/10) est
verifiee comme tombee, avec sa valeur mesuree. Le verdict est borne par le
scelle, jamais par ces tests.
"""

from __future__ import annotations

import copy
import json
from fractions import Fraction as F
from pathlib import Path

import pytest

from ict import whitehead_calibrated_null as wcn
from ict import whitehead_extensive_connection as wec

ICT_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = ICT_DIR.parent.parent.parent.parent
SEALED_DOC = REPO_ROOT / "docs" / "ict" / "whitehead-calibrated-null-pre-enregistrement.md"
RESULTS = ICT_DIR / "results" / "whitehead_calibrated_null_results.json"


@pytest.fixture(scope="module")
def sealed_text():
    assert SEALED_DOC.is_file(), f"scelle introuvable : {SEALED_DOC}"
    return SEALED_DOC.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def report():
    """Une execution complete du banc (recensement exhaustif a n = 6)."""
    return wcn.run_all()


@pytest.fixture(scope="module")
def second_report():
    """Seconde execution independante : seul le determinisme en depend."""
    return wcn.run_all()


# --------------------------------------------------------------------------- #
# 1. Scalaires du scelle
# --------------------------------------------------------------------------- #


def test_reach_is_the_nine_hypotheses_of_the_reading():
    """La portee exacte est de neuf hypotheses, A17 comprise (elle n'apparait qu'a n = 6)."""
    assert wcn.REACH == (2, 3, 8, 9, 11, 15, 16, 17, 18)
    assert len(wcn.REACH) == 9
    assert 17 in wcn.REACH and 12 not in wcn.REACH and 20 not in wcn.REACH
    # A9 est dans la portee (violee partout) sans etre violable au sens de L7 :
    # elle n'est jamais vraie, ce qui est une autre forme de theoreme de lecture.
    assert 9 in wcn.REACH and wcn.UNCONDITIONAL_FALSE == (9,)


def test_theorems_and_exclusive_pair_are_the_sealed_ones():
    """T1/T2 (A12, A20 vraies partout), T3 (A9 fausse partout), T4 (A3 et A17 exclusives)."""
    assert wcn.THEOREMS_OF_READING == (12, 20)
    assert wcn.UNCONDITIONAL_FALSE == (9,)
    assert wcn.EXCLUSIVE_PAIR == (3, 17)
    assert not set(wcn.THEOREMS_OF_READING) & set(wcn.REACH)


@pytest.mark.parametrize(
    "scalar, value",
    [
        ("SIZE", 6),
        ("CEILING", 8),
        ("TRANSFER_SIZE", 8),
    ],
)
def test_sealed_scalars(scalar, value):
    """Chaque nombre du protocole est celui du scelle, pas un ajustement posterieur."""
    assert getattr(wcn, scalar) == value


def test_sealed_fractions():
    """Le niveau du noyau et le quantile du seuil sont des fractions exactes."""
    assert wcn.CORE_LEVEL == F(9, 10)
    assert wcn.CONFIDENCE == F(95, 100)


def test_density_grid_is_exactly_the_twenty_firsts():
    """Grille scellee : k/20 pour k = 0..20, plus les quatre points reellement echantillonnes."""
    assert wcn.DENSITY_GRID == tuple(F(k, 20) for k in range(21))
    assert len(wcn.DENSITY_GRID) == 21
    assert wcn.DENSITY_GRID[0] == 0 and wcn.DENSITY_GRID[-1] == 1
    assert wcn.SAMPLED_GRID == (F(149, 1000), F(299, 1000), F(699, 1000), F(849, 1000))
    # Les quatre points echantillonnes sont les densites nominales decalees d'un
    # millieme par `randint(1, 1000) < density` : 3/20=150/1000 tire 149/1000.
    assert [point + F(1, 1000) for point in wcn.SAMPLED_GRID] == [
        F(3, 20), F(3, 10), F(7, 10), F(17, 20)]


def test_sweep_densities_and_the_exploratory_arm():
    """Trois densites scellees ; 17/20 est declaree exploratoire et hors verdict."""
    assert wcn.SWEEP_DENSITIES == (F(3, 20), F(3, 10), F(7, 10))
    assert wcn.EXPLORATORY_DENSITY == F(17, 20)
    assert wcn.EXPLORATORY_DENSITY not in wcn.SWEEP_DENSITIES


def test_seeds_are_fresh_and_disjoint_from_the_published_ones():
    """Graines de test, de controle et de balayage, disjointes des familles publiees."""
    assert wcn.TRANSFER_SEEDS == (101, 202, 303, 404, 505)
    assert wcn.TRANSFER_CONTROL_SEEDS == (111, 222, 333)
    assert wcn.SWEEP_SEEDS == (611, 722, 833, 944, 1055)
    published = (set(wcn.PUBLISHED_SEEDS) | set(wcn.PUBLISHED_CONTROL_SEEDS)
                 | set(wcn.PUBLISHED_SWEEP_SEEDS))
    fresh = (set(wcn.TRANSFER_SEEDS) | set(wcn.TRANSFER_CONTROL_SEEDS)
             | set(wcn.SWEEP_SEEDS))
    assert not fresh & published
    assert not set(wcn.TRANSFER_SEEDS) & set(wcn.TRANSFER_CONTROL_SEEDS)
    assert not set(wcn.TRANSFER_SEEDS) & set(wcn.SWEEP_SEEDS)
    assert not set(wcn.TRANSFER_CONTROL_SEEDS) & set(wcn.SWEEP_SEEDS)


def test_clause_lists_partition_the_eighteen_legs():
    """La section 5 repartit les clauses entre les deux verdicts, sans trou ni recouvrement."""
    portee = set(wcn.PORTEE_LEGS)
    null = set(wcn.NULL_LEGS)
    assert not portee & null
    assert len(portee) == 10 and len(null) == 8
    for prefix in ("Q1a", "Q1b", "Q1c", "Q1d", "Q1e", "Q4a", "Q4b", "Q4c",
                   "Q3b", "Q5d"):
        assert any(leg.startswith(prefix) for leg in portee), prefix
    for prefix in ("Q2a", "Q2b", "Q2c", "Q3a", "Q3c", "Q5a", "Q5b", "Q5c"):
        assert any(leg.startswith(prefix) for leg in null), prefix


def test_sealed_doc_carries_the_reach_the_null_and_the_verdict_rule(sealed_text):
    """Le doc est la source normative : portee, null, graines et echelle y sont ecrits."""
    for marker in ("R = {2, 3, 8, 9, 11, 15, 16, 17, 18}", "32 768", "95/100",
                   "9/10", "499/1000", "17/20", "SUPPORTED", "PARTIEL",
                   "RÉFUTÉ", "NON_CONCLUSIF_INSTRUMENT"):
        assert marker in sealed_text, f"le scelle ne nomme pas {marker}"
    for clause in ("Q1a", "Q1e", "Q2c", "Q3c", "Q4d", "Q5d"):
        assert clause in sealed_text, f"le scelle ne nomme pas {clause}"
    # Les cinq livrables annonces sont nommes dans le doc lui-meme.
    for deliverable in ("whitehead_calibrated_null.py",
                        "test_whitehead_calibrated_null.py",
                        "whitehead_calibrated_null_results.json",
                        "docs/ict/README.md"):
        assert deliverable in sealed_text, deliverable
    # Les seuils 12 et 14 de la case 28 y sont retires, pas seulement echoues.
    assert "retir" in sealed_text


# --------------------------------------------------------------------------- #
# 2. Primitives dont dependent les verdicts
# --------------------------------------------------------------------------- #


def test_census_at_n5_reproduces_the_published_reach_and_never_violates_a17():
    """Garde de la continuite avec la case 28, et du fait nouveau de la case 28b.

    La case 28 a recense les relations a n <= 5 (1 099) et publie
    `[2, 3, 8, 9, 11, 15, 16, 18]`. Le recensement a n = 5 seul doit rendre la
    meme portee, sans A17 : c'est a n = 6 que A17 devient violable, et c'est ce
    que la case 28b mesure.
    """
    census = wcn.census(5)
    assert census["relations"] == 2 ** 10
    assert census["portee_observee"] == [2, 3, 8, 9, 11, 15, 16, 18]
    assert census["violations_observees"]["17"] == 0
    assert census["relations_A3_et_A17"] == 0


def test_census_at_n6_is_the_exhaustive_universe():
    """A n = 6 l'univers est 2^15 relations ; A17 y est violee, sur peu de relations."""
    census = wcn.census(6)
    assert census["relations"] == 2 ** 15 == 32768
    assert census["portee_observee"] == list(wcn.REACH)
    assert 0 < census["violations_observees"]["17"] < census["relations"]
    assert census["violations_observees"]["9"] == census["relations"]


def test_witness_w_is_evaluated_by_name_and_satisfies_its_clause():
    """T4 temoin positif : A3 vraie, violations contenant {2, 8, 9, 11, 17, 18}."""
    witness = wcn.witnesses()["W"]
    assert witness["clause"] == "superset"
    assert witness["conforme"] is True
    assert witness["A3_vraie"] is True
    assert set(witness["attendu"]) <= set(witness["violations"])
    assert set(witness["violations"]) <= set(wcn.REACH)


def test_witness_g_reaches_the_ceiling_with_a3_false():
    """Le certificat du plafond : K3 + K2 + K1, huit violations, A3 fausse."""
    witness = wcn.witnesses()["G"]
    assert witness["clause"] == "equal"
    assert witness["conforme"] is True
    assert witness["A3_vraie"] is False
    assert witness["violations"] == [2, 3, 8, 9, 11, 15, 16, 18]
    assert len(witness["violations"]) == wcn.CEILING


def test_complete_graph_is_the_dense_end_of_the_sealed_curve():
    """Q4c : K6 viole {2, 3, 8, 9, 18}, satisfait A11/A15/A17, viole A16."""
    complete = wcn.complete_edge()
    assert complete["violations"] == [2, 3, 8, 9, 16, 18]
    assert complete["statuts"]["11"] == "true"
    assert complete["statuts"]["15"] == "true"
    assert complete["statuts"]["17"] == "true"
    assert complete["statuts"]["16"] == "false"


def test_statuses_partition_the_printed_hypotheses():
    """Les vingt-quatre hypotheses imprimees, et la portee mesuree contre la partition de L7.

    L7 annonce treize hypotheses non violables et onze violables. La case 28b
    mesure neuf hypotheses violees : les onze violables moins les deux theoremes
    de lecture (A12 et A20). C'est le gain exact du rescellement.
    """
    statuses = wcn._statuses(wcn.relation_from_mask(6, 0))
    assert set(statuses) == set(range(1, 13)) | set(range(15, 27))
    never = set(wec.NEVER_VIOLABLE)
    violable = set(wec.VIOLABLE)
    assert not never & violable
    assert never | violable == set(statuses)
    assert len(never) == 13 and len(violable) == 11
    assert set(wcn.REACH) == violable - set(wcn.THEOREMS_OF_READING)
    assert statuses[12] == "true" and statuses[20] == "true"
    assert statuses[9] == "false"


def test_relation_from_witness_and_from_mask_agree_on_the_same_edge_set():
    """Deux constructeurs, une seule semantique : les temoins sont des relations comme les autres."""
    wanted = set()
    for index, (_, neighbours) in enumerate(wcn.WITNESS_G):
        for other in neighbours:
            wanted.add((min(index, other), max(index, other)))
    mask = 0
    for position, (first, second) in enumerate(wcn._edges(6)):
        if (min(first, second), max(first, second)) in wanted:
            mask |= 1 << position
    from_witness = wcn.relation_from_witness(wcn.WITNESS_G, "G")
    from_mask = wcn.relation_from_mask(6, mask, "G")
    assert wcn._statuses(from_witness) == wcn._statuses(from_mask)


def test_summary_cites_the_published_case_28_census(report):
    """Le resume du scelle cite la case 28 : 1 099 relations, taille maximale 5.

    Le compte se derive : 1 + 2 + 8 + 64 + 1024 relations pour n = 1..5.
    """
    expected = sum(2 ** (size * (size - 1) // 2) for size in range(1, 6))
    assert expected == 1099
    assert report["summary"]["census_case_28"] == {"relations": expected, "taille_max": 5}


# --------------------------------------------------------------------------- #
# 3. Mesures
# --------------------------------------------------------------------------- #


def test_run_is_byte_for_byte_deterministic(report, second_report):
    """Aucun horodatage, aucune iteration sur un ensemble non ordonne."""
    first = json.dumps(report, sort_keys=True, default=wec._json_default)
    second = json.dumps(second_report, sort_keys=True, default=wec._json_default)
    assert first == second


def test_census_invariants(report):
    """Ce que le recensement exhaustif etablit, sans exception."""
    census = report["census"]
    assert census["relations"] == 32768
    assert census["relations_indecises"] == 0
    assert census["relations_hors_portee"] == 0
    assert census["relations_A3_et_A17"] == 0
    assert census["portee_observee"] == list(wcn.REACH)
    assert census["plafond"] == wcn.CEILING
    assert census["plafond_atteint"] is True
    assert census["violations_observees"]["12"] == 0
    assert census["violations_observees"]["20"] == 0
    assert census["violations_observees"]["9"] == census["relations"]
    assert all(report["lemmes"].values())


def test_exact_null_is_the_uniform_law(report):
    """Q2 : q9 = 0, q12 = q20 = 1, noyau contenu dans R, k* dans {3, 4}."""
    calibration = report["calibration"]
    assert calibration["k_etoile"] == 4
    assert calibration["k_etoile"] in (3, 4)
    assert calibration["noyau_dixieme"] == [2, 9, 11, 15]
    assert calibration["noyau_inclus_dans_portee"] is True
    assert calibration["noyau_contient_le_publie"] is True
    assert calibration["q_exactes"]["9"] == 0
    assert calibration["q_exactes"]["12"] == 1
    assert calibration["q_exactes"]["20"] == 1
    ceiling_mass = F(report["census"]["relations_au_plafond"], report["census"]["relations"])
    assert calibration["P_K_superieur_ou_egal"]["8"] == ceiling_mass


def test_density_curve_keeps_the_theorem(report):
    """Q4b : a toute densite de la grille, q9 = 0 (T3), en fractions exactes.

    La courbe porte les vingt et un points de la grille et les quatre densites
    reellement echantillonnees, comme le scelle les declare.
    """
    assert set(report["courbe"]) == ({str(density) for density in wcn.DENSITY_GRID}
                                     | {str(density) for density in wcn.SAMPLED_GRID})
    for density in wcn.DENSITY_GRID + wcn.SAMPLED_GRID:
        assert report["courbe"][str(density)]["9"] == 0, density


def test_transfer_is_within_reach_on_eight_fresh_relations(report):
    """Q3 : les huit relations (cinq tests, trois controles) restent dans la portee."""
    transfer = report["transfert"]
    assert transfer["relations"] == 8
    assert transfer["portee_respectee"] == 8
    assert transfer["comptes"]["A9"] == 8
    assert transfer["comptes"]["A15"] >= 7
    assert transfer["comptes"]["A2"] >= 6
    assert transfer["comptes"]["A11"] >= 5
    assert transfer["K_superieur_ou_egal_3"] >= 6
    assert transfer["K_minimum"] <= 4


def test_sweep_arms_and_the_fallen_clause(report):
    """Q5a-Q5d : deux bras tiennent, le troisieme porte la clause tombee (A18 a 7/10).

    La bande scellee « A18 sur au moins 3/5 a 7/10 » est mesuree a 0/5 et tombe.
    Le test la fige comme tombee : un chiffre remonte sans nouvelle mesure serait
    une bande deplacee apres coup.
    """
    arms = report["balayage"]
    for density in wcn.SWEEP_DENSITIES:
        assert arms[str(density)]["portee_respectee"] == 5, density
        assert arms[str(density)]["comptes"]["9"] == 5, density
        assert arms[str(density)]["K_maximum"] <= wcn.CEILING, density
    assert arms["3/20"]["comptes"]["2"] == 5
    assert arms["3/20"]["comptes"]["15"] == 5
    assert arms["3/10"]["comptes"]["2"] == 5
    assert arms["3/10"]["comptes"]["15"] == 5
    assert arms["7/10"]["comptes"]["11"] == 5
    assert arms["7/10"]["comptes"]["15"] == 5
    assert arms["7/10"]["comptes"]["18"] == 0
    assert report["questions"]["Q5c_balayage_7_10"] is False
    assert arms[str(wcn.EXPLORATORY_DENSITY)]["hors_verdict"] is True


def test_verdict_is_bounded_by_the_sealed_rule(report):
    """La regle de la section 5 appliquee aux mesures : une clause tombee = PARTIEL."""
    assert report["verdict_portee"] == "SUPPORTED"
    assert report["verdict_null"] == "PARTIEL"
    assert report["verdict"] == "PARTIEL"
    assert report["summary"]["clauses_fausses"] == ["Q5c_balayage_7_10"]
    assert report["summary"]["seuils_case_28_retires"] == [12, 14]


def test_sealed_rule_maps_the_broken_legs_the_way_it_says(report):
    """Garde de la regle elle-meme : une jambe tombee = PARTIEL, deux = REFUTE, lemme faux = REFUTE."""
    one = copy.deepcopy(report)
    one["questions"]["Q5c_balayage_7_10"] = True
    one["questions"]["Q5a_balayage_3_20"] = False
    assert wcn.verdict(one) == ("SUPPORTED", "PARTIEL", "PARTIEL")

    two = copy.deepcopy(one)
    two["questions"]["Q3a_transfert_frequences"] = False
    assert wcn.verdict(two)[1] == "REFUTE"

    lemma = copy.deepcopy(report)
    lemma["lemmes"]["T1_A12_jamais_violee"] = False
    assert wcn.verdict(lemma) == ("REFUTE", "PARTIEL", "REFUTE")


def test_committed_results_match_a_fresh_run(report):
    """L'artefact committe est reproductible : le fichier entier, a l'octet de champ pres."""
    if not RESULTS.is_file():
        pytest.skip(f"artefact non encore genere : {RESULTS}")
    fresh = json.loads(json.dumps(report, sort_keys=True, default=wec._json_default))
    committed = json.loads(RESULTS.read_text(encoding="utf-8"))
    assert committed == fresh
