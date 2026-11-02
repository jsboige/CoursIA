"""Tests de scripts/ci/check_cancelled_only_commits.py (#22088).

Chaque verdict est verifie par un CONTROLE POSITIF (la forme mesuree est
reconnue) ET par son CONTROLE NEGATIF. Le controle negatif qui compte le plus
est celui du rouge MERITE : un commit porteur d'une vraie jambe en echec ne
doit jamais etre classe « annulation seule », sinon l'organe blanchirait une
regression -- exactement l'inverse du service rendu.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_cancelled_only_commits import analyse, classify, leg_conclusion, leg_name  # noqa: E402


def test_succes_ordinaire():
    assert classify("SUCCESS", [("Build", "SUCCESS")]) == "OK"


def test_commit_sans_aucune_jambe():
    # Un commit dont les workflows ne se declenchent pas n'est pas rouge.
    assert classify(None, []) == "OK"


def test_rouge_merite_par_une_vraie_jambe():
    assert classify("FAILURE", [("Tests", "FAILURE")]) == "OK"


def test_rouge_emprunte_par_une_annulation_seule():
    # Le defaut #22088 : aucune jambe n'a echoue, pourtant le commit est rouge.
    assert classify("FAILURE", [("Scripts Tests (CPU)", "CANCELLED")]) == "CANCELLED_ONLY"


def test_annulation_plus_jambes_vertes_reste_empruntee():
    legs = [("A", "CANCELLED"), ("B", "SUCCESS"), ("C", "SKIPPED"), ("D", "NEUTRAL")]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_annulation_plus_vraie_panne_n_est_pas_empruntee():
    # Controle negatif central : la presence d'une annulation n'excuse rien.
    legs = [("A", "CANCELLED"), ("B", "FAILURE")]
    assert classify("FAILURE", legs) == "OK"


def test_rouge_sans_jambe_lisible_n_est_pas_accuse():
    # FAILURE avec uniquement du vert : conclusion non modelisee, pas un blanc-seing.
    assert classify("FAILURE", [("A", "NEUTRAL")]) == "UNKNOWN"


def test_troncature_interdit_l_accusation():
    # Une vraie panne peut se trouver au-dela de la page de 100 contextes.
    assert classify("FAILURE", [("A", "CANCELLED")], truncated=True) == "UNKNOWN"


def test_troncature_ne_blanchit_pas_une_panne_visible():
    # Une panne deja visible reste meritee, troncature ou pas.
    assert classify("FAILURE", [("A", "FAILURE"), ("B", "CANCELLED")], truncated=True) == "OK"


def test_en_cours_n_est_pas_un_verdict():
    assert classify("PENDING", [("A", "CANCELLED")]) == "PENDING"


def test_lecture_des_deux_typologies_de_jambes():
    # Un CheckRun porte `name`+`conclusion`, un StatusContext `context`+`state`.
    check_run = {"name": "Build Quarto site", "conclusion": "CANCELLED"}
    status_ctx = {"context": "ci/legacy", "state": "FAILURE"}
    assert leg_name(check_run) == "Build Quarto site"
    assert leg_conclusion(check_run) == "CANCELLED"
    assert leg_name(status_ctx) == "ci/legacy"
    assert leg_conclusion(status_ctx) == "FAILURE"


def test_analyse_extrait_la_fenetre_et_le_verdict():
    node = {
        "oid": "a" * 40,
        "committedDate": "2026-10-23T21:48:04Z",
        "messageHeadline": "Fix(ci): exemple",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun", "name": "validate", "conclusion": "SUCCESS"},
                    {"__typename": "CheckRun", "name": "Scripts Tests (CPU)", "conclusion": "CANCELLED"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == "CANCELLED_ONLY"
    assert row["non_green"] == ["Scripts Tests (CPU)=CANCELLED"]
    assert row["truncated"] is False


def test_analyse_signale_la_troncature():
    node = {
        "oid": "b" * 40,
        "committedDate": "2026-10-23T21:48:04Z",
        "messageHeadline": "Fix(ci): exemple tronque",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": True},
                "nodes": [
                    {"__typename": "CheckRun", "name": "A", "conclusion": "CANCELLED"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["truncated"] is True
    assert row["verdict"] == "UNKNOWN"
