"""Tests de scripts/ci/check_cancelled_only_commits.py (#22088).

Chaque verdict est verifie par un CONTROLE POSITIF (la forme mesuree est
reconnue) ET par son CONTROLE NEGATIF. Le controle negatif qui compte le plus
est celui du rouge MERITE : un commit porteur d'une vraie jambe en echec ne
doit jamais etre classe « annulation seule », sinon l'organe blanchirait une
regression -- exactement l'inverse du service rendu.
"""

import pathlib
import sys
from datetime import datetime, timedelta

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_cancelled_only_commits import (  # noqa: E402
    KILLED,
    STARTED_GRACE_SECONDS,
    SUPERSEDED,
    analyse,
    cancelled_kind,
    classify,
    leg_conclusion,
    leg_fields,
    leg_name,
)

#: Debut arbitraire, construit une fois : toute duree de test se derive d'ici
#: par arithmetique (`timedelta`). Interpoler les chiffres du seuil dans une
#: chaine ISO -- l'ancien ``f"04:00:0{G // 60}Z"`` -- ne marchait que pour un
#: seuil dont les minutes tiennent sur un chiffre : 600 s y devenait
#: ``04:00:010Z``, que ``fromisoformat`` lit comme 1 seconde de vie.
_STARTED = datetime.fromisoformat("2026-11-13T04:00:00+00:00")
_STARTED_Z = "2026-11-13T04:00:00Z"


def _ended_after(seconds):
    """Horodatage de fin ISO (suffixe Z) a ``seconds`` du debut de reference."""
    return (_STARTED + timedelta(seconds=seconds)).isoformat().replace("+00:00", "Z")


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


# --- #25181 : deux annulations, un seul rendu ---------------------------------
#
# `cancelled` couvre deux evenements que l'UI peint a l'identique. Les tests
# ci-dessous separent la supersession de file (empruntee) de la mort d'infra
# (meritee), et verifient que le doute ne blanchit jamais le second.


def test_deux_uplets_restent_acceptes():
    # La forme historique (name, conclusion) reste lisible : un StatusContext
    # ne porte aucune mesure de duree, et un appelant doit pouvoir classer.
    assert leg_fields(("A", "CANCELLED")) == ("A", "CANCELLED", None, None)


def test_annulation_sans_demarrage_est_empruntee():
    # Aucun startedAt : le job n'a jamais eu de runner. Rien de mesure.
    assert cancelled_kind(None, None) == SUPERSEDED
    legs = [("Scripts Tests (CPU)", "CANCELLED", None, None)]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_job_tue_a_son_timeout_est_une_mort_d_infra():
    # Controle positif du defaut #25181 : 60 min de runner, puis `cancelled`.
    legs = [("Build Quarto site", "CANCELLED",
             "2026-11-13T04:00:00Z", "2026-11-13T05:00:17Z")]
    assert cancelled_kind(*legs[0][2:]) == KILLED
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_demarrage_sans_fin_lisible_reste_une_mort_d_infra():
    # Le doute ne doit jamais disculper un job qui a tenu un runner.
    legs = [("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z", None)]
    assert cancelled_kind("2026-11-13T04:00:00Z", None) == KILLED
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_supersession_mixee_a_une_mort_d_infra_reste_infra():
    legs = [
        ("Another build", "CANCELLED", None, None),
        ("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z",
         "2026-11-13T05:00:15Z"),
    ]
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_annulation_sous_le_seuil_reste_empruntee():
    # Un job qui n'a vecu que quelques secondes n'a pas ete tue : il a perdu
    # sa place. Le seuil separe la file du travail.
    legs = [("Build", "CANCELLED", _STARTED_Z,
             _ended_after(STARTED_GRACE_SECONDS - 1))]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_la_frontiere_du_seuil_est_mesuree_a_la_seconde_pres():
    # Controle de bornes G-1 / G / G+1 : la frontiere est inclusive (``>=``),
    # et sa preuve ne depend pas du nombre de chiffres du seuil -- un seuil a
    # trois chiffres ne doit rien changer au verdict des bornes.
    g = STARTED_GRACE_SECONDS
    assert cancelled_kind(_STARTED_Z, _ended_after(g - 1)) == SUPERSEDED
    assert cancelled_kind(_STARTED_Z, _ended_after(g)) == KILLED
    assert cancelled_kind(_STARTED_Z, _ended_after(g + 1)) == KILLED


def test_une_vraie_panne_reste_meritee_meme_avec_une_mort_d_infra():
    # Controle negatif : le nouveau verdict n'absorbe pas le rouge merite.
    legs = [
        ("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z",
         "2026-11-13T05:00:15Z"),
        ("Tests", "FAILURE"),
    ]
    assert classify("FAILURE", legs) == "OK"


def test_analyse_expose_la_preuve_de_chaque_annulation():
    # Le rapport doit dire POURQUOI la jambe est INFRA, sinon le lecteur voit
    # le meme mot `CANCELLED` que pour une supersession.
    node = {
        "oid": "c" * 40,
        "committedDate": "2026-11-13T05:01:00Z",
        "messageHeadline": "Feat(x): exemple",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun", "name": "Build Quarto site",
                     "conclusion": "CANCELLED",
                     "startedAt": "2026-11-13T04:00:00Z",
                     "completedAt": "2026-11-13T05:00:15Z"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == "INFRA_ONLY"
    assert row["cancelled_evidence"] == ["Build Quarto site=KILLED(60 min)"]
