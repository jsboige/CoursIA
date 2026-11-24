"""La QUALIFICATION cote CONSOMMATEUR -- la porte avant tout claim/edition.

`check_lane_claim.py` est la commande que le protocole impose avant
d'**editer** un fichier pour un grain rattache a une issue (#N). Depuis
#27225, cette commande applique aussi la QUALIFICATION : le meme organe que
le tirage (`tapis_rapide.etats`), joue sur le FIL COMPLET que la lecture a
deja rendu. Un grain ecarte par la qualification n'est ni reclame ni edite.

Aucun test ne touche le reseau : le payload est fabrique.
"""
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

LANE = "myia-ai-01:CoursIA-2"
AUTRE = "myia-po-2025:CoursIA-2"
NOW = datetime(2026, 11, 18, 9, 0, tzinfo=UTC)


def _payload(body: str = "", commentaires: list[str] | None = None,
             labels: list[str] | None = None, numero: int = 7) -> dict:
    """Un payload `gh issue view --json` minimal."""
    quand = (NOW - timedelta(days=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {
        "number": numero, "title": "Grain 7", "body": body,
        "createdAt": "2026-11-01T00:00:00Z",
        "labels": [{"name": lab} for lab in (labels or [])],
        "comments": [{"body": b, "createdAt": quand,
                      "author": {"login": "jsboige"}} for b in (commentaires or [])],
    }


def test_un_grain_propre_passe_la_qualification():
    """Un grain sans ecart passe : la porte ne bloque pas le travail normal."""
    assert clc._qualification_grain(_payload(), LANE, NOW) is None


def test_une_issue_rendue_recentement_est_refusee():
    """Une issue RENDUE par une autre lane il y a moins de 3 jours est
    refusee : son motif (barriere, siege) vaut encore (fenetre RELACHEE).

    C'est le cas que la voie legere ne peut plus voir -- elle classe sur
    metadonnees seules -- et que le consommateur doit voir.
    """
    code_motif = clc._qualification_grain(
        _payload(commentaires=[f"[RELEASED] lane {AUTRE} -- motif : bloque par X"]),
        LANE, NOW)
    assert code_motif is not None
    code, motif = code_motif
    assert code == "RELACHEE"
    assert "rendue par" in motif


def test_une_issue_gelee_est_refusee():
    """Une ligne [FROZEN] dans le body gele l'issue : elle n'est pas
    reclamee."""
    code_motif = clc._qualification_grain(
        _payload(body="[FROZEN] ce grain est gele"), LANE, NOW)
    assert code_motif is not None
    assert code_motif[0] == "GEL"


def test_un_label_de_cloture_est_refuse():
    """Le label `candidate-delivered` est une urne de cloture : elle est
    reservee au coordinateur et a l'adjoint."""
    code_motif = clc._qualification_grain(
        _payload(labels=["candidate-delivered"]), LANE, NOW)
    assert code_motif is not None
    assert code_motif[0] == "LABEL"


def test_la_porte_refuse_le_check_et_donc_le_claim(capsysbinary):
    """La porte est sur le CHEMIN du claim : un grain ecarte sort en 1, donc
    `[CLAIMED]` n'est pas poste (le `--claim` refuse de poster si le check
    rend autre chose que 0)."""
    rc = clc._run_check(
        _payload(commentaires=[f"[RELEASED] lane {AUTRE} -- motif : bloque par X"]),
        LANE, now=NOW)
    capture = capsysbinary.readouterr()
    assert rc == 1
    assert "[QUALIFICATION]" in capture.err.decode("utf-8")
