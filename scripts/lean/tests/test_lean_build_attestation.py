"""Tests du format canonique d'attestation Lean (module lean_build_attestation).

Le champ etiquete `timeout: defer` (#27516 volet 3) distingue une attestation
posee sur un build **tombé en timeout** (budget de temps, deferral CI) d'une
attestation sur un build **réussi** : la distinction porte dans le CHAMP,
jamais dans la prose. Le module est partagé entre l'organe qui ECRIT
(`attest_local_build.py`) et la garde qui LIT (`merge_ready.py`) : un round-
trip render -> parse qui perd le champ ferait diverger les deux cotes en
silence.

Aucun lake, aucun reseau, aucune machine.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import lean_build_attestation  # noqa: E402
from lean_build_attestation import (  # noqa: E402
    ATTESTATION_TAG,
    parse_attestation,
    render_attestation,
)

SHA = "3f2a1b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a"


def test_render_timeout_emet_le_champ_defer():
    body = render_attestation(sha=SHA, lakes=["knot"], jobs=4, timeout=True)
    assert "timeout: defer" in body


def test_render_sans_timeout_n_emet_pas_le_champ():
    body = render_attestation(sha=SHA, lakes=["knot"], jobs=4)
    assert "timeout:" not in body


def test_parse_round_trip_conserve_le_timeout():
    body = render_attestation(sha=SHA, lakes=["knot"], jobs=4, timeout=True)
    parsed = parse_attestation(body)
    assert parsed is not None
    assert parsed["sha"] == SHA
    assert parsed["timeout"] is True


def test_parse_sans_champ_donne_timeout_faux():
    body = render_attestation(sha=SHA, lakes=["knot"], jobs=4)
    parsed = parse_attestation(body)
    assert parsed is not None
    assert parsed["timeout"] is False


def test_parse_lit_le_champ_timeout_manuel():
    body = (
        "\n".join(
            [ATTESTATION_TAG, "", f"tete: {SHA}", "lakes: knot", "jobs: 2",
             "timeout: defer"]
        )
        + "\n"
    )
    parsed = parse_attestation(body)
    assert parsed is not None
    assert parsed["timeout"] is True


def test_le_mot_timeout_en_prose_n_est_pas_un_champ():
    # Une attestation qui cite le mot « timeout » en prose (sans le champ
    # etiquete en debut de ligne) ne doit PAS etre lue comme un timeout :
    # seul le champ etiquete fait foi.
    body = (
        "\n".join(
            [ATTESTATION_TAG, "", f"tete: {SHA}", "lakes: knot",
             "le build a ete tue en timeout par le minuteur"]
        )
        + "\n"
    )
    parsed = parse_attestation(body)
    assert parsed is not None
    assert parsed["timeout"] is False
