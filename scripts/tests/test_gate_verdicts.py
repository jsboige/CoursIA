"""Tests de `scripts/ci/gate_verdicts.py` -- l'organe des verdicts d'etat.

#26564 (residu 1 de #26551) : le gate `PR gate` emet `INCONCLUSIVE -- ...`
quand le quota d'installation GitHub App est epuise. Ce verdict dit que l'etat
des checks est **INCONNU, pas faux** : il ne nomme aucun organe, et il ne se
repare pas dans le diff de la PR.

Comme le DWELL (#15910), c'est un ETAT : le module le rend lisible, et ne
fabrique aucune cause. Le format de chaque message appartient a son emetteur
(`merge_dwell`, `pr_gate`) -- le module ne fait que le lire.
"""

from __future__ import annotations

import json
import pathlib
import sys

import pytest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "ci"))

import gate_verdicts as gv  # noqa: E402

INCONCLUSIVE_ANN = (
    "[pr-gate] INCONCLUSIVE -- quota d'installation GitHub App epuisee : "
    "l'etat des checks est INCONNU, pas faux. REJOUABLE : relancer la jambe "
    "(`gh run rerun <run_id> --job <job_id>`) apres le reset horaire, ou "
    "attendre le balayage `pr-gate-stale-sweep`. Source : HTTP 403 "
    "installation quota exhausted"
)
FAIL_ANN = "[pr-gate] FAIL -- failing checks: perimeter"


class _FakeCompleted:
    def __init__(self, stdout):
        self.stdout = stdout


def _patch_gh(monkeypatch, messages):
    def fake_run(cmd, **kwargs):
        return _FakeCompleted(json.dumps([{"message": m} for m in messages]))
    monkeypatch.setattr(gv.subprocess, "run", fake_run)


def test_optional_parser_returns_none_for_a_missing_module():
    """Un organe absent rend le verdict ILLISIBLE, jamais une exception."""
    assert gv.optional_parser("module_qui_nexiste_pas", "parse", pathlib.Path(".")) is None


def test_verdict_from_annotations_finds_the_first_verdict(monkeypatch):
    """Le verdict porte est rendu tel quel, sans interpretation."""
    parser = lambda message: {"detail": message} if message.startswith("X") else None
    assert gv.verdict_from_annotations([{"message": "X1"}, {"message": "X2"}], parser) == {
        "detail": "X1"}
    assert gv.verdict_from_annotations([{"message": "autre"}], parser) is None
    # Annotations illisibles ou parser absent : None (fail-closed de l'appelant).
    assert gv.verdict_from_annotations(None, parser) is None
    assert gv.verdict_from_annotations([{"message": "X"}], None) is None


def test_unknown_verdict_reads_the_inconclusive_annotation(monkeypatch):
    """Le message REEL du gate rend l'etat lisible, avec son motif."""
    _patch_gh(monkeypatch, [INCONCLUSIVE_ANN])
    verdict = gv.unknown_verdict(123)
    assert verdict is not None
    assert verdict["state"] == "inconclusive"
    assert verdict["kind"] == "quota-installation"
    assert "quota d'installation" in verdict["detail"]


def test_unknown_verdict_control_negative_fail_and_unreadable(monkeypatch):
    """Controle NEGATIF : un FAIL nomme et une panne ne sont pas un etat inconnu.

    Sans ce controle, un detecteur qui rendrait un verdict sur n'importe quelle
    annotation ferait passer le test precedent avec un motif faux -- et
    l'annulation de cause emporterait les vrais rouges avec elle.
    """
    _patch_gh(monkeypatch, [FAIL_ANN])
    assert gv.unknown_verdict(1) is None

    def _raise_gh(cmd, **kwargs):
        raise OSError("gh indisponible")

    monkeypatch.setattr(gv.subprocess, "run", _raise_gh)
    assert gv.unknown_verdict(2) is None


def test_read_annotations_uses_the_cache_callbacks(monkeypatch):
    """Le cache du caller evite l'appel reseau repete."""
    _patch_gh(monkeypatch, [INCONCLUSIVE_ANN])
    calls = []

    def _read(run_id):
        calls.append(run_id)
        return None

    stored = {}

    def _store(run_id, annotations):
        stored[run_id] = annotations

    annotations = gv.read_annotations(7, _read, _store)
    assert [a["message"] for a in annotations] == [INCONCLUSIVE_ANN]
    assert calls == [7]
    assert 7 in stored

    # Cache_hit : plus aucun appel reseau.
    def _read_hit(run_id):
        return [{"message": "cache"}]

    calls.clear()
    annotations = gv.read_annotations(7, _read_hit, _store)
    assert annotations == [{"message": "cache"}]
    assert calls == []


def test_print_inconclusive_waiting_says_the_only_gesture_is_the_replay(capsys):
    """La sortie humaine doit porter le geste : rejouer, ne pas pousser.

    Un push ne rejoue pas un quota epuise : il consomme un cycle et laisse le
    rouge en place.
    """
    gv.print_inconclusive_waiting([
        {"number": 26551, "check": "PR gate", "detail": "quota epuise"}])
    out = capsys.readouterr().out
    assert "#26551" in out
    assert "INCONNU" in out
    assert "gh run rerun" in out
    assert "NE PAS pousser" in out
    # Silence total quand il n'y a rien : pas de section vide a lire.
    gv.print_inconclusive_waiting([])
    assert capsys.readouterr().out == ""


if __name__ == "__main__":  # pragma: no cover
    pytest.main([__file__])
