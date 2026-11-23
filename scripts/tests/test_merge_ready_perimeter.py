"""Contrat de la voie L1 de #28131 : le merge n'attend pas la file du garde.

Le garde de perimetre heberge (`perimeter review guard (#11268)`) peut rester
en file 9 a 11 min apres un APPROVE (mesure du 22/11). Quand son run n'a
aucune jambe TERMINEE sur la tete evaluee, `merge_ready` mesure le perimetre
LOCALEMENT, avec le meme organe, et adopte son verdict.

Ces tests sont le CONTRAT de ce comportement :
  * un verdict local OK ne bloque pas (et le dit dans le detail) ;
  * un verdict local FAIL bloque ;
  * une mesure IMPOSSIBLE bloque (fail-closed) ;
  * une tete deplacee entre la lecture et la mesure bloque.

Temoin negatif : sans la branche L1, le premier test echoue (la PR reste
bloquee sur `no-completed-leg`).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "coordination"))
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import merge_ready as mr  # noqa: E402
import merge_ready_perimeter as perimeter  # noqa: E402

HEAD = "d3dd98736d93aa5357205dc574f5aba030f8765c"
PR = 26381
PERIM = perimeter.PERIMETER_CHECK_NAME


class FakeRunner:
    """Runner de test : repond aux trois lectures du chemin L1."""

    def __init__(self, *, organ_rc=0, organ_out="VERDICT: OK", sha=HEAD,
                 head_rc=0):
        self.organ_rc = organ_rc
        self.organ_out = organ_out
        self.sha = sha
        self.head_rc = head_rc
        self.calls: list[list[str]] = []

    def run(self, cmd, env=None):
        self.calls.append(list(cmd))
        joined = " ".join(cmd)
        if "check-runs" in joined:
            return mr.RunResult(0, self._legs(), "")
        if "/pulls/" in joined and "--jq" in joined:
            if self.head_rc != 0:
                return mr.RunResult(self.head_rc, "", "head illisible")
            return mr.RunResult(0, self.sha + "\n", "")
        if any("check_pr_perimeter.py" in part for part in cmd):
            return mr.RunResult(self.organ_rc, self.organ_out, "")
        return mr.RunResult(0, "", "")

    def sleep(self, seconds):  # pragma: no cover - jamais appele ici
        return None

    @staticmethod
    def _legs() -> str:
        rows = [
            {"name": "PR gate", "conclusion": "success",
             "status": "completed", "started_at": "2026-11-22T21:00:00Z",
             "id": 1},
            # Le garde heberge : EN FILE, aucune jambe terminee sur cette tete.
            {"name": PERIM, "conclusion": None, "status": "queued",
             "started_at": "2026-11-22T21:00:30Z", "id": 2},
        ]
        return "\n".join(json.dumps(r) for r in rows) + "\n"


def _reason(runner: FakeRunner) -> tuple[str | None, str]:
    return mr.unstable_state_reason(runner, PR, HEAD, {"GH_TOKEN": "x"})


def test_un_verdict_local_ok_ne_bloque_pas_le_merge():
    """La PR passe : le merge n'attend pas la file du garde heberge."""
    runner = FakeRunner(organ_rc=0, organ_out="VERDICT: OK")
    reason, detail = _reason(runner)
    assert reason is None, f"la PR devrait passer, raison={reason}"
    assert "perimeter-local" in detail
    assert any("check_pr_perimeter.py" in " ".join(c) for c in runner.calls), (
        "l'organe de perimetre doit etre appele -- pas une recopie de grammaire"
    )


def test_un_verdict_local_fail_bloque_le_merge():
    """Un verdict local BLOQUANT bloque, comme un verdict heberge."""
    runner = FakeRunner(organ_rc=1, organ_out="VERDICT: FAIL\n  !! perimetre faux")
    reason, detail = _reason(runner)
    assert reason is not None
    assert PERIM in reason
    assert "verdict-local:FAIL" in reason
    assert "verdict-local:FAIL" in detail


def test_une_mesure_impossible_bloque_le_merge():
    """Fail-closed : une sortie illisible n'est PAS un verdict favorable."""
    runner = FakeRunner(organ_rc=2, organ_out="Traceback (most recent call last)")
    reason, _ = _reason(runner)
    assert reason is not None
    assert PERIM in reason
    assert "illisible" in reason


def test_une_tete_deplacee_bloque_le_merge():
    """La mesure doit porter sur la tete qui va etre fusionnee."""
    runner = FakeRunner(sha="0" * 40)
    reason, detail = _reason(runner)
    assert reason is not None
    assert "tete-deplacee" in reason
    assert "tete-deplacee" in detail


def test_une_tete_inconnue_bloque_le_merge():
    """Lecture de tete impossible : fail-closed."""
    runner = FakeRunner(head_rc=1)
    reason, detail = _reason(runner)
    assert reason is not None
    assert "tete-inconnue" in reason
    assert "tete-inconnue" in detail


def test_le_nom_du_check_est_celui_du_workflow_heberge():
    """Le nom doit rester celui que publie le workflow (surface officielle)."""
    workflow = (
        REPO_ROOT / ".github" / "workflows" / "perimeter-review-guard.yml"
    ).read_text(encoding="utf-8")
    assert PERIM in workflow
    assert "ubuntu-latest" in workflow, "le garde reste sur l'heberge"


@pytest.mark.parametrize("blocking,detail", [
    (False, "verdict-local:OK"),
    (True, "verdict-local:FAIL"),
    (None, "verdict-local:illisible"),
])
def test_le_verdict_local_est_binaire_ou_illisible(blocking, detail):
    """Trois etats, jamais quatre : la mesure est faite, ou elle ne l'est pas."""
    assert isinstance(perimeter.LocalVerdict(blocking, detail).blocking, bool | type(None))
    assert perimeter.LocalVerdict(blocking, detail).detail == detail
