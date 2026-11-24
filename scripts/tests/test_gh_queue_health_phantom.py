#!/usr/bin/env python3
"""La classe « phantom non annulable » de `scripts/ci/gh_queue_health.py`.

Un run en file qui n'a jamais ete admis a un runner ne peut PAS etre
annule : l'API refuse en 409 « has not been queued yet », sur `cancel` comme
sur `force-cancel`.

Mesure du 14/11 sur `jsboige/CoursIA` : 91 runs de plus de 24 h (76
`issue_comment` + 15 `pull_request_review`), tous sans job, tous refuses en
409 sur les deux endpoints. Le leveur « annuler les runs qui paddingent la
file » n'existe donc pas.

Ce que ces tests tiennent :

1. **Controle positif** -- un 409 sur `cancel` EST la classe phantom, et le
   verdict dit que le run n'est PAS annulable (etat permanent, pas une
   erreur a retenter) ;
2. **Controle positif jumeau** -- le meme refus sur `force-cancel` tombe dans
   la meme classe : le refus n'est pas un artefact du premier endpoint ;
3. **Controle negatif** -- une annulation ACCEPTEE reste une annulation, et
   un echec qui n'est pas le refus reste une erreur ordinaire ;
4. **Le rapport** separe les fantomes des runs vivants, et ne recommande
   plus `--apply` pour une classe que l'API refuse.

Run: python -m pytest scripts/tests/test_gh_queue_health_phantom.py
"""
from __future__ import annotations

import datetime as dt
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent.parent / "ci" / "gh_queue_health.py"

#: Libelle REEL mesure en direct le 14/11 (`gh api -X POST .../cancel`) :
#: "gh: Cannot cancel a workflow run that has not been queued yet. (HTTP 409)"
#: -- et le point-virgule avant le code HTTP fait partie du message.
CANCEL_REFUSAL = (
    "gh: Cannot cancel a workflow run that has not been queued yet. (HTTP 409)"
)
#: L'endpoint `force-cancel` repond le MEME libelle que `cancel` : c'est
#: mesure, pas suppose (le verbe « force » n'apparait pas dans le message).
FORCE_CANCEL_REFUSAL = CANCEL_REFUSAL


def _mod():
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433 (import after path insert)
    return mod


class _FakeProc:
    """A `subprocess.run` result shaped like gh's."""

    def __init__(self, returncode: int, stdout: str = "", stderr: str = ""):
        self.returncode, self.stdout, self.stderr = returncode, stdout, stderr


def _fake_gh(refusal: str):
    """A `gh api` that always answers the given refusal."""
    def fake_run(cmd, **kwargs):
        return _FakeProc(1, stderr=refusal)
    return fake_run


# ---------------------------------------------------------------------------
# 1. la reconnaissance du refus
# ---------------------------------------------------------------------------


def test_le_refus_409_est_reconnu_par_la_phrase() -> None:
    """The marker is the PHRASE, not the HTTP code.

    `cancel` and `force-cancel` answer the same refusal with a different
    verb; a 409 of another nature (lock, conflict) does not carry it.
    """
    mod = _mod()

    assert mod.is_not_queued_refusal(CANCEL_REFUSAL)
    assert mod.is_not_queued_refusal(FORCE_CANCEL_REFUSAL)
    assert not mod.is_not_queued_refusal("gh: HTTP 409 (HTTP 409)")
    assert not mod.is_not_queued_refusal("")
    assert not mod.is_not_queued_refusal(None)


# ---------------------------------------------------------------------------
# 2. controles positif et negatif sur le VERDICT
# ---------------------------------------------------------------------------


def test_le_409_sur_cancel_est_classe_fantome_non_annulable(monkeypatch) -> None:
    """POSITIVE CONTROL: the 409 on `cancel` is the phantom class.

    The verdict says the run is NOT cancellable -- that is the whole point:
    the refusal is a permanent state, not an error to retry.
    """
    mod = _mod()

    monkeypatch.setattr(mod.subprocess, "run", _fake_gh(CANCEL_REFUSAL))
    verdict = mod.cancel_run("o/r", 42)
    assert verdict["class"] == "phantom"
    assert verdict["status"] == mod.PHANTOM_REASON
    assert verdict["cancellable"] is False
    assert verdict["ok"] is False
    assert "has not been queued yet" in verdict["error"]


def test_le_409_sur_force_cancel_est_classe_fantome_non_annulable(monkeypatch) -> None:
    """POSITIVE CONTROL: the 409 on `force-cancel` is the same class.

    The second endpoint proves the refusal is not an artefact of the first
    one -- the run is not in the runner queue at all.
    """
    mod = _mod()

    monkeypatch.setattr(mod.subprocess, "run", _fake_gh(FORCE_CANCEL_REFUSAL))
    verdict = mod.force_cancel_run("o/r", 42)
    assert verdict["class"] == "phantom"
    assert verdict["status"] == mod.PHANTOM_REASON
    assert verdict["cancellable"] is False


def test_force_cancel_appelle_le_bon_endpoint(monkeypatch) -> None:
    """`force=True` hits `force-cancel`, `force=False` hits `cancel`."""
    mod = _mod()

    seen: list[str] = []

    def fake_run(cmd, **kwargs):
        seen.append(next(part for part in cmd if part.startswith("repos/")))
        return _FakeProc(0)

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    mod.cancel_run("o/r", 1)
    mod.cancel_run("o/r", 1, force=True)
    assert seen == [
        "repos/o/r/actions/runs/1/cancel",
        "repos/o/r/actions/runs/1/force-cancel",
    ]


def test_une_annulation_acceptee_nest_pas_un_fantome(monkeypatch) -> None:
    """NEGATIVE CONTROL: an accepted cancellation stays a cancellation.

    The class must not swallow the ordinary success: a run the API accepted
    is cancelled, and it is still cancellable.
    """
    mod = _mod()

    monkeypatch.setattr(mod.subprocess, "run", lambda cmd, **kw: _FakeProc(0))
    verdict = mod.cancel_run("o/r", 42)
    assert verdict["ok"] is True
    assert verdict["class"] == "cancelled"
    assert verdict["status"] == "cancelled"
    assert verdict["cancellable"] is True


def test_un_echec_autre_que_le_409_reste_une_erreur_ordinaire(monkeypatch) -> None:
    """A failure that is not the refusal stays an ordinary error.

    Only the refusal is permanent; a 500 or a lock error may be retried.
    """
    mod = _mod()

    monkeypatch.setattr(
        mod.subprocess, "run",
        lambda cmd, **kw: _FakeProc(1, stderr="gh: Internal Server Error (HTTP 500)"))
    verdict = mod.cancel_run("o/r", 42)
    assert verdict["class"] == "error"
    assert verdict["cancellable"] is True
    assert verdict["status"].startswith("rc=")


# ---------------------------------------------------------------------------
# 3. la classification : le fantome n'est pas un run vivant
# ---------------------------------------------------------------------------


def test_le_phantom_est_hors_du_seau_des_runs_vivants() -> None:
    """The classified phantom is a ghost, not a live run.

    A run the API refuses to cancel is dead padding: it must not inflate
    the live queue, which is the drift signal the watch reads.
    """
    mod = _mod()

    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    runs = [
        {"id": 1, "created_at": "2026-11-11T20:54:21Z", "event": "issue_comment"},
        {"id": 2, "created_at": "2026-11-14T14:00:00Z", "event": "pull_request"},
    ]
    out = mod.classify_runs(runs, cutoff, phantom_non_annulable={1})
    reasons = {g["id"]: g["reason"] for g in out["ghosts"]}
    assert reasons == {1: mod.PHANTOM_REASON}
    assert [entry["id"] for entry in out["live"]] == [2]


def test_la_preuve_de_l_api_prime_sur_la_detection_structurelle() -> None:
    """A run proven non-annulable carries the phantom reason, not `no-job`.

    The API answer is the stronger evidence: it names the exact class.
    """
    mod = _mod()

    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    runs = [{"id": 1, "created_at": "2026-11-11T20:54:21Z", "event": "issue_comment"}]
    out = mod.classify_runs(runs, cutoff, no_job={1}, phantom_non_annulable={1})
    assert out["ghosts"][0]["reason"] == mod.PHANTOM_REASON


# ---------------------------------------------------------------------------
# 4. le rapport : separation et suppression de la proposition `--apply`
# ---------------------------------------------------------------------------


def _no_job_fixture(monkeypatch) -> None:
    """Three queued runs: two dead ones (no job), one really waiting."""
    mod = _mod()

    runs = [
        {"id": 11, "name": "Variation Tag Guard", "event": "issue_comment",
         "created_at": "2026-11-11T20:54:21Z", "html_url": "https://gh/11"},
        {"id": 22, "name": "perimeter-review-guard", "event": "pull_request_review",
         "created_at": "2026-11-11T20:54:22Z", "html_url": "https://gh/22"},
        {"id": 33, "name": "PR gate", "event": "pull_request",
         "created_at": "2026-11-14T14:00:00Z", "head_branch": "feature/x",
         "html_url": "https://gh/33"},
    ]
    monkeypatch.setattr(mod, "fetch_queued_runs", lambda repo: runs)
    monkeypatch.setattr(mod, "fetch_pr_states", lambda repo, branches: {})
    monkeypatch.setattr(
        mod, "detect_no_job_runs",
        lambda *a, **k: {"ids": {11, 22}, "checked": 2, "probed": 2, "unknown": 0})


def test_le_rapport_separe_les_fantomes_des_runs_vivants(monkeypatch, capsys) -> None:
    """The report separates the dead padding from the live runs.

    The 91 runs of the measurement occupy queue slots while producing
    nothing; the report must show them apart from the runs that are really
    waiting for a runner.
    """
    mod = _mod()

    _no_job_fixture(monkeypatch)
    mod.main(["--repo", "o/r", "--cancel", "no-job"])
    body = json.loads(capsys.readouterr().out)

    assert body["no_job"]["phantoms"] == [11, 22]
    assert body["no_job"]["cancellable"] == []
    assert body["no_job"]["apply_recommended"] is False
    assert "409" in body["no_job"]["apply_refusal"]

    ghost_ids = {g["id"] for g in body["ghosts"]}
    live_ids = {r["id"] for r in body["live"]}
    assert live_ids == {33}
    assert ghost_ids == {11, 22}


def test_le_rapport_ne_recommande_pas_apply_pour_les_fantomes(monkeypatch, capsys) -> None:
    """`--apply` is not recommended for a class the API refuses to cancel.

    The applied pass PROVES the refusal; it does not repair anything, so
    the report must not present it as a repair lever.
    """
    mod = _mod()

    _no_job_fixture(monkeypatch)
    monkeypatch.setattr(
        mod, "verify_no_job_before_cancel",
        lambda repo, run_ids, max_workers=8: (list(run_ids), []))
    monkeypatch.setattr(
        mod, "cancel_runs_parallel",
        lambda repo, run_ids, max_workers=8, force=False: [
            {"id": rid, "ok": False, "status": mod.PHANTOM_REASON,
             "class": "phantom", "cancellable": False,
             "error": "Cannot cancel a workflow run that has not been queued yet"}
            for rid in run_ids
        ])
    mod.main(["--repo", "o/r", "--cancel", "no-job", "--apply"])
    body = json.loads(capsys.readouterr().out)

    assert body["no_job"]["phantoms"] == [11, 22]
    assert body["no_job"]["cancelled"] == []
    assert body["no_job"]["apply_recommended"] is False
    # The proven class wins over the structural one.
    reasons = {g["id"]: g["reason"] for g in body["ghosts"]}
    assert reasons == {11: mod.PHANTOM_REASON, 22: mod.PHANTOM_REASON}


def test_une_annulation_acceptee_est_classee_annulee(monkeypatch, capsys) -> None:
    """NEGATIVE CONTROL at the report level: an accepted cancel is cancelled.

    The phantom bucket must not swallow the ordinary success.
    """
    mod = _mod()

    _no_job_fixture(monkeypatch)
    monkeypatch.setattr(
        mod, "verify_no_job_before_cancel",
        lambda repo, run_ids, max_workers=8: (list(run_ids), []))
    monkeypatch.setattr(
        mod, "cancel_runs_parallel",
        lambda repo, run_ids, max_workers=8, force=False: [
            {"id": rid, "ok": True, "status": "cancelled", "class": "cancelled",
             "cancellable": True}
            for rid in run_ids
        ])
    mod.main(["--repo", "o/r", "--cancel", "no-job", "--apply"])
    body = json.loads(capsys.readouterr().out)

    assert body["no_job"]["cancelled"] == [11, 22]
    assert body["no_job"]["phantoms"] == []
