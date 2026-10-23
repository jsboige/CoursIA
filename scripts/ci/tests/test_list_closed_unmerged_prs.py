"""Tests de `scripts/ci/list_closed_unmerged_prs.py` (#22166).

Ce que le fichier prouve
------------------------
  1. Les cinq verdicts sont atteignables, et l'ordre d'evaluation est celui du
     contrat : un contenu sur `main` n'est jamais un accident, une fermeture
     expliquee n'est jamais un orphelin, `UNKNOWN` n'est jamais un vert.
  2. Le signal d'accident est le couple **force-push + fermeture du MEME acteur
     dans les 60 s** -- un force-push d'une autre lane ne suffit pas.
  3. `See #N` / `Part of #N` dans le body ne designent PAS un successeur : c'est
     le piege que #20374 porte lui-meme (`Part of #20316`).
  4. Le balayage complet fonctionne sur des dicts injectes (aucun reseau).
  5. **Controle positif sur le cas reel #20374** : il doit sortir en
     `ACCIDENTAL_EMPTY_CLOSE`. Le test est ignore si `gh` ou le depot ne sont
     pas disponibles, mais il ne se rabat jamais sur une fixture.
  6. **Controle negatif** : une PR fermee volontairement avec une raison doit
     sortir en `SUPERSEDED` (ou `INTEGRATED`).

Run: python -m pytest scripts/ci/tests/test_list_closed_unmerged_prs.py -q
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "list_closed_unmerged_prs.py"
_SPEC = importlib.util.spec_from_file_location("list_closed_unmerged_prs", _MODULE_PATH)
lcu = importlib.util.module_from_spec(_SPEC)
assert _SPEC and _SPEC.loader
_SPEC.loader.exec_module(lcu)

REPO = "jsboige/CoursIA"
NOW = datetime(2026, 10, 23, 12, 0, tzinfo=timezone.utc)


# --- 1. les cinq verdicts et l'ordre d'evaluation ---------------------------------

def test_integrated_wins_over_every_other_signal():
    v, _ = lcu.verdict_of(integrated=True, successor=1, force_push_to_close_s=5.0,
                          branch_present=True, content_lost=3)
    assert v == lcu.INTEGRATED


def test_successor_wins_over_the_accident_signature():
    v, d = lcu.verdict_of(integrated=False, successor=42, force_push_to_close_s=5.0,
                          branch_present=True, content_lost=3)
    assert v == lcu.SUPERSEDED and "#42" in d


def test_abandon_reason_wins_over_the_accident_signature():
    v, _ = lcu.verdict_of(integrated=False, abandon_reason=True,
                          force_push_to_close_s=5.0, branch_present=True, content_lost=3)
    assert v == lcu.SUPERSEDED


def test_accidental_is_the_force_push_signature():
    v, d = lcu.verdict_of(integrated=False, force_push_to_close_s=33.0,
                          branch_present=True, content_lost=11)
    assert v == lcu.ACCIDENTAL and "33 s" in d


def test_orphaned_needs_content_off_main_and_no_reason():
    v, _ = lcu.verdict_of(integrated=False, force_push_to_close_s=3600.0,
                          branch_present=True, content_lost=4)
    assert v == lcu.ORPHANED


def test_unknown_is_never_green():
    assert lcu.verdict_of(api_error=True)[0] == lcu.UNKNOWN
    assert lcu.verdict_of(integrated=None)[0] == lcu.UNKNOWN
    # branche supprimee + contenu non verifiable
    assert lcu.verdict_of(branch_present=False, content_lost=None)[0] == lcu.UNKNOWN


def test_branch_present_without_lost_content_is_integrated():
    assert lcu.verdict_of(integrated=False, branch_present=True, content_lost=0)[0] == lcu.INTEGRATED


# --- 2. le force-push doit venir du meme acteur -----------------------------------

def _ev(kind, ts, login="jsboige"):
    return {"event": kind, "created_at": ts, "actor": {"login": login}}


def test_force_push_of_the_closer_counts():
    events = [_ev("head_ref_force_pushed", "2026-10-12T10:19:41Z"),
              _ev("closed", "2026-10-12T10:20:14Z")]
    assert lcu.force_push_to_close_seconds(events, datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)) == 33.0


def test_force_push_of_another_actor_does_not_count():
    events = [_ev("head_ref_force_pushed", "2026-10-12T10:19:41Z", login="myia-po-2023"),
              _ev("closed", "2026-10-12T10:20:14Z", login="jsboige")]
    assert lcu.force_push_to_close_seconds(events, datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)) is None


def test_force_push_after_the_close_is_ignored():
    # #20374 porte un force-push a 10:20:15Z, une seconde APRES la fermeture :
    # c'est le vrai commit, pas la cause.
    events = [_ev("head_ref_force_pushed", "2026-10-12T10:20:15Z"),
              _ev("closed", "2026-10-12T10:20:14Z")]
    assert lcu.force_push_to_close_seconds(events, datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)) is None


def test_only_the_closest_force_push_is_reported():
    events = [_ev("head_ref_force_pushed", "2026-10-12T09:00:04Z"),
              _ev("head_ref_force_pushed", "2026-10-12T10:19:41Z"),
              _ev("closed", "2026-10-12T10:20:14Z")]
    assert lcu.force_push_to_close_seconds(events, datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)) == 33.0


# --- 3. successeur : formes explicites seulement ----------------------------------

CLOSED = datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)


def _c(body, ts="2026-10-12T10:20:00Z"):
    return {"body": body, "created_at": ts}


@pytest.mark.parametrize("body", [
    "Superseded by #20400",
    "superseded by #20400",
    "Remplacee par #20400",
    "closed in favor of #20400",
    "Doublon de #20400",
])
def test_explicit_successor_forms_are_recognised(body):
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[0] == 20400


@pytest.mark.parametrize("body", [
    "Part of #20316 · See #16231 (EPIC GT-03 split)",
    "See #16231",
    "Part of #20316",
])
def test_parent_references_are_not_successors(body):
    """Le piege exact de #20374 : son body cite son parent, pas un successeur."""
    assert lcu.closing_evidence(body, [], CLOSED)[0] is None


def test_abandon_reason_is_recognised():
    assert lcu.closing_evidence("", [_c("PR obsolete, sans objet")], CLOSED)[1] is True


def test_a_far_away_comment_does_not_close_the_case():
    # trois semaines avant la fermeture : ce commentaire parlait d'autre chose
    assert lcu.closing_evidence("", [_c("superseded by #1", "2026-09-20T10:00:00Z")], CLOSED)[0] is None


def test_bot_markers_are_not_abandon_reasons():
    bot = _c("<!-- BASE-NOT-MAIN:START --> ## Base != main (advisory, #10918) <!-- BASE-NOT-MAIN:END -->")
    assert lcu.closing_evidence("", [bot], CLOSED)[1] is False


# --- 4. balayage sur dicts injectes ------------------------------------------------

def _pr(number, branch, closed_at="2026-10-20T10:00:00Z", body="", base="main"):
    return {"number": number, "title": f"pr {number}", "body": body,
            "closed_at": closed_at, "merged_at": None, "html_url": f"https://x/{number}",
            "head": {"ref": branch}, "base": {"ref": base}}


def test_scan_aggregates_and_sorts_by_severity(monkeypatch):
    prs = [_pr(1, "gone"), _pr(2, "kept")]
    monkeypatch.setattr(lcu, "timeline", lambda repo, n: [])

    def fake_comments(repo, n):
        # PR #1 : une raison d'abandon dans un COMMENTAIRE de fermeture (le body
        # ne compte plus, cf fix). PR #2 : aucune raison -> orpheline.
        if n == 1:
            return [{"body": "PR obsolete, sans objet", "created_at": "2026-10-20T09:59:00Z"}]
        return []

    monkeypatch.setattr(lcu, "comments", fake_comments)
    monkeypatch.setattr(lcu, "content_state", lambda b, t, m: (False, 5))
    res = lcu.scan(REPO, 14, now=NOW, prs=prs, branches={"gone": "aaa", "kept": "bbb"})
    assert res["counts"][lcu.ORPHANED] == 1
    assert res["counts"][lcu.SUPERSEDED] == 1
    # ORPHANED est plus severe : il passe en tete du rapport
    assert [r["number"] for r in res["rows"]] == [2, 1]


def test_scan_reports_integrated_for_content_on_main(monkeypatch):
    monkeypatch.setattr(lcu, "timeline", lambda repo, n: [])
    monkeypatch.setattr(lcu, "comments", lambda repo, n: [])
    monkeypatch.setattr(lcu, "content_state", lambda b, t, m: (True, 0))
    res = lcu.scan(REPO, 14, now=NOW, prs=[_pr(9, "b")], branches={"b": "ccc"})
    assert res["counts"][lcu.INTEGRATED] == 1


def test_scan_marks_unknown_when_timeline_fails(monkeypatch):
    def boom(repo, n):
        raise RuntimeError("502")
    monkeypatch.setattr(lcu, "timeline", boom)
    monkeypatch.setattr(lcu, "comments", lambda repo, n: [])
    res = lcu.scan(REPO, 14, now=NOW, prs=[_pr(3, "b")], branches={"b": "ddd"})
    assert res["counts"][lcu.UNKNOWN] == 1


def test_render_carries_markers_and_counts():
    res = {"repo": REPO, "window_days": 14, "since": "2026-10-09T12:00:00+00:00",
           "counts": {v: 0 for v in lcu.VERDICTS},
           "rows": [{"number": 20374, "branch": "feature/x", "base": "feature/y",
                     "closed_at": "2026-10-12T10:20:14Z", "url": "https://x/20374",
                     "verdict": lcu.ACCIDENTAL, "detail": "fermee 33 s apres un force-push"}]}
    out = lcu.render(res)
    assert lcu.MARKER_START in out and lcu.MARKER_END in out
    assert "#20374" in out


# --- 4b. upsert marker-guarde ----------------------------------------------------

def _result_with(pr_number, verdict):
    return {"repo": REPO, "window_days": 14, "since": "2026-10-09T12:00:00+00:00",
            "counts": {v: 0 for v in lcu.VERDICTS},
            "rows": [{"number": pr_number, "branch": "b", "base": "main",
                      "closed_at": "2026-10-20T10:00:00Z", "url": "u",
                      "verdict": verdict, "detail": "d"}]}


def test_upsert_appends_when_no_block():
    out = lcu.upsert_report(22166, _result_with(20374, lcu.ACCIDENTAL), "Intro du body.")
    assert lcu.MARKER_START in out and lcu.MARKER_END in out
    assert "Intro du body." in out
    assert out.count(lcu.MARKER_START) == 1


def test_upsert_replaces_existing_block_without_duplicating():
    current = "Intro.\n\n" + lcu.render(_result_with(1, lcu.ORPHANED)) + "\n\nSuite."
    out = lcu.upsert_report(22166, _result_with(2, lcu.ORPHANED), current)
    assert out.count(lcu.MARKER_START) == 1
    assert "Intro." in out and "Suite." in out
    assert "#2" in out and "#1" not in out.split(lcu.MARKER_START)[1]  # l'ancien bloc est remplace


# --- 5. controle POSITIF sur le cas reel #20374 ------------------------------------

def _gh_ready() -> bool:
    try:
        proc = subprocess.run(["gh", "auth", "status"], capture_output=True, text=True,
                              check=False, encoding="utf-8", errors="replace")
        return proc.returncode == 0
    except (OSError, FileNotFoundError):
        return False


needs_gh = pytest.mark.skipif(not _gh_ready(), reason="gh absent ou non authentifie")


@needs_gh
def test_real_20374_is_accidental_empty_close():
    """Controle positif exige par #22166 : le cas fondateur doit sortir ACCIDENTAL."""
    pr = json.loads(subprocess.run(
        ["gh", "api", f"repos/{REPO}/pulls/20374"],
        capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace").stdout)
    branches = lcu.obs.remote_branches(REPO)
    assert pr["head"]["ref"] in branches, "la branche de #20374 doit encore exister"
    row = lcu.evaluate_pr(pr, REPO, "origin/main", branches)
    assert row["verdict"] == lcu.ACCIDENTAL, row
    assert row["force_push_to_close_s"] is not None and row["force_push_to_close_s"] <= 60.0
    assert row["files_lost"] and row["files_lost"] > 0


# --- 6. controle NEGATIF ------------------------------------------------------------

@needs_gh
def test_a_real_deliberate_close_is_not_orphaned():
    """Controle negatif : sur la fenetre reelle, aucune fermeture expliquee ne
    doit etre classee ORPHANED ni ACCIDENTAL."""
    prs = lcu.closed_unmerged(REPO, datetime(2026, 10, 9, tzinfo=timezone.utc))
    if not prs:
        pytest.skip("aucune PR fermee sans merge sur la fenetre")
    branches = lcu.obs.remote_branches(REPO)
    rows = [lcu.evaluate_pr(pr, REPO, "origin/main", branches) for pr in prs]
    for row in rows:
        if "raison d'abandon" in row.get("detail", "") or "successeur nomme" in row.get("detail", ""):
            assert row["verdict"] == lcu.SUPERSEDED, row
