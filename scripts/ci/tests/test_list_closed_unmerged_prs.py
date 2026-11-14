"""Tests de `scripts/ci/list_closed_unmerged_prs.py` (#22166).

Ce que le fichier prouve
------------------------
  1. Les six verdicts sont atteignables, et l'ordre d'evaluation est celui du
     contrat : un contenu sur `main` n'est jamais un accident, une fermeture
     expliquee n'est jamais un orphelin, `UNKNOWN` n'est jamais un vert.
  2. Le signal d'accident est le couple **force-push + fermeture du MEME acteur
     dans les 60 s** -- un force-push d'une autre lane ne suffit pas.
  3. `See #N` / `Part of #N` dans le body ne designent PAS un successeur : c'est
     le piege que #20374 porte lui-meme (`Part of #20316`).
  4. Le balayage complet fonctionne sur des dicts injectes (aucun reseau).
  5. **Controle positif sur le cas reel #20374** : il doit sortir en
     `ACCIDENTAL_EMPTY_CLOSE`.
  6. **Controle negatif** : une PR fermee volontairement avec une raison doit
     sortir en `SUPERSEDED` (ou `INTEGRATED`).
  7. **Controles reels hermetiques** (#24676) : les controles `test_real_*` lisent
     un snapshot versionne (`fixtures/list_closed_unmerged_prs_snapshot.json`)
     au lieu du depot vivant ; ils tournent sans reseau et ne sont jamais `skip`.

Run: python -m pytest scripts/ci/tests/test_list_closed_unmerged_prs.py -q
(hors reseau : `GH_TOKEN=invalid HTTPS_PROXY=http://127.0.0.1:9 python -m pytest ...`)
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone
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


# --- 2b. pagination : arret sur updated_at, pas sur closed_at (grain 1) -----------

def _p(closed, updated, number=1, merged=False):
    return {"number": number, "closed_at": closed, "updated_at": updated,
            "merged_at": "2026-10-01T00:00:00Z" if merged else None,
            "head": {"ref": f"b{number}"}, "base": {"ref": "main"},
            "title": f"pr {number}", "body": "", "html_url": "u"}


def test_pagination_stops_on_updated_at_not_closed_at():
    """Une PR fermee il y a 40 j mais mise a jour aujourd'hui reste en page 1 :
    couper sur son closed_at perdrait les orphelines de la page 2 en silence."""
    since = datetime(2026, 10, 9, tzinfo=timezone.utc)
    # page 1 : 100 elements, dont une vieille fermeture commentee aujourd'hui.
    # Le DERNIER element a un updated_at recent -> la page 2 doit etre lue.
    p1 = [_p("2026-08-01T00:00:00Z", "2026-10-23T10:00:00Z", number=1)]  # fermee 40+ j, maj aujourd'hui
    p1 += [_p("2026-10-01T00:00:00Z", "2026-10-01T00:00:00Z", number=i, merged=True) for i in range(2, 100)]
    p1.append(_p("2026-10-01T00:00:00Z", "2026-10-23T09:00:00Z", number=100, merged=True))
    # page 2 : une fermeture DANS la fenetre, seule orpheline reelle
    p2 = [_p("2026-10-20T10:00:00Z", "2026-10-20T10:00:00Z", number=200)]
    pages = {1: p1, 2: p2}
    seen = []

    def fetch(n):
        seen.append(n)
        return pages.get(n, [])

    out = lcu.closed_unmerged(REPO, since, fetch_page=fetch)
    assert seen == [1, 2], "la page 2 doit etre lue"
    assert [pr["number"] for pr in out] == [200]


def test_pagination_stops_when_last_updated_is_older_than_the_window():
    since = datetime(2026, 10, 9, tzinfo=timezone.utc)
    p1 = [_p("2026-09-01T00:00:00Z", "2026-09-01T00:00:00Z", number=i, merged=True) for i in range(1, 100)]
    p1.append(_p("2026-09-02T00:00:00Z", "2026-09-02T00:00:00Z", number=100, merged=True))
    seen = []

    def fetch(n):
        seen.append(n)
        return {1: p1}.get(n, [])

    out = lcu.closed_unmerged(REPO, since, fetch_page=fetch)
    assert seen == [1] and out == []


# --- 2c. pas d'evenement closed = pas de signature (grain 2) -----------------------

def test_no_closed_event_yields_no_accident_signature():
    events = [_ev("head_ref_force_pushed", "2026-10-12T10:19:41Z")]
    assert lcu.force_push_to_close_seconds(
        events, datetime(2026, 10, 12, 10, 20, 14, tzinfo=timezone.utc)) is None


def test_no_closed_event_falls_back_to_orphaned():
    v, _ = lcu.verdict_of(integrated=False, force_push_to_close_s=None,
                          branch_present=True, content_lost=3)
    assert v == lcu.ORPHANED


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


# --- vocabulaire des fournees (Q162, 03/11) -- instance #24196 -----------------------

@pytest.mark.parametrize("body,expected", [
    # verbatim du commentaire de fermeture de #24196 (03:16:42Z)
    ("Contenu fondu en fournee dans #24354 (contre-audit GameTheory, concern #24280) "
     "-- le commit est preserve par cherry-pick, rien n'est reecrit. "
     "Cette PR se ferme vers la fournee.", 24354),
    # meme forme, avec l'accent
    ("Contenu fondu en fournée dans #24354", 24354),
    # verbatim du second commentaire de fermeture de #24196 (04:21:36Z)
    ("[REPLIÉE] Repliée en fournée dans la PR #24361 "
     "(classe contre-audit GameTheory, mandat user 02/11 "
     "« thin-prs-go-out-in-class-batches »).", 24361),
    # meme forme, sans accents
    ("[REPLIE] Repliee en fournee dans la PR #24361", 24361),
    # sans la mention « la PR »
    ("Repliee en fournee dans #24361", 24361),
    ("Repliée en fournée dans #24361", 24361),
    # la forme anglaise
    ("folded into #24354", 24354),
    ("Folded into #24354", 24354),
])
def test_fournee_vocabulary_names_a_successor(body, expected):
    """Le vocabulaire des fournees nomme un successeur.

    Sans ces formes, une PR repliee proprement sortait ``ORPHANED_CONTENT``
    (« aucune raison de fermeture nommee ») alors que ses commentaires
    nommaient le successeur -- instance mesuree : #24196.
    """
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[0] == expected


@pytest.mark.parametrize("body", [
    "Contenu fondu en fournee dans le batch de relecture de la semaine",
    "Le contenu a fondu dans la fournee, sans PR nommee",
    "Repliee en fournee, a confirmer",
])
def test_fournee_without_a_number_is_not_a_successor(body):
    """Un vocabulaire de fournee sans numero ne nomme rien : pas de successeur."""
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[0] is None


# --- vocabulaire elargi (dispatch du coordinateur, 14/11) ----------------------
#
# Trois formes de fermeture nommee ne etaient pas reconnues : « superseded
# par », « repliee dans », « incluse dans #N ». Elles sortaient de l'organe en
# `ORPHANED_CONTENT` (« aucune raison de fermeture nommee ») alors que le
# commentaire de fermeture nommeit le successeur.

@pytest.mark.parametrize("body,expected", [
    ("superseded par #20400", 20400),
    ("Superseded par #20400", 20400),
    ("Repliée dans #24361", 24361),
    ("Repliee dans #24361", 24361),
    ("Repliée dans la PR #24361", 24361),
    ("incluse dans #20400", 20400),
    ("inclus dans #20400", 20400),
    ("Incluse dans la PR #20400", 20400),
])
def test_formes_elargies_nomment_un_successeur(body, expected):
    """Chaque forme elargie nomme le successeur qu'elle designe."""
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[0] == expected


@pytest.mark.parametrize("body", [
    # Les references de parent restent exclues : le piege de #20374.
    "Part of #20316 · See #16231 (EPIC GT-03 split)",
    "See #16231",
    # Une forme elargie SANS numero ne nomme rien.
    "Le contenu est inclus dans la fournée de la semaine",
    "superseded par la nouvelle version",
    "Repliee en fournee, a confirmer",
])
def test_formes_elargies_sans_numero_ne_nomment_rien(body):
    """Le controle negatif : elargir le vocabulaire ne l'elargit pas au vide."""
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[0] is None


@pytest.mark.parametrize("body", [
    "Repliee en fournee, a confirmer",
    "superseded par la nouvelle version",
])
def test_une_fermeture_deliberee_sans_successeur_nomme_est_deliberee(body):
    """Une repliee ou un superseded SANS successeur nomme : fermeture deliberee.

    La forme dit que la fermeture est assumee ; elle ne dit pas ou est le
    contenu. C'est `SUPERSEDED` (fermeture expliquee), pas `ORPHANED_CONTENT`
    (contenu perdu) -- la difference est celle du triage du secretariat.
    """
    assert lcu.closing_evidence("", [_c(body)], CLOSED)[1] is True


def test_une_fermeture_sans_forme_connue_ne_devient_pas_deliberee():
    """Le controle negatif de l'elargissement : une prose ordinaire ne suffit pas."""
    assert lcu.closing_evidence("", [_c("PR fermee, contenu a verifier")], CLOSED)[1] is False


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


# --- 5. controles REELS, hermetiques (#24676) ----------------------------------------
#
# Les controles `test_real_*` lisaient le depot vivant (API, timeline, ls-remote,
# objets git) : leur verdict changeait avec le depot, sans qu'une ligne du produit
# change. Ils lisent desormais le snapshot versionne
# `fixtures/list_closed_unmerged_prs_snapshot.json`. L'oracle (`evaluate_pr`,
# `closed_unmerged`, `content_state`) tourne tel quel ; seules les fonctions d'acces
# (API, ls-remote, `git merge-base`, `content_diff`) sont remplacees.
#
# Capture (une fois, 2026-11-07, lectures GET uniquement) :
#   gh api repos/jsboige/CoursIA/pulls?state=closed&sort=updated&direction=desc&per_page=100&page=N  (N=1..15, arret de closed_unmerged)
#   GET repos/jsboige/CoursIA/issues/N/timeline?per_page=100 et .../comments?per_page=100 (pagines), PR de la fenetre + 20374 + 24196
#   git ls-remote --heads https://github.com/jsboige/CoursIA.git
#   git merge-base origin/main <tete> ; orphan_branch_scan.content_diff(branche, tete, origin/main)
#   avec origin/main = e6397230f43765afa9612bc8f4935f53409d3eaa
# Projection, pseudonymisation des logins et regles d'absence : bloc `_meta` du fichier.
# Un controle se rejoue en re-capturant ; il ne se rejoue jamais en lisant le depot.

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "list_closed_unmerged_prs_snapshot.json"
SNAP = json.loads(FIXTURE.read_text(encoding="utf-8"))
MAIN = SNAP["_meta"]["main_label"]  # "origin/main", fige a SNAP["_meta"]["main_sha"]
WINDOW_SINCE = datetime(2026, 11, 4, 17, 0, tzinfo=timezone.utc)  # ~72 h avant captured_utc


class _Unpinned(AssertionError):
    """Acces a une donnee non epinglee : un controle ne retombe JAMAIS sur le reseau."""


@pytest.fixture
def pinned(monkeypatch):
    """Remplace les seules fonctions d'acces par le snapshot. Tout acces manquant echoue."""

    def _entry(number):
        try:
            return SNAP["prs"][str(number)]
        except KeyError:
            raise _Unpinned(f"PR #{number} absente du snapshot")

    def _timeline(repo, number):
        return _entry(number)["timeline"]

    def _comments(repo, number):
        return _entry(number)["comments"]

    def _remote_branches(repo):
        return dict(SNAP["branches"])

    def _content_diff(branch, branch_tip, main_ref="origin/main"):
        assert main_ref == MAIN, main_ref
        try:
            return SNAP["content"][branch_tip]["files"]
        except KeyError:
            raise _Unpinned(f"contenu de la tete {branch_tip} non epingle")

    def _run(cmd):
        # Seul `git merge-base <main> <tete>` est lu par content_state.
        if cmd[:2] != ["git", "merge-base"] or cmd[2] != MAIN:
            raise _Unpinned(f"commande git non epinglee : {cmd}")
        try:
            merge_base = SNAP["content"][cmd[3]]["merge_base"]
        except KeyError:
            raise _Unpinned(f"tete {cmd[3]} non epinglee")
        return subprocess.CompletedProcess(cmd, 0, stdout=merge_base + "\n", stderr="")

    monkeypatch.setattr(lcu, "timeline", _timeline)
    monkeypatch.setattr(lcu, "comments", _comments)
    monkeypatch.setattr(lcu.obs, "remote_branches", _remote_branches)
    monkeypatch.setattr(lcu.obs, "content_diff", _content_diff)
    monkeypatch.setattr(lcu, "_run", _run)
    return SNAP


def _pinned_page(page_number):
    """Page d'API rejouee. Item compact : [numero, closed_at, merged_at, updated_at, complet].
    `complet` = 1 : la PR est dans la fenetre et non fusionnee, son enregistrement vit dans
    SNAP["prs"][N]["pr"] (pas de copie du body dans les pages)."""
    pages = SNAP["closed_pages"]
    if not 1 <= page_number <= len(pages):
        return []
    out = []
    for number, closed_at, merged_at, updated_at, full in pages[page_number - 1]:
        if full:
            out.append(SNAP["prs"][str(number)]["pr"])
        else:
            out.append({"number": number, "closed_at": closed_at,
                        "merged_at": merged_at, "updated_at": updated_at})
    return out


def _pinned_pr(number):
    return SNAP["prs"][str(number)]["pr"]


@pytest.mark.usefixtures("pinned")
def test_real_20374_is_accidental_empty_close():
    """Controle positif exige par #22166 : le cas fondateur doit sortir ACCIDENTAL.

    Signature : `closed` 33 s apres un `head_ref_force_pushed` du meme acteur, et
    19 fichiers absents/divergents de `main` (tete de branche epinglee dans le
    snapshot). Verdict attendu : `ACCIDENTAL_EMPTY_CLOSE`, sans reseau.
    """
    row = lcu.evaluate_pr(_pinned_pr(20374), REPO, MAIN, lcu.obs.remote_branches(REPO))
    assert row["force_push_to_close_s"] is not None, row
    assert row["force_push_to_close_s"] <= 60.0, row
    assert row["verdict"] == lcu.ACCIDENTAL, row
    assert row["files_lost"] and row["files_lost"] > 0, row


@pytest.mark.usefixtures("pinned")
def test_real_24196_is_superseded():
    """Controle positif exige par la reouverture (Q162, 03/11).

    #24196 a ete repliee dans une fournee : ses commentaires de fermeture nomment
    le successeur (#24354 puis #24361). Verdict attendu : `SUPERSEDED`, sans reseau.
    """
    row = lcu.evaluate_pr(_pinned_pr(24196), REPO, MAIN, lcu.obs.remote_branches(REPO))
    assert row["verdict"] == lcu.SUPERSEDED, row
    assert "successeur nomme" in row["detail"], row


@pytest.mark.usefixtures("pinned")
def test_a_real_deliberate_close_is_not_orphaned():
    """Controle negatif : sur la fenetre, aucune fermeture expliquee ne doit sortir
    ORPHANED ni ACCIDENTAL. La fenetre (~72 h avant la capture) est epinglee avec les
    pages que closed_unmerged lit reellement. Le controle doit rester non trivial :
    la fenetre contient au moins une fermeture a successeur nomme et au moins une a
    raison d'abandon ; si elle devient vide ou triviale, le test rougit."""
    assert SNAP["_meta"]["window_since"] == WINDOW_SINCE.isoformat(), SNAP["_meta"]["window_since"]
    prs = lcu.closed_unmerged(REPO, WINDOW_SINCE, fetch_page=_pinned_page)
    assert prs, "snapshot sans fenetre : le controle ne prouve rien"
    branches = lcu.obs.remote_branches(REPO)
    rows = [lcu.evaluate_pr(pr, REPO, MAIN, branches) for pr in prs]
    successors = [r for r in rows if "successeur nomme" in r.get("detail", "")]
    abandons = [r for r in rows if "raison d'abandon" in r.get("detail", "")]
    assert len(successors) > 0, "fenetre sans fermeture a successeur nomme : controle trivial"
    assert len(abandons) > 0, "fenetre sans fermeture a raison d'abandon : controle trivial"
    for row in successors + abandons:
        assert row["verdict"] == lcu.SUPERSEDED, row


# --- lignes de tri tardives + parked-veto (#22166 point 2, reouverture 03/11) --------

def test_tri_marker_comment_is_read_outside_the_window():
    """Controle positif : une ligne [TRI] postee 3 j apres la fermeture nomme un successeur.

    Le tri du secretariat est pose apres coup ; la fenetre de 30 min autour de
    closed_at le rendait structurellement invisible (#22166 point 2).
    """
    c = _c("[TRI] Repliee en fournee dans la PR #24361", ts="2026-10-15T10:20:00Z")
    assert lcu.closing_evidence("", [c], CLOSED)[0] == 24361


def test_tri_marker_with_abandon_word_outside_the_window():
    c = _c("[TRI] Abandonnee : le canon 3.13 a rendu la reexecution obsolete",
           ts="2026-10-15T10:20:00Z")
    assert lcu.closing_evidence("", [c], CLOSED)[1] is True


@pytest.mark.parametrize("prefix", ["[TRI]", "[tri]", "  [TRI]", "[TRI] #22166 point 2"])
def test_tri_marker_forms_are_case_and_space_tolerant(prefix):
    c = _c(f"{prefix} -- fondu en fournee dans #24354", ts="2026-10-15T10:20:00Z")
    assert lcu.closing_evidence("", [c], CLOSED)[0] == 24354


def test_late_comment_without_marker_stays_ignored():
    """Controle negatif : la forme reconnue SANS marqueur reste hors fenetre = ignoree.

    La garde est le marqueur : elargir la fenetre a toute la prose tardive
    rouvrirait le piege que le commentaire de lane quelconque classe une PR.
    """
    c = _c("Repliee en fournee dans la PR #24361", ts="2026-10-15T10:20:00Z")
    assert lcu.closing_evidence("", [c], CLOSED)[0] is None


def test_tri_marker_alone_classifies_nothing():
    """Un marqueur sans forme reconnue dedans ne classe pas : liste close."""
    c = _c("[TRI] ligne de tri sans successeur ni raison", ts="2026-10-15T10:20:00Z")
    succ, abandon = lcu.closing_evidence("", [c], CLOSED)
    assert succ is None and abandon is False


def test_window_comment_still_beats_nothing_when_no_tri():
    c = _c("Doublon de #20400")  # dans la fenetre par defaut (ts == CLOSED - 14 s)
    assert lcu.closing_evidence("", [c], CLOSED)[0] == 20400


def test_parked_label_yields_parked_verdict():
    v, d = lcu.verdict_of(integrated=False, parked=True, branch_present=True, content_lost=2)
    assert v == lcu.PARKED and "parked-veto" in d


def test_integrated_beats_parked():
    """Un contenu deja sur main est le fait le plus fort, meme garé."""
    assert lcu.verdict_of(integrated=True, parked=True)[0] == lcu.INTEGRATED


def test_successor_beats_parked():
    """Un successeur nomme est le fait actionnable, meme sur une PR garée."""
    assert lcu.verdict_of(integrated=False, parked=True, successor=42)[0] == lcu.SUPERSEDED


def test_parked_beats_accidental_signature():
    """Un veto assume n'est pas l'accident du force-push, meme dans les 60 s."""
    v, _ = lcu.verdict_of(integrated=False, parked=True,
                          force_push_to_close_s=5.0, branch_present=True, content_lost=1)
    assert v == lcu.PARKED
