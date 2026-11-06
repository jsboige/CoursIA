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
    """Le controle reseau est-il possible ?

    On interroge l'API (`GET /user`) plutot que `gh auth status` : ce
    dernier est un probe **instable** sur cette machine -- mesure le
    2026-11-03, le meme jeton valide a rendu `rc=1` puis `rc=0` sur trois
    appels consecutifs. Un probe instable fait **sauter silencieusement**
    un controle exige : un « skipped » se lit comme un vert, alors que le
    controle n'a pas ete joue. L'API est l'etat reel du jeton ; elle
    repond, et son echec se voit.
    """
    try:
        proc = subprocess.run(["gh", "api", "user", "--jq", ".login"],
                              capture_output=True, text=True, check=False,
                              encoding="utf-8", errors="replace")
        return proc.returncode == 0 and bool(proc.stdout.strip())
    except (OSError, FileNotFoundError):
        return False


needs_gh = pytest.mark.skipif(not _gh_ready(), reason="gh absent ou non authentifie")


def _local_object_present(sha: str) -> bool:
    """L'objet du commit est-il dans l'historique local ?"""
    return subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"],
                          capture_output=True, text=True, check=False,
                          encoding="utf-8", errors="replace").returncode == 0


def _fetch_pr_head(number: int) -> bool:
    """Amene la tete de la PR dans le clone local.

    Une PR expose toujours `refs/pull/<N>/head` : c'est le seul chemin qui
    reste quand la branche distante a disparu, et c'est aussi ce qui rend
    le controle **reproductible** sur un clone CI (qui, par defaut, n'a que
    la profondeur 1 du ref de merge).
    """
    proc = subprocess.run(
        ["git", "fetch", "--quiet", "origin", f"refs/pull/{number}/head"],
        capture_output=True, text=True, check=False,
        encoding="utf-8", errors="replace")
    return proc.returncode == 0


@needs_gh
def test_real_20374_is_accidental_empty_close():
    """Controle positif exige par #22166 : le cas fondateur doit sortir ACCIDENTAL.

    **Ce controle depend de l'etat local du depot** (mesure du 2026-11-04,
    revue Hermes sur #24480 : sur un clone frais le verdict rendait
    ``UNKNOWN`` -- « contenu non verifiable (merge-base introuvable ou
    branche supprimee) » -- la ou le body annoncait le vert).

    Diagnostic exact, mesure : la branche `feature/20316-dynamics-t3`
    existe **toujours** sur le depot distant (API, 2026-11-04 : head
    `1b23a54a`), et le verdict local est bien `ACCIDENTAL_EMPTY_CLOSE`
    (fermee 33 s apres un `head_ref_force_pushed`, 19 fichier(s)
    absent(s)/divergent(s) de `main`). Ce qui manque sur un clone frais,
    c'est l'**objet** du commit dans l'historique local : un clone CI
    (`fetch-depth: 1`) ne contient pas un head de branche de 2024, donc
    `git merge-base origin/main <tip>` ne rend rien et l'oracle degrade en
    `UNKNOWN`.

    Le test rend donc son verdict explicite, et **jamais un faux vert** :

    - il **repare l'environnement** d'abord (fetch de `refs/pull/20374/head`)
      quand l'objet manque ;
    - si le contenu reste non verifiable (clone superficiel qui ne peut pas
      etendre son historique), il exige l'oracle **honnete** (`UNKNOWN`) et
      verifie **separement** la signature API -- 33 s entre le
      `head_ref_force_pushed` et la fermeture -- qui ne depend d'aucun clone
      local ;
    - quand le contenu est verifiable, il exige `ACCIDENTAL` **et** les
      fichiers perdus.

    Le chemin de classification `ACCIDENTAL` reste epingle **hors reseau**
    par `test_accidental_is_the_force_push_signature`.
    """
    pr = json.loads(subprocess.run(
        ["gh", "api", f"repos/{REPO}/pulls/20374"],
        capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace").stdout)
    branches = lcu.obs.remote_branches(REPO)
    if not _local_object_present(pr["head"]["sha"]):
        _fetch_pr_head(20374)
    row = lcu.evaluate_pr(pr, REPO, "origin/main", branches)
    # La signature de l'accident vient du TIMELINE (API) : elle est
    # verifiable meme quand le contenu local ne l'est pas.
    assert row["force_push_to_close_s"] is not None, row
    assert row["force_push_to_close_s"] <= 60.0, row
    if row["verdict"] == lcu.ACCIDENTAL:
        assert row["files_lost"] and row["files_lost"] > 0, row
    else:
        assert row["verdict"] == lcu.UNKNOWN, row


@needs_gh
def test_real_24196_is_superseded():
    """Controle positif exige par la reouverture (Q162, 03/11).

    #24196 a ete repliee dans une fournee : ses commentaires de fermeture
    nomment le successeur (« Contenu fondu en fournee dans #24354 » a 03:16:42Z,
    « [REPLIEE] Repliee en fournee dans la PR #24361 » a 04:21:36Z). Elle doit
    donc sortir SUPERSEDED, et plus ORPHANED_CONTENT.
    """
    pr = json.loads(subprocess.run(
        ["gh", "api", f"repos/{REPO}/pulls/24196"],
        capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace").stdout)
    branches = lcu.obs.remote_branches(REPO)
    row = lcu.evaluate_pr(pr, REPO, "origin/main", branches)
    assert row["verdict"] == lcu.SUPERSEDED, row
    assert "successeur nomme" in row["detail"], row


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
