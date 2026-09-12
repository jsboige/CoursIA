#!/usr/bin/env python3
r"""Tests guard_comment_upsert -- PATCH en place, jamais de mur (#15372).

Corpus reel rejoint : #15146 portait 10 commentaires, dont 4 HUMAINS
(3 ``jsboige`` + 1 ``myia-ai-01``) citant le marqueur
``<!-- vtr-prev-close-keyword -->`` verbatim dans des comptes rendus.
Une recherche marqueur-seul editerait un commentaire humain -- le filtre
d'auteur est l'acceptance 3 de l'issue.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import guard_comment_upsert as gcu  # noqa: E402

MARKER = "<!-- vtr-prev-close-keyword -->"


def _comment(cid, login, body, marker=MARKER):
    return {"id": cid, "body": body, "user": {"login": login}}


class FakeProc:
    def __init__(self, returncode=0, stdout="[]", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class RecordingGh:
    """Rejoue un monde de commentaires et enregistre les appels gh."""

    def __init__(self, pages):
        self.pages = pages
        self.calls = []

    def __call__(self, cmd, **kwargs):
        self.calls.append(list(cmd))
        if "--paginate" in cmd:
            import json
            return FakeProc(stdout=json.dumps(self.pages))
        # PATCH / POST renvoient le commentaire ecrit
        return FakeProc(stdout='{"id": 999}')

    @property
    def endpoints(self):
        return [c[3] for c in self.calls if len(c) > 3 and c[0] == "gh"]

    def find(self, fragment):
        for c in self.calls:
            if fragment in " ".join(c):
                return c
        return None


# ---------------------------------------------------------------------------
# find_guard_comment_id -- le filtre d'auteur n'est pas decoratif
# ---------------------------------------------------------------------------

class TestFindGuardCommentId:
    def test_corpus_15346_marker_alone_is_not_enough(self):
        """Acceptance 3 : le corpus #15146 -- 4 humains portent le
        marqueur, 1 bot aussi. Seul le commentaire bot est cible."""
        comments = [
            _comment(101, "jsboige", f"compte rendu citant {MARKER} verbatim"),
            _comment(102, "jsboige", f"autre rapport {MARKER}"),
            _comment(103, "myia-ai-01", f"revue citant {MARKER}"),
            _comment(104, "jsboige", f"troisieme {MARKER}"),
            _comment(105, "github-actions[bot]",
                     f"{MARKER}\n**bloquant (#10093)**"),
        ]
        assert gcu.find_guard_comment_id(comments, MARKER) == 105

    def test_humans_only_returns_none(self):
        comments = [
            _comment(201, "jsboige", MARKER),
            _comment(202, "myia-po-2025", f"cite {MARKER}"),
        ]
        assert gcu.find_guard_comment_id(comments, MARKER) is None

    def test_other_bots_are_untouchable(self):
        """dependabot/konvergence portant le marqueur : jamais edite."""
        comments = [
            _comment(301, "dependabot[bot]", MARKER),
            _comment(302, "konvergence-pcg[bot]", f"x {MARKER}"),
        ]
        assert gcu.find_guard_comment_id(comments, MARKER) is None

    def test_lookalike_login_github_actions_xyz_is_not_the_bot(self):
        """Review ai-01 #15374 : sur un depot public un tiers peut porter
        ``github-actions-xyz`` -- le prefixe ne suffit pas, un SET EXACT
        seul protege. Ce commentaire ne doit jamais etre PATCHe."""
        comments = [
            _comment(305, "github-actions-xyz", f"{MARKER} faux reponse"),
            _comment(306, "github-actions[bot]", f"{MARKER} vrai verdict"),
        ]
        # le lookalike SEUL -> aucun cible (pas de PATCH sur un tiers)
        assert gcu.find_guard_comment_id(comments[:1], MARKER) is None
        # melange au bot veritable -> seul le bot est cible
        assert gcu.find_guard_comment_id(comments, MARKER) == 306

    def test_legacy_login_github_actions_counts(self):
        comments = [_comment(401, "github-actions", MARKER)]
        assert gcu.find_guard_comment_id(comments, MARKER) == 401

    def test_last_bot_comment_wins(self):
        """Le mur existant : plusieurs commentaires bot -> l'id MAX (le
        corps actuellement affiche en bas), pas le plus ancien."""
        comments = [
            _comment(501, "github-actions[bot]", MARKER),
            _comment(502, "github-actions[bot]", MARKER),
            _comment(503, "github-actions[bot]", MARKER),
        ]
        assert gcu.find_guard_comment_id(comments, MARKER) == 503

    def test_marker_absent_returns_none(self):
        comments = [_comment(601, "github-actions[bot]",
                             "<!-- vtr-required-block --> autre garde")]
        assert gcu.find_guard_comment_id(comments, MARKER) is None

    def test_empty_and_none_inputs(self):
        assert gcu.find_guard_comment_id([], MARKER) is None
        assert gcu.find_guard_comment_id(None, MARKER) is None


# ---------------------------------------------------------------------------
# upsert -- PATCH au lieu de POST
# ---------------------------------------------------------------------------

class TestUpsertComment:
    def test_existing_bot_comment_is_patched_not_duplicated(self):
        """Acceptance 1 : le commentaire porte le marqueur ET l'auteur
        bot -> PATCH issues/comments/{id}, AUCUN nouveau POST."""
        gh = RecordingGh([
            [_comment(701, "jsboige", MARKER),
             _comment(702, "github-actions[bot]", f"{MARKER} bloquant")],
        ])
        result = gcu.upsert_comment(42, MARKER, "corps bloquant",
                                    "o/r", runner=gh)
        assert result == {"action": "patched", "comment_id": 702}
        patch = gh.find("--method")
        assert patch is not None, "un PATCH devait etre emis"
        assert "PATCH" in patch
        assert "repos/o/r/issues/comments/702" in patch
        assert "corps bloquant" in patch[-1]
        post = gh.find("--method")
        assert not any("POST" in c for c in gh.calls), (
            "un commentaire bot existant ne doit JAMAIS etre duplique"
        )

    def test_absent_comment_creates_first_one(self):
        gh = RecordingGh([[]])
        result = gcu.upsert_comment(43, MARKER, "premier blocage",
                                    "o/r", runner=gh)
        assert result["action"] == "created"
        post = gh.find("POST")
        assert post is not None
        assert "repos/o/r/issues/43/comments" in " ".join(post)

    def test_list_uses_rest_api_not_graphql_id(self):
        """L'id de gh pr view --json comments est un node id GraphQL
        (IC_...), inutilisable en PATCH REST -- le listing doit passer
        par l'API REST (mesure #15373 : IC_kwDO... vs 5600457600)."""
        gh = RecordingGh([[]])
        gcu.upsert_comment(44, MARKER, "x", "o/r", runner=gh)
        listing = gh.find("--paginate")
        assert "repos/o/r/issues/44/comments" in listing
        assert "--slurp" in listing

    def test_multi_page_listing_is_flattened(self):
        gh = RecordingGh([
            [_comment(801, "github-actions[bot]", MARKER)],
            [_comment(802, "jsboige", "apres page 1")],
        ])
        result = gcu.upsert_comment(45, MARKER, "y", "o/r", runner=gh)
        assert result["comment_id"] == 801


# ---------------------------------------------------------------------------
# lift -- un mur qui ne se ferme jamais n'est pas un signal
# ---------------------------------------------------------------------------

class TestLiftComment:
    def test_green_run_rewrites_block_as_lifted_in_place(self):
        """Acceptance 2 : run vert + commentaire bloquant existant ->
        reecrit LEVE, horodate, nommant les prev acceptes. Le marqueur
        RESTE porte (le prochain upsert doit retrouver ce commentaire)."""
        gh = RecordingGh([
            [_comment(901, "github-actions[bot]",
                      f"{MARKER}\n**bloquant (#10093)** ancien verdict")],
        ])
        result = gcu.lift_comment(
            46, MARKER, "prev acceptés : #15306", "o/r", runner=gh)
        assert result == {"action": "patched", "comment_id": 901}
        patch_call = gh.find("PATCH")
        body = patch_call[-1]
        assert "LEVÉ" in body
        assert "2026-" in body or "20" in body  # horodatage UTC présent
        assert "prev acceptés : #15306" in body
        assert MARKER in body, (
            "le marqueur doit rester porte par le corps leve, sinon le "
            "prochain upsert perd la chaine"
        )
        assert not any("POST" in c or "DELETE" in c for c in gh.calls), (
            "lever = reecrire, jamais supprimer (acceptance 4)"
        )

    def test_green_run_on_never_blocked_pr_is_silent(self):
        """Un vert sur une PR jamais bloquee ne fabrique pas de bruit :
        aucun PATCH, aucun POST."""
        gh = RecordingGh([[]])
        result = gcu.lift_comment(47, MARKER, "note", "o/r", runner=gh)
        assert result == {"action": "noop", "comment_id": None}
        assert not any("PATCH" in c or "POST" in c for c in gh.calls)

    def test_lifted_body_is_still_findable_for_next_upsert(self):
        """Boucle upsert : le corps releve porte le marqueur -> un run
        rouge suivant re-PATCHera le meme id (pas de nouveau POST)."""
        body = gcu.build_lifted_body(MARKER, "titre", "note", ts="2026-09-09T11:00:00Z")
        comments = [_comment(911, "github-actions[bot]", body)]
        assert gcu.find_guard_comment_id(comments, MARKER) == 911


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

class TestMain:
    def test_body_file_mode_invokes_upsert(self, tmp_path, monkeypatch):
        body_file = tmp_path / "blocked.md"
        body_file.write_text(f"{MARKER}\ncorps", encoding="utf-8")
        monkeypatch.setenv("GITHUB_REPOSITORY", "jsboige/CoursIA")
        gh = RecordingGh([[_comment(1001, "github-actions[bot]", MARKER)]])
        rc = gcu.main(["--pr", "48", "--marker", MARKER,
                       "--body-file", str(body_file)], runner=gh)
        assert rc == 0
        assert gh.find("PATCH") is not None

    def test_lift_mode_invokes_lift(self, tmp_path, monkeypatch):
        monkeypatch.setenv("GITHUB_REPOSITORY", "jsboige/CoursIA")
        gh = RecordingGh([[]])
        rc = gcu.main(["--pr", "49", "--marker", MARKER, "--lift",
                       "--note", "prev: #15306"], runner=gh)
        assert rc == 0
        assert not any("PATCH" in c or "POST" in c for c in gh.calls)

    def test_modes_are_mutually_exclusive(self, tmp_path, monkeypatch):
        body_file = tmp_path / "b.md"
        body_file.write_text("x", encoding="utf-8")
        monkeypatch.setenv("GITHUB_REPOSITORY", "o/r")
        import pytest
        with pytest.raises(SystemExit):
            gcu.main(["--pr", "50", "--marker", MARKER,
                      "--body-file", str(body_file), "--lift"])


# ---------------------------------------------------------------------------
# Câblage workflow -- l'échec de lift/upsert doit rester OBSERVABLE (#15374)
# ---------------------------------------------------------------------------

WORKFLOW = (
    Path(__file__).resolve().parents[2]
    / ".github" / "workflows" / "always-on-guards.yml"
)


class TestWorkflowWiring:
    r"""Review ai-01 #15374 : le chemin vert ne doit plus avaler l'échec de
    lift par ``>/dev/null 2>&1 || true`` -- sinon le commentaire bloquant
    survit affiché faux sans aucun signal (le défaut racine de #15372).
    Le gate reste vert, mais l'échec devient un ``::warning``."""

    def test_lift_failure_emits_warning(self):
        text = WORKFLOW.read_text(encoding="utf-8")
        assert "::warning::prev-guard lift failed" in text, (
            "le chemin vert du prev-guard doit rendre l'échec de lift "
            "observable (review ai-01 #15374)")

    def test_upsert_failure_emits_warning(self):
        text = WORKFLOW.read_text(encoding="utf-8")
        assert "::warning::prev-guard upsert failed" in text, (
            "le chemin rouge ne doit pas présenter un échec d'upsert "
            "comme une écriture réussie (review ai-01 #15374)")

    def test_no_silently_swallowed_upsert_call(self):
        """Le buggy pattern : un appel guard_comment_upsert.py suivi (à
        ~6 lignes, le temps des arguments multilignes) d'un ``|| true``
        seul -- sans if/warning, l'échec est invisible."""
        lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if "guard_comment_upsert.py" in line:
                window = lines[i:i + 7]
                swallowed = [l for l in window if l.strip() == ">/dev/null 2>&1 || true"]
                assert not swallowed, (
                    f"appel guard_comment_upsert.py l.{i + 1} avalé par "
                    "|| true -- l'échec doit être observable")
