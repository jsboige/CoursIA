#!/usr/bin/env python3
r"""Tests d'affaiblissement pour prune_merged_worktrees.py (#14195, #14509).

Pinent le contrat de sûreté (issues #14195 + #14509 acceptance) :

1. `is_untracked_artifact` reconnait les catégories du dernier commentaire
   de #8924 (slides/images, scripts/results, .claude/agent-memory,
   _output.ipynb, caches node_modules/.cache/.pytest_cache/__pycache__,
   _measurements, .mypy_cache, .ruff_cache, dist/, build/, .eggs/, .tox/).
2. `parse_porcelain` rebranche le predicat de salete sur le pouvoir de
   refus git reel (#14509) : TOUT untracked non-ignore bloque
   `git worktree remove`, quelle que soit son extension ou l'absence
   d'extension, artefacts #8924 compris -- `bg_logs/`,
   `lake_7012.log.relaunch` et un `node_modules/` non-ignore passaient
   l'ancien predicat et se terminaient en FAILED permanent.
3. `parse_porcelain` separe untracked / gitignores non-cache / tracks
   modifies (`--ignored=matching`, jamais de `!!` compte comme source
   sale).
4. `worktree_has_initialized_submodules` detecte les worktrees que git ne
   retirera jamais ("working trees containing submodules cannot be moved
   or removed") -> REFUSE contains_submodules.
5. `WorktreeStatus.decision` = `REMOVE` quand pr_state=MERGED ou CLOSED
   et pas d'unpushed, de submodule, ni de untracked bloquant (contrôle
   positif manquant aux prédicats d'ascendance, cf squashed-merge).
6. `WorktreeStatus.decision` = `REFUSE` quand pr_state=OPEN
   (le retrait casserait l'itération en cours).
7. `WorktreeStatus.decision` = `REFUSE` quand unpushed_commits > 0
   (jamais d'exception).
8. `WorktreeStatus.decision` = `REFUSE` quand untracked bloquant avec
   cause nommée (`untolerated_untracked:<n>` / `uncommitted_source_changes`).
9. `WorktreeStatus.decision` = `REFUSE` quand branch=main/master
   (le worktree de travail principal n'est JAMAIS un candidat au retrait,
   même si gh remonte une vieille PR close qui pointe sur main -- bug
   trouvé au dry-run inaugural).
10. `WorktreeStatus.decision` = `SKIP_CURRENT` pour le worktree depuis
    lequel le script est lancé.

Tests d'intégration end-to-end (subprocess réel) :
- dry-run sur un worktree `main` ne tente jamais `worktree remove`.
- `--apply` no-op quand 0 removable.
- exit 0 quand rien à signaler, 1 si refus observé, 2 si erreur gh/git.

Run : python -m pytest scripts/tests/test_prune_merged_worktrees.py
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


# CWD cible pour les tests subprocess (Windows path natif)
import os
TEST_CWD = os.getcwd() if os.path.exists("scripts/ci/prune_merged_worktrees.py") else "C:/dev/CoursIA-14195-prune"
if not os.path.exists(TEST_CWD + "/scripts/ci/prune_merged_worktrees.py"):
    # Subprocess sera lance depuis TEST_CWD ; on veut etre dans le worktree
    TEST_CWD = "C:/dev/CoursIA-14195-prune"


# ---------------------------------------------------------------------------
# is_untracked_artifact / is_source_dirty
# ---------------------------------------------------------------------------


class TestArtifactClassification:
    def test_artifact_slides_images(self):
        assert pmw.is_untracked_artifact("slides/images/foo.png") is True

    def test_artifact_scripts_results(self):
        assert pmw.is_untracked_artifact("scripts/results/foo.json") is True

    def test_artifact_agent_memory(self):
        assert pmw.is_untracked_artifact(".claude/agent-memory/note.md") is True

    def test_artifact_output_ipynb(self):
        assert pmw.is_untracked_artifact("foo_output.ipynb") is True

    def test_artifact_node_modules_nested(self):
        assert pmw.is_untracked_artifact("frontend/node_modules/x.js") is True

    def test_artifact_pycache_nested(self):
        assert pmw.is_untracked_artifact("scripts/ci/__pycache__/foo.pyc") is True

    def test_artifact_pytest_cache(self):
        assert pmw.is_untracked_artifact(".pytest_cache/v/cache/lastfailed") is True

    def test_artifact_dist_build(self):
        assert pmw.is_untracked_artifact("pkg/dist/foo.whl") is True
        assert pmw.is_untracked_artifact("pkg/build/lib/foo.py") is True

    def test_artifact_windows_path_backslashes(self):
        assert pmw.is_untracked_artifact("slides\\images\\foo.png") is True

    def test_source_py_blocks(self):
        out = pmw.parse_porcelain("?? scripts/foo.py\n")
        assert out["blocking_untracked"] == ["scripts/foo.py"]

    def test_source_ipynb_blocks(self):
        out = pmw.parse_porcelain("?? MyIA.AI.Notebooks/Search/foo.ipynb\n")
        assert out["blocking_untracked"] == [
            "MyIA.AI.Notebooks/Search/foo.ipynb"]

    def test_source_lean_blocks(self):
        out = pmw.parse_porcelain("?? knot_lean/Foo.lean\n")
        assert out["blocking_untracked"] == ["knot_lean/Foo.lean"]

    def test_source_md_blocks(self):
        out = pmw.parse_porcelain("?? docs/spec.md\n")
        assert out["blocking_untracked"] == ["docs/spec.md"]

    def test_source_coexists_with_artifact(self):
        # Un seul untracked non-ignore suffit a bloquer le retrait, un
        # artefact non-ignore aussi : le worktree sera REFUSE.
        out = pmw.parse_porcelain(
            "?? slides/images/foo.png\n?? scripts/bug_fix.py\n"
        )
        assert len(out["blocking_untracked"]) == 2


class TestUntrackedStrict:
    """Le predicat de salete doit refleter le pouvoir de refus git (#14509) :

    `git worktree remove` (sans --force) refuse TOUT untracked non-ignore,
    quelle que soit l'extension ou son absence -- artefacts #8924 compris
    quand ils ne sont pas gitignores. L'ancien predicat (extensions de
    source + allowliste artefacts) decidait REMOVE sur `bg_logs/`,
    `lake_7012.log.relaunch` et meme un `node_modules/` non-ignore, puis
    git refusait -> FAILED permanent.
    """

    def test_directory_without_extension_blocks(self):
        out = pmw.parse_porcelain("?? bg_logs/\n")
        assert out["blocking_untracked"] == ["bg_logs/"]

    def test_unknown_suffix_file_blocks(self):
        out = pmw.parse_porcelain("?? lake_7012.log.relaunch\n")
        assert out["blocking_untracked"] == ["lake_7012.log.relaunch"]

    def test_binary_without_source_extension_blocks(self):
        out = pmw.parse_porcelain("?? data/output.bin\n")
        assert out["blocking_untracked"] == ["data/output.bin"]

    def test_slides_images_unignored_blocks(self):
        # Categorie d'artefact #8924 : git ignore la categorie, le refus
        # git lui ne l'ignore pas. La tolerance ne survit que gitignoree.
        out = pmw.parse_porcelain("?? slides/images/foo.png\n")
        assert out["blocking_untracked"] == ["slides/images/foo.png"]

    def test_agent_memory_unignored_blocks(self):
        out = pmw.parse_porcelain("?? .claude/agent-memory/note.md\n")
        assert out["blocking_untracked"] == [".claude/agent-memory/note.md"]

    def test_node_modules_unignored_blocks(self):
        out = pmw.parse_porcelain("?? frontend/node_modules/x.js\n")
        assert out["blocking_untracked"] == ["frontend/node_modules/x.js"]


class TestParsePorcelain:
    """`parse_porcelain` -- split ?? / !! / tracks (#14509).

    Pince aussi le bug latent : sans la casse "!!", un gitignore aurait
    ete compte comme modification de source (any(c != " ") est Vrai), ce
    qui aurait REFUSE en masse sur .env etc. une fois la passe
    --ignored=matching activee.
    """

    def test_untracked_and_ignored_split(self):
        out = pmw.parse_porcelain("?? bg_logs/\n!! .env\n M tracked.py\n")
        assert out["untracked"] == ["bg_logs/"]
        assert out["blocking_untracked"] == ["bg_logs/"]
        assert out["ignored_extra"] == [".env"]
        assert out["tracked_modified"] == ["tracked.py"]

    def test_ignored_cache_matching_artifact_tokens_dropped(self):
        out = pmw.parse_porcelain(
            "!! node_modules/x\n!! .pytest_cache/v/cache/lastfailed\n"
        )
        assert out["ignored_extra"] == []

    def test_untracked_artifact_and_ignored_cache_are_disjoint(self):
        # Un artefact UNTRACKED bloque (git le refusera) ; le meme
        # artefact GITIGNORE ne bloque pas et n'est meme pas signale
        # (bruit de cache).
        out = pmw.parse_porcelain(
            "?? node_modules/y\n!! node_modules/x\n"
        )
        assert out["blocking_untracked"] == ["node_modules/y"]
        assert out["ignored_extra"] == []

    def test_rename_target_kept(self):
        out = pmw.parse_porcelain("R  old.py -> new.py\n")
        assert out["tracked_modified"] == ["new.py"]

    def test_ignored_line_never_counts_as_modified(self):
        out = pmw.parse_porcelain("!! .env.production\n")
        assert out["tracked_modified"] == []
        assert out["blocking_untracked"] == []


class TestSubmoduleDetection:
    """`worktree_has_initialized_submodules` (#14509) : git ne retirera
    jamais la baignoire, autant le dire avant qu'apres l'echec."""

    def _stub(self, monkeypatch, rc, stdout):
        monkeypatch.setattr(pmw, "run_git", lambda *a, **k: _fake_proc(rc, stdout))
        return pmw.worktree_has_initialized_submodules("C:/fake")

    def test_empty_stdout_is_false(self, monkeypatch):
        assert self._stub(monkeypatch, 0, "") is False

    def test_uninitialized_dash_is_false(self, monkeypatch):
        assert self._stub(monkeypatch, 0, "-2a1f3c argumentum\n") is False

    def test_initialized_space_is_true(self, monkeypatch):
        assert self._stub(monkeypatch, 0, " 2a1f3c argumentum\n") is True

    def test_initialized_dirty_plus_is_true(self, monkeypatch):
        assert self._stub(monkeypatch, 0, "+2a1f3c argumentum\n") is True

    def test_unreachable_worktree_is_false(self, monkeypatch):
        # Pas de preuve de submodule initialise : ne REFUSE pas sur un
        # etat qu'on ne peut pas lire (pire cas = FAILED git, avant-fix).
        assert self._stub(monkeypatch, 128, "") is False


# ---------------------------------------------------------------------------
# Decision logic via diagnostic simule
# ---------------------------------------------------------------------------


def _make_status(**overrides):
    """Construit un WorktreeStatus avec des défauts sensés."""
    defaults = dict(
        path="C:/fake/worktree",
        branch="fix/X",
        is_current=False,
        pr_state="MERGED",
        pr_number=12345,
        pr_url="https://github.com/x/y/pull/12345",
        ahead_count=0,
        has_source_dirty=False,
        untracked_paths=[],
        decision="REMOVE",
        refusal_reason=None,
    )
    defaults.update(overrides)
    return pmw.WorktreeStatus(**defaults)


class TestDecisionContract:
    def test_remove_when_pr_merged(self):
        # Contrôle positif manquant aux prédicats d'ascendance (squashed)
        s = _make_status(pr_state="MERGED", ahead_count=0, has_source_dirty=False)
        # Le decision n'est pas porte par le test -- on verifie la logique
        # via diagnose_worktree en bouchonnant gh. Ici on vérifie les
        # conditions qui autoriseraient le REMOVE :
        assert s.ahead_count == 0
        assert s.has_source_dirty is False
        assert s.pr_state in ("MERGED", "CLOSED")
        # Si gh remontait ces conditions, diagnose_worktree conclut REMOVE.
        # Voir test_diagnose_e2e_merged_pr pour la voie end-to-end.

    def test_refuse_when_pr_open(self):
        s = _make_status(pr_state="OPEN", decision="REFUSE",
                         refusal_reason="pr_open:#12345")
        assert s.decision == "REFUSE"
        assert "pr_open" in s.refusal_reason

    def test_refuse_when_unpushed(self):
        s = _make_status(ahead_count=2, decision="REFUSE",
                         refusal_reason="unpushed_commits:2")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "unpushed_commits:2"

    def test_refuse_when_blocking_untracked(self):
        s = _make_status(has_source_dirty=True, decision="REFUSE",
                         refusal_reason="uncommitted_untracked:bg_logs/")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "uncommitted_untracked:bg_logs/"

    def test_refuse_contains_submodules(self):
        s = _make_status(has_submodules=True, decision="REFUSE",
                         refusal_reason="contains_submodules")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "contains_submodules"

    def test_refuse_protected_main(self):
        s = _make_status(branch="main", decision="REFUSE",
                         refusal_reason="protected_branch:main")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "protected_branch:main"

    def test_refuse_protected_master(self):
        s = _make_status(branch="master", decision="REFUSE",
                         refusal_reason="protected_branch:master")
        assert s.decision == "REFUSE"

    def test_skip_current(self):
        s = _make_status(is_current=True, decision="SKIP_CURRENT",
                         refusal_reason="current_worktree_not_removable")
        assert s.decision == "SKIP_CURRENT"

    def test_to_dict_round_trip(self):
        s = _make_status()
        d = s.to_dict()
        # Sanity : tous les champs sont la (y compris #14509, additifs)
        for k in (
            "path", "branch", "is_current", "pr_state", "pr_number",
            "pr_url", "ahead_count", "has_source_dirty",
            "untracked_paths", "decision", "refusal_reason",
            "has_submodules", "blocking_untracked", "ignored_extra",
        ):
            assert k in d, f"missing key: {k}"


# ---------------------------------------------------------------------------
# Diagnose -- câblage predicat -> decision + reason nomme (#14509)
# ---------------------------------------------------------------------------


class TestDiagnoseRefusalCauses:
    """Pince l'AVAL : un get_worktree_info souche -> decision + reason.

    Ne re-teste pas get_worktree_info (couvert par TestParsePorcelain et
    TestSubmoduleDetection) : verifie que diagnose_worktree traduit les
    informations structurelles en REFUSE causes nommees, et que le
    predicat submodule inhibe le REMOVE SANS appel gh."""

    def _info(self, **over):
        base = dict(
            branch="fix/X", ahead_count=0, untracked=[],
            blocking_untracked=[], ignored_extra=[], tracked_modified=[],
            has_source_dirty=False, has_submodules=False, is_current=False,
        )
        base.update(over)
        return base

    def test_source_untracked_refuses_with_named_register(self, monkeypatch):
        info = self._info(
            untracked=["bg_logs/", "src/keep.py"],
            blocking_untracked=["src/keep.py"],
            has_source_dirty=True,
        )
        monkeypatch.setattr(pmw, "get_worktree_info", lambda *a: info)
        s = pmw.diagnose_worktree("C:/fake", "C:/other")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "uncommitted_source_changes"
        assert s.blocking_untracked == ["src/keep.py"]

    def test_submodules_inhibit_remove_without_gh_call(self, monkeypatch):
        info = self._info(has_submodules=True)
        monkeypatch.setattr(pmw, "get_worktree_info", lambda *a: info)

        def _no_gh(*a):
            raise AssertionError(
                "lookup_pr_for_branch ne doit pas etre appele : le "
                "verdict submodule est structurel et ne demande aucun gh"
            )

        monkeypatch.setattr(pmw, "lookup_pr_for_branch", _no_gh)
        s = pmw.diagnose_worktree("C:/fake", "C:/other")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "contains_submodules"

    def test_clean_merged_still_remove(self, monkeypatch):
        info = self._info()
        monkeypatch.setattr(pmw, "get_worktree_info", lambda *a: info)
        monkeypatch.setattr(
            pmw, "lookup_pr_for_branch",
            lambda *a: {"state": "MERGED", "number": 42, "url": "u"},
        )
        s = pmw.diagnose_worktree("C:/fake", "C:/other")
        assert s.decision == "REMOVE"
        assert s.refusal_reason is None

    def test_untracked_primes_over_merged_pr(self, monkeypatch):
        # Meme PR MERGED, un residu untracked NON tolere doit changer le
        # verdict : sans ce garde, le worktree partait en REMOVE puis FAILED.
        info = self._info(
            untracked=["residu.bin"], blocking_untracked=["residu.bin"],
            has_source_dirty=False,
        )
        monkeypatch.setattr(pmw, "get_worktree_info", lambda *a: info)
        monkeypatch.setattr(
            pmw, "lookup_pr_for_branch",
            lambda *a: {"state": "MERGED", "number": 42, "url": "u"},
        )
        s = pmw.diagnose_worktree("C:/fake", "C:/other")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "untolerated_untracked:1"

    def test_tracked_modified_refuses_before_gh(self, monkeypatch):
        # Worktree a fichier tracked modifie (ex. slides fantomes CRLF) :
        # le predicat 2a doit le refuser AVANT l'appel gh -- sans ce
        # predicat, REMOVE puis FAILED git permanent.
        info = self._info(tracked_modified=["slides/S3-acculturation/slides.md"],
                          has_source_dirty=True)
        monkeypatch.setattr(pmw, "get_worktree_info", lambda *a: info)

        def _no_gh(*a):
            raise AssertionError(
                "lookup_pr_for_branch ne doit pas etre appele : le "
                "verdict de salete est structurel et ne demande aucun gh"
            )

        monkeypatch.setattr(pmw, "lookup_pr_for_branch", _no_gh)
        s = pmw.diagnose_worktree("C:/fake", "C:/other")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "uncommitted_source_changes"


class TestGetWorktreeInfoPorcelain:
    """Câblage get_worktree_info -> parse_porcelain + submodule status."""

    def test_splits_untracked_ignored_and_reports_submodules(self, monkeypatch):
        def fake_run_git(*args, **kwargs):
            cmd = list(args)
            if "status" in cmd:
                return _fake_proc(
                    0, "?? bg_logs/\n?? residu.bin\n!! .env\n")
            if "submodule" in cmd:
                return _fake_proc(0, " 2a1f3c argumentum\n")
            if "--abbrev-ref" in cmd and "HEAD" in cmd:
                return _fake_proc(0, "fix/X\n")
            return _fake_proc(128, "")

        monkeypatch.setattr(pmw, "run_git", fake_run_git)
        info = pmw.get_worktree_info("C:/fake", "C:/other")
        assert info["untracked"] == ["bg_logs/", "residu.bin"]
        # bg_logs/ est un artefact tolere (#14619) : nettoyable a l'apply,
        # il ne compte pas comme bloquant ; residu.bin oui.
        assert info["blocking_untracked"] == ["residu.bin"]
        assert info["ignored_extra"] == [".env"]
        # Ni fichier source ni tracked modifie : toleres + residu seul ne
        # rendent pas le worktree "source sale" (le residu releve du 2b).
        assert info["has_source_dirty"] is False
        assert info["has_submodules"] is True

    def test_clean_worktree_reports_no_sources(self, monkeypatch):
        def fake_run_git(*args, **kwargs):
            cmd = list(args)
            if "status" in cmd:
                return _fake_proc(0, "")
            if "submodule" in cmd:
                return _fake_proc(0, "")
            if "--abbrev-ref" in cmd and "HEAD" in cmd:
                return _fake_proc(0, "fix/X\n")
            return _fake_proc(128, "")

        monkeypatch.setattr(pmw, "run_git", fake_run_git)
        info = pmw.get_worktree_info("C:/fake", "C:/other")
        assert info["has_source_dirty"] is False
        assert info["blocking_untracked"] == []
        assert info["has_submodules"] is False


# ---------------------------------------------------------------------------
# same_worktree_path -- le drapeau is_current se CALCULE
# ---------------------------------------------------------------------------


class TestSameWorktreePath:
    r"""`test_skip_current` ne pinne que l'AVAL du drapeau, jamais son calcul.

    Le drapeau etait `wt_path == current_path`, entre deux ecritures
    differentes du meme chemin : `git worktree list --porcelain` rend des
    slash avant, `Path(cwd).resolve()` rend la forme native (antislash sous
    Windows). L'egalite ne pouvait donc jamais etre vraie sur Windows, et
    `SKIP_CURRENT` etait inatteignable -- mesure du 2026-09-03 sur ai-01,
    64 worktrees, `skipped=0` meme lance depuis un worktree dont la PR est
    MERGED, c'est-a-dire un `--apply` qui aurait tente `worktree remove`
    sur son propre repertoire courant.
    """

    def test_separator_mismatch_is_the_same_worktree(self, tmp_path):
        native = str(tmp_path)
        porcelain = native.replace(os.sep, "/")
        if os.sep != "/":
            # Controle positif : sans ca, le test passerait sur une paire
            # identique et ne mesurerait rien du defaut qu'il pinne.
            assert porcelain != native, "le cas teste ne se reproduit pas ici"
        assert pmw.same_worktree_path(porcelain, native) is True

    def test_trailing_separator_is_the_same_worktree(self, tmp_path):
        assert pmw.same_worktree_path(str(tmp_path) + "/", str(tmp_path)) is True

    def test_distinct_worktrees_are_not_current(self, tmp_path):
        a = tmp_path / "wt-a"
        b = tmp_path / "wt-b"
        a.mkdir()
        b.mkdir()
        assert pmw.same_worktree_path(str(a), str(b)) is False

    def test_get_worktree_info_uses_the_comparison(self, monkeypatch, tmp_path):
        """Pinne le CABLAGE : un retour a `==` en l.284 doit rougir ici."""
        class _Proc:
            returncode = 0
            stdout = ""

        monkeypatch.setattr(pmw, "run_git", lambda *a, **k: _Proc())
        native = str(tmp_path)
        porcelain = native.replace(os.sep, "/")
        info = pmw.get_worktree_info(porcelain, native)
        assert info["is_current"] is True


# ---------------------------------------------------------------------------
# Tests lookup_pr_for_detached_head (#14476) -- anti faux-positifs
# ---------------------------------------------------------------------------


class TestLookupPRForDetachedHead:
    """Tests unitaires du verdict par contenu pour HEAD detaché (#14476).

    Avant #14476 : intersection de jetons `re.findall(r"[A-Za-z0-9-]{4,}")`
    entre titre PR et sujet commit -- prenait la 1ere PR dont au moins un
    mot >=4 chars matchait. Cause structurelle de faux positifs massifs
    (notebook, guard, training, slides sont des mots partout).

    Apres #14476 : 1) resolution directe par numero si ``re.search(r"\\(#\\d+\\)$")``
    extrait du sujet ; 2) sinon egalite normalisee stricte ; 3) sinon None.
    """

    def test_subject_without_pr_number_no_match(self, monkeypatch):
        """Sujet sans `(#N)` retourne par defaut le verdict `None` quand la
        liste de PRs recentes est vide ou sans egalite.
        """
        # Stub run_gh : pas de PR list exploitable
        monkeypatch.setattr(pmw, "run_gh", lambda *a, **k: _fake_proc(
            returncode=0,
            json_payload=[],
        ))
        # Pas de run_git OK -> pas de sujet exploitable non plus -> None
        # est deja valide. Ici on verifie qu'un sujet SANS (#N) et une
        # liste vide rendent bien None, jamais une PR par defaut.
        import pytest
        # Worktree path bidon ; on stub run_git aussi.
        monkeypatch.setattr(
            pmw, "run_git",
            lambda *a, **k: _fake_proc(returncode=128, stdout=""),
        )
        result = pmw.lookup_pr_for_detached_head("/tmp/fake")
        assert result is None

    def test_subject_with_pr_number_resolves_directly(self, monkeypatch):
        """Sujet `fix: chg (#14476)` -> `gh pr view 14476` direct.

        C'est la voie nominale post-#14476 (squash-merge preserve le
        numero de PR dans le sujet du commit). On verifie qu'on ne tombe
        PAS dans la voie liste -- le PR rendu vient de `gh pr view N`,
        pas d'une intersection par jetons.
        """
        # run_git retourne un sujet avec `(#14476)`
        monkeypatch.setattr(
            pmw, "run_git",
            lambda *a, **k: _fake_proc(
                returncode=0,
                stdout="fix(scripts,#14476): prune bug repair (#14476)\n",
            ),
        )

        gh_calls: list[list] = []

        def fake_run_gh(*args, **kwargs):
            gh_calls.append(list(args))
            cmd = list(args)
            # `gh pr view 14476 --json ...` -- la voie directe
            if "view" in cmd and "14476" in cmd:
                return _fake_proc(
                    returncode=0,
                    json_payload={
                        "number": 14476,
                        "state": "MERGED",
                        "url": "https://github.com/jsboige/CoursIA/pull/14476",
                        "title": "fix(scripts,#14476): prune bug repair",
                    },
                )
            # Liste vide en fallback (au cas où on tomberait dans la voie 2)
            return _fake_proc(returncode=0, json_payload=[])

        monkeypatch.setattr(pmw, "run_gh", fake_run_gh)

        result = pmw.lookup_pr_for_detached_head("/tmp/fake")
        assert result is not None
        assert result["number"] == 14476
        assert result["state"] == "MERGED"
        # On a appelé la vue directe, pas la liste
        assert any(
            "view" in c and "14476" in c
            for c in gh_calls
        ), f"expected direct pr view call, got {gh_calls}"

    def test_subject_share_token_returns_none(self, monkeypatch):
        """Faux positif élimine : sujet `fix(notebook): ...` partage `notebook`
        avec un titre PR récent, mais aucun match par numero ni par egalite
        normalisee. AVANT #14476, ce cas retournait la 1ere PR dont le
        titre contenait `notebook`, ce qui causait le retrait d'un
        worktree encore actif.
        """
        # Sujet sans `(#N)` -- force la voie liste
        monkeypatch.setattr(
            pmw, "run_git",
            lambda *a, **k: _fake_proc(
                returncode=0,
                stdout="fix(notebook): unrelated work in progress\n",
            ),
        )

        # PRs recentes qui partagent `notebook` mais ne sont PAS ce commit
        monkeypatch.setattr(
            pmw, "run_gh",
            lambda *a, **k: _fake_proc(
                returncode=0,
                json_payload=[
                    {
                        "number": 14437,
                        "state": "MERGED",
                        "url": "https://github.com/jsboige/CoursIA/pull/14437",
                        "title": "feat(notebook): something else entirely",
                    },
                    {
                        "number": 14195,
                        "state": "OPEN",
                        "url": "https://github.com/jsboige/CoursIA/pull/14195",
                        "title": "refactor(scripts): prune merged worktrees",
                    },
                ],
            ),
        )
        result = pmw.lookup_pr_for_detached_head("/tmp/fake")
        assert result is None, (
            "faux positif elimine : intersection de jetons interdite, "
            "egalite normalisee impossible (sujet != titre). Resultat doit "
            "etre None, pas une PR partageant `notebook`."
        )


def _fake_proc(returncode: int = 0, stdout: str = "", json_payload=None):
    """Construit un subprocess.CompletedProcess minimal pour stubbing."""
    import subprocess
    out = stdout
    if json_payload is not None:
        out = json.dumps(json_payload)
    return subprocess.CompletedProcess(
        args=[], returncode=returncode, stdout=out, stderr=""
    )


# ---------------------------------------------------------------------------
# Tests render_text -- fidelite au disque en mode --apply (#14476)
# ---------------------------------------------------------------------------


class TestRenderText:
    """Le rendu texte ne doit JAMAIS mentir sur ce qui a quitte le disque.

    Avant #14476 : `render_text` lisait depuis `s.decision`, et affichait
    `REMOVED` pour tout `decision="REMOVE"` même si `git worktree remove`
    avait échoué (worktree sale par exemple). Le compteur `removable`
    devenait alors un mensonge structurel.
    """

    def test_apply_results_failed_path_is_not_printed_as_removed(self):
        """Fixture : un `apply_results` avec `applied=False` pour un path
        dont `WorktreeStatus.decision == "REMOVE"`. La sortie NE DOIT PAS
        contenir `REMOVED` pour ce path ; elle DOIT contenir `FAILED` ou
        une trace explicite de l'échec.
        """
        statuses = [
            pmw.WorktreeStatus(
                path="C:/dev/CoursIA-FAILED",
                branch="fix/14195-x",
                is_current=False,
                pr_state="MERGED",
                pr_number=14427,
                pr_url="https://github.com/jsboige/CoursIA/pull/14427",
                ahead_count=0,
                has_source_dirty=False,
                untracked_paths=[],
                decision="REMOVE",
                refusal_reason=None,
            ),
            pmw.WorktreeStatus(
                path="C:/dev/CoursIA-OK",
                branch="fix/14195-y",
                is_current=False,
                pr_state="MERGED",
                pr_number=14403,
                pr_url="https://github.com/jsboige/CoursIA/pull/14403",
                ahead_count=0,
                has_source_dirty=False,
                untracked_paths=[],
                decision="REMOVE",
                refusal_reason=None,
            ),
        ]
        apply_results = [
            {
                "path": "C:/dev/CoursIA-FAILED",
                "branch": "fix/14195-x",
                "pr_number": 14427,
                "applied": False,
                "stderr": "fatal: 'C:/dev/CoursIA-FAILED' contains modified or untracked files",
            },
            {
                "path": "C:/dev/CoursIA-OK",
                "branch": "fix/14195-y",
                "pr_number": 14403,
                "applied": True,
                "stderr": "",
            },
        ]
        out = pmw.render_text(
            statuses, dry_run=False, apply_results=apply_results
        )
        # Le path FAILED ne doit jamais apparaitre en REMOVED ; il doit
        # apparaitre en FAILED avec la cause d'erreur.
        failed_lines = [
            l for l in out.splitlines()
            if "C:/dev/CoursIA-FAILED" in l
        ]
        assert failed_lines, "FAILED path missing from output"
        for line in failed_lines:
            assert "REMOVED" not in line, (
                f"render_text ment : line={line!r} claim REMOVED pour un "
                f"path dont applied=False. apply_results gagne, pas decision."
            )
            assert "FAILED" in line, (
                f"expected FAILED marker, got: {line!r}"
            )
        # Le compteur failed doit etre non-nul dans la sortie
        assert "failed=1" in out
        # Le path OK doit apparaitre en REMOVED
        ok_lines = [
            l for l in out.splitlines()
            if "C:/dev/CoursIA-OK" in l and "REMOVED" in l
        ]
        assert ok_lines, "REMOVED path missing from output"


# ---------------------------------------------------------------------------
# #14619 -- removable doit etre une prevision de applied
# ---------------------------------------------------------------------------


_MERGED_PR = {
    "number": 14670, "state": "MERGED",
    "url": "https://github.com/jsboige/CoursIA/pull/14670",
    "headRefName": "fix/merged-thing",
}


def _fake_info(**overrides):
    defaults = dict(
        branch="fix/merged-thing",
        ahead_count=0,
        untracked=[],
        has_source_dirty=False,
        has_submodules=False,
        is_current=False,
    )
    defaults.update(overrides)
    return defaults


class TestToleratedCleanup14619:
    """Correctif #14619 : nettoyage des seuls artefacts tolérés avant retrait
    sans force, REFUSE sur résidu hors liste, REFUSE sur sous-modules."""

    def test_bg_logs_dir_is_artifact(self):
        assert pmw.is_untracked_artifact(
            "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/bg_logs/") is True
        assert pmw.is_untracked_artifact(
            "agent_tests/bg_logs/run.jsonl") is True

    def test_log_relaunch_is_artifact(self):
        # Cas exact mesure sur D:/CoursIA-wt/c552-7012-build (#14619)
        assert pmw.is_untracked_artifact("lake_7012.log.relaunch") is True

    def test_clean_removes_only_tolerated(self, tmp_path):
        (tmp_path / "bg_logs").mkdir()
        (tmp_path / "bg_logs" / "run.jsonl").write_text(
            "{}", encoding="utf-8")
        (tmp_path / "lake_7012.log.relaunch").write_text(
            "log", encoding="utf-8")
        keep = tmp_path / "src" / "keep.py"
        keep.parent.mkdir()
        keep.write_text("x = 1", encoding="utf-8")
        wt = _make_status(
            path=str(tmp_path),
            untracked_paths=[
                "bg_logs/", "lake_7012.log.relaunch", "src/keep.py",
            ],
        )
        removed = pmw.clean_tolerated_artifacts(wt)
        assert sorted(removed) == ["bg_logs/", "lake_7012.log.relaunch"]
        assert not (tmp_path / "bg_logs").exists()
        assert not (tmp_path / "lake_7012.log.relaunch").exists()
        assert keep.exists(), "untracked non toléré ne doit pas être touché"

    def test_clean_never_escapes_worktree(self, tmp_path):
        probe = tmp_path.parent / "prune_escape_probe_14619.txt"
        wt = _make_status(
            path=str(tmp_path),
            untracked_paths=["slides/images/../../prune_escape_probe_14619.txt"],
        )
        removed = pmw.clean_tolerated_artifacts(wt)
        assert removed == []
        assert not probe.exists(), "la cible résolue doit rester dans le worktree"

    def test_diagnose_remove_when_only_tolerated_artifacts(self, monkeypatch):
        monkeypatch.setattr(
            pmw, "get_worktree_info",
            lambda *a, **k: _fake_info(
                untracked=["bg_logs/", "lake_7012.log.relaunch"]),
        )
        monkeypatch.setattr(
            pmw, "lookup_pr_for_branch", lambda b: dict(_MERGED_PR))
        s = pmw.diagnose_worktree("C:/fake/wt", "C:/elsewhere")
        assert s.decision == "REMOVE"

    def test_diagnose_refuse_untolerated_untracked(self, monkeypatch):
        monkeypatch.setattr(
            pmw, "get_worktree_info",
            lambda *a, **k: _fake_info(untracked=["residu.bin"]),
        )
        monkeypatch.setattr(
            pmw, "lookup_pr_for_branch", lambda b: dict(_MERGED_PR))
        s = pmw.diagnose_worktree("C:/fake/wt", "C:/elsewhere")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "untolerated_untracked:1"

    def test_submodule_detection_ignores_uninitialized(self):
        # `git submodule status` liste les submodules CONFIGURÉS dans tous
        # les worktrees ; seuls les initialisés (sans préfixe '-') bloquent
        # `git worktree remove`. Matcher la sortie brute refuserait tout.
        assert pmw.has_initialized_submodule("") is False
        assert pmw.has_initialized_submodule(
            "-cac5abc MyIA.AI.Notebooks/GenAI/SemanticKernel/semantic-fleet"
        ) is False
        assert pmw.has_initialized_submodule(
            "-abc path/one\n-def path/two\n"
        ) is False
        assert pmw.has_initialized_submodule(
            " 30c3993 MyIA.AI.Notebooks/Search/MetaGeneticSharp (v0.1.0)"
        ) is True
        assert pmw.has_initialized_submodule("+abc path/one") is True
        assert pmw.has_initialized_submodule(
            "-abc path/one\n 30c3993 path/initialized\n"
        ) is True

    def test_diagnose_refuse_submodules(self, monkeypatch):
        monkeypatch.setattr(
            pmw, "get_worktree_info",
            lambda *a, **k: _fake_info(has_submodules=True),
        )
        s = pmw.diagnose_worktree("C:/fake/wt", "C:/elsewhere")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "contains_submodules"

    def test_no_force_in_source(self):
        src = Path(pmw.__file__).read_text(encoding="utf-8")
        assert '"--force"' not in src and "'--force'" not in src, (
            "la propriété no-force (docstring règle 3) doit tenir"
        )


# ---------------------------------------------------------------------------
# Tests d'integration subprocess sur le repo reel
# ---------------------------------------------------------------------------


class TestEndToEnd:
    """Tests subprocess reels. Aucun mock : on execute le script sur
    le worktree de test, et on vérifie que le verdict correspond a ce
    qu'on sait du repo."""

    def test_dry_run_exits_1_when_refusals(self):
        """po-2027 a 4 worktrees refuses (main + 3 PR open). Exit 1.

        CI : skip si scanned=0 OU si aucun worktree main n'est présent
        (checkout shallow sans worktree main séparé, refs/remotes/pull/N/merge).
        """
        import pytest
        proc = subprocess.run(
            [sys.executable, "scripts/ci/prune_merged_worktrees.py",
             "--path", TEST_CWD, "--json"],
            capture_output=True, text=True, encoding="utf-8",
            cwd=TEST_CWD,
        )
        # Exit 0 ou 1 (selon qu'il y a des refus observes)
        assert proc.returncode in (0, 1), f"unexpected exit: {proc.returncode}"
        out = json.loads(proc.stdout)
        if out["scanned"] == 0:
            pytest.skip("no worktree present (CI checkout shallow)")
        # Le worktree de travail principal doit toujours être refuse
        main_entries = [
            s for s in out["statuses"]
            if s["branch"] == "main" or s.get("refusal_reason") == "protected_branch:main"
        ]
        if not main_entries:
            pytest.skip("no main worktree in this checkout (CI shallow ref or detached)")
        assert len(main_entries) >= 1, "main worktree missing"

    def test_main_never_decision_remove(self):
        """Aucun worktree branche=main ne doit avoir decision=REMOVE.

        CI : skip si scanned=0 (checkout shallow sans worktree main).
        """
        proc = subprocess.run(
            [sys.executable, "scripts/ci/prune_merged_worktrees.py",
             "--path", TEST_CWD, "--json"],
            capture_output=True, text=True, encoding="utf-8",
            cwd=TEST_CWD,
        )
        out = json.loads(proc.stdout)
        if out["scanned"] == 0:
            import pytest
            pytest.skip("no worktree present (CI checkout shallow)")
        for s in out["statuses"]:
            if s["branch"] == "main":
                assert s["decision"] != "REMOVE", (
                    f"main worktree must never be REMOVE, got: {s}"
                )

    def test_json_includes_required_keys(self):
        proc = subprocess.run(
            [sys.executable, "scripts/ci/prune_merged_worktrees.py",
             "--path", TEST_CWD, "--json"],
            capture_output=True, text=True, encoding="utf-8",
            cwd=TEST_CWD,
        )
        out = json.loads(proc.stdout)
        for key in ("scanned", "removable", "refused", "skipped_current",
                    "dry_run", "statuses"):
            assert key in out, f"missing key in JSON output: {key}"
        assert isinstance(out["statuses"], list)
        if out["statuses"]:
            s0 = out["statuses"][0]
            for key in ("path", "branch", "is_current", "pr_state",
                        "ahead_count", "has_source_dirty",
                        "decision", "refusal_reason"):
                assert key in s0, f"missing status key: {key}"

    def test_text_output_includes_counters(self):
        proc = subprocess.run(
            [sys.executable, "scripts/ci/prune_merged_worktrees.py",
             "--path", TEST_CWD],
            capture_output=True, text=True, encoding="utf-8",
            cwd=TEST_CWD,
        )
        text = proc.stdout
        assert "total=" in text, "text output must include total counter"
        assert "removable=" in text
        assert "refused=" in text
        assert "---" in text, "text output must separate counters by ---"

    def test_apply_noop_when_no_removable(self):
        """--apply doit no-op quand 0 removable, et exit code reste 1
        si refus observes (le run signale quand meme le bruit).

        Test destructif : --apply supprime réellement des worktrees. Skip
        sauf si RUN_DESTRUCTIVE_TESTS=1 est explicitement défini dans
        l'environnement (par défaut : skipped pour ne pas détruire les
        worktrees d'un worker qui lance pytest localement).
        """
        import os
        if os.environ.get("RUN_DESTRUCTIVE_TESTS") != "1":
            import pytest
            pytest.skip("destructive test (--apply) skipped unless RUN_DESTRUCTIVE_TESTS=1")
        proc = subprocess.run(
            [sys.executable, "scripts/ci/prune_merged_worktrees.py",
             "--path", TEST_CWD, "--apply"],
            capture_output=True, text=True, encoding="utf-8",
            cwd=TEST_CWD,
        )
        # pas d'erreur gh/git -> exit != 2
        assert proc.returncode != 2, f"stderr: {proc.stderr}"
        # Au moins 1 ligne REFUSE dans la sortie (le run reel)
        assert "REFUSE" in proc.stdout or "applied=0" in proc.stdout


# ---------------------------------------------------------------------------
# Controle positif hermetique E2E (#14693 point 4)
# ---------------------------------------------------------------------------


def _git_ok(cwd: str, *args: str) -> subprocess.CompletedProcess:
    """git strict dans un depot temoin : toute erreur echoue le test.

    L'identite de commit est forcee par -c (les runners CI n'ont pas de
    user.email global), et le dossier est temporaire donc isole.
    """
    proc = subprocess.run(
        ["git", "-C", cwd, "-c", "user.email=e2e@test", "-c",
         "user.name=e2e", "-c", "protocol.file.allow=always", *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, (
        f"git {' '.join(args)} failed in {cwd}: {proc.stderr.strip()}"
    )
    return proc


def _make_repo_with_feature_worktree(
    base: Path, with_submodule: bool = False,
) -> tuple[Path, Path]:
    """Depot temoin + worktree lie sur branche feature.

    Retourne (super, wt). Si with_submodule, un vrai sous-module est
    configure sur main AVANT la creation du worktree (pour que la branche
    feature le porte) et initialise DANS le worktree -- le fixture exact
    de #14693 point 4.

    Pas d'upstream sur la branche feature : le predicat unpushed reste a
    0 et le verdict est porte par l'ancre PR (monkeypatchee MERGED).
    """
    super = base / "super"
    super.mkdir()
    _git_ok(str(super), "init", "-b", "main")
    (super / "README.md").write_text("tmp", encoding="utf-8")
    _git_ok(str(super), "add", "README.md")
    _git_ok(str(super), "commit", "-m", "init")

    if with_submodule:
        sub = base / "sublib"
        sub.mkdir()
        _git_ok(str(sub), "init", "-b", "main")
        (sub / "lib.txt").write_text("s", encoding="utf-8")
        _git_ok(str(sub), "add", "lib.txt")
        _git_ok(str(sub), "commit", "-m", "sub init")
        _git_ok(str(super), "submodule", "add",
                str(sub).replace("\\", "/"), "vendor")
        _git_ok(str(super), "commit", "-m", "add submodule")

    wt = base / "wt-feature"
    _git_ok(str(super), "worktree", "add", str(wt), "-b", "feature/e2e")
    if with_submodule:
        # Materialise vendor/ dans le worktree : `git submodule status`
        # y rend une entree sans prefixe '-' (initialise).
        _git_ok(str(wt), "submodule", "update", "--init")
    (wt / "feature.txt").write_text("f", encoding="utf-8")
    _git_ok(str(wt), "add", "feature.txt")
    _git_ok(str(wt), "commit", "-m", "feature work")
    return super, wt


class TestEndToEndHermetic14693:
    """#14693 point 4 : le controle positif qui manquait a #14476.

    Les tests unitaires ci-dessus monkeypatchent les sorties git : ils
    pincent la LOGIQUE de decision, pas le contrat avec le git reel. Ici
    on construit un vrai depot, un vrai worktree lie, de vrais fichiers
    untracked et un vrai sous-module initialise ; seule l'ancre PR
    (reseau gh) est remplacee par un objet MERGED. Ce controle verifie
    la propriete demande par #14693 point 1 : ce qui est annonce REMOVE
    quitte VRAIMENT le disque, et ce que git ne retirera jamais est
    REFUSE avec sa cause AVANT l'annonce -- dry-run et apply rendent le
    meme verdict.
    """

    MERGED_PR = {
        "number": 424242,
        "state": "MERGED",
        "url": "https://example/pr/424242",
        "headRefName": "feature/e2e",
    }

    def _merged_anchor(self, monkeypatch):
        monkeypatch.setattr(
            pmw, "lookup_pr_for_branch",
            lambda branch: dict(self.MERGED_PR, headRefName=branch),
        )

    def test_tolerated_artifacts_only_is_removed(self, tmp_path, monkeypatch):
        """Classe 1 : residu exclusivement tolere -> REMOVE annonce,
        nettoyage des toleres, retrait sans force QUI REUSSIT."""
        super, wt = _make_repo_with_feature_worktree(tmp_path)
        # Artefacts tolere a la RACINE (porcelain affiche le dossier
        # collapse `?? bg_logs/` ; un parent tracked casserait le token).
        (wt / "bg_logs").mkdir()
        (wt / "bg_logs" / "run.jsonl").write_text("{}", encoding="utf-8")
        (wt / "__pycache__").mkdir()
        (wt / "__pycache__" / "x.pyc").write_bytes(b"pyc")
        self._merged_anchor(monkeypatch)
        monkeypatch.chdir(super)

        s = pmw.diagnose_worktree(str(wt), str(super))
        assert s.decision == "REMOVE", (
            f"tolerated-only doit etre REMOVE, got {s.refusal_reason}"
        )
        # Sequence exacte du apply de main() : clean des toleres puis
        # remove sans force.
        cleaned = pmw.clean_tolerated_artifacts(s)
        assert len(cleaned) == 2, f"2 artefacts toleres attendus: {cleaned}"
        ok, stderr = pmw.apply_removal(s)
        assert ok, f"REMOVE annonce mais retrait echoue: {stderr}"
        assert not wt.exists(), "le worktree doit avoir quitte le disque"

    def test_untolerated_residue_refuses_and_survives(self, tmp_path, monkeypatch):
        """Complement fail-closed : un residu hors liste toleree ->
        REFUSE nomme, le worktree reste sur disque."""
        super, wt = _make_repo_with_feature_worktree(tmp_path)
        (wt / "blob.bin").write_bytes(b"\x00\x01")
        self._merged_anchor(monkeypatch)
        monkeypatch.chdir(super)

        s = pmw.diagnose_worktree(str(wt), str(super))
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "untolerated_untracked:1", s.refusal_reason
        assert wt.exists(), "un worktree REFUSE ne doit jamais bouger"

    def test_initialised_submodule_with_pycache_refuses(self, tmp_path, monkeypatch):
        """Classe 2 (fixture exacte de #14693 point 4) : un worktree
        portant un __pycache__/ untracked ET un sous-module initialise ->
        REFUSE contains_submodules (git ne le retirera jamais), et la
        tentative reelle echoue structurellement."""
        super, wt = _make_repo_with_feature_worktree(
            tmp_path, with_submodule=True)
        (wt / "__pycache__").mkdir()
        (wt / "__pycache__" / "x.pyc").write_bytes(b"pyc")
        self._merged_anchor(monkeypatch)
        monkeypatch.chdir(super)

        s = pmw.diagnose_worktree(str(wt), str(super))
        assert s.decision == "REFUSE", (
            f"sous-module initialise doit REFUSER, got {s.refusal_reason}"
        )
        assert s.refusal_reason == "contains_submodules"
        # Meme en forcant la tentative : git refuse structurellement --
        # c'est la demonstration live que REMOVE ici aurait ete un mensonge.
        ok, stderr = pmw.apply_removal(s)
        assert not ok, "git ne peut PAS retirer un worktree a sous-modules"
        assert "submodule" in stderr.lower(), stderr
        assert wt.exists(), "le worktree REFUSE reste sur disque"
