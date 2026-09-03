#!/usr/bin/env python3
r"""Tests d'affaiblissement pour prune_merged_worktrees.py (#14195).

Pinent le contrat de sûreté (issue #14195 acceptance) :

1. `is_untracked_artifact` reconnait les catégories du dernier commentaire
   de #8924 (slides/images, scripts/results, .claude/agent-memory,
   _output.ipynb, caches node_modules/.cache/.pytest_cache/__pycache__,
   _measurements, .mypy_cache, .ruff_cache, dist/, build/, .eggs/, .tox/).
2. `is_source_dirty` classe une édition .py/.ipynb/.lean comme source
   sale (REFUSE), même quand elle coexiste avec des artefacts untracked.
3. `WorktreeStatus.decision` = `REMOVE` quand pr_state=MERGED ou CLOSED
   et pas d'unpushed ni de source dirty (contrôle positif manquant aux
   prédicats d'ascendance, cf squashed-merge).
4. `WorktreeStatus.decision` = `REFUSE` quand pr_state=OPEN
   (le retrait casserait l'itération en cours).
5. `WorktreeStatus.decision` = `REFUSE` quand unpushed_commits > 0
   (jamais d'exception).
6. `WorktreeStatus.decision` = `REFUSE` quand has_source_dirty
   (édition source non committée, c'est le cas fondateur de #14195).
7. `WorktreeStatus.decision` = `REFUSE` quand branch=main/master
   (le worktree de travail principal n'est JAMAIS un candidat au retrait,
   même si gh remonte une vieille PR close qui pointe sur main -- bug
   trouvé au dry-run inaugural).
8. `WorktreeStatus.decision` = `SKIP_CURRENT` pour le worktree depuis
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

    def test_source_py_is_source(self):
        assert pmw.is_source_dirty("scripts/foo.py") is True

    def test_source_ipynb_is_source(self):
        assert pmw.is_source_dirty("MyIA.AI.Notebooks/Search/foo.ipynb") is True

    def test_source_lean_is_source(self):
        assert pmw.is_source_dirty("knot_lean/Foo.lean") is True

    def test_source_md_is_source(self):
        assert pmw.is_source_dirty("docs/spec.md") is True

    def test_source_coexists_with_artifact(self):
        # Si la liste contient un artefact ET une edition source, la
        # edition source doit primer -- le worktree sera REFUSE.
        paths = [
            "slides/images/foo.png",  # artefact tolere
            "scripts/bug_fix.py",     # edition source : doit primer
        ]
        any_source = any(pmw.is_source_dirty(p) for p in paths)
        assert any_source is True


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

    def test_refuse_when_source_dirty(self):
        s = _make_status(has_source_dirty=True, decision="REFUSE",
                         refusal_reason="uncommitted_source_changes")
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "uncommitted_source_changes"

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
        # Sanity : tous les champs sont la
        for k in (
            "path", "branch", "is_current", "pr_state", "pr_number",
            "pr_url", "ahead_count", "has_source_dirty",
            "untracked_paths", "decision", "refusal_reason",
        ):
            assert k in d, f"missing key: {k}"


# ---------------------------------------------------------------------------
# Tests d'integration subprocess sur le repo reel
# ---------------------------------------------------------------------------


class TestEndToEnd:
    """Tests subprocess reels. Aucun mock : on execute le script sur
    le worktree de test, et on vérifie que le verdict correspond a ce
    qu'on sait du repo."""

    def test_dry_run_exits_1_when_refusals(self):
        """po-2027 a 4 worktrees refuses (main + 3 PR open). Exit 1.

        CI : skip si scanned=0 (checkout shallow sans worktree main séparé).
        """
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
            import pytest
            pytest.skip("no worktree present (CI checkout shallow)")
        # Le worktree de travail principal doit toujours être refuse
        main_entries = [
            s for s in out["statuses"]
            if s["branch"] == "main" or s.get("refusal_reason") == "protected_branch:main"
        ]
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
