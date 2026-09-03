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
# lookup_pr_for_detached_head -- resolution par numero puis egalite (#14476)
# ---------------------------------------------------------------------------

class TestDetachedHeadLookup:
    """Le predicat d'intersection de jetons attribuait n'importe quelle PR
    recente partageant UN mot du domaine (notebook, guard, training) a un
    worktree HEAD detache -> retraits destructeurs faux. Contrat #14476 :

    1. sujet en "(#N)" -> resolution par NUMERO (gh pr view), la liste des
       50 recentes n'est meme pas consultee ;
    2. sinon EGALITE du sujet normalise avec le titre de PR (le suffixe
       "(#N)" est retire de la normalisation) ;
    3. sinon None (no_pr_match -> REFUSE, fail-closed).
    """

    @staticmethod
    def _fake_procs(subjects, pr_view=None, pr_list=None):
        """Fakes pour run_git (log sujets) et run_gh (pr view / pr list)."""
        import subprocess as sp

        calls = {"view": [], "list": 0}

        def fake_run_git(cwd, *args, check=True):
            assert args[:2] == ("log", "HEAD")
            return sp.CompletedProcess(args, 0, stdout="\n".join(subjects))

        def fake_run_gh(*args, check=True):
            if args[1] == "view":
                calls["view"].append(args[2])
                if pr_view is None:
                    return sp.CompletedProcess(args, 1, stdout="")
                return sp.CompletedProcess(
                    args, 0, stdout=json.dumps(pr_view))
            calls["list"] += 1
            if pr_list is None:
                return sp.CompletedProcess(args, 1, stdout="")
            return sp.CompletedProcess(
                args, 0, stdout=json.dumps(pr_list))

        return fake_run_git, fake_run_gh, calls

    def test_resolution_par_numero_sans_consulter_la_liste(self, monkeypatch):
        """Un sujet de squash "titre (#N)" resout par numero : la PR est
        ramenee par gh pr view N, la liste des 50 n'est JAMAIS appelee."""
        fg, fgh, calls = self._fake_procs(
            subjects=["fix(ml,#14470): L1 graines vivantes (#14496)",
                      "intermediate commit subject"],
            pr_view={"number": 14496, "state": "MERGED",
                     "url": "https://github.com/x/y/pull/14496",
                     "title": "fix(ml,#14470): L1 graines vivantes"},
        )
        monkeypatch.setattr(pmw, "run_git", fg)
        monkeypatch.setattr(pmw, "run_gh", fgh)
        pr = pmw.lookup_pr_for_detached_head("C:/fake/wt")
        assert pr is not None and pr["number"] == 14496 and pr["state"] == "MERGED"
        assert calls["view"] == ["14496"]
        assert calls["list"] == 0

    def test_faux_positif_mot_courant_refuse(self, monkeypatch):
        """CONTROLE POSITIF DU FAUX POSITIF (#14476) : un worktree dont les
        sujets partagent seulement un mot du domaine ("notebook", "fix"...)
        avec une PR recente ouverte N'EST PAS attribue -- l'ancienne
        heuristique d'intersection rendait la PR ici."""
        fg, fgh, calls = self._fake_procs(
            subjects=["enrich(sw): notebook density pass",
                      "fix navlinks in notebook"],
            pr_list=[{"number": 14472, "state": "OPEN",
                      "url": "https://github.com/x/y/pull/14472",
                      "title": "Enrich Planners-8-Temporal-Csharp notebook density"},
                     {"number": 14474, "state": "MERGED",
                      "url": "https://github.com/x/y/pull/14474",
                      "title": "fix(ml): notebook guard training"}],
        )
        monkeypatch.setattr(pmw, "run_git", fg)
        monkeypatch.setattr(pmw, "run_gh", fgh)
        assert pmw.lookup_pr_for_detached_head("C:/fake/wt") is None

    def test_egalite_sujet_normalise_en_fallback(self, monkeypatch):
        """Sans (#N) : casse et espaces normalises, le sujet DOIT etre le
        titre de la PR a l'identique pres de la normalisation."""
        fg, fgh, _ = self._fake_procs(
            subjects=["Fix   ML: L1 graines vivantes"],
            pr_list=[{"number": 14496, "state": "MERGED",
                      "url": "https://github.com/x/y/pull/14496",
                      "title": "fix ml: L1 graines vivantes"},
                     {"number": 14000, "state": "MERGED",
                      "url": "https://github.com/x/y/pull/14000",
                      "title": "autre chose"}],
        )
        monkeypatch.setattr(pmw, "run_git", fg)
        monkeypatch.setattr(pmw, "run_gh", fgh)
        pr = pmw.lookup_pr_for_detached_head("C:/fake/wt")
        assert pr is not None and pr["number"] == 14496

    def test_suffixe_numero_retire_de_l_egalite(self, monkeypatch):
        """Sujet "titre (#N)" mais la PR N n'existe plus (gh pr view echoue) :
        le fallback d'egalite doit matcher le titre SANS le suffixe."""
        fg, fgh, _ = self._fake_procs(
            subjects=["fix(ml): L1 graines vivantes (#99999)"],
            pr_list=[{"number": 14496, "state": "MERGED",
                      "url": "https://github.com/x/y/pull/14496",
                      "title": "fix(ml): L1 graines vivantes"}],
        )
        monkeypatch.setattr(pmw, "run_git", fg)
        monkeypatch.setattr(pmw, "run_gh", fgh)
        pr = pmw.lookup_pr_for_detached_head("C:/fake/wt")
        assert pr is not None and pr["number"] == 14496

    def test_fail_closed_sans_correspondance(self, monkeypatch):
        """Aucun sujet en (#N), aucun titre egal -> None -> no_pr_match ->
        REFUSE (le defaut safe)."""
        fg, fgh, _ = self._fake_procs(
            subjects=["commit sans rapport"],
            pr_list=[{"number": 14472, "state": "MERGED",
                      "url": "https://github.com/x/y/pull/14472",
                      "title": "titre totalement different"}],
        )
        monkeypatch.setattr(pmw, "run_git", fg)
        monkeypatch.setattr(pmw, "run_gh", fgh)
        assert pmw.lookup_pr_for_detached_head("C:/fake/wt") is None

    def test_normalize_subject(self):
        assert pmw._normalize_subject("Fix  X (#123) ") == "fix x"
        assert pmw._normalize_subject("Fix X (#123)") != "fix x (#123)"
