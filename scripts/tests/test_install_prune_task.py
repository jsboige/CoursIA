#!/usr/bin/env python3
r"""Tests de l'installateur de tache planifiee prune (#14473).

Pinent :
1. la garde de securite : --install REFUSE si le script cible ne contient
   pas le fix #14476 (resolution par numero + _normalize, cf #14481) --
   un cron --apply quotidien ne doit JAMAIS deployer l'attribution
   fausse par intersection de jetons ;
2. l'idempotence : schtasks /Create /F (relançable sans doublon) ;
3. la commande de tache appelle bien --run (le mode journalisant) avec le
   --repo explicit, et l'organe en --apply vient de cmd_run seulement ;
4. le journal est horodate a un chemin nomme (LOCALAPPDATA).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import install_prune_task as ipt  # noqa: E402


# ---------------------------------------------------------------------------
# garde de securite #14476
# ---------------------------------------------------------------------------

class TestPruneFixGuard:
    def test_refuse_quand_le_fix_est_absent(self, tmp_path):
        repo = tmp_path / "CoursIA"
        (repo / "scripts" / "ci").mkdir(parents=True)
        # version SANS le fix : l'heuristique d'intersection d'origine
        (repo / "scripts" / "ci" / "prune_merged_worktrees.py").write_text(
            "def lookup_pr_for_detached_head():\n"
            "    title_tokens & subj_tokens  # intersection de jetons\n",
            encoding="utf-8")
        ok, msg = ipt.check_prune_fix_present(repo)
        assert not ok
        assert "#14476" in msg or "#14481" in msg

    def test_accepte_quand_le_fix_est_present(self, tmp_path):
        repo = tmp_path / "CoursIA"
        (repo / "scripts" / "ci").mkdir(parents=True)
        # extrait fidele des DEUX voies du fix #14481 telles que mergees
        # (le marqueur historique _normalize_subject etait une fixture
        # circulaire : le test ecrivait lui-meme le symbole attendu)
        (repo / "scripts" / "ci" / "prune_merged_worktrees.py").write_text(
            "# 1. Resolution directe par numero extractible du sujet\n"
            "def lookup_pr_for_detached_head():\n"
            "    def _normalize(s: str) -> str:\n"
            "        return s.strip().lower()\n"
            "    return None\n",
            encoding="utf-8")
        ok, _ = ipt.check_prune_fix_present(repo)
        assert ok

    def test_refuse_si_une_seule_voie_du_fix_est_presente(self, tmp_path):
        """Un seul des deux marqueurs (ex : _normalize sans la resolution
        par numero) ne doit pas suffire -- la voie 1 est la protection
        principale contre l'attribution fausse."""
        repo = tmp_path / "CoursIA"
        (repo / "scripts" / "ci").mkdir(parents=True)
        (repo / "scripts" / "ci" / "prune_merged_worktrees.py").write_text(
            "def _normalize(s: str) -> str:\n    return s.strip().lower()\n",
            encoding="utf-8")
        ok, msg = ipt.check_prune_fix_present(repo)
        assert not ok
        assert "Resolution directe par numero" in msg

    def test_garde_accepte_le_vrai_fichier_du_depot(self):
        """Anti-dérive : la garde doit rester satisfaisable par le VRAI
        scripts/ci/prune_merged_worktrees.py du depot (incident 2026-09-04 :
        le marqueur '_normalize_subject' ne correspondait a aucun symbole
        merge -- refus perpetual, meme sur main frais). Si ce test echoue,
        un refactor a renomme les voies du fix : resynchroniser
        REQUIRED_FIX_MARKERS."""
        repo = Path(__file__).resolve().parents[2]
        ok, msg = ipt.check_prune_fix_present(repo)
        assert ok, f"la garde refuse le fichier reel du depot : {msg}"

    def test_refuse_si_le_script_est_absent(self, tmp_path):
        ok, msg = ipt.check_prune_fix_present(tmp_path)
        assert not ok and "introuvable" in msg

    def test_cmd_install_refuse_sans_fix(self, tmp_path, monkeypatch, capsys):
        """Le mode --install entier doit exit 2 AVANT tout appel schtasks."""
        repo = tmp_path / "CoursIA"
        (repo / "scripts" / "ci").mkdir(parents=True)
        (repo / "scripts" / "ci" / "prune_merged_worktrees.py").write_text(
            "# vieille version", encoding="utf-8")
        called = []
        monkeypatch.setattr(ipt, "_run", lambda cmd, **kw: called.append(cmd)
                            or subprocess.CompletedProcess(cmd, 0, stdout="", stderr=""))
        rc = ipt.cmd_install(repo, "03:17")
        assert rc == 2
        assert called == []  # aucun effet de bord planificateur
        assert "REFUSE" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# construction de la tache / idempotence
# ---------------------------------------------------------------------------

class TestTaskConstruction:
    def test_commande_de_tache_est_le_mode_run_avec_repo_explicite(self, tmp_path):
        cmd = ipt.task_command(tmp_path)
        assert "--run" in cmd and "--repo" in cmd
        # le python interpreteur est absolu (contexte planificateur sans PATH venv)
        assert Path(cmd[0]).is_absolute()
        # JAMAIS --apply dans la ligne de tache : il vient de cmd_run
        assert "--apply" not in cmd

    def test_schtasks_create_est_force_donc_idempotent(self, tmp_path):
        line = ipt.build_schtasks_install(ipt.task_command(tmp_path), "03:17")
        assert line[0] == "schtasks" and "/Create" in line and "/F" in line
        assert "/SC" in line and "DAILY" in line
        assert "/TN" in line and ipt.TASK_NAME in line
        # quotidienne a l'heure demandee
        i = line.index("/ST")
        assert line[i + 1] == "03:17"

    def test_nom_de_tache_namespaced(self):
        assert "CoursIA" in ipt.TASK_NAME


# ---------------------------------------------------------------------------
# journal
# ---------------------------------------------------------------------------

class TestJournal:
    def test_chemin_nomme_et_hordate(self, tmp_path, monkeypatch):
        monkeypatch.setattr(ipt, "LOG_DIR", tmp_path)
        import datetime as dt
        p = ipt.log_path_for(dt.date(2026, 9, 3))
        assert p == tmp_path / "prune_20260903.log"
        assert p.name.startswith("prune_")

    def test_cmd_run_journalise_et_transmet_le_code_retour(self, tmp_path, monkeypatch):
        repo = tmp_path / "CoursIA"
        (repo / "scripts" / "ci").mkdir(parents=True)
        target = repo / "scripts" / "ci" / "prune_merged_worktrees.py"
        target.write_text("print('organ output')\n", encoding="utf-8")
        monkeypatch.setattr(ipt, "LOG_DIR", tmp_path / "logs")

        recorded = {}

        def fake_run(cmd, stdout=None, stderr=None, **kw):
            recorded["cmd"] = cmd
            recorded["stdout"] = stdout
            # simule un refus d'organe (worktree vivant) -> rc=1
            stdout.write("REFUSE uncommitted_source_changes\n")
            return subprocess.CompletedProcess(cmd, 1)

        monkeypatch.setattr(subprocess, "run", fake_run)
        rc = ipt.cmd_run(repo)
        assert rc == 1  # le code de l'organe traverse
        assert recorded["cmd"][-2:] == ["--apply"] or "--apply" in recorded["cmd"]
        assert str(repo) in recorded["cmd"]
        log = (tmp_path / "logs").glob("prune_*.log")
        logs = list(log)
        assert len(logs) == 1
        content = logs[0].read_text(encoding="utf-8")
        assert "run start" in content and "run end rc=1" in content
        assert "REFUSE uncommitted_source_changes" in content
