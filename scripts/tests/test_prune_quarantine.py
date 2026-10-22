#!/usr/bin/env python3
r"""Tests de la voie de decontamination par quarantaine (#21743).

Pinent le contrat de surete des quatre conditions de l'issue :

1. PREUVE de preservation -- apres le deplacement, les objets du
   sous-module sont encore lisibles (`count-objects` non vide, pas
   d'`objects/info/alternates` qui casserait la chaine de resolution).
2. PERIMETRE -- la racine de quarantaine est refusee si elle vit DANS le
   depot ou DANS le worktree retire (elle y perdrait les objets qu'elle
   pretend preserver).
3. EMPLACEMENT -- idem : hors depot, hors worktree.
4. OPT-IN -- la decontamination n'est jamais un effet de bord du
   `--apply` ; la purge est une voie NOMMEE (`--purge-quarantine`), qui
   refuse une racine qu'elle n'a pas creee (marqueur).

Run : python -m pytest scripts/tests/test_prune_quarantine.py
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers : fabriquer de vrais gitdirs (la lisibilite des objets se mesure,
# elle ne se simule pas -- c'est tout l'objet de la condition 1)
# ---------------------------------------------------------------------------


def _git(*args, cwd=None):
    return subprocess.run(
        ["git", *args], cwd=cwd, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


def _real_worktree(root: Path) -> Path:
    """Un worktree git reel : `rev-parse --absolute-git-dir` y repond."""
    wt = root / "wt"
    wt.mkdir(parents=True)
    proc = _git("init", "-q", str(wt))
    assert proc.returncode == 0, proc.stderr
    return wt


def _bare_submodules(wt: Path, names: list[str]) -> Path:
    """Cree `<gitdir>/modules/<name>` avec de VRAIS objets, comme git le fait.

    Un worktree lie qui a initialise un sous-module porte son gitdir dans
    `<gitdir-du-worktree>/modules/<nom>` : c'est ce repertoire que le
    deplacement en quarantaine doit lever sans perdre d'objet.
    """
    modules = pmw.worktree_gitdir(str(wt)) / "modules"
    modules.mkdir(parents=True, exist_ok=True)
    seed = wt.parent / "seed.txt"
    seed.write_text("contenu a objectiver\n", encoding="utf-8")
    for name in names:
        sub = modules / name
        proc = _git("init", "-q", "--bare", str(sub))
        assert proc.returncode == 0, proc.stderr
        proc = _git("--git-dir", str(sub), "hash-object", "-w", str(seed))
        assert proc.returncode == 0, proc.stderr
        assert proc.stdout.strip(), "hash-object doit ecrire un objet"
    return modules


def _count_objects(gitdir: Path) -> int:
    proc = _git("--git-dir", str(gitdir), "count-objects", "-v")
    assert proc.returncode == 0, proc.stderr
    total = 0
    for line in proc.stdout.splitlines():
        if line.startswith(("count:", "in-pack:")):
            total += int(line.split(":", 1)[1].strip() or 0)
    return total


# ---------------------------------------------------------------------------
# Condition 3/4 : emplacement et racine de quarantaine
# ---------------------------------------------------------------------------


class TestQuarantineRoot:
    def test_defaut_suit_localappdata(self, tmp_path, monkeypatch):
        monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
        assert pmw.default_quarantine_root() == (
            tmp_path / "CoursIA" / "prune_quarantine")

    def test_defaut_repli_home_sans_localappdata(self, tmp_path, monkeypatch):
        monkeypatch.delenv("LOCALAPPDATA", raising=False)
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert pmw.default_quarantine_root() == (
            tmp_path / ".local" / "share" / "CoursIA" / "prune_quarantine")

    def test_racine_dans_le_depot_refusee(self, tmp_path):
        repo = tmp_path / "repo"
        repo.mkdir()
        reason = pmw.quarantine_root_refusal(
            repo / "quarantine", repo_root=str(repo))
        assert reason == "quarantine-root-inside-repo"

    def test_racine_egale_au_depot_refusee(self, tmp_path):
        repo = tmp_path / "repo"
        repo.mkdir()
        assert pmw.quarantine_root_refusal(
            repo, repo_root=str(repo)) == "quarantine-root-inside-repo"

    def test_racine_dans_le_worktree_refusee(self, tmp_path):
        wt = tmp_path / "wt"
        wt.mkdir()
        assert pmw.quarantine_root_refusal(
            wt / "q", None, wt_path=str(wt)) == "quarantine-root-inside-worktree"

    def test_racine_hors_depot_et_hors_worktree_acceptee(self, tmp_path):
        repo = tmp_path / "repo"
        wt = tmp_path / "wt"
        repo.mkdir()
        wt.mkdir()
        assert pmw.quarantine_root_refusal(
            tmp_path / "q", repo_root=str(repo), wt_path=str(wt)) is None


# ---------------------------------------------------------------------------
# Condition 1 : preuve de preservation
# ---------------------------------------------------------------------------


class TestPreservationProof:
    def test_gitdir_absent_des_objets(self, tmp_path):
        gitdir = tmp_path / "g"
        gitdir.mkdir()
        assert pmw._gitdir_is_readable(gitdir) == (False, "objects-absent")

    def test_gitdir_avec_alternates_refuse(self, tmp_path):
        gitdir = tmp_path / "g"
        (gitdir / "objects" / "info").mkdir(parents=True)
        (gitdir / "objects" / "info" / "alternates").write_text(
            "/ailleurs/objects\n", encoding="utf-8")
        assert pmw._gitdir_is_readable(gitdir) == (False, "objects-alternates")

    def test_gitdir_vide_n_est_pas_une_preservation(self, tmp_path):
        """0 objet = le deplacement aurait vide la copie : refus, pas succes."""
        gitdir = tmp_path / "g"
        _git("init", "-q", "--bare", str(gitdir))
        assert pmw._gitdir_is_readable(gitdir) == (False, "objects-empty")

    def test_gitdir_avec_objets_est_lisible(self, tmp_path):
        gitdir = tmp_path / "g"
        _git("init", "-q", "--bare", str(gitdir))
        seed = tmp_path / "s.txt"
        seed.write_text("x\n", encoding="utf-8")
        _git("--git-dir", str(gitdir), "hash-object", "-w", str(seed))
        ok, why = pmw._gitdir_is_readable(gitdir)
        assert (ok, why) == (True, "")


# ---------------------------------------------------------------------------
# Deplacement (le geste qui leve le garde de git)
# ---------------------------------------------------------------------------


class TestQuarantineWorktreeModules:
    def test_sans_modules_est_un_no_op(self, tmp_path):
        wt = _real_worktree(tmp_path)
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is True and msg == ""
        assert info == {"quarantine": None, "modules": [], "preserved": True}
        assert not (tmp_path / "q").exists(), "rien ne doit etre cree"

    def test_modules_deplaces_et_objets_preserves(self, tmp_path):
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["Argumentum"])
        before = _count_objects(modules / "Argumentum")
        assert before > 0

        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest", repo_root=str(tmp_path / "wt"))
        assert ok is True, msg
        assert info["preserved"] is True
        assert [m["readable"] for m in info["modules"]] == [True]

        moved = Path(info["quarantine"]) / "modules" / "Argumentum"
        assert moved.is_dir(), "le gitdir est DEPLACE, pas supprime"
        assert _count_objects(moved) == before, "aucun objet perdu"
        assert not modules.exists(), "le garde de git est bien leve"
        assert (tmp_path / "q" / pmw.QUARANTINE_MARKER).exists()

    def test_destination_existante_refusee(self, tmp_path):
        wt = _real_worktree(tmp_path)
        _bare_submodules(wt, ["A"])
        (tmp_path / "q" / "dest").mkdir(parents=True)
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-destination-exists"
        assert info is None
        assert (pmw.worktree_gitdir(str(wt)) / "modules" / "A").is_dir(), (
            "un refus ne deplace rien")

    def test_modules_vide_refuse(self, tmp_path):
        """Un `modules/` sans sous-gitdir ne preserve rien : on le dit."""
        wt = _real_worktree(tmp_path)
        (pmw.worktree_gitdir(str(wt)) / "modules").mkdir()
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-empty-modules"
        assert info["preserved"] is False

    def test_submodule_en_alternates_refuse_et_rien_ne_bouge(self, tmp_path):
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["A"])
        (modules / "A" / "objects" / "info" / "alternates").write_text(
            "/ailleurs\n", encoding="utf-8")
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-unreadable:objects-alternates"
        assert info["preserved"] is False

    def test_racine_dans_le_worktree_refusee_avant_tout_deplacement(
            self, tmp_path):
        wt = _real_worktree(tmp_path)
        _bare_submodules(wt, ["A"])
        ok, msg, _ = pmw.quarantine_worktree_modules(
            str(wt), wt / "q", "dest")
        assert ok is False
        assert msg == "quarantine-root-inside-worktree"
        assert (pmw.worktree_gitdir(str(wt)) / "modules" / "A").is_dir()


# ---------------------------------------------------------------------------
# Condition 4 : le drapeau ATTEINT le diagnostic (il est parse, pas perime)
# ---------------------------------------------------------------------------


class TestFlagReachesDiagnosis:
    """Un drapeau parse mais jamais transmis est indiscernable d'un drapeau
    absent : c'est exactement ce que le dry-run mesurait encore
    (`contains_submodules: 2` avec ET sans `--quarantine-submodules`)."""

    def _info(self):
        return {
            "is_current": False,
            "branch": "feature/x",
            "ahead_count": 0,
            "has_source_dirty": True,
            "untracked": [],
            "has_submodules": True,
            "blocking_untracked": [],
            "ignored_extra": [],
            "lane_owner": None,
        }

    def test_sans_drapeau_contains_submodules_refuse(self, monkeypatch):
        monkeypatch.setattr(pmw, "get_worktree_info",
                            lambda *a, **k: self._info())
        s = pmw.diagnose_worktree("wt", "cur",
                                  quarantine_submodules=False)
        assert s.decision == "REFUSE"
        assert s.refusal_reason == "contains_submodules"

    def test_avec_drapeau_le_garde_sous_module_est_leve(self, monkeypatch):
        """Meme entree, drapeau arme : le refus `contains_submodules`
        disparait et le predicat suivant decide (source sale ici, sans
        aucun appel reseau)."""
        monkeypatch.setattr(pmw, "get_worktree_info",
                            lambda *a, **k: self._info())
        s = pmw.diagnose_worktree("wt", "cur",
                                  quarantine_submodules=True)
        assert s.refusal_reason != "contains_submodules"
        assert s.refusal_reason == "uncommitted_source_changes"

    def test_main_transmet_le_drapeau_au_diagnostic(self, monkeypatch):
        """Le cablage `main()` -> `diagnose_worktree` est verifie par le
        fait : sans lui, le dry-run avec drapeau rend les memes comptes
        qu'apres retrait du drapeau."""
        seen = {}

        def _spy(wt_path, current_path, **kwargs):
            seen.update(kwargs)
            raise RuntimeError("arret du test apres capture")

        monkeypatch.setattr(pmw, "diagnose_worktree", _spy)
        monkeypatch.setattr(pmw, "probe_gh_availability", lambda: None)
        monkeypatch.setattr(pmw, "list_worktrees",
                            lambda *a, **k: [{"path": "wt",
                                              "head_sha": "abc"}])
        monkeypatch.setattr(sys, "argv", ["prune", "--quarantine-submodules"])
        rc = pmw.main()
        assert rc == 2, "le RuntimeError du spy est rapporte, pas avale"
        assert seen.get("quarantine_submodules") is True


# ---------------------------------------------------------------------------
# Purge : voie nommee, fail-closed sur une racine qui n'est pas la notre
# ---------------------------------------------------------------------------


class TestPurgeQuarantine:
    def test_racine_absente_est_un_succes_vide(self, tmp_path):
        ok, msg, info = pmw.purge_quarantine(tmp_path / "absent")
        assert (ok, msg) == (True, "")
        assert info == {"root": str(tmp_path / "absent"),
                        "removed": [], "bytes": 0}

    def test_racine_sans_marqueur_refusee(self, tmp_path):
        root = tmp_path / "q"
        (root / "quelquun").mkdir(parents=True)
        (root / "quelquun" / "f.txt").write_text("x", encoding="utf-8")
        ok, msg, info = pmw.purge_quarantine(root)
        assert ok is False
        assert msg == f"quarantine-root-not-ours:{root}"
        assert info is None
        assert (root / "quelquun" / "f.txt").exists(), (
            "on ne supprime jamais un repertoire qu'on n'a pas cree")

    def test_purge_effective_garde_le_marqueur(self, tmp_path):
        root = tmp_path / "q"
        (root / "d1").mkdir(parents=True)
        (root / "d1" / "f.bin").write_bytes(b"0123456789")
        (root / pmw.QUARANTINE_MARKER).write_text("x", encoding="utf-8")
        ok, msg, info = pmw.purge_quarantine(root)
        assert (ok, msg) == (True, "")
        assert info["removed"] == [str(root / "d1")]
        assert info["bytes"] == 10
        assert not (root / "d1").exists()
        assert (root / pmw.QUARANTINE_MARKER).exists()


# ---------------------------------------------------------------------------
# OPT-IN : la purge est une voie CLI nommee, pas un effet de bord
# ---------------------------------------------------------------------------


class TestCliWiring:
    def _run(self, *args):
        script = Path(pmw.__file__)
        return subprocess.run(
            [sys.executable, str(script), *args],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", cwd=str(script.parents[1]),
            env={**os.environ, "PYTHONIOENCODING": "utf-8"},
        )

    def test_purge_quarantine_json_sur_racine_absente(self, tmp_path):
        root = tmp_path / "q"
        proc = self._run("--purge-quarantine", "--quarantine-root", str(root),
                         "--json")
        assert proc.returncode == 0, proc.stderr
        payload = json.loads(proc.stdout)["purge_quarantine"]
        assert payload["ok"] is True
        assert payload["removed"] == []

    def test_purge_quarantine_sans_marqueur_rc_1(self, tmp_path):
        root = tmp_path / "q"
        (root / "autre").mkdir(parents=True)
        proc = self._run("--purge-quarantine", "--quarantine-root", str(root))
        assert proc.returncode == 1
        assert "quarantine-root-not-ours" in proc.stderr
        assert (root / "autre").exists()

    def test_le_drapeau_de_quarantaine_existe_et_est_opt_in(self):
        proc = self._run("--help")
        assert proc.returncode == 0, proc.stderr
        assert "--quarantine-submodules" in proc.stdout
        assert "--quarantine-root" in proc.stdout
        assert "--purge-quarantine" in proc.stdout
