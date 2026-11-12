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
import stat
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
        # `decontaminated` complete le contrat : la liste des marqueurs
        # `.git` de sous-modules deplaces hors du worktree (vide ici : rien
        # a decontaminer, aucun marqueur pendant).
        assert info == {"quarantine": None, "modules": [],
                        "decontaminated": [], "preserved": True}
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

    def test_modules_vide_refuse_et_restaure(self, tmp_path):
        """Un `modules/` sans sous-gitdir ne preserve rien : on le dit, et
        le deplacement est ANNULE -- un refus laisse le depot dans l'etat
        ou la passe l'a trouve (review #22094, point 2)."""
        wt = _real_worktree(tmp_path)
        modules = pmw.worktree_gitdir(str(wt)) / "modules"
        modules.mkdir()
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-empty-modules"
        assert info["preserved"] is False
        assert info["restored"] is True
        assert modules.is_dir(), "le modules/ vide est de retour au worktree"
        assert not (tmp_path / "q" / "dest").exists(), (
            "la destination vide ne reste pas en quarantaine"
        )

    def test_submodule_en_alternates_refuse_et_restaure(self, tmp_path):
        """Preuve non tenue (alternates) : retrait annule ET modules/
        retourne au worktree. Sans restauration, une passe ulterieure
        sans le drapeau retirerait le worktree puis la purge detruirait
        les seuls objets restants (review #22094, point 2)."""
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["A"])
        (modules / "A" / "objects" / "info" / "alternates").write_text(
            "/ailleurs\n", encoding="utf-8")
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-unreadable:objects-alternates"
        assert info["preserved"] is False
        assert info["restored"] is True
        assert (modules / "A").is_dir(), "le gitdir du sous-module est rendu"
        assert not (tmp_path / "q" / "dest").exists()

    def test_restauration_echouee_est_une_panne_nommee(self, tmp_path,
                                                       monkeypatch):
        """Si le deplacement inverse echoue, l'etat est incoherent (objets
        en quarantaine, worktree non decontamine) : le message le nomme,
        c'est le seul refus de quarantaine qui sortira en erreur."""
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["A"])
        # La preuve doit echouer (alternates) pour atteindre la branche de
        # restauration ; c'est elle qu'on fait echouer a son tour.
        (modules / "A" / "objects" / "info" / "alternates").write_text(
            "/ailleurs\n", encoding="utf-8")
        monkeypatch.setattr(
            pmw, "_restore_modules_from_quarantine",
            lambda dest_root, modules_dir: (False, "restore-move-failed:x"),
        )
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest")
        assert ok is False
        assert msg == "quarantine-restore-failed:restore-move-failed:x"
        assert info is None

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
# Refus de quarantaine a l'apply : decision (exit 0 + decompte), panne
# nommee seulement si la restauration echoue (review #22094, point 3)
# ---------------------------------------------------------------------------


class TestQuarantineRefusalExitCode:
    def _run_main(self, monkeypatch, q_result, capsys):
        """main() in-process : un statut REMOVE a sous-modules dont la
        decontamination est bouchonnee, resolution PR hors disque."""
        status = _make_status_apply()
        monkeypatch.setattr(pmw, "list_worktrees", lambda: [
            {"path": status.path, "branch": status.branch}])
        monkeypatch.setattr(pmw, "probe_gh_availability", lambda: None)
        monkeypatch.setattr(
            pmw, "diagnose_worktree",
            lambda path, cur, **kwargs: status)
        monkeypatch.setattr(
            pmw, "get_pr_resolution",
            lambda: pmw.PrResolution(cache_path=None))
        monkeypatch.setattr(
            pmw, "quarantine_worktree_modules", lambda *a, **k: q_result)
        monkeypatch.setattr(
            sys, "argv",
            ["prune_merged_worktrees.py", "--apply", "--json"])
        rc = pmw.main()
        out = json.loads(capsys.readouterr().out)
        return rc, out

    def test_refus_de_quarantaine_sort_en_0_avec_son_decompte(
            self, monkeypatch, capsys):
        rc, out = self._run_main(monkeypatch, (
            False, "quarantine-empty-modules",
            {"quarantine": None, "modules": [], "preserved": False,
             "restored": True},
        ), capsys)
        assert rc == 0, "un refus est une decision, pas une panne (#3895)"
        assert out["applied"] == 0
        assert out["apply_errors"] == 0
        assert out["apply_quarantine_refusals"] == 1
        assert out["apply_results"][0]["applied"] is False
        assert "quarantine-refused:quarantine-empty-modules" == \
            out["apply_results"][0]["stderr"]

    def test_restauration_echouee_sort_en_2(self, monkeypatch, capsys):
        """Seul cas d'erreur : le modules/ n'a pas pu etre rendu, l'etat
        est incoherent -- la tache planifiee doit le voir."""
        rc, out = self._run_main(monkeypatch, (
            False, "quarantine-restore-failed:restore-move-failed:x", None,
        ), capsys)
        assert rc == 2
        assert out["apply_errors"] == 1
        assert out["apply_quarantine_refusals"] == 0


def _make_status_apply():
    return pmw.WorktreeStatus(
        path="C:/fake/apply0", branch="fix/X", is_current=False,
        pr_state="MERGED", pr_number=999, pr_url=None, ahead_count=0,
        has_source_dirty=False, untracked_paths=[], decision="REMOVE",
        refusal_reason=None, has_submodules=True,
    )


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


# ---------------------------------------------------------------------------
# Fichiers en lecture seule : le cas Windows (les objets git sont en 0444)
# ---------------------------------------------------------------------------


class TestReadOnlyObjects:
    """Le deplacement inter-volumes echouait sur les objets git.

    Les packs et les objets loos sont crees en lecture seule. `shutil.move`
    entre volumes distincts fait `copytree` + `rmtree`, et `rmtree` echoue
    alors sur ces fichiers (`PermissionError [WinError 5]`) : la copie en
    quarantaine aboutit, la suppression de la source echoue, l'organe refuse
    le retrait -- et la quarantaine accumule une copie de plus a chaque
    passe. Les tests existants ne le voyaient pas : `tmp_path` et la racine
    de quarantaine sont sur le meme volume, donc `shutil.move` y fait un
    `os.rename` (pas de `rmtree`).
    """

    @staticmethod
    def _force_readonly(tree: Path) -> None:
        for f in tree.rglob("*"):
            if f.is_file():
                os.chmod(f, stat.S_IREAD)

    @staticmethod
    def _force_cross_volume(monkeypatch) -> None:
        """Simule un deploiement inter-volumes (D: -> C:).

        `os.rename` echoue avec EXDEV, et `shutil.move` bascule alors sur
        `copytree` + `rmtree` -- le chemin ou le defaut se voyait.
        """
        def _exdev(src, dst, **kwargs):
            raise OSError(getattr(os, "EXDEV", 18),
                          "Invalid cross-device link")
        monkeypatch.setattr(os, "rename", _exdev)

    def test_lever_attribut_lecture_seule(self, tmp_path):
        f = tmp_path / "pack.pack"
        f.write_text("x", encoding="utf-8")
        os.chmod(f, stat.S_IREAD)
        assert not (f.stat().st_mode & stat.S_IWRITE)
        assert pmw._clear_readonly_files(tmp_path) == 1
        assert f.stat().st_mode & stat.S_IWRITE

    def test_quarantaine_reussit_avec_des_objets_en_lecture_seule(
            self, tmp_path, monkeypatch):
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["sous-module"])
        self._force_readonly(modules)
        self._force_cross_volume(monkeypatch)
        ok, why, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"
        dest = Path(info["quarantine"]) / "modules" / "sous-module"
        assert _count_objects(dest) > 0, "les objets doivent rester lisibles"
        assert not (pmw.worktree_gitdir(str(wt)) / "modules").exists(), (
            "la source doit etre liberee apres le deplacement")

    def test_le_echec_laisse_la_source_intacte(self, tmp_path, monkeypatch):
        """Un echec de deplacement ne doit pas decroter la source."""
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["sous-module"])
        self._force_readonly(modules)
        self._force_cross_volume(monkeypatch)
        # Destination impossible : le deplacement echoue apres coup.
        monkeypatch.setattr(
            pmw, "_move_dir_robust",
            lambda src, dst: (_ for _ in ()).throw(
                OSError(13, "Acces refuse")),
        )
        ok, why, _info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok is False
        assert "quarantine-move-failed" in why
        assert modules.is_dir(), "la source doit rester en place"
        assert _count_objects(modules / "sous-module") > 0


class TestPurgeEtRestauration:
    """Les deux fins de la chaine de quarantaine : la purge et l'annulation.

    - La **purge** explicite (#21743) doit aboutir sous Windows : les
      objets git sont en lecture seule et `copytree`/`copystat` preserve le
      mode, donc les entrees de quarantaine portent ce mode. Sans lever
      l'attribut avant la suppression, `shutil.rmtree` echoue (WinError 5).
    - L'**annulation** (deplacement reussi puis echec) doit remettre le
      `modules/` a sa place : sinon une passe suivante, meme sans le
      drapeau, ne verrait plus le garde `contains_submodules`, retirerait le
      worktree, et la purge detruirait les seuls objets restants.
    """

    def test_la_purge_reussit_avec_des_objets_en_lecture_seule(self, tmp_path):
        root = tmp_path / "quarantaine"
        root.mkdir()
        (root / pmw.QUARANTINE_MARKER).write_text(
            "racine de quarantaine\n", encoding="utf-8")
        entry = root / "20240101T000000-1-wt"
        pack = entry / "modules" / "sous-module" / "objects" / "pack.pack"
        pack.parent.mkdir(parents=True)
        pack.write_text("contenu\n", encoding="utf-8")
        os.chmod(pack, stat.S_IREAD)

        ok, why, _info = pmw.purge_quarantine(root)
        assert ok, f"la purge doit aboutir : {why}"
        assert not entry.exists(), "l'entree doit etre supprimee"
        assert (root / pmw.QUARANTINE_MARKER).exists(), (
            "le marqueur de la racine doit rester : la racine est la notre")

    def test_echec_apres_deplacement_restaure_le_modules(
            self, tmp_path, monkeypatch):
        wt = _real_worktree(tmp_path)
        modules = _bare_submodules(wt, ["sous-module"])
        vrai_move = pmw._move_dir_robust
        appels = {"n": 0}

        def move_puis_echec(src, dst):
            """Le deplacement aboutit, puis l'appel echoue."""
            appels["n"] += 1
            vrai_move(src, dst)
            if appels["n"] == 1:
                raise OSError(13, "Acces refuse")

        monkeypatch.setattr(pmw, "_move_dir_robust", move_puis_echec)
        ok, why, _info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok is False
        assert "quarantine-move-failed" in why
        assert modules.is_dir(), (
            "le modules/ doit revenir dans le worktree : un refus laisse le "
            "depot dans l'etat ou la passe l'a trouve")
        assert _count_objects(modules / "sous-module") > 0, (
            "les objets doivent rester lisibles apres la restauration")


# ---------------------------------------------------------------------------
# Sous-module de chemin imbrique : `modules/a/b/c` est le gitdir
# ---------------------------------------------------------------------------


class TestNestedGitdir:
    """Un sous-module enregistre sous un chemin imbrique.

    `modules/a/b/c` est le gitdir ; `modules/a` n'est qu'un repertoire de
    chemin. La preuve de conservation doit porter sur le gitdir, sinon elle
    refuse un depot parfaitement sain (`objects-absent`) et le worktree
    n'est jamais recycle.
    """

    @staticmethod
    def _nested_submodule(wt: Path) -> Path:
        modules = pmw.worktree_gitdir(str(wt)) / "modules"
        sub = modules / "MyIA.AI.Notebooks" / "SymbolicAI" / "SMT" / "Z3.Linq"
        sub.mkdir(parents=True, exist_ok=True)
        proc = _git("init", "-q", "--bare", str(sub))
        assert proc.returncode == 0, proc.stderr
        seed = wt.parent / "seed.txt"
        seed.write_text("contenu a objectiver\n", encoding="utf-8")
        proc = _git("--git-dir", str(sub), "hash-object", "-w", str(seed))
        assert proc.returncode == 0, proc.stderr
        assert proc.stdout.strip(), "hash-object doit ecrire un objet"
        return sub

    def test_le_gitdir_imbrique_est_reconnu(self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = self._nested_submodule(wt)
        modules = pmw.worktree_gitdir(str(wt)) / "modules"
        found = pmw._submodule_gitdirs(modules)
        assert found == [sub], (
            "seul le gitdir est un gitdir, pas les repertoires de chemin")
        ok, why = pmw._gitdir_is_readable(found[0])
        assert ok, why

    def test_quarantaine_reussit_avec_un_gitdir_imbrique(self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = self._nested_submodule(wt)
        ok, why, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"
        dest = (Path(info["quarantine"]) / "modules"
                / "MyIA.AI.Notebooks" / "SymbolicAI" / "SMT" / "Z3.Linq")
        assert _count_objects(dest) > 0, (
            "les objets doivent rester lisibles cote quarantaine")
        assert not sub.exists(), "la source doit etre liberee"


# ---------------------------------------------------------------------------
# Le gitfile du sous-module doit suivre son gitdir en quarantaine
# ---------------------------------------------------------------------------


class TestDecontaminationSubmodule:
    """Le marqueur `.git` d'un sous-module est ce que git lit pour savoir
    qu'un sous-module est POPULE dans le worktree -- et c'est sa presence
    qui declenche "working trees containing submodules cannot be moved or
    removed".

    Mesure (depot scratch, etat de production replique) :
      - marqueur REPOINTE vers un gitdir valide -> refus ;
      - marqueur PENDANT (gitdir deja deplace)  -> "fatal: not a git
        repository" ;
      - marqueur DEPLACE hors du worktree       -> le retrait SANS
        `--force` aboutit.
    La decontamination DEPLACE donc le marqueur en quarantaine : rien n'est
    supprime, son contenu est conserve.
    """

    def _worktree_avec_sous_module(self, tmp_path):
        wt = _real_worktree(tmp_path)
        modules = pmw.worktree_gitdir(str(wt)) / "modules"
        rel = Path("a") / "b" / "sous-module"
        sub = modules / rel
        sub.mkdir(parents=True)
        proc = _git("init", "-q", "--bare", str(sub))
        assert proc.returncode == 0, proc.stderr
        seed = wt.parent / "seed.txt"
        seed.write_text("contenu a objectiver\n", encoding="utf-8")
        proc = _git("--git-dir", str(sub), "hash-object", "-w", str(seed))
        assert proc.returncode == 0, proc.stderr
        # Le checkout du sous-module et le marqueur que git y ecrit.
        checkout = wt / rel
        checkout.mkdir(parents=True)
        marker = checkout / ".git"
        marker.write_text(f"gitdir: {sub}\n", encoding="utf-8")
        return wt, rel, marker

    def test_le_marqueur_est_deplace_en_quarantaine(self, tmp_path):
        wt, rel, marker = self._worktree_avec_sous_module(tmp_path)

        ok, why, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"
        assert not marker.exists(), (
            "le marqueur doit avoir quitte le worktree -- c'est lui qui "
            "fait dire a git que le sous-module y est peuple")
        deplace = Path(info["quarantine"]) / "gitfiles" / rel / ".git"
        assert deplace.is_file(), "le marqueur doit etre conserve en quarantaine"
        assert "gitdir:" in deplace.read_text(encoding="utf-8")
        assert info["decontaminated"] == [str(rel)]

    def test_marqueur_pendant_deplace_vers_l_entree_existante(self, tmp_path):
        """Cas d'une passe precedente : les modules sont deja en quarantaine."""
        wt = _real_worktree(tmp_path)
        rel = Path("a") / "b" / "sous-module"
        checkout = wt / rel
        checkout.mkdir(parents=True)
        marker = checkout / ".git"
        marker.write_text(
            "gitdir: ../../../../../../absent/modules/a/b/sous-module\n",
            encoding="utf-8")
        # Une entree de quarantaine pour ce worktree (nommee <nom>-<worktree>).
        # Le `modules/` qu'elle porte contient de VRAIS gitdirs : c'est ce
        # qu'une passe precedente y deplace.
        qroot = tmp_path / "quarantaine"
        entry = qroot / f"20240101T000000-1-{wt.name}"
        sub = entry / "modules" / rel
        sub.mkdir(parents=True)
        proc = _git("init", "-q", "--bare", str(sub))
        assert proc.returncode == 0, proc.stderr

        ok, why, info = pmw.quarantine_worktree_modules(
            str(wt), qroot, "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"
        assert not marker.exists(), "le marqueur pendant doit quitter le worktree"
        deplace = entry / "gitfiles" / rel / ".git"
        assert deplace.is_file(), "le marqueur doit rejoindre l'entree qui porte les objets"
        assert info["decontaminated"] == [str(rel)]


class TestDecontaminationFailClosed:
    """Un deplacement de marqueur qui echoue doit produire un motif NOMME.

    Fail-closed : le marqueur reste dans le worktree (rien n'est perdu), le
    retrait n'a pas lieu, et l'organe le dit par un motif
    `decontamination-failed:<chemin>` -- au lieu de laisser git echouer de
    facon cryptique ("not a git repository", "working trees containing
    submodules...").
    """

    def test_echec_du_deplacement_refuse_avec_un_motif_nomme(
            self, tmp_path, monkeypatch):
        wt = _real_worktree(tmp_path)
        modules = pmw.worktree_gitdir(str(wt)) / "modules"
        rel = Path("a") / "b" / "sous-module"
        sub = modules / rel
        sub.mkdir(parents=True)
        proc = _git("init", "-q", "--bare", str(sub))
        assert proc.returncode == 0, proc.stderr
        seed = wt.parent / "seed.txt"
        seed.write_text("contenu a objectiver\n", encoding="utf-8")
        proc = _git("--git-dir", str(sub), "hash-object", "-w", str(seed))
        assert proc.returncode == 0, proc.stderr
        checkout = wt / rel
        checkout.mkdir(parents=True)
        marker = checkout / ".git"
        marker.write_text(f"gitdir: {sub}\n", encoding="utf-8")

        vrai_move = pmw.shutil.move

        def move_casse(src, dst):
            # Seul le deplacement du MARQUEUR echoue : le deplacement des
            # `modules/` (quarantaine) doit aboutir.
            if "gitfiles" in str(dst):
                raise OSError("simule: deplacement impossible")
            return vrai_move(src, dst)

        monkeypatch.setattr(pmw.shutil, "move", move_casse)

        ok, why, _ = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert not ok, "la quarantaine doit etre refusee"
        assert why.startswith("decontamination-failed:"), why
        assert str(rel) in why, why
        assert marker.exists(), (
            "le marqueur doit rester dans le worktree : rien n'est supprime")


class TestRetraitSansForce:
    """Le comportement de git LUI-MEME, mesure -- pas une hypothese.

    Un superprojet reel avec un sous-module reelement enregistre (chemin
    imbrique), un worktree lie, puis le geste de l'organe : la quarantaine
    deplace le `modules/` du gitdir ET le marqueur `.git` du sous-module.
    Apres ce geste, `git worktree remove` SANS `--force` doit aboutir.

    Le controle est le repointage : avec le marqueur repointe vers un gitdir
    valide (donc un sous-module "peuple"), git refuse. Sans ce controle,
    le test ne prouverait que le retrait "marche", pas que c'est la
    decontamination qui le permet.
    """

    SUB = "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq"

    def _superprojet(self, tmp_path):
        src = tmp_path / "src"
        src.mkdir()
        assert _git("init", "-q", str(src)).returncode == 0
        _git("config", "user.email", "t@t.t", cwd=str(src))
        _git("config", "user.name", "t", cwd=str(src))
        (src / "file.txt").write_text("contenu\n", encoding="utf-8")
        _git("add", "file.txt", cwd=str(src))
        _git("commit", "-qm", "init", cwd=str(src))

        sup = tmp_path / "super"
        sup.mkdir()
        assert _git("init", "-q", str(sup)).returncode == 0
        _git("config", "user.email", "t@t.t", cwd=str(sup))
        _git("config", "user.name", "t", cwd=str(sup))
        (sup / "file.txt").write_text("x\n", encoding="utf-8")
        _git("add", "file.txt", cwd=str(sup))
        _git("commit", "-qm", "init", cwd=str(sup))
        proc = _git("-c", "protocol.file.allow=always", "submodule", "add",
                    "-q", str(src), self.SUB, cwd=str(sup))
        assert proc.returncode == 0, proc.stderr
        _git("commit", "-qm", "add submodule", cwd=str(sup))

        wt = tmp_path / "wt"
        proc = _git("worktree", "add", "-q", "-b", "wtbranch", str(wt),
                    "HEAD", cwd=str(sup))
        assert proc.returncode == 0, proc.stderr
        proc = _git("-c", "protocol.file.allow=always", "submodule",
                    "update", "--init", "-q", "--recursive", cwd=str(wt))
        assert proc.returncode == 0, proc.stderr
        assert (wt / self.SUB / ".git").is_file(), (
            "le sous-module doit etre initialise dans le worktree")
        return sup, wt

    def test_apres_decontamination_le_retrait_aboutit_sans_force(self, tmp_path):
        sup, wt = self._superprojet(tmp_path)

        ok, why, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"
        assert info["decontaminated"], "le marqueur doit etre decontamine"

        proc = _git("worktree", "remove", str(wt), cwd=str(sup))
        assert proc.returncode == 0, (
            "le retrait doit aboutir SANS --force apres decontamination : "
            f"{proc.stderr}")
        assert not wt.exists(), "le worktree doit avoir disparu"

    def test_le_marqueur_present_refuse_meme_avec_un_gitdir_valide(
            self, tmp_path):
        """CONTROLE : le marqueur PRESENT suffit a faire refuser git.

        Ici rien n'est deplace : le marqueur est celui que git a ecrit, il
        pointe vers un gitdir VALIDE, et le sous-module est donc "peuple"
        aux yeux de git. Le retrait est refuse. C'est ce controle qui etablit
        que c'est la PRESENCE du marqueur dans le worktree qui declenche le
        garde -- et non l'etat du disque ou la position du gitdir.
        """
        sup, wt = self._superprojet(tmp_path)
        marker = wt / self.SUB / ".git"
        assert marker.is_file(), "le marqueur doit etre la"

        proc = _git("worktree", "remove", str(wt), cwd=str(sup))
        assert proc.returncode != 0, (
            "avec le marqueur present, git doit refuser le retrait")
        assert "submodules" in proc.stderr, proc.stderr
        assert wt.exists(), "le worktree doit avoir survecu"

    def test_sans_decontamination_git_refuse_le_retrait(self, tmp_path,
                                                        monkeypatch):
        """CONTROLE : meme quarantaine, mais SANS decontamination -> refus.

        Le geste de l'organe est le meme ; seule la decontamination est
        neutralisee (monkeypatch). Le retrait doit alors echouer : c'est
        elle, et non la quarantaine, qui rend le retrait possible.
        """
        sup, wt = self._superprojet(tmp_path)
        monkeypatch.setattr(
            pmw, "_decontaminate_submodule_gitfiles", lambda *a, **k: [])

        ok, why, _ = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "quarantaine", "dest")
        assert ok, f"la quarantaine doit aboutir : {why}"

        proc = _git("worktree", "remove", str(wt), cwd=str(sup))
        assert proc.returncode != 0, (
            "sans decontamination, git doit refuser le retrait")
        assert wt.exists(), "le worktree doit avoir survecu"
