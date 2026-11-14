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

import errno
import json
import os
import shutil
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


def _count_objects_with_work_tree(gitdir: Path) -> int:
    """`count-objects` en neutralisant le `core.worktree` par
    l'environnement -- c'est ce que fait l'organe pour sa preuve."""
    proc = subprocess.run(
        ["git", "--git-dir", str(gitdir), "count-objects", "-v"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        env={**os.environ, "GIT_WORK_TREE": str(gitdir)},
    )
    assert proc.returncode == 0, proc.stderr
    total = 0
    for line in proc.stdout.splitlines():
        if line.startswith(("count:", "in-pack:")):
            total += int(line.split(":", 1)[1].strip() or 0)
    return total


def _fake_exdev_on(monkeypatch, target: Path):
    """Force le code de chemin « volumes differents » (`EXDEV`) pour un
    deplacement donne -- c'est le cas mesur sur cette machine (la
    quarantaine est sur C:, le depot sur D:)."""
    real_replace = os.replace

    def _replace(src, dst, *args, **kwargs):
        if Path(src) == target:
            raise OSError(errno.EXDEV, "EXDEV simule")
        return real_replace(src, dst, *args, **kwargs)

    monkeypatch.setattr(pmw.os, "replace", _replace)


def _nested_submodule(wt: Path, rel: str) -> Path:
    """Cree `<gitdir>/modules/<rel>` avec de VRAIS objets.

    C'est la disposition REELLE d'un worktree lie : le sous-module est
    enregistre sous `modules/<chemin-du-sous-module>`, donc imbrique
    (`modules/MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq`), et son
    `config` porte un `core.worktree` RELATIF vers l'arborescence de
    travail d'origine (mesure, #25838).
    """
    modules = pmw.worktree_gitdir(str(wt)) / "modules"
    sub = modules / rel
    sub.mkdir(parents=True, exist_ok=True)
    proc = _git("init", "-q", "--bare", str(sub))
    assert proc.returncode == 0, proc.stderr
    seed = wt.parent / "seed.txt"
    seed.write_text("contenu a objectiver\n", encoding="utf-8")
    proc = _git("--git-dir", str(sub), "hash-object", "-w", str(seed))
    assert proc.returncode == 0, proc.stderr
    (sub / "config").write_text(
        "[core]\n"
        "\trepositoryformatversion = 0\n"
        "\tfilemode = false\n"
        "\tbare = false\n"
        "\tsymlinks = false\n"
        "\tignorecase = true\n"
        "\tworktree = ../../../../../../../../../CoursIA-2-wt/absent/"
        "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq\n",
        encoding="utf-8",
    )
    return sub


def _readonly_tree(root: Path) -> Path:
    """Un arbre dont les fichiers sont en lecture seule (mode 444)."""
    root.mkdir(parents=True, exist_ok=True)
    payload = root / "objects" / "ab"
    payload.mkdir(parents=True, exist_ok=True)
    blob = payload / "cdef0123"
    blob.write_bytes(b"objet git")
    os.chmod(blob, 0o444)
    os.chmod(payload, 0o555)
    os.chmod(root / "objects", 0o555)
    os.chmod(root, 0o555)
    return blob


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
# #25838 : le deplacement entre volumes et les objets git en lecture seule
#
# Cause mesuree : `shutil.move` entre volumes distincts (D: -> C:) retombe
# sur `copytree` + `rmtree` ; le `rmtree` echoue sur les objets git en
# lecture seule (mode 444) -> `[WinError 5]`. La copie aboutit, la source
# reste : la charge utile est dupliquee a chaque passe (4,8 Go mesures).
#
# Asymetrie des plateformes, mesuree sur le runner Linux du 14/11 :
# sous Windows, l'attribut du FICHIER bloque l'unlink ; sous POSIX, le
# mode du fichier est sans effet et c'est le REPERTOIRE parent (555)
# qui bloque. Un correctif qui rend ecrivant le seul fichier passe donc
# sous Windows et echoue sous Linux (`PermissionError [Errno 13]`) --
# c'est ce qui a rendu la PR #26561 rouge sur la CI.
# ---------------------------------------------------------------------------


class TestPosixReadonlyDirectory:
    """Le cas POSIX pur : le repertoire est 555, le fichier est ecritable."""

    def test_repertoire_lecture_seule_bloque_l_unlink_natif(self, tmp_path):
        """Le symptome isole : sous POSIX, c'est le repertoire qui bloque."""
        if os.name == "nt":
            pytest.skip("Windows ignore le mode du repertoire")
        payload = tmp_path / "objects" / "ab"
        payload.mkdir(parents=True)
        blob = payload / "cdef0123"
        blob.write_bytes(b"objet git")
        os.chmod(payload, 0o555)
        with pytest.raises(PermissionError):
            blob.unlink()

    def test_suppression_tolerant_quand_seul_le_repertoire_est_lecture_seule(
            self, tmp_path):
        """Le correctif doit rendre ecrivant le repertoire, pas le fichier."""
        payload = tmp_path / "objects" / "ab"
        payload.mkdir(parents=True)
        blob = payload / "cdef0123"
        blob.write_bytes(b"objet git")
        os.chmod(payload, 0o555)
        pmw._rmtree_readonly_tolerant(tmp_path / "objects")
        assert not (tmp_path / "objects").exists()

    def test_unlink_tolerant_quand_seul_le_repertoire_est_lecture_seule(
            self, tmp_path):
        payload = tmp_path / "objects" / "ab"
        payload.mkdir(parents=True)
        blob = payload / "cdef0123"
        blob.write_bytes(b"objet git")
        os.chmod(payload, 0o555)
        pmw._unlink_readonly_tolerant(blob)
        assert not blob.exists()

    def test_purge_tolerant_quand_seul_le_repertoire_est_lecture_seule(
            self, tmp_path):
        """Le chemin de purge de la quarantaine (voie nommee #21743)."""
        root = tmp_path / "q"
        root.mkdir()
        (root / pmw.QUARANTINE_MARKER).write_text("x", encoding="utf-8")
        payload = root / "dest" / "objects" / "ab"
        payload.mkdir(parents=True)
        blob = payload / "cdef0123"
        blob.write_bytes(b"objet git")
        os.chmod(payload, 0o555)
        ok, why, _info = pmw.purge_quarantine(root)
        assert (ok, why) == (True, "")


class TestMoveReadonlySafe:
    def test_renommage_atomique_meme_volume(self, tmp_path):
        src = tmp_path / "src"
        (src / "a").mkdir(parents=True)
        (src / "a" / "f.txt").write_text("x", encoding="utf-8")
        dst = tmp_path / "dst"
        pmw._move_tree_readonly_safe(src, dst)
        assert (dst / "a" / "f.txt").read_text(encoding="utf-8") == "x"
        assert not src.exists()

    def test_shutil_rmtree_echoue_sur_un_objet_en_lecture_seule(self, tmp_path):
        """Le symptome mesure, isole : sans traitement, la suppression
        echoue en `[WinError 5]`."""
        root = tmp_path / "ro"
        _readonly_tree(root)
        try:
            with pytest.raises(PermissionError):
                shutil.rmtree(root)
        finally:
            pmw._rmtree_readonly_tolerant(root)

    def test_suppression_tolerant_au_lecture_seule(self, tmp_path):
        root = tmp_path / "ro"
        _readonly_tree(root)
        pmw._rmtree_readonly_tolerant(root)
        assert not root.exists()

    def test_volume_different_copie_puis_supprime_la_source(
            self, tmp_path, monkeypatch):
        """EXDEV : la copie aboutit, la suppression doit aboutir aussi --
        sinon la source reste et la charge utile est dupliquee."""
        src = tmp_path / "src"
        _readonly_tree(src)
        dst = tmp_path / "dst"
        _fake_exdev_on(monkeypatch, src)
        pmw._move_tree_readonly_safe(src, dst)
        assert not src.exists(), "la source doit avoir ete supprimee"
        assert (dst / "objects" / "ab" / "cdef0123").exists()

    def test_restauration_entre_volumes_et_lecture_seule(
            self, tmp_path, monkeypatch):
        """La restauration est un deplacement lui aussi : elle doit
        tolerer le changement de volume ET les objets en lecture seule."""
        wt = _real_worktree(tmp_path)
        modules_dir = pmw.worktree_gitdir(str(wt)) / "modules"
        root = tmp_path / "q"
        root.mkdir()
        (root / pmw.QUARANTINE_MARKER).write_text("x", encoding="utf-8")
        dest_root = root / "dest"
        dest_root.mkdir()
        dest_modules = dest_root / "modules"
        payload = dest_modules / "A" / "objects" / "ab"
        payload.mkdir(parents=True)
        blob = payload / "cdef"
        blob.write_bytes(b"objet git")
        os.chmod(blob, 0o444)
        _fake_exdev_on(monkeypatch, dest_modules)
        ok, why = pmw._restore_modules_from_quarantine(dest_root, modules_dir)
        assert (ok, why) == (True, "")
        assert (modules_dir / "A" / "objects" / "ab" / "cdef").exists()


class TestRealNestedLayout:
    """La disposition reelle d'un worktree lie est IMBRIQUEE : le
    sous-module vit sous `modules/<chemin-du-sous-module>`."""

    def test_gitdir_imbrique_trouve(self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = _nested_submodule(
            wt, "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq")
        found = pmw._submodule_gitdirs(
            pmw.worktree_gitdir(str(wt)) / "modules")
        assert found == [sub]

    def test_quarantaine_imbriquee_preserve_les_objets(self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = _nested_submodule(
            wt, "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq")
        before = _count_objects_with_work_tree(sub)
        assert before > 0
        ok, msg, info = pmw.quarantine_worktree_modules(
            str(wt), tmp_path / "q", "dest", repo_root=str(tmp_path / "wt"))
        assert ok is True, msg
        assert info["preserved"] is True
        assert [m["readable"] for m in info["modules"]] == [True]
        moved = (Path(info["quarantine"]) / "modules"
                 / "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq")
        assert moved.is_dir(), "le gitdir est DEPLACE, pas supprime"
        assert _count_objects_with_work_tree(moved) == before


class TestStaleCoreWorktree:
    """Le `core.worktree` d'un gitdir de sous-module est un chemin
    RELATIF vers l'arborescence de travail d'origine : deplace en
    quarantaine, il ne resout plus et `count-objects` echoue sur
    `fatal: cannot chdir`. La preuve doit survivre a ce pointeur
    perime -- SANS reecrire la charge utile."""

    def test_pointeur_relatif_perime_ne_bloque_plus_la_preuve(
            self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = _nested_submodule(
            wt, "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq")
        # Sans neutralisation, git echoue sur le pointeur perime.
        proc = _git("--git-dir", str(sub), "count-objects", "-v")
        assert proc.returncode != 0, "le pointeur perime doit echouer"
        # L'organe, lui, produit la preuve.
        assert pmw._gitdir_is_readable(sub) == (True, "")

    def test_la_charge_utile_n_est_pas_reecrite(self, tmp_path):
        wt = _real_worktree(tmp_path)
        sub = _nested_submodule(
            wt, "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq")
        config = (sub / "config").read_text(encoding="utf-8")
        pmw._gitdir_is_readable(sub)
        assert (sub / "config").read_text(encoding="utf-8") == config, (
            "la preuve ne doit pas reecrire le config du depot preserve")


class TestPurgeReadonly:
    def test_purge_dune_entree_en_lecture_seule(self, tmp_path):
        """La purge est bloquee par le meme obstacle que le deplacement :
        sans traitement, les 4,8 Go de quarantaine restent intouchables."""
        root = tmp_path / "q"
        root.mkdir()
        (root / pmw.QUARANTINE_MARKER).write_text("x", encoding="utf-8")
        _readonly_tree(root / "d1")
        ok, msg, info = pmw.purge_quarantine(root)
        assert (ok, msg) == (True, "")
        assert not (root / "d1").exists()
        assert (root / pmw.QUARANTINE_MARKER).exists()
