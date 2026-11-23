#!/usr/bin/env python3
"""Temoins de la garde des dossiers de premier niveau (#27141).

La garde doit :
- **rougir** un dossier de premier niveau ajoute et non autorise ;
- **laisser vert** un ajout sous un dossier deja autorise ;
- **laisser vert** une PR qui ajoute le dossier ET sa ligne d'autorisation
  (c'est la voie du GO cite) ;
- **rougir** un renommage dont la DESTINATION est un dossier nouveau ;
- **ne jamais compter vert** quand l'instrument est en panne (diff illisible,
  liste introuvable) : rc 2.

Les tests sont hermetiques : ils construisent un depot git jetable, pas une
copie du depot (un test qui depend du reseau ou de `main` ne prouve rien).

Run: python -m pytest scripts/ci/tests/test_check_toplevel_series.py -q
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import check_toplevel_series as cts  # noqa: E402


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=repo, capture_output=True,
                          text=True, encoding="utf-8", errors="replace")
    assert proc.returncode == 0, f"git {' '.join(args)} : {proc.stderr}"
    return proc.stdout


def _repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    (repo / "MyIA.AI.Notebooks" / "GenAI").mkdir(parents=True)
    (repo / "MyIA.AI.Notebooks" / "GenAI" / "a.ipynb").write_text("{}", encoding="utf-8")
    _git(repo.parent, "init", "-q", str(repo))
    _git(repo, "config", "user.email", "t@example.invalid")
    _git(repo, "config", "user.name", "t")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    return repo


def _allowlist(tmp_path: Path, entries: str) -> Path:
    path = tmp_path / "allowlist.txt"
    path.write_text(entries, encoding="utf-8")
    return path


# --- lecture de la liste -----------------------------------------------------


def test_la_liste_ignore_comments_et_lignes_vides():
    entries = cts.parse_allowlist(
        "# entete\n\nGenAI   # GO #27092\n  Sudoku  \n# fin\n")
    assert entries == ["GenAI", "Sudoku"]


def test_un_fichier_a_la_racine_n_appartient_a_aucun_dossier():
    assert cts.top_level_series([
        "MyIA.AI.Notebooks/x.ipynb",
        "MyIA.AI.Notebooks/GenAI/y.ipynb",
    ]) == {"GenAI"}


def test_le_chemin_hors_racine_est_ignore():
    assert cts.top_level_series(["scripts/ci/x.py"]) == set()


# --- controle sur un depot jetable -------------------------------------------


def test_un_dossier_nouveau_non_autorise_rougit(tmp_path):
    repo = _repo(tmp_path)
    new_dir = repo / "MyIA.AI.Notebooks" / "CodingTheory"
    new_dir.mkdir()
    (new_dir / "b.ipynb").write_text("{}", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "nouveau dossier")

    allowlist = _allowlist(tmp_path, "GenAI\n")
    rc, report = cts.check("HEAD~1...HEAD", allowlist, cwd=repo)
    assert rc == 1
    assert report["new_series"] == ["CodingTheory"]


def test_un_ajout_sous_un_dossier_autorise_reste_vert(tmp_path):
    repo = _repo(tmp_path)
    sub = repo / "MyIA.AI.Notebooks" / "GenAI" / "Image"
    sub.mkdir()
    (sub / "b.ipynb").write_text("{}", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "ajout dans un rayon")

    allowlist = _allowlist(tmp_path, "GenAI\n")
    rc, report = cts.check("HEAD~1...HEAD", allowlist, cwd=repo)
    assert rc == 0, report
    assert report["new_series"] == []


def test_une_pr_qui_ajoute_le_dossier_et_sa_ligne_passe(tmp_path):
    """La voie du GO cite : la PR ajoute le dossier ET sa ligne d'autorisation.

    La liste est lue dans l'etat de la tete : la ligne ajoutee par la PR
    couvre le dossier qu'elle accompagne.
    """
    repo = _repo(tmp_path)
    new_dir = repo / "MyIA.AI.Notebooks" / "InformationCalcul"
    new_dir.mkdir()
    (new_dir / "b.ipynb").write_text("{}", encoding="utf-8")
    (repo / "allowlist.txt").write_text(
        "GenAI\nInformationCalcul   # GO du mainteneur : #27092\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "dossier + autorisation")

    # la liste lue EST celle de la tete (la PR l'a modifiee)
    allowlist = repo / "allowlist.txt"
    rc, report = cts.check("HEAD~1...HEAD", allowlist, cwd=repo)
    assert rc == 0, report
    assert report["new_series"] == []


def test_un_renommage_vers_un_dossier_neuf_rougit(tmp_path):
    """C'est la DESTINATION qui compte : deplacer un carnet vers un dossier
    nouveau ouvre ce dossier."""
    repo = _repo(tmp_path)
    new_dir = repo / "MyIA.AI.Notebooks" / "Neuf"
    new_dir.mkdir()
    _git(repo, "mv", "MyIA.AI.Notebooks/GenAI/a.ipynb",
         "MyIA.AI.Notebooks/Neuf/a.ipynb")
    _git(repo, "commit", "-q", "-m", "deplacement")

    allowlist = _allowlist(tmp_path, "GenAI\n")
    rc, report = cts.check("HEAD~1...HEAD", allowlist, cwd=repo)
    assert rc == 1
    assert report["new_series"] == ["Neuf"]


def test_un_deplacement_vers_un_dossier_autorise_reste_vert(tmp_path):
    """Le contre-temps du renommage : une serie qui REJOINT un rayon existant
    ne doit pas rougir."""
    repo = _repo(tmp_path)
    (repo / "MyIA.AI.Notebooks" / "GenAI" / "Image").mkdir(parents=True)
    _git(repo, "mv", "MyIA.AI.Notebooks/GenAI/a.ipynb",
         "MyIA.AI.Notebooks/GenAI/Image/a.ipynb")
    _git(repo, "commit", "-q", "-m", "deplacement interne")

    allowlist = _allowlist(tmp_path, "GenAI\n")
    rc, report = cts.check("HEAD~1...HEAD", allowlist, cwd=repo)
    assert rc == 0, report


# --- fail-CLOSED --------------------------------------------------------------


def test_un_diff_illisible_rend_2_jamais_vert(tmp_path):
    """Un range git inexistant ne doit JAMAIS produire un quitus."""
    allowlist = _allowlist(tmp_path, "GenAI\n")
    rc, report = cts.check("ref-absent...ref-absent", allowlist)
    assert rc == 2
    assert report["new_series"] == []


def test_une_liste_introuvable_rend_2(tmp_path):
    _repo(tmp_path)
    rc, report = cts.check("HEAD~1...HEAD", tmp_path / "absent.txt")
    assert rc == 2
    assert report["error"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
