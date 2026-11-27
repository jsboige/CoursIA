"""Twin-parity --update : refus du piege du cwd (#27724).

`check_twin_parity.py --update` resout la racine du depot depuis le cwd
(`_repo_root()`). Lance depuis le clone principal alors que la PR vit dans
un worktree, il attestait les blobs de `main` :

- carnet absent de la racine resolue -> sha `null` ecrit sans erreur ;
- carnet present mais a un autre etat -> sha fantome (mesure 2x le 21/11,
  #27707 / #27703 / #27698 : une seule cause, 5 jambes rouges).

Le correctif (#27724) fait deux choses, AVANT toute ecriture :

1. chaque cote de la paire doit exister sous la racine resolue ;
2. aucun sha attendu ne doit etre null a HEAD (fichier non commis).

Refus = exit non nul + message qui nomme la paire, le fichier, la racine
resolue, et donne la commande correcte (lancer depuis le worktree /
--repo-root, ou committer d'abord).

Ces tests ROUGISSENT sur le code d'avant le correctif : les scenarios A et
B y produisent rc=0 et une attestation ecrite avec un sha null.

Aucun appel reseau : mini-depot git jetable (`tmp_path`) et flags
`--no-allocate-against --no-open-claims-floor` (les planchers #22299
interrogent gh, absent du mini-depot).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECK_PATH = REPO_ROOT / "scripts" / "notebook_tools" / "check_twin_parity.py"

PY_REL = "Notebooks/Serie-01/Twin-01-Python.ipynb"
CS_REL = "Notebooks/Serie-01/Twin-01-CSharp.ipynb"


def _git(repo: Path, *args: str) -> str:
    out = subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    return out.stdout.strip()


def _blob_sha(repo: Path, rel: str) -> str:
    return _git(repo, "hash-object", rel)


def _write_pair_file(repo: Path, py_sha: str, cs_sha: str) -> None:
    reg_dir = repo / "scripts" / "notebook_tools" / "twin_pairs.d"
    reg_dir.mkdir(parents=True, exist_ok=True)
    (reg_dir / "twin-01.yaml").write_text(
        "name: Twin-01\n"
        "family: Serie/Test\n"
        "parity_level: full\n"
        f"python: {PY_REL}\n"
        f"csharp: {CS_REL}\n"
        "last_audit:\n"
        "  date: '2026-11-01'\n"
        "  by: lane-de-test\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n",
        encoding="utf-8",
    )


def _run_update(repo: Path):
    reg = repo / "scripts" / "notebook_tools" / "twin_pairs.d"
    return subprocess.run(
        [sys.executable, str(CHECK_PATH),
         "--registry", str(reg),
         "--repo-root", str(repo),
         "--pair", "Twin-01", "--update", "--by", "lane-de-test",
         "--no-allocate-against", "--no-open-claims-floor"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


def _audit_files(repo: Path) -> list[str]:
    slug_dir = (repo / "scripts" / "notebook_tools" / "twin_pairs.d"
                / "twin-01")
    if not slug_dir.exists():
        return []
    return sorted(p.name for p in slug_dir.glob("*.yaml"))


@pytest.fixture
def mini_repo(tmp_path: Path) -> Path:
    """Mini-depot : paire attestee en v1, puis les deux carnets commis en v2.

    Le dernier audit reference v1, donc les blobs v2 a HEAD sont un vrai
    rebaseline (pas un no-op) : sans la garde, --update ecrit.
    """
    pytest.importorskip("yaml")
    repo = tmp_path / "repo"
    (repo / "Notebooks" / "Serie-01").mkdir(parents=True)
    (repo / PY_REL).write_text('{"cells": [], "version": "v1"}\n', encoding="utf-8")
    (repo / CS_REL).write_text('{"cells": [], "version": "v1"}\n', encoding="utf-8")
    _write_pair_file(repo, _blob_sha(repo, PY_REL), _blob_sha(repo, CS_REL))
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "init")
    (repo / PY_REL).write_text('{"cells": [], "version": "v2"}\n', encoding="utf-8")
    (repo / CS_REL).write_text('{"cells": [], "version": "v2"}\n', encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "v2")
    return repo


def test_27724_carnet_absent_de_la_racine_refuse(mini_repo: Path):
    # Scenario A (le piege mesure sur #27707) : le jumeau C# n'existe PAS
    # sous la racine resolue -- c'est le carnet neuf de la PR, la racine est
    # le mauvais arbre. Avant correctif : rc=0, attestation ecrite avec
    # csharp_sha null.
    (mini_repo / CS_REL).unlink()
    _git(mini_repo, "rm", "-q", CS_REL)
    _git(mini_repo, "commit", "-q", "-m", "csharp retire")

    proc = _run_update(mini_repo)
    assert proc.returncode != 0, (
        f"--update a ecrit depuis la mauvaise racine (piege #27724) : "
        f"rc=0, stdout={proc.stdout!r}")
    assert CS_REL in proc.stderr, proc.stderr
    assert str(mini_repo) in proc.stderr, (
        "le refus doit nommer la racine resolue", proc.stderr)
    assert "worktree" in proc.stderr.lower(), (
        "le refus doit donner la commande correcte (worktree)", proc.stderr)
    assert _audit_files(mini_repo) == [], (
        "aucune attestation ne doit etre ecrite pour une paire refusee")


def test_27724_carnet_present_mais_non_commis_refuse(mini_repo: Path):
    # Scenario B : le fichier existe sur disque mais n'est pas a HEAD --
    # l'attestation lirait un blob null. Avant correctif : rc=0, attestation
    # ecrite avec csharp_sha null (mode silencieux du meme piege).
    (mini_repo / CS_REL).unlink()
    _git(mini_repo, "rm", "-q", CS_REL)
    _git(mini_repo, "commit", "-q", "-m", "csharp retire")
    # Reapparait sur disque SANS commit : membre 1 passe, membre 2 (sha
    # null) doit refuser.
    (mini_repo / CS_REL).write_text('{"cells": [], "version": "v3"}\n', encoding="utf-8")

    proc = _run_update(mini_repo)
    assert proc.returncode != 0, proc.stdout
    assert "commit" in proc.stderr.lower(), (
        "le refus doit dire de committer avant de re-attester", proc.stderr)
    assert _audit_files(mini_repo) == []


def test_27724_non_regression_paire_saine_rebaseline(mini_repo: Path):
    # Controle : racine correcte, deux carnets commis -- le garde ne doit
    # PAS bloquer le rebaseline legitime (sinon toute attestation devient
    # impossible).
    proc = _run_update(mini_repo)
    assert proc.returncode == 0, proc.stderr
    audits = _audit_files(mini_repo)
    assert audits, "l'attestation du rebaseline doit etre ecrite"
    # Le plus grand nom = l'audit frais (l'organ migre aussi l'inline
    # last_audit du yaml en fichier, d'ou potentiellement 2 fichiers).
    frais = audits[-1]
    assert "2026-11-21" in frais or "lane-de-test" in frais, audits
    contenu = (mini_repo / "scripts" / "notebook_tools" / "twin_pairs.d"
               / "twin-01" / frais).read_text(encoding="utf-8")
    assert "csharp_sha:" in contenu and "null" not in contenu
