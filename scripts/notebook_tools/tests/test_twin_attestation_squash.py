"""Contrat de l'organe « attestation jumelle decrivant l'arbre de fusion ».

Le scenario reproduit en miniature la classe de defaut qui a gele `main` le
23/11/2026 : une attestation prise sur la branche, puis le carnet change
encore -- le sha atteste ne decrit plus ce que l'arbre de fusion porte, et le
squash le fait atterrir sur `main` sans que personne ne l'ait vu.

Le test est hermetique : un depot git synthetique, aucun reseau.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(
    0, str(Path(__file__).resolve().parents[1])
)

from check_twin_attestation_squash import Unreadable, check  # noqa: E402

REGISTRY = "scripts/notebook_tools/twin_pairs.d"
PAIR = "pair-x"
PY_PATH = "MyIA.AI.Notebooks/X/Pair-X-Python.ipynb"
CS_PATH = "MyIA.AI.Notebooks/X/Pair-X-CSharp.ipynb"


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=True,
    )
    return proc.stdout.strip()


def _write(repo: Path, path: str, text: str) -> None:
    target = repo / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding="utf-8")


def _attestation(python_sha: str, csharp_sha: str, index: str = "0001") -> str:
    return (
        "date: '2026-11-23'\n"
        "by: test\n"
        f"python_sha: {python_sha}\n"
        f"csharp_sha: {csharp_sha}\n"
        "reason: >-\n"
        "  Attestation de test.\n"
    )


def _descriptor() -> str:
    return (
        "- name: \"Pair X\"\n"
        "  family: Test\n"
        f"  python: {PY_PATH}\n"
        f"  csharp: {CS_PATH}\n"
        "  parity_level: native-both\n"
    )


def _make_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-b", "main"], cwd=repo, check=True,
                   capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"],
                   cwd=repo, check=True)
    _write(repo, PY_PATH, "contenu python\n")
    _write(repo, CS_PATH, "contenu csharp\n")
    _write(repo, f"{REGISTRY}/{PAIR}.yaml", _descriptor())
    python_sha = _git(repo, "hash-object", PY_PATH)
    csharp_sha = _git(repo, "hash-object", CS_PATH)
    _write(repo, f"{REGISTRY}/{PAIR}/0001-2026-11-23-test.yaml",
           _attestation(python_sha, csharp_sha))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    return repo


def _branch_with_attestation(repo: Path, python_sha: str, csharp_sha: str,
                              index: str = "0002") -> None:
    _git(repo, "checkout", "-b", "feature")
    _write(repo, f"{REGISTRY}/{PAIR}/{index}-2026-11-23-test.yaml",
           _attestation(python_sha, csharp_sha))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "attestation")


def test_attestation_conforme_rend_ok(tmp_path):
    repo = _make_repo(tmp_path)
    python_sha = _git(repo, "rev-parse", f"HEAD:{PY_PATH}")
    csharp_sha = _git(repo, "rev-parse", f"HEAD:{CS_PATH}")
    _branch_with_attestation(repo, python_sha, csharp_sha)
    report = check(repo, "main", "feature")
    assert report["verdict"] == "OK", report
    assert [p["pair"] for p in report["pairs"]] == [PAIR]


def test_attestation_perimee_rend_mismatch(tmp_path):
    """Le carnet bouge apres l'attestation : le sha atteste ne decrit plus ce
    que l'arbre de fusion porte -- c'est l'orphelin que le squash fait atterrir
    sur `main`."""
    repo = _make_repo(tmp_path)
    stale_python = _git(repo, "rev-parse", f"HEAD:{PY_PATH}")
    stale_csharp = _git(repo, "rev-parse", f"HEAD:{CS_PATH}")
    _git(repo, "checkout", "-b", "feature")
    _write(repo, PY_PATH, "contenu python modifie\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "carnet modifie")
    _write(repo, f"{REGISTRY}/{PAIR}/0002-2026-11-23-test.yaml",
           _attestation(stale_python, stale_csharp))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "attestation perimee")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "MISMATCH", report
    assert report["pairs"][0]["pair"] == PAIR
    assert any("python" in detail for detail in report["pairs"][0]["details"])
    assert report["reason"]


def test_registre_non_touche_ne_porte_aucune_paire(tmp_path):
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    _write(repo, "MyIA.AI.Notebooks/X/autre.ipynb", "rien a voir\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "hors registre")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "OK", report
    assert report["pairs"] == []


def test_lecture_impossible_leve_unreadable(tmp_path):
    repo = _make_repo(tmp_path)
    with pytest.raises(Unreadable):
        check(repo, "main", "ref-inexistant-1234")


def test_descripteur_touche_nomme_la_paire_sans_son_extension(tmp_path):
    """Le descripteur d'une paire est un FICHIER `twin_pairs.d/<slug>.yaml` ;
    son nom porte l'extension, il n'est pas le nom de la paire.

    Regression mesuree le 23/11 sur le balayage de flotte : le descripteur
    touche etait lu comme une paire nommee `<slug>.yaml`, dont le
    descripteur (`<slug>.yaml.yaml`) n'existait pas -- la garde rendait
    NODESC sur des PRs parfaitement conformes.
    """
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    _write(repo, f"{REGISTRY}/{PAIR}.yaml",
           _descriptor() + "  known_differences:\n"
           "    - \"edition de prose\"\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "descripteur edite")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "OK", report
    assert [p["pair"] for p in report["pairs"]] == [PAIR]


def test_attestation_perimee_vie_le_descripteur_touche(tmp_path):
    """Le defaut doit etre vu meme quand la PR ne touche que le descripteur."""
    repo = _make_repo(tmp_path)
    stale_python = _git(repo, "rev-parse", f"HEAD:{PY_PATH}")
    stale_csharp = _git(repo, "rev-parse", f"HEAD:{CS_PATH}")
    _git(repo, "checkout", "-b", "feature")
    _write(repo, PY_PATH, "contenu python modifie\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "carnet modifie")
    _write(repo, f"{REGISTRY}/{PAIR}.yaml",
           _descriptor() + "  known_differences:\n"
           "    - \"edition de prose\"\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "descripteur edite")
    _write(repo, f"{REGISTRY}/{PAIR}/0002-2026-11-23-test.yaml",
           _attestation(stale_python, stale_csharp))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "attestation perimee")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "MISMATCH", report
    assert report["pairs"][0]["pair"] == PAIR
    assert any("python" in detail for detail in report["pairs"][0]["details"])


def test_schema_reserve_ignore_et_paire_reelle_controlee(tmp_path):
    """`_schema.yaml` documente le registre : il n'est pas une paire.

    Regression mesuree le 2026-11-26 sur #28276 : la PR ajoutait
    `twin_pairs.d/_schema.yaml` (documentation du cote `rust:` optionnel) et
    la garde rendait `_schema [NODESC]` -- un refus de fusion sur une PR
    conforme, la documentation etant lue comme une paire sans descripteur.

    Le temoin exige les DEUX moities : le schema est ignore, et la paire
    reelle touchee dans le meme commit reste nommee et controlee.
    """
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-b", "feature")
    _write(repo, f"{REGISTRY}/_schema.yaml",
           "parity_level:\n  - surface\n  - semantic\n  - native-both\n")
    _write(repo, f"{REGISTRY}/{PAIR}.yaml",
           _descriptor() + "  known_differences:\n"
           "    - \"edition de prose\"\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "schema et descripteur")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "OK", report
    assert [p["pair"] for p in report["pairs"]] == [PAIR]


def test_schema_reserve_n_empeche_pas_de_voir_une_paire_perimee(tmp_path):
    """Le schema ignore ne doit pas blanchir la paire a cote : une attestation
    perimee reste vue quand le meme commit touche `_schema.yaml`."""
    repo = _make_repo(tmp_path)
    stale_python = _git(repo, "rev-parse", f"HEAD:{PY_PATH}")
    stale_csharp = _git(repo, "rev-parse", f"HEAD:{CS_PATH}")
    _git(repo, "checkout", "-b", "feature")
    _write(repo, f"{REGISTRY}/_schema.yaml",
           "parity_level:\n  - surface\n  - semantic\n  - native-both\n")
    _write(repo, PY_PATH, "contenu python modifie\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "schema et carnet modifie")
    _write(repo, f"{REGISTRY}/{PAIR}/0002-2026-11-23-test.yaml",
           _attestation(stale_python, stale_csharp))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "attestation perimee")
    report = check(repo, "main", "feature")
    assert report["verdict"] == "MISMATCH", report
    assert report["pairs"][0]["pair"] == PAIR
    assert any("python" in detail for detail in report["pairs"][0]["details"])
