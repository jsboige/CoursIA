"""Tests du selecteur de suites par chemin touche (P2 du plan #25510).

L'instrument est **advisory** : il dit quelles suites sont concernees par un
changement, et rend compte de ce qu'il ne couvre pas. Les proprietes sous
test sont donc deux, et elles sont opposees :

1. **Ne pas sous-selectionner.** Un motif qui rate ne leve pas d'erreur : il
   rend moins de tests, donc un CI plus vert et plus rapide. C'est la forme de
   defaut la plus difficile a voir -- d'ou l'existence meme de l'instrument.
   Chaque regle est donc verifiee sur un cas POSITIF (le motif declenche) et
   le sens de la selection est verrouille (un test absent du perimetre ne doit
   pas etre selectionne par un autre motif).
2. **Dire ce qui n'est pas couvert.** Un fichier touche qu'aucune regle ne
   rattache doit etre signale, jamais passe sous silence : c'est la seule
   maniere de distinguer « aucun test ne s'y interesse » de « la carte ne sait
   pas encore ».
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import select_tests  # noqa: E402


def _write(root: Path, rel: str, content: str = "") -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


@pytest.fixture()
def repo(tmp_path: Path) -> Path:
    """Petit depot synthétique : une suite locale, une suite etrangerere."""
    _write(tmp_path, "src/module.py", "def f():\n    return 1\n")
    _write(tmp_path, "src/other.py", "def g():\n    return 2\n")
    _write(tmp_path, "tests/test_module.py", "def test_f():\n    assert True\n")
    _write(tmp_path, "tests/test_other.py", "def test_g():\n    assert True\n")
    _write(tmp_path, "tests/conftest.py", "import pytest\n")
    _write(tmp_path, "tests/helpers.py", "VALUE = 1\n")
    _write(tmp_path, "elsewhere/test_remote.py", "def test_r():\n    assert True\n")
    return tmp_path


def _rules(selection: select_tests.Selection, test_rel: str) -> set[str]:
    return {reason.rule for reason in selection.selected.get(test_rel, [])}


# --- R1 : identite ---------------------------------------------------------


def test_r1_un_test_touche_selectionne_sa_suite_locale(repo: Path) -> None:
    selection = select_tests.select(repo, ["tests/test_module.py"])
    assert "tests/test_module.py" in selection.selected
    assert "R1-identite" in _rules(selection, "tests/test_module.py")
    # la suite locale complete est selectionnee
    assert "tests/test_other.py" in selection.selected


def test_r1_ne_selectionne_pas_une_suite_etrangere(repo: Path) -> None:
    selection = select_tests.select(repo, ["tests/test_module.py"])
    assert "elsewhere/test_remote.py" not in selection.selected


# --- R2 : convention de nom ------------------------------------------------


def test_r2_convention_de_nom_selectionne_le_test_correspondant(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    assert "R2-convention" in _rules(selection, "tests/test_module.py")


def test_r2_ne_declenche_pas_sur_un_autre_module(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    assert "R2-convention" not in _rules(selection, "tests/test_other.py")


# --- R3 : reference textuelle ---------------------------------------------


def test_r3_un_test_qui_cite_le_fichier_le_selectionne(repo: Path) -> None:
    _write(repo, "tests/test_pins.py", "# regarde scripts/ci/select_tests.py\ndef test_p():\n    pass\n")
    selection = select_tests.select(repo, ["scripts/ci/select_tests.py"])
    assert "R3-reference" in _rules(selection, "tests/test_pins.py")


def test_r3_la_preuve_porte_la_ligne_de_citation(repo: Path) -> None:
    _write(repo, "tests/test_pins.py", "# ligne 1\n# ligne 2 : src/module.py\ndef test_p():\n    pass\n")
    selection = select_tests.select(repo, ["src/module.py"])
    reasons = selection.selected["tests/test_pins.py"]
    evidence = " ".join(r.evidence for r in reasons)
    assert "l. 2" in evidence


def test_r3_ne_selectionne_pas_un_test_sans_mention(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    assert "R3-reference" not in _rules(selection, "elsewhere/test_remote.py")


# --- R4 : portee depot -----------------------------------------------------


def test_r4_un_test_a_portee_depot_est_toujours_selectionne(repo: Path) -> None:
    _write(
        repo,
        "tests/test_scan.py",
        "from pathlib import Path\n"
        "REPO_ROOT = Path(__file__).resolve().parents[1]\n"
        "def test_scan():\n"
        "    for p in REPO_ROOT.rglob('*.py'):\n"
        "        assert p\n",
    )
    selection = select_tests.select(repo, ["src/module.py"])
    assert "R4-portee-depot" in _rules(selection, "tests/test_scan.py")
    assert "tests/test_scan.py" in selection.repo_wide


def test_r4_un_test_qui_ne_parcourt_pas_le_depot_n_est_pas_portee_depot(repo: Path) -> None:
    _write(
        repo,
        "tests/test_local.py",
        "from pathlib import Path\n"
        "def test_local():\n"
        "    assert Path(__file__).exists()\n",
    )
    selection = select_tests.select(repo, ["src/module.py"])
    assert "tests/test_local.py" not in selection.repo_wide


def test_r4bis_un_parcours_a_racine_non_identifiee_est_selectionne_mais_compte_a_part(repo: Path) -> None:
    _write(
        repo,
        "tests/test_walk.py",
        "from pathlib import Path\n"
        "def test_walk():\n"
        "    here = Path(__file__).parent\n"
        "    assert list(here.glob('*.py'))\n",
    )
    selection = select_tests.select(repo, ["src/module.py"])
    assert "tests/test_walk.py" in selection.parcours_non_racine
    assert "tests/test_walk.py" in selection.selected
    assert "tests/test_walk.py" not in selection.repo_wide


# --- R5 : suite locale -----------------------------------------------------


def test_r5_un_fichier_non_test_dans_un_dossier_de_tests_selectionne_ce_dossier(repo: Path) -> None:
    selection = select_tests.select(repo, ["tests/helpers.py"])
    assert "R5-suite-locale" in _rules(selection, "tests/test_module.py")


# --- R6 : conftest ---------------------------------------------------------


def test_r6_un_conftest_touche_selectionne_le_dossier(repo: Path) -> None:
    selection = select_tests.select(repo, ["tests/conftest.py"])
    assert "R6-conftest" in _rules(selection, "tests/test_module.py")
    assert "R6-conftest" in _rules(selection, "tests/test_other.py")


# --- Non couvert -----------------------------------------------------------


def test_un_fichier_touche_sans_test_est_signale_non_couvert(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/isolate.py"])
    assert selection.uncovered == ["src/isolate.py"]


def test_un_fichier_couvert_n_est_pas_signale_non_couvert(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    assert selection.uncovered == []


# --- Rendu -----------------------------------------------------------------


def test_le_rendu_markdown_porte_le_compte_et_la_reduction(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    markdown = select_tests.render_markdown(selection)
    assert "fichiers de test selectionnes" in markdown
    assert "reduction mesuree" in markdown
    assert "tests/test_module.py" in markdown


def test_la_sortie_json_expose_les_regles_et_les_suites(repo: Path) -> None:
    selection = select_tests.select(repo, ["src/module.py"])
    payload = selection.as_dict()
    assert payload["selected"]["tests/test_module.py"][0]["rule"] == "R2-convention"
    assert "tests" in payload["selected_suites"]
    assert payload["stats"]["fichiers_de_test_du_depot"] == selection.total_tests
    # le plancher "toujours selectionne" est visible dans la sortie
    assert "parcours_non_racine" in payload
    assert "excluded_suites" in payload


# --- Enumeration : suivis git, pas les non suivis (#25510 annexe) ----------


def _git_env(tmp_path: Path) -> dict[str, str]:
    return {
        "GIT_AUTHOR_NAME": "t",
        "GIT_AUTHOR_EMAIL": "t@example.com",
        "GIT_COMMITTER_NAME": "t",
        "GIT_COMMITTER_EMAIL": "t@example.com",
        "PATH": "/usr/bin:/bin:/usr/local/bin",
        "HOME": str(tmp_path),
    }


def test_iter_all_files_enumere_les_suivis_git_pas_les_non_suivis(
    tmp_path: Path,
) -> None:
    """#25510 annexe : le parcours doit suivre `git ls-files`.

    Defaut mesure : dans un checkout de developpement contenant des
    repertoires non suivis (worktrees, scratch), `os.walk` enumerait 250
    fichiers de test la ou la CI en voyait 126 -- la mesure locale ne
    correspondait plus a celle de la CI. Un fichier .py NON suivi ne doit
    pas entrer dans l'enumeration ; un suivi, oui.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    env = _git_env(tmp_path)
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True, env=env)
    _write(repo, "tests/test_module.py", "def test_f():\n    assert True\n")
    # un fichier non suivi : jamais enumere
    _write(
        repo, ".claude/worktrees/autre/tests/test_fantome.py",
        "def test_fantome():\n    assert True\n",
    )
    subprocess.run(["git", "add", "tests/test_module.py"], cwd=repo, check=True, env=env)
    subprocess.run(
        ["git", "commit", "-q", "-m", "init"], cwd=repo, check=True, env=env
    )
    found = select_tests.iter_all_files(repo)
    names = [p.name for p in found]
    assert "test_module.py" in names
    assert "test_fantome.py" not in names


def test_iter_all_files_repli_os_walk_sans_git(tmp_path: Path) -> None:
    """Hors de tout depot git (fixtures), l'enumeration reste le parcours."""
    repo = tmp_path / "plain"
    repo.mkdir()
    _write(repo, "tests/test_module.py", "def test_f():\n    assert True\n")
    found = select_tests.iter_all_files(repo)
    assert [p.name for p in found] == ["test_module.py"]


def test_iter_all_files_refuse_un_sous_dossier_de_depot(tmp_path: Path) -> None:
    """`git -C <sous-dossier> ls-files` rend des chemins relatifs a la
    racine du depot : composer `sous_dossier / chemin` fabriquerait des
    chemins faux. L'enumeration git ne doit s'appliquer que si la racine
    demandee EST la racine git ; sinon, repli sur le parcours."""
    repo = tmp_path / "repo"
    repo.mkdir()
    env = _git_env(tmp_path)
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True, env=env)
    _write(repo, "tests/test_module.py", "def test_f():\n    assert True\n")
    subprocess.run(["git", "add", "tests/test_module.py"], cwd=repo, check=True, env=env)
    subprocess.run(
        ["git", "commit", "-q", "-m", "init"], cwd=repo, check=True, env=env
    )
    sub = repo / "inner"
    sub.mkdir()
    _write(sub, "test_inner.py", "def test_inner():\n    assert True\n")
    # le sous-dossier n'est pas la racine git : le fichier du sous-dossier
    # est enumere par le parcours, avec un chemin exact (pas compose).
    found = select_tests.iter_all_files(sub)
    assert [p.name for p in found] == ["test_inner.py"]


# --- Lecture du diff -------------------------------------------------------


def test_la_lecture_du_diff_git_renvoie_les_fichiers_modifies(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    env = {
        "GIT_AUTHOR_NAME": "t",
        "GIT_AUTHOR_EMAIL": "t@example.com",
        "GIT_COMMITTER_NAME": "t",
        "GIT_COMMITTER_EMAIL": "t@example.com",
        "PATH": "/usr/bin:/bin:/usr/local/bin",
        "HOME": str(tmp_path),
    }
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True, env=env)
    _write(repo, "a.txt", "a\n")
    subprocess.run(["git", "add", "a.txt"], cwd=repo, check=True, env=env)
    subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=repo, check=True, env=env)
    _write(repo, "b.txt", "b\n")
    subprocess.run(["git", "add", "b.txt"], cwd=repo, check=True, env=env)
    subprocess.run(["git", "commit", "-q", "-m", "second"], cwd=repo, check=True, env=env)

    changed = select_tests.changed_from_git(repo, "HEAD~1...HEAD")
    assert changed == ["b.txt"]


def test_un_diff_illisible_rend_une_erreur_explicite(tmp_path: Path) -> None:
    with pytest.raises(RuntimeError):
        select_tests.changed_from_git(tmp_path, "main...HEAD")


# --- CLI -------------------------------------------------------------------


def test_la_cli_rend_du_json_et_signale_le_non_couvert(repo: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CI_DIR / "select_tests.py"),
            "--repo-root",
            str(repo),
            "--changed",
            "src/isolate.py",
            "--json",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["uncovered"] == ["src/isolate.py"]


def test_la_cli_sort_en_echec_si_un_fichier_n_est_pas_couvert(repo: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CI_DIR / "select_tests.py"),
            "--repo-root",
            str(repo),
            "--changed",
            "src/isolate.py",
            "--fail-on-uncovered",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 1
