"""Tests pour scripts/notebook_tools/check_rust_notebook_contract.py.

Le contrat Rust (Pli 3 de l'Epic #26510, #27098, point 5) repose sur trois
controles : le `:dep` en tete de carnet, l'absence d'erreur volontaire (C.1) et
l'execution complete commitee (C.2).

Les tests sont ecrits dans les deux sens :

- **controle positif** sur le carnet Rust reel du depot (le pilote DancingLinks)
  : il doit passer sans finding ;
- **controles negatifs** sur des copies mutees : chaque mutation doit produire
  le finding attendu, nomme et indexe ;
- **controle de faux positif** : un `:dep` cite dans un commentaire `//` n'est
  pas une dependance, il ne doit declencher aucun finding ;
- **controle d'instrument** : un carnet illisible rend 2, jamais un vert muet.
"""

import json
import shutil
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

from check_rust_notebook_contract import (  # noqa: E402
    check_notebook,
    is_rust_notebook,
    main,
    run,
)

PILOT = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku" / "Sudoku-02-DancingLinks-Rust.ipynb"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _dump(path: Path, notebook: dict) -> Path:
    path.write_text(json.dumps(notebook, ensure_ascii=False, indent=1), encoding="utf-8")
    return path


def _copy_pilot(tmp_path: Path) -> Path:
    """Copie du carnet Rust pilote, prete a muter."""
    target = tmp_path / "copie-Rust.ipynb"
    shutil.copy(PILOT, target)
    return target


def _codes(notebook: dict) -> list[int]:
    return [i for i, c in enumerate(notebook["cells"]) if c["cell_type"] == "code"]


# ---------------------------------------------------------------------------
# Detection d'un carnet Rust
# ---------------------------------------------------------------------------

def test_le_suffixe_canonique_suffit(tmp_path: Path) -> None:
    assert is_rust_notebook(Path("x-Rust.ipynb"))


def test_le_kernelspec_rust_suffit(tmp_path: Path) -> None:
    path = tmp_path / "sans-suffixe.ipynb"
    _dump(path, {"cells": [], "metadata": {"kernelspec": {"name": "rust"}}})
    assert is_rust_notebook(path, _load(path))


def test_un_carnet_non_rust_est_ignore(tmp_path: Path) -> None:
    path = tmp_path / "python.ipynb"
    _dump(path, {"cells": [], "metadata": {"kernelspec": {"name": "python3"}}})
    assert not is_rust_notebook(path, _load(path))
    assert check_notebook(path) == []


# ---------------------------------------------------------------------------
# Controle positif -- le carnet Rust du depot passe
# ---------------------------------------------------------------------------

def test_le_carnet_pilote_passe_sans_finding() -> None:
    findings = check_notebook(PILOT)
    assert findings == [], "le carnet Rust du depot doit etre conforme : {}".format(findings)


def test_le_carnet_pilote_passe_en_ligne_de_commande(capsys: pytest.CaptureFixture) -> None:
    rc = main([str(PILOT)])
    assert rc == 0
    assert "0 finding(s)" in capsys.readouterr().out


# ---------------------------------------------------------------------------
# Controle 1 -- le `:dep` se declare en tete
# ---------------------------------------------------------------------------

def test_un_dep_tardif_est_signale_avec_son_index(tmp_path: Path) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    # On deplace la ligne `:dep` du code vers une cellule ulterieure.
    first = notebook["cells"][codes[0]]
    first["source"] = [l for l in "".join(first["source"]).splitlines()
                       if not l.strip().startswith(":dep")]
    notebook["cells"][codes[2]]["source"] = [":dep dlx = \"0.8\""]
    _dump(path, notebook)

    findings = check_notebook(path)
    dep = [f for f in findings if f["code"] == "DEP_TARDIVE"]
    assert len(dep) == 1
    assert dep[0]["cell"] == codes[2]


def test_un_carnet_sans_dep_nest_pas_un_finding(tmp_path: Path) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    for cell in notebook["cells"]:
        if cell["cell_type"] == "code":
            cell["source"] = [l for l in "".join(cell["source"]).splitlines()
                              if not l.strip().startswith(":dep")]
    _dump(path, notebook)

    assert [f for f in check_notebook(path) if f["code"] == "DEP_TARDIVE"] == []


def test_un_dep_dans_un_commentaire_ne_compte_pas(tmp_path: Path) -> None:
    """Faux positif aReprevenir : `:dep` cite dans un commentaire n'est pas une
    dependance, et un carnet sans dependance reelle ne doit pas rougir."""
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    notebook["cells"][codes[0]]["source"] = [
        "// pour ajouter une dependance : :dep serde = \"1.0\"",
        "let x = 1;",
    ]
    for cell in notebook["cells"]:
        if cell["cell_type"] == "code":
            text = "".join(cell["source"])
            if text.strip().startswith(":dep"):
                cell["source"] = [l for l in text.splitlines()
                                  if not l.strip().startswith(":dep")]
    _dump(path, notebook)

    findings = check_notebook(path)
    assert [f for f in findings if f["code"] == "DEP_TARDIVE"] == []


# ---------------------------------------------------------------------------
# Controle 2 -- C.1, pas d'erreur volontaire
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("motif", ["panic!(\"boom\")", "unimplemented!()",
                                  "todo!(\"a faire\")", "unreachable!()"])
def test_une_erreur_volontaire_est_signalee(tmp_path: Path, motif: str) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    notebook["cells"][codes[-1]]["source"] = [motif]
    _dump(path, notebook)

    findings = [f for f in check_notebook(path) if f["code"] == "C1_RUST"]
    assert len(findings) == 1
    assert findings[0]["cell"] == codes[-1]


def test_un_motif_cite_dans_un_commentaire_ne_compte_pas(tmp_path: Path) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    notebook["cells"][codes[-1]]["source"] = [
        "// TODO etudiant : ne pas panic!(\"boom\") ici",
        "let y = 2;",
    ]
    _dump(path, notebook)

    assert [f for f in check_notebook(path) if f["code"] == "C1_RUST"] == []


# ---------------------------------------------------------------------------
# Controle 3 -- C.2, execution complete commitee
# ---------------------------------------------------------------------------

def test_une_cellule_non_executee_est_signalee(tmp_path: Path) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    notebook["cells"][codes[1]]["execution_count"] = None
    _dump(path, notebook)

    findings = [f for f in check_notebook(path) if f["code"] == "C2_EXEC"]
    assert len(findings) == 1
    assert findings[0]["cell"] == codes[1]


def test_une_cellule_sans_sortie_est_conforme(tmp_path: Path) -> None:
    """Sous evcxr une cellule de declarations n'affiche rien : l'absence
    d'`outputs` n'est pas un defaut, l'absence d'`execution_count` en est un."""
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    for cell in notebook["cells"]:
        if cell["cell_type"] == "code":
            cell["outputs"] = []
    _dump(path, notebook)

    assert [f for f in check_notebook(path) if f["code"] == "C2_EXEC"] == []


# ---------------------------------------------------------------------------
# Sorties de l'instrument
# ---------------------------------------------------------------------------

def test_un_carnet_illisible_rend_une_pas_un_vert(tmp_path: Path) -> None:
    path = tmp_path / "casse-Rust.ipynb"
    path.write_text("{ pas du json", encoding="utf-8")

    findings = check_notebook(path)
    assert len(findings) == 1
    assert findings[0]["code"] == "NOTEBOOK_ILLISIBLE"


def test_un_carnet_absent_rend_2(tmp_path: Path) -> None:
    rc, report = run([tmp_path / "absent-Rust.ipynb"])
    assert rc == 2
    assert report["errors"]


def test_le_code_de_sortie_refuse_un_finding(tmp_path: Path) -> None:
    path = _copy_pilot(tmp_path)
    notebook = _load(path)
    codes = _codes(notebook)
    notebook["cells"][codes[0]]["source"] = ["panic!(\"boom\")"]
    _dump(path, notebook)

    assert main([str(path)]) == 1


def test_un_diff_illisible_rend_2(tmp_path: Path, capsys: pytest.CaptureFixture) -> None:
    assert main(["--diff", "origin/main...HEAD", "--repo-root", str(tmp_path)]) == 2
    assert '"rc": 2' in capsys.readouterr().out
