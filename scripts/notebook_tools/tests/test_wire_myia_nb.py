"""Tests pour scripts/notebook_tools/wire_myia_nb.py.

Le cablage de la crate `myia_nb` (Pli 3 de l'Epic #26510, #27098, organe 3)
repose sur un fixer volontairement etroit : il pose la ligne `:dep` en tete du
premier bloc de code et ne remplace que les definitions de `py_bool` dont le
corps est semantiquement identique a la version partagee.

Les tests sont ecrits dans les deux sens :

- **controle positif** sur le carnet pilote reel (`Sudoku-14-BDD-Rust.ipynb`) :
  il est deja cable, `--check` rend 0 ;
- **controle negatif** sur un carnet reel du depot non cable : `--check` rend 1
  et nomme le `py_bool` a remplacer ;
- **controles unitaires** du plan : la forme stricte est reconnue, les formes
  voisines (autre texte, autre variable, type incoherent) sont refusees et
  signalees, jamais reecrites ;
- **profondeur du chemin** : le `:dep` est relatif au dossier du carnet ;
- **idempotence et fin de ligne** : deux `--apply` laissent le fichier
  byte-identique, un carnet CRLF le reste ;
- **controle d'instrument** : un carnet illisible est rapporte, jamais un vert muet.
"""

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

from wire_myia_nb import _dep_line, analyse, apply_plan, main  # noqa: E402

PILOT = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku" / "Sudoku-14-BDD-Rust.ipynb"

STRICT = "fn py_bool(b: bool) -> &'static str { if b { \"True\" } else { \"False\" } }"
AS_STRING = (
    'fn py_bool(b: bool) -> String '
    '{ if b { "True".to_string() } else { "False".to_string() } }'
)
# Retour String mais corps sans `.to_string()` : ce n'est pas la meme fonction.
STRING_SANS_TO_STRING = (
    'fn py_bool(b: bool) -> String { if b { "True" } else { "False" } }'
)
AUTRE_TEXTE = "fn py_bool(b: bool) -> &'static str { if b { \"Vrai\" } else { \"Faux\" } }"
AUTRE_VARIABLE = (
    'fn py_bool(b: bool) -> &\'static str { if c { "True" } else { "False" } }'
)
PY_LIST_LOCAL = 'fn py_list(mask: u32) -> String { format!("{:b}", mask) }'


def _nb(*sources: str) -> dict:
    """Carnet minimal : une cellule code par source fournie."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [s],
            }
            for s in sources
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _sources(nb: dict) -> list[str]:
    return ["".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code"]


def _write_nb(path: Path, nb: dict, newline: str = "\n") -> Path:
    text = json.dumps(nb, indent=1, ensure_ascii=False)
    if newline == "\r\n":
        text = text.replace("\n", "\r\n")
    path.write_text(text, encoding="utf-8", newline="")
    return path


# ---------------------------------------------------------------------------
# Profondeur du chemin : le kernel resout `path` contre le dossier du carnet
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "relative_depth, prefix",
    [
        # La crate vit sous `MyIA.AI.Notebooks/Config/rust/` : un carnet a `d`
        # niveaux sous l'arbre des carnets remonte `d` niveau pour l'atteindre,
        # et le carnet a la racine (`d = 0`) y descend sans remonter.
        (1, ""),
        (2, "../"),
        (3, "../../"),
        (4, "../../../"),
    ],
)
def test_dep_est_relatif_au_dossier_du_carnet(
    tmp_path: Path, relative_depth: int, prefix: str
) -> None:
    """Le carnet est a `relative_depth - 1` niveaux sous `MyIA.AI.Notebooks/`."""
    notebook = tmp_path / "MyIA.AI.Notebooks" / Path(*["serie"] * (relative_depth - 1))
    notebook.mkdir(parents=True)
    nb_path = notebook / "Exemple-Rust.ipynb"
    line = _dep_line(nb_path, tmp_path)
    assert line == ':dep myia_nb = { path = "%sConfig/rust/myia_nb" }' % prefix


# ---------------------------------------------------------------------------
# Le plan : forme stricte reconnue, voisines refusees et signalees
# ---------------------------------------------------------------------------


def test_forme_stricte_reconnue() -> None:
    plan = analyse(_nb(STRICT), "dep")
    assert len(plan["replacements"]) == 1
    assert plan["replacements"][0][3] == "static_str"
    assert plan["unhandled"] == []


def test_forme_string_reconnue() -> None:
    plan = analyse(_nb(AS_STRING), "dep")
    assert len(plan["replacements"]) == 1
    assert plan["replacements"][0][3] == "string"


@pytest.mark.parametrize(
    "source",
    [
        STRING_SANS_TO_STRING,
        AUTRE_TEXTE,
        AUTRE_VARIABLE,
    ],
)
def test_formes_voisines_refusees_et_signalees(source: str) -> None:
    plan = analyse(_nb(source), "dep")
    assert plan["replacements"] == []
    assert plan["unhandled"] == [{"cell": 0, "name": "py_bool"}]


def test_autres_py_signales_jamais_reecrites() -> None:
    nb = _nb(STRICT, PY_LIST_LOCAL)
    plan = analyse(nb, "dep")
    assert plan["unhandled"] == [{"cell": 1, "name": "py_list"}]
    apply_plan(nb, plan)
    assert "fn py_list(mask: u32)" in _sources(nb)[1]


# ---------------------------------------------------------------------------
# L'application : `:dep` en tete, `use` a la place de la definition
# ---------------------------------------------------------------------------


def test_apply_pose_le_dep_en_tete_du_premier_bloc() -> None:
    nb = _nb("let x = 1;", STRICT)
    dep = ':dep myia_nb = { path = "../Config/rust/myia_nb" }'
    stats = apply_plan(nb, analyse(nb, dep))
    cellules = _sources(nb)
    assert cellules[0].startswith(dep + "\n")
    assert "use myia_nb::py_bool;" in cellules[1]
    assert stats == {"py_bool_removed": 1, "dep_added": True, "dep_path_updated": False}


def test_type_string_prend_py_bool_string_et_garde_le_nom_appele() -> None:
    nb = _nb('let s = py_bool(true);\n' + AS_STRING)
    apply_plan(nb, analyse(nb, ':dep myia_nb = { path = "../Config/rust/myia_nb" }'))
    source = _sources(nb)[0]
    assert "use myia_nb::py_bool_string as py_bool;" in source
    # Aucun site d'appel ne bouge.
    assert "let s = py_bool(true);" in source


def test_dep_deja_present_n_est_pas_duplique() -> None:
    dep = ':dep myia_nb = { path = "../Config/rust/myia_nb" }'
    nb = _nb(dep + "\nlet x = 1;")
    stats = apply_plan(nb, analyse(nb, dep))
    assert stats["dep_added"] is False
    assert _sources(nb)[0].count(":dep myia_nb") == 1


# ---------------------------------------------------------------------------
# L'organe en ligne de commande : check / apply / idempotence / instrument
# ---------------------------------------------------------------------------


def test_dep_au_chemin_perime_est_reecrit() -> None:
    """Crate deplacee : la ligne existe, mais son chemin ne resout plus."""
    perime = ':dep myia_nb = { path = "../AncienRangement/myia_nb" }'
    nouveau = ':dep myia_nb = { path = "../Config/rust/myia_nb" }'
    nb = _nb(perime + "\nlet x = 1;")
    plan = analyse(nb, nouveau)
    assert plan["dep_present"] is True
    assert plan["dep_stale"] is not None
    stats = apply_plan(nb, plan)
    assert stats["dep_path_updated"] is True
    assert _sources(nb)[0].startswith(nouveau + "\n")
    assert "AncienRangement" not in _sources(nb)[0]


def test_check_voit_un_chemin_perime_puis_apply_le_repare(tmp_path: Path) -> None:
    perime = ':dep myia_nb = { path = "../AncienRangement/myia_nb" }'
    path = _write_nb(tmp_path / "Exemple-Rust.ipynb", _nb(perime + "\nlet x = 1;"))
    assert main(["--check", str(path), "--repo-root", str(tmp_path)]) == 1
    assert main(["--apply", str(path), "--repo-root", str(tmp_path)]) == 0
    assert main(["--check", str(path), "--repo-root", str(tmp_path)]) == 0


def test_check_rend_un_carnet_non_cable(tmp_path: Path) -> None:
    path = _write_nb(tmp_path / "Exemple-Rust.ipynb", _nb(STRICT))
    assert main(["--check", str(path), "--repo-root", str(tmp_path)]) == 1


def test_apply_puis_check_rend_zero_et_deux_apply_sont_idempotents(
    tmp_path: Path,
) -> None:
    path = _write_nb(tmp_path / "Exemple-Rust.ipynb", _nb(STRICT))
    assert main(["--apply", str(path), "--repo-root", str(tmp_path)]) == 0
    premier = path.read_bytes()
    assert main(["--check", str(path), "--repo-root", str(tmp_path)]) == 0
    assert main(["--apply", str(path), "--repo-root", str(tmp_path)]) == 0
    assert path.read_bytes() == premier


def test_crlf_preserve(tmp_path: Path) -> None:
    path = _write_nb(tmp_path / "Exemple-Rust.ipynb", _nb(STRICT), newline="\r\n")
    assert main(["--apply", str(path), "--repo-root", str(tmp_path)]) == 0
    with open(path, encoding="utf-8", newline="") as f:
        text = f.read()
    assert "\r\n" in text
    assert text.count("\n") == text.count("\r\n")


def test_carnet_illisible_est_rapporte(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    path = tmp_path / "Casse-Rust.ipynb"
    path.write_text("{ pas du json", encoding="utf-8")
    assert main(["--check", str(path), "--repo-root", str(tmp_path), "--json"]) == 1
    rapport = json.loads(capsys.readouterr().out)
    assert rapport["notebooks"][0]["error"]
    # En mode apply, la panne de l'instrument rend 2, jamais 0.
    assert main(["--apply", str(path), "--repo-root", str(tmp_path)]) == 2


def test_aucun_carnet_rend_deux(tmp_path: Path) -> None:
    (tmp_path / "MyIA.AI.Notebooks").mkdir()
    assert main(["--check", "--all", "--repo-root", str(tmp_path)]) == 2


# ---------------------------------------------------------------------------
# Controle positif et negatif sur les carnets reels du depot
# ---------------------------------------------------------------------------


def test_controle_positif_le_pilote_est_cable() -> None:
    assert PILOT.exists(), "le carnet pilote a disparu du depot"
    assert main(["--check", str(PILOT), "--repo-root", str(REPO_ROOT)]) == 0


def test_controle_negatif_un_carnet_reel_non_cable() -> None:
    """Au moins un carnet Rust du depot n'est pas encore cable (adoption au fil des grains)."""
    candidats = []
    for path in sorted((REPO_ROOT / "MyIA.AI.Notebooks").rglob("*-Rust.ipynb")):
        if path == PILOT:
            continue
        with open(path, encoding="utf-8", newline="") as f:
            nb = json.load(f)
        plan = analyse(nb, _dep_line(path, REPO_ROOT))
        if plan["replacements"] or not plan["dep_present"]:
            candidats.append(path)
    if not candidats:
        pytest.skip("tous les carnets Rust sont cables : plus de controle negatif possible")
    path = candidats[0]
    assert main(["--check", str(path), "--repo-root", str(REPO_ROOT)]) == 1
