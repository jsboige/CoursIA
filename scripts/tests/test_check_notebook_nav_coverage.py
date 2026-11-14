"""Tests for scripts/notebook_tools/check_notebook_nav_coverage.py (#24224).

L'organe mesure le deficit de barre de navigation PAR DOSSIER, restreint aux
dossiers qui exhibent deja la convention. Trois proprietes sont testees ici,
et chacune a coute une mesure :

1. **Le dossier scope, jamais le depot.** Un dossier entierement sans barre
   n'a pas de convention a respecter : il ne produit aucun finding. C'est la
   regle qui evite de rougir 79 % du depot (issue #24224 §2).

2. **La barre est un LIEN de navigation, pas un mot.** Une premiere version
   cherchait un marqueur de navigation n'importe ou dans la cellule markdown :
   « next » et « suivant » sont des mots de prose ordinaire, et l'organe
   rendait 1655 carnets « avec barre » sur 1733 -- un faux negatif geant qui
   masquait exactement ce qu'il devait voir. La detection passe par
   `_looks_nav`, importee de check_notebook_nav_chain.py.

3. **Une barre ecrite avec des chevrons est une barre.** #24224 §4 compte la
   presence litterale de « Precedent » / « Suivant » et classe donc `04-5` et
   `04-14` (Audio/04-Applications) parmi les carnets sans barre, alors qu'ils
   en portent une. Le controle ci-dessous fige ce cas.

Controle negatif rouge obligatoire (acceptance #24224 §5) : un dossier
construit a 3 carnets dont 1 avec barre doit rougir, et pas seulement rendre 0
sur `main`.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

import check_notebook_nav_coverage as cov  # noqa: E402

SCRIPT = Path(__file__).resolve().parent.parent / "notebook_tools" / "check_notebook_nav_coverage.py"

# Rangee canonique du depot : index + precedent + suivant sur une seule ligne.
BAR = "**Navigation** : [Index](README.md) | [<< Precedent](01-a.ipynb) | [Suivant >>](03-c.ipynb)"
# Variante sans les mots « Precedent » / « Suivant » : c'est la forme de
# Audio/04-5, que #24224 §4 classe a tort comme « sans barre ».
BAR_CHEVRONS = "**Navigation :** [<< 01-a](01-a.ipynb) | [Index](README.md) | [Image >>](../../Image/README.md)"
NO_BAR = "# Titre\n\nUne phrase de prose, sans aucun lien de navigation."


def _write_nb(path: Path, source: str) -> Path:
    nb = {
        "cells": [{"cell_type": "markdown", "metadata": {}, "source": source}],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


def _folder(tmp_path: Path, name: str = "Serie", bars=(), nobars=()):
    folder = tmp_path / name
    folder.mkdir(parents=True, exist_ok=True)
    for stem in bars:
        _write_nb(folder / f"{stem}.ipynb", BAR)
    for stem in nobars:
        _write_nb(folder / f"{stem}.ipynb", NO_BAR)
    return folder


def _run(*args):
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


# --- controle negatif rouge (acceptance #24224 §5) -------------------------

def test_three_notebooks_one_with_bar_is_a_finding(tmp_path):
    """3 carnets, 1 avec barre : le dossier est en deficit de 2."""
    _folder(tmp_path, bars=("01-a",), nobars=("02-b", "03-c"))
    folders, errors = cov.collect(tmp_path)
    report = cov.analyse(folders)
    assert errors == []
    assert report["folders_with_convention"] == 1
    assert report["folders_deficit"] == 1
    finding = report["findings"][0]
    assert finding["folder"] == "Serie"
    assert (finding["with_bar"], finding["without_bar"]) == (1, 2)
    assert finding["missing"] == ["Serie/02-b.ipynb", "Serie/03-c.ipynb"]


def test_negative_control_goes_red_via_cli(tmp_path):
    """Le controle negatif rougit par l'organe, pas seulement en interne."""
    _folder(tmp_path, bars=("01-a",), nobars=("02-b", "03-c"))
    proc = _run("--root", str(tmp_path), "--check", "--quiet")
    assert proc.returncode == 1, proc.stderr
    # Et sans --check, le rapport sort en advisory (code 0).
    assert _run("--root", str(tmp_path), "--quiet").returncode == 0


def test_complete_folder_is_not_a_finding(tmp_path):
    _folder(tmp_path, bars=("01-a", "02-b", "03-c"))
    report = cov.analyse(cov.collect(tmp_path)[0])
    assert report["findings"] == []
    assert report["complete"] == [{"folder": "Serie", "with_bar": 3}]


def test_folder_without_any_bar_is_out_of_scope(tmp_path):
    """Un dossier sans convention n'est pas mesure : pas de finding, pas de bruit."""
    _folder(tmp_path, nobars=("01-a", "02-b", "03-c"))
    report = cov.analyse(cov.collect(tmp_path)[0])
    assert report["findings"] == []
    assert report["folders_with_convention"] == 0
    assert report["no_convention"] == ["Serie"]
    assert report["notebooks_without_bar"] == 3
    assert _run("--root", str(tmp_path), "--check", "--quiet").returncode == 0


# --- ce qu'est une barre ---------------------------------------------------

def test_prose_containing_a_nav_word_is_not_a_bar(tmp_path):
    """Regression mesuree : « next » en prose ne fait pas une barre.

    La premiere version cherchait le marqueur dans toute la cellule et rendait
    1655 carnets « avec barre » sur 1733.
    """
    nb = tmp_path / "prose.ipynb"
    _write_nb(nb, "In the next section we will see the following results.")
    assert cov.has_nav_bar(nb) is False


def test_bar_written_with_chevrons_is_detected(tmp_path):
    """Audio/04-5 porte une barre sans les mots « Precedent » / « Suivant »."""
    nb = tmp_path / "chevrons.ipynb"
    _write_nb(nb, BAR_CHEVRONS)
    assert cov.has_nav_bar(nb) is True


def test_canonical_bar_is_detected(tmp_path):
    nb = tmp_path / "canon.ipynb"
    _write_nb(nb, BAR)
    assert cov.has_nav_bar(nb) is True


def test_unreadable_notebook_is_an_error_not_a_gap(tmp_path):
    """JSON corrompu : ni avec ni sans barre -- compter un deficit serait faux."""
    (tmp_path / "Serie").mkdir()
    (tmp_path / "Serie" / "casse.ipynb").write_text("{not json", encoding="utf-8")
    folders, errors = cov.collect(tmp_path)
    assert errors == ["Serie/casse.ipynb"]
    report = cov.analyse(folders)
    assert report["notebooks_without_bar"] == 0
    assert report["findings"] == []


def test_detection_reuses_the_chain_vocabulary():
    """Une seule definition de « lien de navigation » dans le depot."""
    from check_notebook_nav_chain import _looks_nav
    assert cov._looks_nav is _looks_nav


# --- baseline / cliquet ----------------------------------------------------

def test_baseline_suppresses_known_deficit_and_flags_only_new(tmp_path):
    _folder(tmp_path, bars=("01-a",), nobars=("02-b",))
    report = cov.analyse(cov.collect(tmp_path)[0])
    baseline = cov._baseline_doc(report, {"non_main": False})
    assert baseline["deficit"] == {"Serie": ["Serie/02-b.ipynb"]}

    new_folders, new_notebooks = cov._new_deficit(report, baseline)
    assert new_folders == [] and new_notebooks == []

    # Un carnet entre dans le deficit : lui seul est nouveau.
    _write_nb(tmp_path / "Serie" / "03-c.ipynb", NO_BAR)
    report2 = cov.analyse(cov.collect(tmp_path)[0])
    new_folders, new_notebooks = cov._new_deficit(report2, baseline)
    assert new_notebooks == ["Serie/03-c.ipynb"]
    assert new_folders[0]["new"] == ["Serie/03-c.ipynb"]


def test_baseline_is_a_set_not_a_count(tmp_path):
    """Un echange (un carnet sorti, un autre entre) n'est pas « rien n'a change »."""
    _folder(tmp_path, bars=("01-a",), nobars=("02-b",))
    baseline = cov._baseline_doc(cov.analyse(cov.collect(tmp_path)[0]), {})

    (tmp_path / "Serie" / "02-b.ipynb").unlink()
    _write_nb(tmp_path / "Serie" / "09-z.ipynb", NO_BAR)
    report = cov.analyse(cov.collect(tmp_path)[0])
    assert report["findings"][0]["without_bar"] == 1  # meme compte qu'avant
    _, new_notebooks = cov._new_deficit(report, baseline)
    assert new_notebooks == ["Serie/09-z.ipynb"]


def test_cli_baseline_refuses_outside_clean_main_then_roundtrips(tmp_path):
    """Ecriture refusee hors de `main` propre (#22121), acceptee avec --baseline-anyway."""
    _folder(tmp_path, bars=("01-a",), nobars=("02-b",))
    baseline_path = tmp_path / "baseline.json"

    refused = _run("--root", str(tmp_path), "--baseline",
                   "--baseline-path", str(baseline_path))
    assert refused.returncode in (0, 3), refused.stderr
    if refused.returncode == 3:
        assert "refuse" in refused.stderr
        assert not baseline_path.exists()

    written = _run("--root", str(tmp_path), "--baseline", "--baseline-anyway",
                   "--baseline-path", str(baseline_path))
    assert written.returncode == 0, written.stderr
    doc = json.loads(baseline_path.read_text(encoding="utf-8"))
    assert doc["deficit"] == {"Serie": ["Serie/02-b.ipynb"]}
    assert doc["instrument"] == cov.INSTRUMENT_VERSION

    assert _run("--root", str(tmp_path), "--check", "--quiet",
                "--baseline-path", str(baseline_path)).returncode == 0

    _write_nb(tmp_path / "Serie" / "04-d.ipynb", NO_BAR)
    assert _run("--root", str(tmp_path), "--check", "--quiet",
                "--baseline-path", str(baseline_path)).returncode == 1


def test_json_output_is_machine_readable(tmp_path):
    _folder(tmp_path, bars=("01-a",), nobars=("02-b",))
    proc = _run("--root", str(tmp_path), "--json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["folders_deficit"] == 1
    assert payload["findings"][0]["folder"] == "Serie"
    assert payload["new_notebooks"] == ["Serie/02-b.ipynb"]
