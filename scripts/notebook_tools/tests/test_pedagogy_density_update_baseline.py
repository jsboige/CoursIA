"""Tests for the incremental baseline update of scripts/notebook_tools/pedagogy_density.py.

#26762: rewriting the whole density baseline in one go mixes two decisions --
a VALUE change (a notebook whose prose/code ratio moved) and a SET change (a
notebook the baseline never keyed). The set change is a decision: 155 notebooks
were never under the ratchet, and admitting them "because the file was
rewritten" is not a measurement, it is an accident.

These tests pin the three behaviours the issue asks for:

* ``--only <paths>`` rewrites only the named keys; the others are carried
  over verbatim;
* keying a notebook the baseline never keyed requires an explicit
  ``--admit-unkeyed``;
* the write keeps the canonical (sorted) order, so a full run that changes no
  value produces a byte-identical file -- an EMPTY diff, not a churn of
  re-ordered lines.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import pedagogy_density as pd

import pytest

A_KEY = "MyIA.AI.Notebooks/Foo/A.ipynb"
B_KEY = "MyIA.AI.Notebooks/Foo/B.ipynb"


def _notebook(markdown: str, code: str = "print(1)") -> str:
    """A minimal notebook whose density is ``len(markdown)`` (one code cell)."""
    return json.dumps({
        "cells": [
            {"cell_type": "markdown", "source": markdown.splitlines(keepends=True)},
            {"cell_type": "code", "source": code.splitlines(keepends=True)},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    })


def _write(root: Path, key: str, markdown: str, code: str = "print(1)") -> None:
    path = root / key
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_notebook(markdown, code), encoding="utf-8")


@pytest.fixture
def baseline_file(tmp_path, monkeypatch):
    """A baseline file in a tmp_path, wired as the organ's :data:`BASELINE_FILE`.

    The CWD is moved to the tmp_path: the population keys are repo-relative
    paths, and the measurement reads them from the working directory.
    """
    monkeypatch.chdir(tmp_path)
    target = tmp_path / "pedagogy_density_baseline.json"
    monkeypatch.setattr(pd, "BASELINE_FILE", target)
    return target


@pytest.fixture
def population(monkeypatch):
    """Control the population of the organ (the tracked, density-judged set)."""

    def _set(keys):
        monkeypatch.setattr(pd, "_baseline_population", lambda: [Path(k) for k in keys])

    return _set


def _payload(baseline_file: Path) -> dict:
    return json.loads(baseline_file.read_text(encoding="utf-8"))


class TestFullRun:
    """The complete run: the keys already present are re-measured."""

    def test_une_execution_sans_changement_de_valeur_rend_un_diff_nul(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY, B_KEY])

        assert pd._update_baseline(admit_unkeyed=True) == 0
        before = baseline_file.read_bytes()

        # Second run, nothing changed on disk: the file must come out
        # byte-identical (a null diff), which is the property the canonical
        # order buys.
        assert pd._update_baseline() == 0
        assert baseline_file.read_bytes() == before

    def test_le_mode_complet_n_admet_pas_les_carnets_jamais_keyes(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0

        # B joins the population without being keyed: it must stay out.
        population([A_KEY, B_KEY])
        assert pd._update_baseline() == 0

        payload = _payload(baseline_file)
        assert set(payload["notebooks"]) == {A_KEY}
        assert payload["count"] == 1

    def test_admit_unkeyed_admet_le_carnet_jamais_keye(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        population([A_KEY, B_KEY])

        assert pd._update_baseline(admit_unkeyed=True) == 0

        payload = _payload(baseline_file)
        assert set(payload["notebooks"]) == {A_KEY, B_KEY}
        assert payload["count"] == 2


class TestIncrementalRun:
    """``--only``: only the named keys are rewritten."""

    def test_le_mode_incremental_ne_reecrit_que_les_cles_nommees(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY, B_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        old_b = _payload(baseline_file)["notebooks"][B_KEY]

        # B's prose grows: its density MOVES, but B was not named.
        _write(tmp_path, B_KEY, "# Autre\n\nUn paragraphe de plus.\n")
        assert pd._update_baseline(only=[A_KEY]) == 0

        payload = _payload(baseline_file)
        assert payload["notebooks"][B_KEY] == old_b

    def test_la_cle_nommee_est_bien_remesuree(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0

        _write(tmp_path, A_KEY, "# Titre\n\nUn paragraphe de plus.\n")
        assert pd._update_baseline(only=[A_KEY]) == 0

        payload = _payload(baseline_file)
        expected = round(len("# Titre\n\nUn paragraphe de plus.\n") / 1, 3)
        assert payload["notebooks"][A_KEY] == expected

    def test_un_carnet_jamais_keye_exige_un_admit_unkeyed_explicite(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        before = baseline_file.read_bytes()
        population([A_KEY, B_KEY])

        assert pd._update_baseline(only=[B_KEY]) == 2
        assert baseline_file.read_bytes() == before

    def test_admit_unkeyed_admet_le_carnet_nomme(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        population([A_KEY, B_KEY])

        assert pd._update_baseline(only=[B_KEY], admit_unkeyed=True) == 0

        payload = _payload(baseline_file)
        assert B_KEY in payload["notebooks"]
        assert payload["notebooks"][B_KEY] == round(len("# Autre\n") / 1, 3)

    def test_un_chemin_hors_population_est_refuse(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        before = baseline_file.read_bytes()

        assert pd._update_baseline(only=["MyIA.AI.Notebooks/Foo/ZZZ.ipynb"]) == 2
        assert baseline_file.read_bytes() == before

    def test_un_carnet_keye_et_devenu_ilisible_conserve_sa_valeur(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        population([A_KEY])
        assert pd._update_baseline(admit_unkeyed=True) == 0
        old_a = _payload(baseline_file)["notebooks"][A_KEY]

        (tmp_path / A_KEY).write_text("{ pas du json", encoding="utf-8")
        assert pd._update_baseline(only=[A_KEY]) == 0

        payload = _payload(baseline_file)
        assert payload["notebooks"][A_KEY] == old_a
        assert any(e["path"] == A_KEY for e in payload.get("unmeasured", []))


class TestCanonicalOrder:
    """The write keeps the canonical (sorted) order."""

    def test_les_cles_sont_ecrites_dans_l_ordre_canonique(
        self, tmp_path, baseline_file, population
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        _write(tmp_path, B_KEY, "# Autre\n")
        population([A_KEY, B_KEY])

        assert pd._update_baseline(admit_unkeyed=True) == 0

        keys = list(_payload(baseline_file)["notebooks"])
        assert keys == sorted(keys)


class TestCli:
    """The CLI surface of the two flags."""

    def test_le_cli_expose_only_et_admit_unkeyed(
        self, tmp_path, baseline_file, population, capsys
    ):
        _write(tmp_path, A_KEY, "# Titre\n")
        population([A_KEY])

        assert pd.main(["--update-baseline", "--admit-unkeyed"]) == 0
        assert A_KEY in _payload(baseline_file)["notebooks"]

    def test_only_hors_update_baseline_est_refuse(self, baseline_file):
        with pytest.raises(SystemExit):
            pd.main(["--only", A_KEY])

    def test_only_sans_chemin_est_refuse(self, baseline_file):
        with pytest.raises(SystemExit):
            pd.main(["--update-baseline", "--only"])
