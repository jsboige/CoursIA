"""Tests for audit_quantbooks_unexec.py — QuantBook unexecuted-cell classifier.

All tests are hermetic: build a temp directory tree of synthetic quantbooks
covering each classification branch + config.json edge cases, then run the
real ``scan_notebook`` / ``scan_projects`` / ``main`` functions against it.

Coverage:
  - ``_is_unexecuted_code`` cell filter (code only, no execution_count, no outputs)
  - ``_has_strip_marker`` markdown Stop&Repair regex (case-insensitive, multiple phrasings)
  - ``scan_notebook`` classification: HEALTHY / STOP_REPAIR_STRIPPED / PREEXISTING_UNEXEC / ERROR
  - ``_config_status`` config.json parsing: ALIVE / DEAD / MISSING / malformed
  - ``scan_projects`` glob + ordering + missing root
  - ``main`` --json / --project / --check exit codes / --md write
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import audit_quantbooks_unexec as aqm  # noqa: E402


# -- helpers --

def _cell(cell_type, source="", execution_count=None, outputs=None):
    """Build a minimal notebook cell dict."""
    return {
        "cell_type": cell_type,
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
    }


def _nb(cells, kernel="python3"):
    """Build a minimal notebook dict with kernelspec."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel}},
    }


def _write_project(root: Path, name: str, cells, config: dict | None = None,
                   kernel: str = "python3") -> Path:
    """Create ``root/<name>/quantbook.ipynb`` (+ optional config.json)."""
    proj = root / name
    proj.mkdir(parents=True, exist_ok=True)
    nb = _nb(cells, kernel=kernel)
    (proj / "quantbook.ipynb").write_text(
        json.dumps(nb, ensure_ascii=False), encoding="utf-8"
    )
    if config is not None:
        (proj / "config.json").write_text(
            json.dumps(config, ensure_ascii=False), encoding="utf-8"
        )
    return proj


# -- _is_unexecuted_code --

class TestIsUnexecutedCode:
    def test_code_cell_without_exec_count(self):
        c = _cell("code", "qb = QuantBook()", execution_count=None, outputs=[])
        assert aqm._is_unexecuted_code(c) is True

    def test_code_cell_with_exec_count(self):
        c = _cell("code", execution_count=1, outputs=[])
        assert aqm._is_unexecuted_code(c) is False

    def test_code_cell_with_outputs_but_no_exec_count(self):
        c = _cell("code", execution_count=None, outputs=[{"output_type": "stream"}])
        assert aqm._is_unexecuted_code(c) is False

    def test_markdown_cell_ignored(self):
        c = _cell("markdown", execution_count=None, outputs=[])
        assert aqm._is_unexecuted_code(c) is False

    def test_outputs_none_treated_as_empty(self):
        # Cell where outputs key is missing entirely
        c = {"cell_type": "code", "source": "qb = QuantBook()", "execution_count": None}
        assert aqm._is_unexecuted_code(c) is True

    def test_empty_code_cell_is_not_unexecuted(self):
        # Une cellule vide satisfait ``ec is None and outputs == []`` par
        # construction : il n'y a rien a executer, donc rien a signaler.
        # Sans ce garde-fou, --check echoue en CI sur un notebook sain et la
        # seule remediation serait de supprimer les cellules vides.
        assert aqm._is_unexecuted_code(_cell("code", "")) is False

    def test_whitespace_only_code_cell_is_not_unexecuted(self):
        assert aqm._is_unexecuted_code(_cell("code", "  \n\t\n")) is False

    def test_empty_source_as_list_is_not_unexecuted(self):
        assert aqm._is_unexecuted_code(_cell("code", ["", "\n"])) is False


# -- _has_strip_marker --

class TestHasStripMarker:
    def _md(self, text):
        return _cell("markdown", source=text)

    def test_no_marker(self):
        nb = _nb([self._md("hello world")])
        assert aqm._has_strip_marker(nb) is False

    def test_sortie_strippee(self):
        nb = _nb([self._md("> Sortie strippee (FABRICATED). Re-execution required.")])
        assert aqm._has_strip_marker(nb) is True

    def test_fabricated_caps(self):
        nb = _nb([self._md("> **FABRICATED** row marker.")])
        assert aqm._has_strip_marker(nb) is True

    def test_blank_png_hyphenated(self):
        nb = _nb([self._md("Cell emitted a blank-PNG (1x1, 70B).")])
        assert aqm._has_strip_marker(nb) is True

    def test_case_insensitive(self):
        nb = _nb([self._md("> sortie Strippée")])
        assert aqm._has_strip_marker(nb) is True

    def test_source_as_list(self):
        nb = _nb([{"cell_type": "markdown", "source": ["> Sortie ", "strippee."]}])
        assert aqm._has_strip_marker(nb) is True

    def test_marker_in_code_cell_ignored(self):
        # Markers live in markdown only; we don't double-count code cells.
        nb = _nb([_cell("code", source="sortie strippee", execution_count=None)])
        assert aqm._has_strip_marker(nb) is False


# -- _config_status --

class TestConfigStatus:
    def test_no_config(self, tmp_path):
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert r["has_config"] is False

    def test_config_alive(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": 12345}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "ALIVE"
        assert r["cloud_id"] == 12345

    def test_config_dead_zero(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": 0}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "DEAD"
        assert r["cloud_id"] == 0

    def test_config_dead_negative(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": -1}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "DEAD"

    def test_config_missing_cloud_id(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"language": "Py"}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert r["cloud_id"] is None

    def test_config_malformed_json(self, tmp_path):
        (tmp_path / "config.json").write_text("{not json")
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert "error" in r


# -- scan_notebook classification --

class TestScanNotebook:
    def test_healthy_all_executed(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "def foo(): pass", execution_count=2, outputs=[]),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "HEALTHY"
        assert r["code_total"] == 2
        assert r["code_unexecuted"] == 0
        assert r["code_executed"] == 2

    def test_strip_marker_with_unexec(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("markdown", "> Sortie strippee (FABRICATED). Re-execution required."),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "STOP_REPAIR_STRIPPED"
        assert r["code_unexecuted"] == 1
        assert r["strip_marker"] is True

    def test_preexisting_unexec_no_marker(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("code", "z = 3", execution_count=None, outputs=[]),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "PREEXISTING_UNEXEC"
        assert r["code_unexecuted"] == 2
        assert r["unexecuted_indexes"] == [1, 2]
        assert r["strip_marker"] is False

    def test_def_only_cell_is_still_caught(self, tmp_path):
        """Le verdict est conservatif : un ``def`` unexec est signale comme le reste.

        La docstring du module a longtemps promis l'inverse ("un notebook avec
        un seul ``def`` unexec et pas d'autre cellule = HEALTHY", "pas de faux
        positif ... parce qu'on regarde aussi le markdown contextuel"). Aucune
        de ces deux clauses n'a jamais ete implementee : le markdown contextuel
        ne fait que ROUTER entre les classes STOP_REPAIR_*, il ne produit
        jamais HEALTHY. Ce test epingle le contrat reel.
        """
        proj = _write_project(tmp_path, "DefOnly", [
            _cell("markdown", "## Fonctions utilitaires"),
            _cell("code", "def helper(x):\n    return x * 2",
                  execution_count=None, outputs=[]),
        ])
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "PREEXISTING_UNEXEC"
        assert r["code_unexecuted"] == 1

    def test_error_unreadable(self, tmp_path):
        proj = tmp_path / "BadProj"
        proj.mkdir()
        (proj / "quantbook.ipynb").write_text("{not json", encoding="utf-8")
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "ERROR"
        assert "error" in r

    def test_kernel_passed_through(self, tmp_path):
        proj = _write_project(tmp_path, "P", [_cell("code")], kernel="csharp")
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["kernel"] == "csharp"


# -- scan_projects glob --

class TestScanProjects:
    def test_scans_only_quantbook(self, tmp_path):
        _write_project(tmp_path, "A", [_cell("code")])
        _write_project(tmp_path, "B", [_cell("code", execution_count=None)])
        # A non-quantbook file must be ignored
        (tmp_path / "C").mkdir()
        (tmp_path / "C" / "research.ipynb").write_text("{}", encoding="utf-8")
        # A project with no quantbook must be ignored
        (tmp_path / "D").mkdir()
        (tmp_path / "D" / "main.py").write_text("# code", encoding="utf-8")

        results = aqm.scan_projects(tmp_path)
        names = sorted(Path(r["path"]).parent.name for r in results)
        assert names == ["A", "B"]

    def test_ordered(self, tmp_path):
        for n in ["Z", "A", "M"]:
            _write_project(tmp_path, n, [_cell("code")])
        results = aqm.scan_projects(tmp_path)
        names = [Path(r["path"]).parent.name for r in results]
        assert names == ["A", "M", "Z"]

    def test_missing_root_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            aqm.scan_projects(tmp_path / "nope")


# -- main --

class TestMain:
    def test_json_output_to_stdout(self, tmp_path, capsys):
        # Healthy = all code cells executed; pass an exec_count + outputs.
        _write_project(tmp_path, "P", [
            _cell("code", "x = 1", execution_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
        ])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--json"])
        assert rc == 0
        out = json.loads(capsys.readouterr().out)
        assert out["scanned"] == 1
        assert out["by_class"]["HEALTHY"] == 1
        assert out["results"][0]["classification"] == "HEALTHY"

    def test_project_filter(self, tmp_path, capsys):
        _write_project(tmp_path, "Good", [_cell("code", "x = 1", execution_count=1)])
        _write_project(tmp_path, "Bad", [_cell("code", "x = 1", execution_count=None)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--project", "Bad", "--json"])
        assert rc == 0
        out = json.loads(capsys.readouterr().out)
        assert out["scanned"] == 1
        assert out["results"][0]["classification"] == "PREEXISTING_UNEXEC"

    def test_project_not_found_exits_2(self, tmp_path):
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--project", "NOPE"])
        assert rc == 2

    def test_quant_root_missing_exits_2(self, tmp_path):
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", "nope"])
        assert rc == 2

    def test_check_exits_1_when_preexisting(self, tmp_path):
        _write_project(tmp_path, "Bad", [_cell("code", "x = 1", execution_count=None)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--check"])
        assert rc == 1

    def test_check_ignores_empty_cells(self, tmp_path):
        """Un notebook dont les seules cellules 'unexec' sont vides est sain.

        Le gate CI ne doit pas exiger une remediation dont la seule forme
        possible serait de supprimer des cellules vides.
        """
        _write_project(tmp_path, "EmptyOnly", [
            _cell("code", "x = 1", execution_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "", execution_count=None, outputs=[]),
        ])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--check"])
        assert rc == 0

    def test_check_exits_0_when_clean(self, tmp_path):
        _write_project(tmp_path, "Good", [_cell("code", execution_count=1)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--check"])
        assert rc == 0

    def test_md_write(self, tmp_path):
        _write_project(tmp_path, "P", [_cell("code", execution_count=1)])
        out_path = tmp_path / "report.md"
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--md", str(out_path)])
        assert rc == 0
        assert out_path.exists()
        content = out_path.read_text(encoding="utf-8")
        assert "QuantBooks scanned" in content
        assert "HEALTHY" in content


# -- integration: realistic multi-project scenario matching #6891 --

class TestIntegration6891:
    """Simulate the bug-class matrix observed in #6891 follow-up."""

    def test_matrix(self, tmp_path):
        # HEALTHY: all exec, no marker
        _write_project(tmp_path, "Healthy", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
        ])
        # STOP_REPAIR_STRIPPED: has unexec + has marker (body #6891 scope)
        _write_project(tmp_path, "Stripped", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("markdown", "> **Sortie strippee** (FABRICATED). Re-execution required."),
        ], config={"cloud-id": 12345})
        # PREEXISTING_UNEXEC: has unexec, no marker
        _write_project(tmp_path, "Preexisting", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
        ], config={"cloud-id": 0})
        # DEAD cloud-id case (FamaFrench-like)
        _write_project(tmp_path, "DeadCloud", [
            _cell("code", "y = 2", execution_count=None, outputs=[]),
        ], config={"cloud-id": 0})

        results = aqm.scan_projects(tmp_path)
        by_name = {Path(r["path"]).parent.name: r for r in results}

        assert by_name["Healthy"]["classification"] == "HEALTHY"
        assert by_name["Stripped"]["classification"] == "STOP_REPAIR_STRIPPED"
        assert by_name["Preexisting"]["classification"] == "PREEXISTING_UNEXEC"
        assert by_name["DeadCloud"]["classification"] == "PREEXISTING_UNEXEC"
        assert by_name["Stripped"]["config"]["status"] == "ALIVE"
        assert by_name["DeadCloud"]["config"]["status"] == "DEAD"
        assert by_name["Preexisting"]["config"]["status"] == "DEAD"


# -- _uses_quantbook (fenetre par CONTENU, #7575 / #8598) --

class TestUsesQuantbook:
    def test_code_cell_instantiating_quantbook(self):
        nb = _nb([_cell("code", "qb = QuantBook()")])
        assert aqm._uses_quantbook(nb) is True

    def test_self_quantbook_attribute(self):
        nb = _nb([_cell("code", "history = self.QuantBook.History(spy, 10)")])
        assert aqm._uses_quantbook(nb) is True

    def test_source_as_list_of_lines(self):
        nb = _nb([_cell("code", ["import x\n", "qb = QuantBook()\n"])])
        assert aqm._uses_quantbook(nb) is True

    def test_markdown_mention_only_is_not_a_quantbook(self):
        # Un tutoriel qui PARLE de QuantBook n'a pas besoin du runtime QC Cloud.
        nb = _nb([_cell("markdown", "On utilise `QuantBook()` pour la recherche.")])
        assert aqm._uses_quantbook(nb) is False

    def test_no_mention_at_all(self):
        nb = _nb([_cell("code", "import pandas as pd")])
        assert aqm._uses_quantbook(nb) is False


# -- scan_repo : sur-ensemble strict de scan_projects --

def _write_nb(path: Path, cells, kernel="python3") -> Path:
    """Write an arbitrary notebook at ``path`` (parents created)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_nb(cells, kernel=kernel), ensure_ascii=False),
                    encoding="utf-8")
    return path


class TestScanRepo:
    """La fenetre est le CONTENU (``QuantBook()``), pas le chemin ni le basename."""

    @staticmethod
    def _tree(tmp_path):
        nb_root = tmp_path / "MyIA.AI.Notebooks"
        quant_root = nb_root / "QuantConnect" / "projects"
        # Canonique : dans la fenetre d'origine, avec config.json.
        _write_project(quant_root, "Canonical", [
            _cell("code", "qb = QuantBook()", execution_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
        ], config={"cloud-id": 12345})
        # Hors fenetre d'origine (ni le dossier, ni le basename) mais VRAI quantbook.
        _write_nb(nb_root / "QuantConnect" / "research" / "research.ipynb", [
            _cell("code", "qb = QuantBook()", execution_count=None, outputs=[]),
        ])
        # Meme dossier canonique, autre basename -- la seconde moitie du proxy.
        _write_nb(quant_root / "Canonical" / "research.ipynb", [
            _cell("code", "qb = QuantBook()", execution_count=None, outputs=[]),
        ])
        # Bruit : ne doit PAS entrer dans la fenetre.
        _write_nb(nb_root / "Search" / "tutorial.ipynb",
                  [_cell("markdown", "`QuantBook()` sert a la recherche.")])
        _write_nb(nb_root / "ML" / "plain.ipynb",
                  [_cell("code", "import pandas", execution_count=None, outputs=[])])
        _write_nb(nb_root / "Foo" / ".ipynb_checkpoints" / "x.ipynb",
                  [_cell("code", "qb = QuantBook()", execution_count=None, outputs=[])])
        (nb_root / "Bad").mkdir(parents=True, exist_ok=True)
        (nb_root / "Bad" / "broken.ipynb").write_text("{not json", encoding="utf-8")
        return nb_root, quant_root

    def _paths(self, results, nb_root):
        return {Path(r["path"]).relative_to(nb_root).as_posix() for r in results}

    def test_catches_quantbooks_outside_the_path_window(self, tmp_path):
        nb_root, quant_root = self._tree(tmp_path)
        got = self._paths(aqm.scan_repo(nb_root, quant_root), nb_root)
        assert "QuantConnect/research/research.ipynb" in got
        assert "QuantConnect/projects/Canonical/research.ipynb" in got

    def test_ignores_non_quantbooks_checkpoints_and_unreadable(self, tmp_path):
        nb_root, quant_root = self._tree(tmp_path)
        got = self._paths(aqm.scan_repo(nb_root, quant_root), nb_root)
        assert "Search/tutorial.ipynb" not in got   # markdown-only mention
        assert "ML/plain.ipynb" not in got          # aucune mention
        assert "Foo/.ipynb_checkpoints/x.ipynb" not in got
        assert "Bad/broken.ipynb" not in got        # JSON invalide : pas de crash

    def test_is_a_strict_superset_that_reclassifies_nothing(self, tmp_path):
        nb_root, quant_root = self._tree(tmp_path)
        old = {r["path"]: r for r in aqm.scan_projects(quant_root)}
        new = {r["path"]: r for r in aqm.scan_repo(nb_root, quant_root)}
        assert set(old) <= set(new)
        for path, before in old.items():
            assert new[path]["classification"] == before["classification"]

    def test_canonical_entries_keep_their_config_cross_reference(self, tmp_path):
        nb_root, quant_root = self._tree(tmp_path)
        new = {Path(r["path"]).as_posix(): r for r in aqm.scan_repo(nb_root, quant_root)}
        canonical = next(v for k, v in new.items() if k.endswith("Canonical/quantbook.ipynb"))
        assert canonical["config"]["status"] == "ALIVE"

    def test_no_duplicate_entries(self, tmp_path):
        nb_root, quant_root = self._tree(tmp_path)
        results = aqm.scan_repo(nb_root, quant_root)
        paths = [r["path"] for r in results]
        assert len(paths) == len(set(paths))

    def test_missing_notebooks_root_yields_canonical_only(self, tmp_path):
        """Rien a elargir n'est pas une erreur -- main() garde l'exit 2 explicite."""
        _, quant_root = self._tree(tmp_path)
        results = aqm.scan_repo(tmp_path / "nope", quant_root)
        assert [r["path"] for r in results] == [r["path"] for r in aqm.scan_projects(quant_root)]


class TestMainScope:
    def test_default_scope_is_wider_than_projects(self, tmp_path, capsys):
        nb_root, quant_root = TestScanRepo._tree(tmp_path)
        rc = aqm.main(["--root", str(tmp_path), "--json"])
        assert rc == 0
        wide = json.loads(capsys.readouterr().out)["scanned"]
        rc = aqm.main(["--root", str(tmp_path), "--scope", "projects", "--json"])
        assert rc == 0
        narrow = json.loads(capsys.readouterr().out)["scanned"]
        assert wide > narrow

    def test_explicit_missing_notebooks_root_exits_2(self, tmp_path):
        self_tree = TestScanRepo._tree(tmp_path)
        assert self_tree  # fixture built
        rc = aqm.main(["--root", str(tmp_path), "--notebooks-root", "nope"])
        assert rc == 2
