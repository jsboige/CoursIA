#!/usr/bin/env python3
"""Tests pour scripts/check_quantconnect_notebook_freshness.py.

Le guard distingue 3 cas (OK / GITIGNORED / MISSING). Ces tests fabriquent un
mini-notebook dans un sous-dossier repo-like et assertent la classification
pour chaque cas, sans dependre de l'etat reel du repo (on shunte git via
mock de subprocess).
"""
import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
import check_quantconnect_notebook_freshness as g  # noqa: E402


class TestExtractPaths(unittest.TestCase):
    """Extraire (scripts|)results/<X>/... depuis le source code."""

    def test_simple_path(self):
        src = "results_path = Path('scripts/results/m15_lstm_rv_h32/results.json')"
        paths = g.extract_paths(src)
        self.assertEqual(paths, ["scripts/results/m15_lstm_rv_h32/results.json"])

    def test_multiple_paths(self):
        src = """
        p1 = Path("scripts/results/foo/results.json")
        p2 = Path("results/bar/baz.json")
        p3 = Path("scripts/results/foo/other.json")
        """
        paths = g.extract_paths(src)
        self.assertEqual(len(paths), 3)
        self.assertIn("scripts/results/foo/results.json", paths)
        self.assertIn("results/bar/baz.json", paths)
        self.assertIn("scripts/results/foo/other.json", paths)

    def test_dedup(self):
        src = """
        p1 = Path("scripts/results/foo/x.json")
        p2 = Path('scripts/results/foo/x.json')
        p3 = Path("scripts/results/foo/x.json")
        """
        paths = g.extract_paths(src)
        self.assertEqual(len(paths), 1)

    def test_ignores_non_results(self):
        src = """
        env_path = Path(".env")
        cache = Path("/tmp/cache.json")
        unrelated = "scripts/utils.py"
        """
        paths = g.extract_paths(src)
        self.assertEqual(paths, [])

    def test_both_quote_styles(self):
        src = 'p1 = "scripts/results/x/y.json"'
        paths = g.extract_paths(src)
        self.assertEqual(paths, ["scripts/results/x/y.json"])


class TestClassifyPath(unittest.TestCase):
    """Classifier un path en OK / GITIGNORED / MISSING."""

    def _mock_subprocess(self, ls_tree_stdout="", check_ignore_rc=1):
        """Mock git subprocess calls.

        ls_tree_stdout : str (vide = pas tracked, non-vide = tracked)
        check_ignore_rc : int (0 = gitignored, 1 = non gitignored)
        """
        def fake_run(cmd, **kwargs):
            result = mock.Mock()
            if cmd[0] == "git" and cmd[1] == "ls-tree":
                result.stdout = ls_tree_stdout
                result.returncode = 0
            elif cmd[0] == "git" and cmd[1] == "check-ignore":
                result.stdout = ""
                result.returncode = check_ignore_rc
            else:
                result.stdout = ""
                result.returncode = 1
            return result
        return fake_run

    def test_ok(self):
        # ls-tree returns the path = tracked.
        fake = self._mock_subprocess(ls_tree_stdout="100644 blob abc...")
        with mock.patch("subprocess.run", fake):
            status = g.classify_path("scripts/results/foo/results.json", pathlib.Path("."))
        self.assertEqual(status, "OK")

    def test_gitignored(self):
        # ls-tree empty + check-ignore rc=0 = gitignored.
        fake = self._mock_subprocess(ls_tree_stdout="", check_ignore_rc=0)
        with mock.patch("subprocess.run", fake):
            status = g.classify_path("scripts/results/foo/results.json", pathlib.Path("."))
        self.assertEqual(status, "GITIGNORED")

    def test_missing(self):
        # ls-tree empty + check-ignore rc=1 = MISSING.
        fake = self._mock_subprocess(ls_tree_stdout="", check_ignore_rc=1)
        with mock.patch("subprocess.run", fake):
            status = g.classify_path("scripts/results/foo/results.json", pathlib.Path("."))
        self.assertEqual(status, "MISSING")


class TestScanNotebook(unittest.TestCase):
    """Scan end-to-end d'un notebook dans un faux repo.

    Les fixtures vivent dans un TemporaryDirectory (issue #13603) : la
    suite ne depose plus test_nb.ipynb / md_only.ipynb / corrupt.ipynb
    dans le cwd du run (worktree propre apres passage complet).
    """

    def setUp(self):
        self._tmpdir = tempfile.TemporaryDirectory()
        self.tmp = pathlib.Path(self._tmpdir.name)

    def tearDown(self):
        self._tmpdir.cleanup()

    def _make_nb(self, code_sources: list) -> pathlib.Path:
        nb = {"cells": [{"cell_type": "code", "source": s} for s in code_sources]}
        nb_path = self.tmp / "test_nb.ipynb"
        nb_path.write_bytes(json.dumps(nb).encode())
        return nb_path

    def test_scan_three_statuses(self):
        # Mock git : tracke le 2e path, gitignore le 1er, MISSING le 3e.
        def fake_run(cmd, **kwargs):
            result = mock.Mock()
            if cmd[0] == "git" and cmd[1] == "ls-tree":
                path_arg = cmd[-1]
                if "baselines" in path_arg:
                    result.stdout = "100644 blob abc... baselines_zeroshot/results.json"
                else:
                    result.stdout = ""
                result.returncode = 0
            elif cmd[0] == "git" and cmd[1] == "check-ignore":
                path_arg = cmd[-1]
                if "GITIGNORED_DIR" in path_arg:
                    result.stdout = ".gitignore:51:results/\n"
                    result.returncode = 0
                else:
                    result.stdout = ""
                    result.returncode = 1
            else:
                result.stdout = ""
                result.returncode = 1
            return result

        with mock.patch("subprocess.run", fake_run):
            with mock.patch.object(g, "find_repo_root", return_value=self.tmp):
                nb_path = self._make_nb(
                    ["results_path = Path('scripts/results/GITIGNORED_DIR/x.json')",
                     "p = Path('scripts/results/baselines_zeroshot/results.json')",
                     "p = Path('scripts/results/NEVER_TRACKED_NEVER_GITIGNORED/x.json')"])
                result = g.scan_notebook(nb_path, self.tmp)

        statuses = [f["status"] for f in result["findings"]]
        self.assertEqual(statuses, ["GITIGNORED", "OK", "MISSING"])

    def test_scan_empty_notebook(self):
        nb_path = self._make_nb([])
        result = g.scan_notebook(nb_path, self.tmp)
        self.assertEqual(result["findings"], [])

    def test_scan_markdown_only(self):
        # Cellules markdown ne produisent pas de paths.
        with mock.patch("subprocess.run", mock.Mock()):
            with mock.patch.object(g, "find_repo_root", return_value=self.tmp):
                nb = {"cells": [{"cell_type": "markdown", "source": ["# scripts/results/foo/results.json\n"]}]}
                nb_path = self.tmp / "md_only.ipynb"
                nb_path.write_bytes(json.dumps(nb).encode())
                result = g.scan_notebook(nb_path, self.tmp)
                self.assertEqual(result["findings"], [])

    def test_scan_corrupt_json(self):
        bad_path = self.tmp / "corrupt.ipynb"
        bad_path.write_bytes(b"{not json")
        result = g.scan_notebook(bad_path, self.tmp)
        self.assertIn("error", result)


class TestRealM15Case(unittest.TestCase):
    """Validation sur le cas fondateur c.290 : m15_lstm_rv_research.ipynb."""

    def test_m15_status(self):
        # On utilise le repo reel (cwd = worktree) sans mock.
        nb_path = pathlib.Path("MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m15_lstm_rv_research.ipynb").resolve()
        if not nb_path.exists():
            self.skipTest(f"Pas de worktree ML-Training-Pipeline ici ({nb_path})")
        repo_root = g.find_repo_root(pathlib.Path("."))
        result = g.scan_notebook(nb_path, repo_root)
        # m15_lstm_rv_h32/results.json est gitignored (catch-all results/)
        # c.290 le confirmait. Donc status doit etre GITIGNORED (et non MISSING
        # qui serait un faux positif).
        paths_seen = {f["path"]: f["status"] for f in result["findings"]}
        self.assertIn("scripts/results/m15_lstm_rv_h32/results.json", paths_seen)
        self.assertEqual(paths_seen["scripts/results/m15_lstm_rv_h32/results.json"], "GITIGNORED")


if __name__ == "__main__":
    unittest.main(verbosity=2)