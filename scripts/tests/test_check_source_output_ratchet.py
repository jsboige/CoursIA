"""Tests for check_source_output_ratchet.py (issue #13562).

The centerpiece is the positive control the issue body demands: reconstruct
the #13550 case (source of cell [26] modified, base outputs kept) and prove
the guard FAILS on it, then PASSES once the outputs are refreshed. The
reconstruction is git-backed - a throwaway repository with a base commit
and a head commit - so the test exercises the real CLI path (resolve_base,
changed_notebooks, git show, exit codes), not just the pure functions.

The module is loaded from its file path because scripts/tests sits outside
the scripts package root and the scripts/ tree is a namespace-package
minefield on Windows: importlib on the direct path sidesteps the ambiguity.
"""

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "notebook_tools" / \
    "check_source_output_ratchet.py"


def _load():
    spec = importlib.util.spec_from_file_location(
        "check_source_output_ratchet", TOOL)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CSR = _load()


def md(*lines):
    return {"cell_type": "markdown", "metadata": {}, "source": list(lines)}


def code(src, outputs, execution_count=1):
    return {"cell_type": "code", "execution_count": execution_count,
            "metadata": {}, "outputs": outputs, "source": [src]}


def nb(cells, kernel="python3"):
    return {"cells": cells,
            "metadata": {"kernelspec": {"display_name": kernel,
                                        "name": kernel}}}


# Two DIFFERENT non-empty outputs: the founding case kept the base output
# byte-identical while editing the source; the patch refreshes it.
OUT_BASE = [{"output_type": "stream", "name": "stdout", "text": ["42\n"]}]
OUT_REFRESHED = [{"output_type": "execute_result",
                  "data": {"text/plain": ["42"]},
                  "execution_count": 7, "metadata": {}}]


def fixture_13550_base():
    """27 cells, index 26 = the code cell the founding PR edited."""
    cells = [md("# Titre"), md("## Section")]
    cells += [code(f"x{i} = {i}", [{"output_type": "stream",
                                    "name": "stdout",
                                    "text": [f"{i}\n"]}]) for i in range(24)]
    cells.append(code("resultat = 40 + 2\nprint(resultat)", OUT_BASE))
    return nb(cells)


def fixture_13550_head(outputs):
    """Same notebook after the source edit, outputs per `outputs`."""
    cells = [md("# Titre"), md("## Section modifiee")]
    cells += [code(f"x{i} = {i}", [{"output_type": "stream",
                                    "name": "stdout",
                                    "text": [f"{i}\n"]}]) for i in range(24)]
    cells.append(code("resultat = 41 + 1  # reformule\nprint(resultat)",
                      outputs))
    return nb(cells)


class GitRepo:
    """Throwaway repository: one commit per notebook state."""

    def __init__(self, states):
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name)
        self._git("init", "-q")
        path = "MyIA.AI.Notebooks/Fake/Fake.ipynb"
        (self.path / "MyIA.AI.Notebooks/Fake").mkdir(parents=True)
        for i, state in enumerate(states):
            (self.path / path).write_text(
                json.dumps(state, ensure_ascii=False, indent=1) + "\n",
                encoding="utf-8")
            self._git("add", "-A")
            self._git("-c", "user.email=t@t", "-c", "user.name=t",
                      "commit", "-q", "-m", f"state {i}")

    def _git(self, *args):
        out = subprocess.run(["git", *args], cwd=self.path,
                             capture_output=True, check=True)
        return out

    def run_guard(self, base="HEAD~1", body=None):
        cmd = [sys.executable, str(TOOL), base, "--json"]
        if body is not None:
            body_file = self.path / "body.md"
            body_file.write_text(body, encoding="utf-8")
            cmd += ["--body-file", str(body_file)]
        return subprocess.run(cmd, cwd=self.path, capture_output=True,
                              text=True, encoding="utf-8")

    def close(self):
        self.dir.cleanup()


class TestPositiveControl13550(unittest.TestCase):
    """The guard the issue demands: FAIL unpatched, PASS patched."""

    def setUp(self):
        # Cell [26] source edited, base outputs kept: the founding defect.
        self.repo = GitRepo([fixture_13550_base(),
                             fixture_13550_head(OUT_BASE)])

    def tearDown(self):
        self.repo.close()

    def test_fails_on_reconstructed_defect(self):
        proc = self.repo.run_guard()
        self.assertEqual(proc.returncode, 1, proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertEqual(payload["regressions"], 1)
        # The target cell is the LAST code cell (index 26 over all cells);
        # the 24 filler code cells before it are UNCHANGED and come first.
        cell = payload["records"][0]["cells"][-1]
        self.assertEqual(cell["index"], 26)
        self.assertEqual(cell["verdict"], "STALE_OUTPUT")

    def test_passes_once_outputs_refreshed(self):
        repo = GitRepo([fixture_13550_base(),
                        fixture_13550_head(OUT_REFRESHED)])
        try:
            proc = repo.run_guard()
            self.assertEqual(proc.returncode, 0, proc.stderr)
            payload = json.loads(proc.stdout)
            self.assertEqual(payload["regressions"], 0)
            cell = payload["records"][0]["cells"][-1]
            self.assertEqual(cell["verdict"], "EXECUTED")
        finally:
            repo.close()

    def test_body_exemption_lifts_the_defect(self):
        body = ("Source-output ratchet: [26] exempte -- comment-only edit, "
                "unchanged output expected.")
        proc = self.repo.run_guard(body=body)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        payload = json.loads(proc.stdout)
        cell = payload["records"][0]["cells"][-1]
        self.assertEqual(cell["verdict"], "EXEMPT_BODY")


class TestClassifyCells(unittest.TestCase):
    """Pure classification, indexed over ALL cells."""

    def test_source_changed_outputs_identical_is_stale(self):
        base = nb([md("intro"), code("print(1)", OUT_BASE)])
        head = nb([md("intro"), code("print(2)", OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["index"], 1)
        self.assertEqual(recs[0]["verdict"], "STALE_OUTPUT")
        self.assertTrue(recs[0]["regression"])

    def test_comment_only_edit_fails_all_the_same(self):
        base = nb([code("print(1)  # note", OUT_BASE)])
        head = nb([code("print(1)  # note corrigee", OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "STALE_OUTPUT")
        self.assertTrue(recs[0]["regression"])

    def test_empty_outputs_never_fail(self):
        base = nb([code("print(1)", [])])
        head = nb([code("print(2)", [])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "NO_OUTPUTS")
        self.assertFalse(recs[0]["regression"])

    def test_unchanged_source_is_clean(self):
        base = nb([code("print(1)", OUT_BASE)])
        head = nb([code("print(1)", OUT_BASE)])
        self.assertEqual(CSR.classify_cells(base, head)[0]["verdict"],
                         "UNCHANGED")

    def test_markdown_cells_are_skipped(self):
        base = nb([md("a"), code("print(1)", OUT_BASE), md("b")])
        head = nb([md("A"), code("print(1)", OUT_BASE), md("B")])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(len(recs), 1)
        self.assertEqual(recs[0]["index"], 1)
        self.assertFalse(recs[0]["regression"])

    def test_all_cell_indexing_survives_markdown_edits(self):
        # Markdown edits around a code cell must not shift its index: the
        # founding evidence quotes cell [26] of the ALL-cell list.
        base = fixture_13550_base()
        head = fixture_13550_head(OUT_REFRESHED)
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[-1]["index"], 26)

    def test_inserted_cell_is_unpaired_not_stale(self):
        # A cell inserted before a code cell shifts it. Without ids, the
        # legacy content pairing (#14297 fallback) pairs the moved
        # UNMODIFIED cell with its own base copy -> UNCHANGED (clean),
        # never a fabricated stale pair. Same semantics as the id branch
        # in test_shifted_cells_pair_by_id_after_conforming_insertion.
        base = nb([code("print(1)", OUT_BASE)])
        head = nb([md("nouveau"), code("print(1)", OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs], ["UNCHANGED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_new_legacy_cell_matching_nothing_stays_unpaired(self):
        # A genuinely NEW code cell (no exact, no fuzzy base partner)
        # stays UNPAIRED - content pairing must not fabricate pairs any
        # more than positional pairing fabricated stale ones.
        base = nb([code("print(1)", OUT_BASE)])
        head = nb([md("nouveau"),
                   code("import numpy as np\narr = np.zeros(3)", OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs], ["UNPAIRED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_insertion_with_ids_does_not_fabricate_stale_pair(self):
        # #14297: positional pairing fabricated 3/3 STALE_OUTPUT on
        # enrichment PRs. Two base code cells share byte-identical
        # outputs (conforming C.1 stubs); a PR inserts an untested stub
        # between them. With ids, the inserted cell has a fresh id
        # (UNPAIRED) and the shifted originals pair to their true base
        # partner (UNCHANGED) - never a fabricated stale pair.
        base = nb([dict(code("print(1)", OUT_BASE), id="c1"),
                   dict(code("print(2)", OUT_BASE), id="c2")])
        head = nb([dict(code("print(1)", OUT_BASE), id="c1"),
                   dict(code("pass", OUT_BASE), id="c3"),
                   dict(code("print(2)", OUT_BASE), id="c2")])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs],
                         ["UNCHANGED", "UNPAIRED", "UNCHANGED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_shifted_cells_pair_by_id_after_conforming_insertion(self):
        # The same insertion with a copied base stub in the middle: the
        # stub is NEW (fresh id) -> UNPAIRED, the originals keep their id
        # identity -> UNCHANGED despite the index shift.
        base = nb([dict(code("print(1)", OUT_BASE), id="c1")])
        head = nb([dict(code("print(1)", OUT_BASE), id="c1"),
                   dict(code("print(1)", OUT_BASE), id="c2"),
                   md("indice")])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs],
                         ["UNCHANGED", "UNPAIRED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_id_pairing_still_flags_real_stale_output(self):
        # Pairing by id must NOT mask a genuine stale output: same id,
        # changed source, byte-identical outputs -> STALE_OUTPUT.
        base = nb([dict(code("print(1)", OUT_BASE), id="c1")])
        head = nb([dict(code("print(2)", OUT_BASE), id="c1")])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "STALE_OUTPUT")
        self.assertTrue(recs[0]["regression"])


class TestLegacyContentPairing(unittest.TestCase):
    """#14297 residual tranche: no-id bases pair by content, not position.

    The three measured FPs were legacy-style notebooks where an enrichment
    insertion shifted cells that positional pairing then confronted with
    UNRELATED C.1 stubs whose uniform outputs are byte-identical. Id
    pairing (#14319) covers nbformat 4.5+ bases; this class pins the
    content fallback that covers the rest, including the two negative
    controls the issue's acceptance demands.
    """

    def test_moved_only_cell_is_unchanged(self):
        # Acceptance §3, first control: a cell only MOVED by an insertion
        # above (the exact #14297 scenario - distinct stubs, identical
        # outputs) -> UNCHANGED, never a fabricated STALE_OUTPUT.
        stub_a = code("# Exercice 1\nprint('Exercice a completer')",
                      OUT_BASE)
        stub_b = code("# Exercice 3\nprint('Exercice a completer')",
                      OUT_BASE)
        base = nb([stub_a, stub_b])
        head = nb([md("## Lecture du resultat"), stub_a, stub_b])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs],
                         ["UNCHANGED", "UNCHANGED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_moved_and_modified_cell_is_stale(self):
        # Acceptance §3, second control: without it, the content fallback
        # would be indistinguishable from disarming the guard - a cell
        # MOVED AND MODIFIED must still confront its own base version.
        base = nb([code("resultat = 40 + 2\nprint(resultat)", OUT_BASE)])
        head = nb([md("## Introduction"),
                   code("resultat = 41 + 1  # reformule\nprint(resultat)",
                        OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs], ["STALE_OUTPUT"])
        self.assertTrue(all(r["regression"] for r in recs))

    def test_modified_cell_pairs_to_own_base_desident_sibling(self):
        # The FP-residual guard: when a modified stub and an untouched
        # sibling stub share byte-identical outputs, the exact pass must
        # consume the untouched one first, and the fuzzy pass must send
        # the MODIFIED cell to its own base version (TRUE stale), not to
        # the sibling (fabricated pair).
        ex1 = "# Exercice 1\n# TODO\nprint('Exercice a completer')"
        ex3 = "# Exercice 3\n# TODO\nprint('Exercice a completer')"
        base = nb([code(ex1, OUT_BASE), code(ex3, OUT_BASE)])
        head = nb([code(ex3, OUT_BASE),
                   code(ex1 + "\n# indice: voir section 2", OUT_BASE)])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs],
                         ["UNCHANGED", "STALE_OUTPUT"])
        self.assertTrue(recs[1]["regression"])


class TestNotebookExemptions(unittest.TestCase):
    """validate_pr_notebooks' predicates, reused not duplicated."""

    def test_lean_kernel_exempt(self):
        base = nb([code("print(1)", OUT_BASE)], kernel="lean4-wsl")
        head = nb([code("print(2)", OUT_BASE)], kernel="lean4-wsl")
        recs = CSR.classify_notebook("Foo/Bar.lean.ipynb", base, head, set())
        self.assertEqual(recs[0]["verdict"], "EXEMPT_KERNEL")
        self.assertFalse(recs[0]["regression"])

    def test_qc_cloud_path_exempt(self):
        path = "MyIA.AI.Notebooks/QuantConnect/Python/Research.ipynb"
        base = nb([code("print(1)", OUT_BASE)])
        head = nb([code("print(2)", OUT_BASE)])
        recs = CSR.classify_notebook(path, base, head, set())
        self.assertEqual(recs[0]["verdict"], "EXEMPT_QC_PATH")

    def test_quantbook_source_exempt(self):
        path = "MyIA.AI.Notebooks/Elsewhere/Research.ipynb"
        base = nb([code("qb = QuantBook()", OUT_BASE)])
        head = nb([code("qb = QuantBook()  # edit", OUT_BASE)])
        recs = CSR.classify_notebook(path, base, head, set())
        self.assertEqual(recs[0]["verdict"], "EXEMPT_QUANTBOOK")

    def test_dotnet_not_exempt(self):
        base = nb([code("Console.WriteLine(1)", OUT_BASE)],
                  kernel=".net-csharp")
        head = nb([code("Console.WriteLine(2)", OUT_BASE)],
                  kernel=".net-csharp")
        recs = CSR.classify_notebook("Foo/Bar.ipynb", base, head, set())
        self.assertEqual(recs[0]["verdict"], "STALE_OUTPUT")
        self.assertTrue(recs[0]["regression"])


class TestBodyExemptions(unittest.TestCase):
    def test_bare_index_matches_any_notebook(self):
        lifted = CSR.parse_body_exemptions(
            "avant\nSource-output ratchet: [12] exempte -- raison\napres")
        self.assertEqual(lifted, {(None, 12)})

    def test_qualified_index_matches_only_that_notebook(self):
        lifted = CSR.parse_body_exemptions(
            "Source-output ratchet: MyIA.AI.Notebooks/Foo.ipynb: [12] "
            "exempte -- raison")
        self.assertEqual(lifted, {("MyIA.AI.Notebooks/Foo.ipynb", 12)})

    def test_case_insensitive_and_multiple(self):
        lifted = CSR.parse_body_exemptions(
            "source-output ratchet: [1] exempte -- a\n"
            "Source-Output Ratchet: [2] exempte -- b")
        self.assertEqual(lifted, {(None, 1), (None, 2)})

    def test_no_sentence_no_lift(self):
        self.assertEqual(CSR.parse_body_exemptions("sorties [12] stables"),
                         set())

    def test_qualifier_scopes_the_lift(self):
        body = ("Source-output ratchet: MyIA.AI.Notebooks/Foo.ipynb: [0] "
                "exempte -- raison")
        lifted = CSR.parse_body_exemptions(body)
        base = nb([code("print(1)", OUT_BASE)])
        head = nb([code("print(2)", OUT_BASE)])
        foo = CSR.classify_notebook("MyIA.AI.Notebooks/Foo.ipynb",
                                    base, head, lifted)
        bar = CSR.classify_notebook("MyIA.AI.Notebooks/Bar.ipynb",
                                    base, head, lifted)
        self.assertEqual(foo[0]["verdict"], "EXEMPT_BODY")
        self.assertEqual(bar[0]["verdict"], "STALE_OUTPUT")
        self.assertTrue(bar[0]["regression"])


if __name__ == "__main__":
    unittest.main()
