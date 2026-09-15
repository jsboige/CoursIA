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


def code(src, outputs, execution_count=1, cell_id=None):
    cell = {"cell_type": "code", "execution_count": execution_count,
            "metadata": {}, "outputs": outputs, "source": [src]}
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


def nb(cells, kernel="python3"):
    # Auto-stamp ids so the by-id pairing path is exercised by default.
    # Tests that need legacy pairing can use nb_legacy() to skip this.
    for j, c in enumerate(cells):
        if c.get("cell_type") == "code" and "id" not in c:
            c["id"] = f"cell-{j}"
    return {"cells": cells,
            "metadata": {"kernelspec": {"display_name": kernel,
                                        "name": kernel}}}


def nb_legacy(cells, kernel="python3"):
    """Notebook without cell ids - exercises content-based pairing."""
    return {"cells": list(cells),
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
            # Issue #14978 split EXECUTED into TEXT_DIFF/PAYLOAD_DIFF/
            # BOTH_DIFF. The refreshed outputs are a different output_type
            # (stream vs execute_result) so canonical_outputs differs and
            # _outputs_text differs -> TEXT_DIFF is the right verdict.
            self.assertEqual(cell["verdict"], "TEXT_DIFF")
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
        base = nb_legacy([code("print(1)", OUT_BASE)])
        head = nb_legacy([md("nouveau"), code("print(1)", OUT_BASE)])
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
        base = nb_legacy([stub_a, stub_b])
        head = nb_legacy([md("## Lecture du resultat"), stub_a, stub_b])
        recs = CSR.classify_cells(base, head)
        self.assertEqual([r["verdict"] for r in recs],
                         ["UNCHANGED", "UNCHANGED"])
        self.assertFalse(any(r["regression"] for r in recs))

    def test_moved_and_modified_cell_is_stale(self):
        # Acceptance §3, second control: without it, the content fallback
        # would be indistinguishable from disarming the guard - a cell
        # MOVED AND MODIFIED must still confront its own base version.
        base = nb_legacy([code("resultat = 40 + 2\nprint(resultat)", OUT_BASE)])
        head = nb_legacy([md("## Introduction"),
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
        base = nb_legacy([code(ex1, OUT_BASE), code(ex3, OUT_BASE)])
        head = nb_legacy([code(ex3, OUT_BASE),
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


class TestDiffOutputsGranularity(unittest.TestCase):
    """Issue #14978: split the single EXECUTED verdict by output-diff kind.

    The NanoClaw bot on #14958 declared "outputs = 0 diff" against a pair
    where 7 of 14 code cells differed - 3 PNG re-encodings and 4 text
    deaccentuations. The ratchet's EXECUTED verdict already caught *that*
    cells moved; what the reviewer missed was naming which cells and why.
    These tests prove the new granularity: TEXT_DIFF, PAYLOAD_DIFF,
    BOTH_DIFF, and the unchanged cells named UNCHANGED_SOURCE.
    """

    def test_classify_marks_source_only_diff_as_unchanged(self):
        # Source unchanged but outputs differ (per #14958 fingerprint):
        # classify_cells still labels the cell UNCHANGED because the
        # source axis is identical - the ratchet's regression class is
        # gated on source change + output drift (STALE_OUTPUT). The
        # granular kind of the OUTPUT drift lives in report_output_diffs,
        # tested separately below.
        base = nb([code("print('Strategie Row')",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Strategie Row\n"]}])])
        head = nb([code("print('Strategie Row')",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Stratégie Row\n"]}])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "UNCHANGED")
        self.assertFalse(recs[0]["regression"])

    def test_report_output_diffs_names_source_only_diff_as_TEXT_DIFF(self):
        # Counterpart of the test above at the report_output_diffs layer.
        # Source identical + outputs differ -> the report must name the
        # diff as TEXT_DIFF (otherwise the user's "0 diff" complaint on
        # #14958 survives). This is the granularity the audit uses.
        base = nb([code("print('Strategie Row')",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Strategie Row\n"]}])])
        head = nb([code("print('Strategie Row')",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Stratégie Row\n"]}])])
        repo = GitRepo.__new__(GitRepo)
        import tempfile
        repo.dir = tempfile.TemporaryDirectory()
        repo.path = Path(repo.dir.name)
        subprocess.run(["git", "init", "-q"], cwd=repo.path, check=True)
        nb_path = "MyIA.AI.Notebooks/Fake/GT-text.ipynb"
        (repo.path / "MyIA.AI.Notebooks/Fake").mkdir(parents=True)
        for state in (base, head):
            (repo.path / nb_path).write_text(
                json.dumps(state, ensure_ascii=False, indent=1) + "\n",
                encoding="utf-8")
            subprocess.run(["git", "add", "-A"], cwd=repo.path, check=True)
            subprocess.run(["git", "-c", "user.email=t@t", "-c",
                            "user.name=t", "commit", "-q", "-m", "s"],
                           cwd=repo.path, check=True)
        try:
            proc = subprocess.run(
                [sys.executable, str(TOOL), "HEAD~1",
                 "--show-output-diffs", "--json"],
                cwd=repo.path, capture_output=True, text=True,
                encoding="utf-8", check=False)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            payload = json.loads(proc.stdout)
            diffs = payload["notebooks"][0]["diffs"]
            self.assertEqual(len(diffs), 1)
            cell = diffs[0]
            self.assertEqual(cell["kind"], "TEXT_DIFF")
            self.assertTrue(cell["source_same"])
            self.assertFalse(cell["text_identical"])
        finally:
            repo.dir.cleanup()

    def test_payload_diff_is_PAYLOAD_DIFF(self):
        # Two PNG payloads of different sizes; identical source.
        png_small = "data:image/png;base64," + "A" * 100
        png_big = "data:image/png;base64," + "A" * 200
        base = nb([code("plt.savefig('out.png')",
                        [{"output_type": "display_data",
                          "data": {"image/png": png_small}}])])
        head = nb([code("plt.savefig('out.png')",
                        [{"output_type": "display_data",
                          "data": {"image/png": png_big}}])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "UNCHANGED")

    def test_classify_marks_TEXT_DIFF_when_source_changed(self):
        # Source AND outputs both move: the ratchet split lands here.
        base = nb([code("x = 'Strategie'",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Strategie\n"]}])])
        head = nb([code("x = 'Stratégie'  # edited accent",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["Stratégie\n"]}])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "TEXT_DIFF")
        self.assertFalse(recs[0]["regression"])

    def test_classify_marks_PAYLOAD_DIFF_when_png_resized(self):
        # Source + PNG payload both change.
        png_v1 = "data:image/png;base64," + "A" * 86064
        png_v2 = "data:image/png;base64," + "A" * 86272
        base = nb([code("plt.savefig('a.png')",
                        [{"output_type": "display_data",
                          "data": {"image/png": png_v1}}])])
        head = nb([code("plt.savefig('a.png', dpi=120)  # tweak",
                        [{"output_type": "display_data",
                          "data": {"image/png": png_v2}}])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "PAYLOAD_DIFF")
        self.assertFalse(recs[0]["regression"])

    def test_classify_marks_BOTH_DIFF(self):
        png_v1 = "data:image/png;base64," + "A" * 100
        png_v2 = "data:image/png;base64," + "A" * 200
        base = nb([code("x = 1\nprint(x)",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["1\n"]},
                         {"output_type": "display_data",
                          "data": {"image/png": png_v1}}])])
        head = nb([code("x = 2  # edited\nprint(x)",
                        [{"output_type": "stream", "name": "stdout",
                          "text": ["2\n"]},
                         {"output_type": "display_data",
                          "data": {"image/png": png_v2}}])])
        recs = CSR.classify_cells(base, head)
        self.assertEqual(recs[0]["verdict"], "BOTH_DIFF")

    def test_diff_outputs_unit(self):
        # Pure diff_outputs unit test on canonical outputs.
        base_cell = {"outputs": [{"output_type": "stream", "name": "stdout",
                                   "text": ["abc\n"]}]}
        head_cell_text = {"outputs": [{"output_type": "stream", "name": "stdout",
                                        "text": ["abd\n"]}]}
        head_cell_payload = {"outputs": [
            {"output_type": "stream", "name": "stdout", "text": ["abc\n"]},
            {"output_type": "display_data",
             "data": {"image/png": "data:image/png;base64," + "A" * 200}}]}
        self.assertEqual(CSR.diff_outputs(base_cell, base_cell), "IDENTICAL")
        self.assertEqual(CSR.diff_outputs(base_cell, head_cell_text),
                         "TEXT_DIFF")
        self.assertEqual(CSR.diff_outputs(base_cell, head_cell_payload),
                         "PAYLOAD_DIFF")
        # Empty base + non-empty head:
        self.assertEqual(CSR.diff_outputs({"outputs": []},
                                          head_cell_payload),
                         "EMPTY_BASE")
        # Non-empty base + empty head:
        self.assertEqual(CSR.diff_outputs(base_cell, {"outputs": []}),
                         "EMPTY_HEAD")

    def test_report_output_diffs_14958_fixture(self):
        """The exact #14958 reconstructed: 14 code cells, 7 differ.

        Source untouched for all 14 cells; the head's outputs carry the
        fresh accents + re-encoded PNGs. Without --show-output-diffs, the
        ratchet's per-cell verdict would be UNCHANGED (source identical)
        and the report would say "0 diff" - precisely NanoClaw's claim.
        report_output_diffs is the read-only truth that names them.
        """
        def stream(text):
            return [{"output_type": "stream", "name": "stdout",
                     "text": [text]}]

        def png(n):
            return [{"output_type": "display_data",
                     "data": {"image/png": "data:image/png;base64,"
                             + "A" * n}}]

        # 14 code cells; 7 of them move on the output axis (4 text +
        # 3 PNG), exactly the #14958 fingerprint.
        bases = []
        heads = []
        for i in range(14):
            if i in (2, 4, 5, 9):
                bases.append(code(f"print({i})",
                                  stream(f"sortie brute {i}\n")))
                heads.append(code(f"print({i})",
                                  stream(f"sortie accentuée {i}\n")))
            elif i in (6, 7, 10):
                bases.append(code(f"plt.savefig('c{i}.png')", png(100)))
                heads.append(code(f"plt.savefig('c{i}.png')",
                                  png(100 + (i - 5))))
            else:
                bases.append(code(f"x{i} = {i}",
                                  stream(f"{i}\n")))
                heads.append(code(f"x{i} = {i}",
                                  stream(f"{i}\n")))
        # Run the report against the throwaway repo the test pattern
        # already uses (GitRepo sets up commits and runs the tool).
        repo = GitRepo.__new__(GitRepo)
        import tempfile
        repo.dir = tempfile.TemporaryDirectory()
        repo.path = Path(repo.dir.name)
        subprocess.run(["git", "init", "-q"], cwd=repo.path, check=True)
        nb_path = "MyIA.AI.Notebooks/Fake/GT-05.ipynb"
        (repo.path / "MyIA.AI.Notebooks/Fake").mkdir(parents=True)
        for state in (nb(bases), nb(heads)):
            (repo.path / nb_path).write_text(
                json.dumps(state, ensure_ascii=False, indent=1) + "\n",
                encoding="utf-8")
            subprocess.run(["git", "add", "-A"], cwd=repo.path, check=True)
            subprocess.run(["git", "-c", "user.email=t@t", "-c",
                            "user.name=t", "commit", "-q", "-m", "s"],
                           cwd=repo.path, check=True)
        try:
            proc = subprocess.run(
                [sys.executable, str(TOOL), "HEAD~1",
                 "--show-output-diffs", "--json"],
                cwd=repo.path, capture_output=True, text=True,
                encoding="utf-8", check=False)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            payload = json.loads(proc.stdout)
            nb_rec = payload["notebooks"][0]
            self.assertEqual(nb_rec["verdict"], "CHANGED")
            self.assertEqual(nb_rec["code_cells"], 14)
            # 7 cells with output diff (4 TEXT_DIFF + 3 PAYLOAD_DIFF),
            # 7 cells UNCHANGED_SOURCE.
            moved = [d for d in nb_rec["diffs"]
                     if d["kind"] != "UNCHANGED_SOURCE"]
            self.assertEqual(len(moved), 7,
                             f"expected 7 moved cells, got {len(moved)}")
            text_moved = [d for d in moved if d["kind"] == "TEXT_DIFF"]
            payload_moved = [d for d in moved if d["kind"] == "PAYLOAD_DIFF"]
            self.assertEqual(len(text_moved), 4)
            self.assertEqual(len(payload_moved), 3)
            # Indices 2, 4, 5, 9 carry TEXT_DIFF; 6, 7, 10 carry PAYLOAD.
            self.assertEqual(sorted(d["index"] for d in text_moved),
                             [2, 4, 5, 9])
            self.assertEqual(sorted(d["index"] for d in payload_moved),
                             [6, 7, 10])
            # At least one payload cell reports a positive byte delta.
            self.assertTrue(any(d["payload_deltas"].get("image/png", 0) > 0
                                for d in payload_moved))
        finally:
            repo.dir.cleanup()

    def test_show_output_diffs_exits_zero_even_with_stale(self):
        # --show-output-diffs is read-only; even a real STALE_OUTPUT pair
        # should not cause non-zero exit (the ratchet gate is bypassed
        # when the audit flag is on, so the caller can read the truth
        # without the run failing on it).
        repo = GitRepo([fixture_13550_base(),
                        fixture_13550_head(OUT_BASE)])
        try:
            proc = subprocess.run(
                [sys.executable, str(TOOL), "HEAD~1",
                 "--show-output-diffs"],
                cwd=repo.path, capture_output=True, text=True,
                encoding="utf-8", check=False)
            self.assertEqual(proc.returncode, 0, proc.stderr)
        finally:
            repo.close()

    def test_identical_outputs_not_counted_as_moved(self):
        # Cell with source changed BUT outputs byte-identical = the
        # STALE_OUTPUT class. ai-01 #16234 review flagged this as a
        # bug: report_output_diffs listed such cells as "moved" because
        # the old filter excluded only UNCHANGED_SOURCE / UNPAIRED, not
        # IDENTICAL. The fix: `moved` counts only cells whose OUTPUTS
        # differ (TEXT_DIFF, PAYLOAD_DIFF, BOTH_DIFF, EMPTY_BASE,
        # EMPTY_HEAD, METADATA_DIFF). IDENTICAL cells remain in `diffs`
        # (with source_same=False, so the STALE_OUTPUT class is named)
        # but are NOT counted as moved.
        def stream(text):
            return [{"output_type": "stream", "name": "stdout",
                     "text": [text]}]

        # 4 cells: 1 STALE (source changed, outputs identical -> kind=IDENTICAL,
        # source_same=False), 1 TEXT_DIFF, 1 UNCHANGED_SOURCE, 1 PAYLOAD_DIFF.
        bases = [
            code("x = 1\nprint(x)", stream("1\n")),
            code("print('foo')", stream("foo\n")),
            code("y = 2\nprint(y)", stream("2\n")),
            code("plt.savefig('a.png')",
                 [{"output_type": "display_data",
                   "data": {"image/png": "data:image/png;base64," + "A" * 100}}]),
        ]
        heads = [
            code("x = 1   # edited comment\nprint(x)", stream("1\n")),  # STALE
            code("print('foo')", stream("foo accentuated\n")),  # TEXT_DIFF
            code("y = 2\nprint(y)", stream("2\n")),  # UNCHANGED_SOURCE
            code("plt.savefig('a.png')",
                 [{"output_type": "display_data",
                   "data": {"image/png": "data:image/png;base64,"
                           + "A" * 200}}]),  # PAYLOAD_DIFF
        ]
        repo = GitRepo.__new__(GitRepo)
        import tempfile
        repo.dir = tempfile.TemporaryDirectory()
        repo.path = Path(repo.dir.name)
        subprocess.run(["git", "init", "-q"], cwd=repo.path, check=True)
        nb_path = "MyIA.AI.Notebooks/Fake/GT-05-IDENTICAL.ipynb"
        (repo.path / "MyIA.AI.Notebooks/Fake").mkdir(parents=True)
        for state in (nb(bases), nb(heads)):
            (repo.path / nb_path).write_text(
                json.dumps(state, ensure_ascii=False, indent=1) + "\n",
                encoding="utf-8")
            subprocess.run(["git", "add", "-A"], cwd=repo.path, check=True)
            subprocess.run(["git", "-c", "user.email=t@t", "-c",
                            "user.name=t", "commit", "-q", "-m", "s"],
                           cwd=repo.path, check=True)
        try:
            proc = subprocess.run(
                [sys.executable, str(TOOL), "HEAD~1",
                 "--show-output-diffs", "--json"],
                cwd=repo.path, capture_output=True, text=True,
                encoding="utf-8", check=False)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            payload = json.loads(proc.stdout)
            nb_rec = payload["notebooks"][0]
            self.assertEqual(nb_rec["verdict"], "CHANGED")
            self.assertEqual(nb_rec["code_cells"], 4)
            # The STALE cell (index 0): IDENTICAL kind, source_same=False.
            stale = [d for d in nb_rec["diffs"]
                     if d["index"] == 0][0]
            self.assertEqual(stale["kind"], "IDENTICAL")
            self.assertFalse(stale["source_same"])
            # UNCHANGED_SOURCE cell (index 2): UNCHANGED_SOURCE kind.
            unchanged = [d for d in nb_rec["diffs"]
                         if d["index"] == 2][0]
            self.assertEqual(unchanged["kind"], "UNCHANGED_SOURCE")
            # The moved count: only TEXT_DIFF (1) + PAYLOAD_DIFF (1) = 2.
            # NOT 3 -- IDENTICAL must NOT be counted.
            moved = [d for d in nb_rec["diffs"]
                     if d["kind"] not in ("UNCHANGED_SOURCE", "UNPAIRED",
                                           "IDENTICAL")]
            self.assertEqual(len(moved), 2,
                             f"expected 2 moved cells (TEXT+PAYLOAD), "
                             f"got {len(moved)}: kinds="
                             f"{[d['kind'] for d in nb_rec['diffs']]}")
            kinds_moved = sorted(d["kind"] for d in moved)
            self.assertEqual(kinds_moved, ["PAYLOAD_DIFF", "TEXT_DIFF"])
        finally:
            repo.dir.cleanup()


if __name__ == "__main__":
    unittest.main()
