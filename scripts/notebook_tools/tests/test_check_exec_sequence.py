"""Tests for check_exec_sequence.py — execution_count coherence organ (#11112 tier 1).

Pins the verdict logic (CLEAN / DUPLICATE / UNORDERED / NOT_FROM_1 / PARTIAL
/ EMPTY / PARSE_ERROR), the independent bucket counting, the --fail-on exit
semantics, and the --tracked-only corpus restriction -- the measurement-basis
guarantee that reference numbers are commit-anchored, not working-tree
anchored. No network, no kernel.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_exec_sequence as ces


class TestVerdict:
    def test_clean(self):
        assert ces.sequence_verdict([1, 2, 3]) == "CLEAN"

    def test_clean_single(self):
        assert ces.sequence_verdict([1]) == "CLEAN"

    def test_duplicate(self):
        assert ces.sequence_verdict([1, 2, 3, 5, 5, 6]) == "DUPLICATE"

    def test_unordered(self):
        assert ces.sequence_verdict([1, 2, 3, 4, 5, 11, 6]) == "UNORDERED"

    def test_not_from_1(self):
        assert ces.sequence_verdict([2, 3, 4]) == "NOT_FROM_1"

    def test_not_from_1_beats_duplicate(self):
        # priority: NOT_FROM_1 > DUPLICATE > UNORDERED for the single label
        assert ces.sequence_verdict([2, 3, 2]) == "NOT_FROM_1"

    def test_duplicate_beats_unordered(self):
        assert ces.sequence_verdict([1, 2, 2, 1]) == "DUPLICATE"

    def test_partial_null(self):
        assert ces.sequence_verdict([1, 2, None, 4]) == "PARTIAL"

    def test_empty(self):
        assert ces.sequence_verdict([]) == "EMPTY"

    def test_restarted_kernel_tail_one(self):
        # the 10_LocalLlama signature: [..., 1] at the end = re-run cell
        assert ces.sequence_verdict([2, 3, 4, 5, 4, 5, 6, 7, 8, 9, 10, 1]) \
            == "NOT_FROM_1"

    def test_pure_gap_is_gap(self):
        # a hole (4 missing) with no repeat and no decrease: dirty per the
        # reference definition (propre = exactly 1..N), labeled GAP
        seq = [1, 2, 3, 5, 6, 7]
        assert ces.sequence_verdict(seq) == "GAP"
        assert ces.buckets_of(seq) == {"GAP"}


class TestBuckets:
    def test_independent_buckets_overlap(self):
        # DUPLICATE + UNORDERED + (from 1) simultaneously
        assert ces.buckets_of([1, 2, 2, 1]) == {"DUPLICATE", "UNORDERED"}

    def test_duplicate_and_gap_disjoint(self):
        # DUPLICATE dominates: [1,2,2,4] has both a repeat and a hole (3),
        # but GAP is only the residual when no named violation exists
        assert ces.buckets_of([1, 2, 2, 4]) == {"DUPLICATE"}

    def test_not_from_1_bucket(self):
        assert ces.buckets_of([3, 4, 5]) == {"NOT_FROM_1"}

    def test_clean_buckets_empty(self):
        assert ces.buckets_of([1, 2, 3, 4]) == set()


def _write_nb(tmp_path, exec_counts, name="nb.ipynb"):
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": e, "outputs": [],
             "source": [f"# cell {i}"]}
            for i, e in enumerate(exec_counts, 1)
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


class TestScan:
    def test_scan_verdicts(self, tmp_path):
        _write_nb(tmp_path, [1, 2, 3], name="clean.ipynb")
        _write_nb(tmp_path, [1, 2, 2], name="dup.ipynb")
        (tmp_path / "broken.ipynb").write_text("{not json", encoding="utf-8")
        recs = ces.scan(tmp_path, tracked_only=False, verbose=False)
        by_name = {r["notebook"].split("/")[-1]: r["verdict"] for r in recs}
        assert by_name["clean.ipynb"] == "CLEAN"
        assert by_name["dup.ipynb"] == "DUPLICATE"
        assert by_name["broken.ipynb"] == "PARSE_ERROR"

    def test_scan_skips_empty_source_cells(self, tmp_path):
        # a cell with empty source must not count toward the sequence
        nb = {"cells": [
            {"cell_type": "code", "execution_count": 1, "outputs": [],
             "source": ["print(1)"]},
            {"cell_type": "code", "execution_count": None, "outputs": [],
             "source": [""]},
        ], "metadata": {}, "nbformat": 4}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        recs = ces.scan(tmp_path, tracked_only=False, verbose=False)
        assert recs[0]["verdict"] == "CLEAN"

    def test_tracked_only_restricts_corpus(self, tmp_path, monkeypatch):
        tracked = tmp_path / "MyIA.AI.Notebooks"
        tracked.mkdir()
        _write_nb(tracked, [1, 2], name="kept.ipynb")
        untracked_dir = tmp_path / ".ipynb_checkpoints"
        untracked_dir.mkdir()
        _write_nb(untracked_dir, [9, 9], name="ignored.ipynb")

        def fake_ls_files(root):
            return {str(tracked / "kept.ipynb").replace("\\", "/")}

        monkeypatch.setattr(ces, "tracked_files", fake_ls_files)
        recs = ces.scan(tmp_path, tracked_only=True, verbose=False)
        names = [r["notebook"].split("/")[-1] for r in recs]
        assert names == ["kept.ipynb"]

    def test_checkpoints_always_excluded(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        _write_nb(cp, [9, 9], name="cp.ipynb")
        recs = ces.scan(tmp_path, tracked_only=False, verbose=False)
        assert recs == []


class TestFailOnCLI:
    def test_run_script_fail_on(self, tmp_path):
        import subprocess
        script = Path(ces.__file__)
        _write_nb(tmp_path, [1, 2, 2], name="dup.ipynb")
        res = subprocess.run(
            [sys.executable, str(script), str(tmp_path), "--fail-on", "DIRTY"],
            capture_output=True, text=True)
        assert res.returncode == 1
        assert "FAIL" in res.stdout

    def test_run_script_clean_passes(self, tmp_path):
        import subprocess
        script = Path(ces.__file__)
        _write_nb(tmp_path, [1, 2, 3], name="ok.ipynb")
        res = subprocess.run(
            [sys.executable, str(script), str(tmp_path), "--fail-on", "DIRTY"],
            capture_output=True, text=True)
        assert res.returncode == 0

    def test_run_script_summary_counts_gap_as_dirty(self, tmp_path):
        # regression: the summary's dirty total once summed only the three
        # named verdicts, silently dropping GAP notebooks from every count
        import subprocess
        script = Path(ces.__file__)
        _write_nb(tmp_path, [1, 2, 3], name="ok.ipynb")
        _write_nb(tmp_path, [1, 2, 4], name="gap.ipynb")
        res = subprocess.run(
            [sys.executable, str(script), str(tmp_path), "--json"],
            capture_output=True, text=True)
        s = json.loads(res.stdout)["summary"]
        assert s["scanned"] == 2
        assert s["fully_executed"] == 2
        assert s["clean"] == 1
        assert s["dirty"] == 1
        assert s["buckets"]["GAP"] == 1

    def test_run_script_json(self, tmp_path):
        import subprocess
        script = Path(ces.__file__)
        _write_nb(tmp_path, [1, 2, 3], name="ok.ipynb")
        res = subprocess.run(
            [sys.executable, str(script), str(tmp_path), "--json"],
            capture_output=True, text=True)
        assert res.returncode == 0
        data = json.loads(res.stdout)
        assert data["summary"]["scanned"] == 1
        assert data["summary"]["clean"] == 1
