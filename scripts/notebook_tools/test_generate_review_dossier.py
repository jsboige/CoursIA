#!/usr/bin/env python3
"""Unit tests for generate_review_dossier (Epic #11259 T2).

Couvre les invariants des lookups du dossier, sans dependre d'un notebook
reel :
- _scope_of : strate A / B / absence (C) depuis production-scope.md
- _registry_entries_for : parsing du bloc YAML du registre editorial
- _twin_of : detection du jumeau -Csharp/-Python sur le disque
- _scan_machine_paths : signature host-path dans les outputs (Stop & Repair)

Run : python scripts/notebook_tools/test_generate_review_dossier.py
"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

import generate_review_dossier as grd  # noqa: E402

SCOPE_FIXTURE = """# scope fixture
## Strate A - proposes (1)
- [ ] `MyIA.AI.Notebooks/QC/A.ipynb`
## Strate B - hors proposition v1 (1)
- [ ] `MyIA.AI.Notebooks/QC/B.ipynb`
"""

REGISTRY_FIXTURE = """# registry fixture
```yaml
- notebook_path: QC/A.ipynb
  reviewer: someone
  review_date: 2026-08-16
  evidence_pr: "#9999"
  review_scope: factual
```
"""


class ScopeLookup(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        grd.SCOPE_FILE = Path(self._tmp.name) / "production-scope.md"
        grd.SCOPE_FILE.write_text(SCOPE_FIXTURE, encoding="utf-8")

    def tearDown(self):
        self._tmp.cleanup()

    def test_strate_a(self):
        self.assertEqual(grd._scope_of("MyIA.AI.Notebooks/QC/A.ipynb"),
                         "A (proposé PRODUCTION)")

    def test_strate_b(self):
        self.assertEqual(grd._scope_of("MyIA.AI.Notebooks/QC/B.ipynb"),
                         "B (hors proposition v1, BETA)")

    def test_absent_is_out_of_scope(self):
        self.assertEqual(grd._scope_of("MyIA.AI.Notebooks/Elsewhere/C.ipynb"),
                         "C / hors périmètre")

    def test_scope_file_missing(self):
        grd.SCOPE_FILE = Path(self._tmp.name) / "absent.md"
        self.assertEqual(grd._scope_of("MyIA.AI.Notebooks/QC/A.ipynb"), "?")


class RegistryLookup(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        grd.REGISTRY_FILE = Path(self._tmp.name) / "registry.md"
        grd.REGISTRY_FILE.write_text(REGISTRY_FIXTURE, encoding="utf-8")

    def tearDown(self):
        self._tmp.cleanup()

    def test_entry_found(self):
        entries = grd._registry_entries_for("QC/A.ipynb")
        self.assertEqual(len(entries), 1)
        self.assertEqual(entries[0]["reviewer"], "someone")
        self.assertEqual(entries[0]["evidence_pr"], "#9999")

    def test_no_entry(self):
        self.assertEqual(grd._registry_entries_for("QC/B.ipynb"), [])


class TwinDetection(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.base = Path(self._tmp.name)
        self._orig_root = grd.REPO_ROOT
        grd.REPO_ROOT = self.base

    def tearDown(self):
        grd.REPO_ROOT = self._orig_root
        self._tmp.cleanup()

    def test_csharp_twin_found(self):
        py = self.base / "Foo-Python.ipynb"
        py.write_text("{}", encoding="utf-8")
        cs = self.base / "Foo-Csharp.ipynb"
        cs.write_text("{}", encoding="utf-8")
        twin_rel, _ = grd._twin_of(cs)
        self.assertEqual(twin_rel, "Foo-Python.ipynb")

    def test_no_twin(self):
        solo = self.base / "Solo.ipynb"
        solo.write_text("{}", encoding="utf-8")
        twin_rel, _ = grd._twin_of(solo)
        self.assertEqual(twin_rel, "")


class MachinePathScan(unittest.TestCase):
    def _nb(self, outputs_blob: str) -> dict:
        return {"cells": [{"cell_type": "code", "outputs": [
            {"output_type": "stream", "text": [outputs_blob]}]}]}

    def test_windows_dev_path_detected(self):
        hits = grd._scan_machine_paths(self._nb(r"saved to D:\Dev\CoursIA\x"))
        self.assertEqual(len(hits), 1)
        self.assertEqual(hits[0][0], 0)

    def test_posix_home_detected(self):
        self.assertEqual(len(grd._scan_machine_paths(self._nb("/home/me/run"))), 1)

    def test_clean_output(self):
        self.assertEqual(grd._scan_machine_paths(self._nb("result: 42")), [])

    def test_repositional_path_clean(self):
        # un chemin relatif dans une source n'est pas un leak d'output
        self.assertEqual(grd._scan_machine_paths(self._nb("data/inputs.csv")), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
