#!/usr/bin/env python3
"""Tests du contrôle de provenance Stacks sur ses deux témoins réels."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts/lean"))
import check_stacks_tag_provenance as provenance


class TestStacksTagProvenance(unittest.TestCase):
    def setUp(self):
        self.readme = provenance.README.read_text(encoding="utf-8")
        self.excerpt = provenance.FIXTURE.read_text(encoding="utf-8")

    def test_real_readme_links_two_tags_to_local_declarations(self):
        errors = provenance.validate_provenance(self.readme, self.excerpt, provenance.LAKE_ROOT)
        self.assertEqual(errors, [])
        tags, pin = provenance.parse_upstream_excerpt(self.excerpt)
        self.assertEqual(pin, "5ed82d14634e8d9576bb844c7bd4e3da66d450e7")
        self.assertEqual(tags["0037"], {"Adjunction.mkOfHomEquiv"})
        self.assertEqual(
            tags["0039"],
            {
                "Adjunction.leftAdjoint_preservesColimits",
                "Adjunction.rightAdjoint_preservesLimits",
            },
        )

    def test_json_reports_an_additional_checked_tag(self):
        row = next(line for line in self.readme.splitlines() if line.startswith("| 0037 |"))
        readme = self.readme.replace(row, row + "\n" + row.replace("| 0037 |", "| 0040 |"))
        excerpt = self.excerpt + "\nadd_to_stacks 0040 \"synthetic\" Adjunction.mkOfHomEquiv\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            readme_path = root / "README.md"
            excerpt_path = root / "excerpt.txt"
            readme_path.write_text(readme, encoding="utf-8")
            excerpt_path.write_text(excerpt, encoding="utf-8")
            run = subprocess.run(
                [sys.executable, str(Path(provenance.__file__)), "--json",
                 "--readme", str(readme_path), "--excerpt", str(excerpt_path)],
                capture_output=True, text=True, encoding="utf-8", check=True,
            )
        result = json.loads(run.stdout)
        self.assertTrue(result["ok"])
        self.assertEqual(result["tags"], ["0037", "0039", "0040"])

    def test_missing_upstream_symbol_is_reported(self):
        changed = self.readme.replace(
            "Adjunction.mkOfHomEquiv", "Adjunction.notInPinnedSource"
        )
        errors = provenance.validate_provenance(changed, self.excerpt, provenance.LAKE_ROOT)
        self.assertTrue(any("absent de l'extrait amont" in error for error in errors), errors)

    def test_missing_local_declaration_is_reported(self):
        changed = self.readme.replace("homEquiv_family", "missing_local_witness")
        errors = provenance.validate_provenance(changed, self.excerpt, provenance.LAKE_ROOT)
        self.assertTrue(any("déclaration locale introuvable" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
