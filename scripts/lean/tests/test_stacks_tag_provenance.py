#!/usr/bin/env python3
"""Tests du contrôle de provenance Stacks sur ses deux témoins réels."""
from __future__ import annotations

import json
import shutil
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
        lean_root = REPO_ROOT / "MyIA.AI.Notebooks/SymbolicAI/Lean"
        [self.groth_root] = [
            lean_root / name
            for name in ("GROTH", "Grothendieck")
            if (lean_root / name).is_dir()
        ]
        self.lake_root = self.groth_root / "grothendieck_lean"
        self.readme = (self.groth_root / "README.md").read_text(encoding="utf-8")
        self.excerpt = provenance.FIXTURE.read_text(encoding="utf-8")

    def copy_witnesses(self, root: Path) -> tuple[Path, Path]:
        readme_path = root / "README.md"
        lake_path = root / "grothendieck_lean"
        witness = Path("Grothendieck/Adjunction.lean")
        (lake_path / witness.parent).mkdir(parents=True)
        readme_path.write_text(self.readme, encoding="utf-8")
        shutil.copyfile(self.lake_root / witness, lake_path / witness)
        return readme_path, lake_path

    def copy_checker(self, root: Path) -> Path:
        scripts = root / "scripts/lean"
        fixture = scripts / "fixtures" / provenance.FIXTURE.name
        fixture.parent.mkdir(parents=True)
        shutil.copyfile(provenance.FIXTURE, fixture)
        for name in ("check_stacks_tag_provenance.py", "lean_material_map.py"):
            shutil.copyfile(REPO_ROOT / "scripts/lean" / name, scripts / name)
        return scripts / "check_stacks_tag_provenance.py"

    def run_checker(self, checker: str | Path, *options: str | Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(checker), "--json", *map(str, options)],
            capture_output=True, text=True, encoding="utf-8",
        )

    def test_real_readme_links_two_tags_to_local_declarations(self):
        errors = provenance.validate_provenance(self.readme, self.excerpt, self.lake_root)
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
            readme_path, lake_path = self.copy_witnesses(root)
            excerpt_path = root / "excerpt.txt"
            readme_path.write_text(readme, encoding="utf-8")
            excerpt_path.write_text(excerpt, encoding="utf-8")
            run = self.run_checker(
                provenance.__file__,
                "--readme", readme_path, "--lake", lake_path, "--excerpt", excerpt_path,
            )
        self.assertEqual(run.returncode, 0, run.stderr or run.stdout)
        result = json.loads(run.stdout)
        self.assertTrue(result["ok"])
        self.assertEqual(result["tags"], ["0037", "0039", "0040"])

    def test_cli_defaults_follow_grothendieck_rename(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checker = self.copy_checker(root)
            lean_root = root / "MyIA.AI.Notebooks/SymbolicAI/Lean"
            self.copy_witnesses(lean_root / "GROTH")
            for name in ("GROTH", "Grothendieck"):
                with self.subTest(name=name):
                    run = self.run_checker(checker)
                    self.assertEqual(run.returncode, 0, run.stderr or run.stdout)
                    self.assertEqual(json.loads(run.stdout)["tags"], ["0037", "0039"])
                if name == "GROTH":
                    (lean_root / "GROTH").rename(lean_root / "Grothendieck")

    def test_cli_rejects_missing_or_ambiguous_default_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checker = self.copy_checker(root)
            missing = self.run_checker(checker)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn("répertoire GROTH ou Grothendieck introuvable", missing.stderr)

            lean_root = root / "MyIA.AI.Notebooks/SymbolicAI/Lean"
            readme_path, lake_path = self.copy_witnesses(lean_root / "GROTH")
            self.copy_witnesses(lean_root / "Grothendieck")
            ambiguous = self.run_checker(checker)
            self.assertNotEqual(ambiguous.returncode, 0)
            self.assertIn("répertoires GROTH et Grothendieck présents", ambiguous.stderr)

            selected = self.run_checker(checker, "--readme", readme_path, "--lake", lake_path)
            self.assertEqual(selected.returncode, 0, selected.stderr or selected.stdout)

    def test_missing_upstream_symbol_is_reported(self):
        changed = self.readme.replace(
            "Adjunction.mkOfHomEquiv", "Adjunction.notInPinnedSource"
        )
        errors = provenance.validate_provenance(changed, self.excerpt, self.lake_root)
        self.assertTrue(any("absent de l'extrait amont" in error for error in errors), errors)

    def test_missing_local_declaration_is_reported(self):
        changed = self.readme.replace("homEquiv_family", "missing_local_witness")
        errors = provenance.validate_provenance(changed, self.excerpt, self.lake_root)
        self.assertTrue(any("déclaration locale introuvable" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
