"""Les basenames ambigus doivent rester visibles sans cible arbitraire."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

SCRIPT = Path(__file__).resolve().parents[1] / "scan_duplicate_test_pairs.py"
spec = importlib.util.spec_from_file_location("duplicate_scanner", SCRIPT)
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)


def write(root, path, content):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")


def test_ambiguous_flat_import_is_named_without_guessing(tmp_path):
    write(tmp_path, "scripts/animal.py", "# shim\n")
    write(tmp_path, "scripts/zoo/animal.py", "# implementation\n")
    write(tmp_path, "scripts/tests/test_animal.py", "from animal import walk\n")
    write(tmp_path, "scripts/tests/test_other.py", "import animal\n")
    found = scanner.find_ambiguous_flat_imports(tmp_path)
    assert found == [{"test_file": "scripts/tests/test_animal.py", "module": "animal",
                      "candidates": ["scripts/animal.py", "scripts/zoo/animal.py"]}]
    assert scanner.scan(tmp_path)["pairs"] == []


def test_json_and_check_contract_unchanged_but_warning_is_visible(tmp_path):
    write(tmp_path, "scripts/animal.py", "# shim\n")
    write(tmp_path, "scripts/zoo/animal.py", "# implementation\n")
    write(tmp_path, "scripts/tests/test_animal.py", "import animal\n")
    run = subprocess.run([sys.executable, str(SCRIPT), "--repo-root", str(tmp_path),
                          "--json", "--check"], capture_output=True, text=True)
    assert run.returncode == 0
    assert set(json.loads(run.stdout)) == {"repo_root", "test_files_scanned", "modules_scanned", "pairs"}
    assert "animal" in run.stderr and "scripts/zoo/animal.py" in run.stderr


def test_check_prefix_matches_corresponding_test_name(tmp_path):
    write(tmp_path, "scripts/check_epic_charter.py", "# shim\n")
    write(tmp_path, "scripts/epic/check_epic_charter.py", "# implementation\n")
    write(tmp_path, "scripts/tests/test_epic_charter.py", "from check_epic_charter import audit\n")
    found = scanner.find_ambiguous_flat_imports(tmp_path)
    assert [row["module"] for row in found] == ["check_epic_charter"]
    assert found[0]["candidates"] == ["scripts/check_epic_charter.py",
                                      "scripts/epic/check_epic_charter.py"]
