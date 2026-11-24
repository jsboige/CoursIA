"""Tests du plancher @requires_jvm (#23542, forme 2).

Le controle positif est le point de fond : un organe qui ne peut pas rougir ne
mesure rien. Les trois verdicts sont donc exerces sur des arbres synthetiques --
croissance non declaree (rouge), perte de couverture (rouge), egalite (vert) --
et le census reel du depot est verifie contre le plancher declare dans
``scripts-tests.yml``.
"""

from __future__ import annotations

import sys
import textwrap
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_jvm_test_census as organ  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]

JVM_TESTS = """\
import pytest

requires_jvm = pytest.mark.skipif(True, reason="no jvm here")


@requires_jvm
def test_one():
    assert True


@requires_jvm
def test_two():
    assert True


def test_plain():
    assert True
"""


def write_tree(tmp_path: Path, files: dict[str, str]) -> Path:
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    for name, body in files.items():
        (tests_dir / name).write_text(textwrap.dedent(body), encoding="utf-8")
    return tests_dir


def test_module_level_definition_is_not_counted(tmp_path):
    """`requires_jvm = pytest.mark.skipif(...)` est une affectation, pas un decorateur."""
    tests_dir = write_tree(tmp_path, {"test_x.py": JVM_TESTS})
    assert organ.census(tests_dir) == {"test_x.py": ["test_one", "test_two"]}


def test_growth_above_declared_floor_is_red(tmp_path, capsys):
    # Controle positif : 2 marqueurs contre un plancher declare a 1.
    tests_dir = write_tree(tmp_path, {"test_x.py": JVM_TESTS})
    rc = organ.main(["--tests-dir", str(tests_dir), "--declared", "1"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "grandit sans declaration" in out
    assert "+1" in out


def test_shrink_below_declared_floor_is_red(tmp_path, capsys):
    tests_dir = write_tree(tmp_path, {"test_x.py": JVM_TESTS})
    rc = organ.main(["--tests-dir", str(tests_dir), "--declared", "3"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "Perte de couverture" in out


def test_equality_is_green(tmp_path, capsys):
    tests_dir = write_tree(tmp_path, {"test_x.py": JVM_TESTS})
    rc = organ.main(["--tests-dir", str(tests_dir), "--declared", "2"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "tous sautes en CI" in out


def test_json_verdict(tmp_path, capsys):
    tests_dir = write_tree(tmp_path, {"test_x.py": JVM_TESTS})
    rc = organ.main(["--tests-dir", str(tests_dir), "--declared", "2", "--json"])
    payload = capsys.readouterr().out
    assert rc == 0
    assert '"verdict": "OK"' in payload
    assert '"measured": 2' in payload


def test_missing_dir_is_red(tmp_path, capsys):
    rc = organ.main(["--tests-dir", str(tmp_path / "absent"), "--declared", "0"])
    assert rc == 1
    assert "n'est pas un dossier" in capsys.readouterr().out


def test_repository_census_matches_the_declared_floor():
    """Le plancher du workflow et le census reel ne peuvent pas diverger en silence."""
    workflow = (REPO_ROOT / ".github/workflows/scripts-tests.yml").read_text(encoding="utf-8")
    declared = [
        line for line in workflow.splitlines() if "check_jvm_test_census.py" in line and "--declared" in line
    ]
    assert declared, "le workflow n'appelle plus le census : le plancher est mort"
    floor = int(declared[0].split("--declared")[1].split()[0])
    measured = sum(len(v) for v in organ.census(REPO_ROOT / organ.DEFAULT_TESTS_DIR).values())
    assert measured == floor, (
        f"census @requires_jvm = {measured}, plancher declare = {floor} : "
        "bumper --declared dans le meme geste"
    )
