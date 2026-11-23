"""Tests for check_risk_kernel_copies.py - copies du noyau de risque (#24698).

La garde doit discriminer : verte sur l'arbre du depot, rouge des qu'une copie
derive (controle positif), qu'un projet importe le noyau sans copie, ou que la
source canonique disparait.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_risk_kernel_copies import CANONICAL_REL, PROJECTS, analyse, main  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]
KERNEL_SRC = "MODES = {'off': (False, False, False)}\n"
MAIN_SRC = "from AlgorithmImports import *\nfrom risk_kernel import RiskKernel, check_mode\n"


def _tree(tmp_path: Path, copies: dict[str, str], mains: dict[str, str] | None = None) -> Path:
    canonical = tmp_path / CANONICAL_REL
    canonical.parent.mkdir(parents=True)
    canonical.write_text(KERNEL_SRC, encoding="utf-8")
    for project, text in copies.items():
        path = tmp_path / PROJECTS / project / "risk_kernel.py"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    for project, text in (mains or {}).items():
        path = tmp_path / PROJECTS / project / "main.py"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return tmp_path


def _codes(result: dict) -> list[str]:
    return [f["code"] for f in result["findings"]]


def test_repo_tree_is_green():
    result = analyse(REPO_ROOT)
    assert result["ok"], result["findings"]
    assert len(result["copies"]) >= 2


def test_identical_copy_is_green(tmp_path):
    root = _tree(tmp_path, {"StratA": KERNEL_SRC}, {"StratA": MAIN_SRC})
    assert analyse(root)["ok"]


def test_crlf_copy_is_green(tmp_path):
    root = _tree(tmp_path, {"StratA": KERNEL_SRC})
    (root / PROJECTS / "StratA" / "risk_kernel.py").write_bytes(KERNEL_SRC.replace("\n", "\r\n").encode())
    assert analyse(root)["ok"]


def test_modified_copy_is_red(tmp_path):
    """Controle positif : une copie volontairement modifiee fait rougir la garde."""
    root = _tree(tmp_path, {"StratA": KERNEL_SRC, "StratB": KERNEL_SRC + "STOP_ATR = 3.0\n"})
    result = analyse(root)
    assert _codes(result) == ["COPY_DRIFT"]
    assert result["findings"][0]["path"].endswith("StratB/risk_kernel.py")
    assert main(["--root", str(root)]) == 1


def test_importer_without_copy_is_red(tmp_path):
    root = _tree(tmp_path, {}, {"StratA": MAIN_SRC})
    assert _codes(analyse(root)) == ["COPY_MISSING"]


def test_missing_canonical_is_red(tmp_path):
    root = _tree(tmp_path, {"StratA": KERNEL_SRC})
    (root / CANONICAL_REL).unlink()
    assert "CANONICAL_MISSING" in _codes(analyse(root))
