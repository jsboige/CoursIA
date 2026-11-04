"""Tests for check_pcm_single_source.py — garde de source unique du PCM (#20188, critère 2).

La garde doit **discriminer** : verte sur un arbre conforme, rouge dès qu'une
copie dérive, qu'une copie non déclarée apparaît, que la source canonique
bouge ou qu'une déclaration devient orpheline. Le contrôle positif exigé par
#20188 est le cas « une copie volontairement modifiée fait rougir la garde ».
"""

import hashlib
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_pcm_single_source import analyse, normalized_sha256  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]
QC_ROOT = "MyIA.AI.Notebooks/QuantConnect"

CANONICAL_REL = f"{QC_ROOT}/projects/SharedPCM/pouches_pcm.py"
COPY_REL = f"{QC_ROOT}/projects/DemoComposite/portfolio_construction.py"

CANONICAL_SRC = """from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    \"\"\"Canonique de test.\"\"\"

    def __init__(self, additive=True, algorithm=None):
        super().__init__()
        self.additive = additive
        self._algorithm = algorithm
"""

COPY_SRC = """from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    \"\"\"Copie declaree de test.\"\"\"

    def __init__(self, additive=False, algorithm=None):
        super().__init__()
        self.additive = additive
        self._algorithm = algorithm
"""


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _tree(tmp_path: Path) -> tuple[Path, Path]:
    """Arbre minimal : canonique + une copie declaree, avec son manifeste."""
    _write(tmp_path, CANONICAL_REL, CANONICAL_SRC)
    _write(tmp_path, COPY_REL, COPY_SRC)
    manifest = {
        "issue": "#20188",
        "canonical": {
            "path": CANONICAL_REL,
            "classes": ["MultiStrategyPouchesPCM"],
            "sha256": _digest(CANONICAL_SRC),
        },
        "declared_copies": [
            {
                "path": COPY_REL,
                "classes": ["MultiStrategyPCM"],
                "sha256": _digest(COPY_SRC),
                "reason": "copie declaree de test",
            }
        ],
    }
    manifest_path = tmp_path / "pcm_single_source.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return tmp_path, manifest_path


def _codes(report: dict) -> set:
    return {finding["code"] for finding in report["findings"]}


def test_arbre_conforme_vert(tmp_path):
    """Cas nominal : aucune copie non declaree, aucune declaration perimee."""
    root, manifest = _tree(tmp_path)
    report = analyse(root, manifest)
    assert report["verdict"] == "OK", report
    assert report["findings"] == []


def test_copie_decleree_modifiee_fait_rougir(tmp_path):
    """CONTROLE POSITIF exigé par #20188 : une copie modifiee doit faire rougir."""
    root, manifest = _tree(tmp_path)
    _write(root, COPY_REL, COPY_SRC + "\n# modification volontaire\n")
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "DECLARATION_STALE" in _codes(report)


def test_copie_non_decleree_fait_rougir(tmp_path):
    """Une nouvelle copie hors du canonique doit etre signalee."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/SneakyComposite/portfolio_construction.py",
        COPY_SRC,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)


def test_canonique_modifie_fait_rougir(tmp_path):
    """La source canonique ne bouge pas sans re-declaration."""
    root, manifest = _tree(tmp_path)
    _write(root, CANONICAL_REL, CANONICAL_SRC + "\n# derive du canonique\n")
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CANONICAL_DRIFT" in _codes(report)


def test_declaration_orpheline_fait_rougir(tmp_path):
    """Une copie declaree qui disparait doit etre signalee (declaration a retirer)."""
    root, manifest = _tree(tmp_path)
    (root / COPY_REL).unlink()
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "DECLARED_COPY_MISSING" in _codes(report)


def test_manifeste_illisible_ne_passe_pas_au_vert(tmp_path):
    """Un manifeste illisible ne vaut pas un feu vert : la garde sedeclare en erreur."""
    root = tmp_path
    manifest = root / "pcm_single_source.json"
    manifest.write_text("{ pas du json", encoding="utf-8")
    report = analyse(root, manifest)
    assert report["verdict"] == "ERROR", report


def test_empreinte_insensible_aux_fins_de_ligne(tmp_path):
    """L'empreinte est la meme en LF et en CRLF (checkout Windows vs Linux)."""
    path = _write(tmp_path, "a.py", "x = 1\ny = 2\n")
    lf = normalized_sha256(path)
    path.write_bytes(b"x = 1\r\ny = 2\r\n")
    assert normalized_sha256(path) == lf


def test_arbre_du_depot_conforme():
    """Le depot lui-meme est conforme : la garde verte est le cas nominal reel."""
    manifest = REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json"
    report = analyse(REPO_ROOT, manifest)
    assert report["verdict"] == "OK", report["findings"]
    assert report["canonical"] == CANONICAL_REL
    assert len(report["declared_copies"]) == 2


@pytest.mark.parametrize(
    "relative",
    [
        f"{QC_ROOT}/projects/TrendWeatherPointInTime/portfolio_construction.py",
        f"{QC_ROOT}/partner-course-quant-trading/kit-transitoire/03-Framework-Composite/main.py",
    ],
)
def test_copies_decltrees_bien_declarees(relative):
    """Les deux copies qui subsistent sont declarees, avec leur raison."""
    manifest = json.loads(
        (REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json").read_text(
            encoding="utf-8"
        )
    )
    declared = {entry["path"]: entry for entry in manifest["declared_copies"]}
    assert relative in declared
    assert declared[relative]["reason"].strip()
    assert declared[relative]["sha256"] == normalized_sha256(REPO_ROOT / relative)
