"""Tests for scripts/audit/extract_claims_vs_outputs.py (#8052 sampling audit).

Covers the two anti-noise fixes added in c.848 (pilote C#) :

  - Fix A : un entier nu (1-3 digits, sans unité) sur une ligne de header markdown
            ("# Search-11", "## Étape 3") n'est PAS un claim pédagogique — c'est un
            numéro de section/titre. Sur les notebooks .NET (titres riches en numéros
            de série), ce bruit explosait à 100+ ``numeric_claim_not_in_outputs`` MAJOR
            qui masquaient les vrais findings.
  - Fix B : sur un notebook .NET Interactive, les outils de visualisation Python
            (matplotlib, seaborn, pyviz) ne sont pas pertinents — un .ipynb C#/.NET
            utilise Plotly/XPlot. Le markdown cite l'équivalent Python à titre
            comparatif ("en Python on aurait utilisé matplotlib"), ce que le litmus 4
            signalait à tort comme "SOTA mentionné non importé".

Le litmus anti-LIGHT du script reste : il EXTRACT, ne décide pas. Ces tests vérifient
seulement que l'extraction ne produit plus ces deux classes de faux positifs, SANS
régresser le comportement sur Python (Fix B doit rester inactif hors .NET).
"""
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT_PATH = HERE.parent / "extract_claims_vs_outputs.py"


def _load_extract():
    spec = importlib.util.spec_from_file_location("extract_claims_vs_outputs", SCRIPT_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _write_nb(path: Path, cells: list, kernel_name: str = ".net-csharp") -> Path:
    """Écrit un mini-notebook nbformat 4.5 valide sur disque."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "cells": cells,
                "metadata": {
                    "kernelspec": {"name": kernel_name, "display_name": kernel_name},
                },
                "nbformat": 4,
                "nbformat_minor": 5,
            },
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )
    return path


def _md(source: str) -> dict:
    return {
        "cell_type": "markdown",
        "id": "md-" + str(abs(hash(source)) % 10**8),
        "metadata": {},
        "source": source,
    }


def _code(source: str, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "id": "code-" + str(abs(hash(source)) % 10**8),
        "metadata": {},
        "execution_count": 1,
        "outputs": outputs or [],
        "source": source,
    }


# === Fix A : header bare integer n'est pas un claim ===


def test_fix_A_header_section_number_is_not_a_claim():
    mod = _load_extract()
    src = "# Search-11 : Métaheuristiques\n\n## Étape 3\n\nSur ce jeu, RMSE = **2,9** et écart **40×**."
    claims = mod.extract_markdown_claims(src)["numeric_claims"]
    values = [c["value"] for c in claims]
    # Numéros de section/étape sur headers = coupés (bruit titre, pas claims)
    assert "11" not in values, f"'11' (header section number) should be filtered, got {values}"
    assert "3" not in values, f"'3' (header step number) should be filtered, got {values}"
    # Claims du corps préservés
    assert "2,9" in values, f"'2,9' (body claim) should be kept, got {values}"
    assert "40" in values, f"'40' (body claim 40x) should be kept, got {values}"


def test_fix_A_claim_with_unit_on_header_is_kept():
    """Un claim qui porte une unité (% , ×) même sur un header doit être conservé.
    Note : le % échappe au ``\\b`` final du regex (non-word→non-word avec le markdown
    ``**``), donc la valeur extraite est ``95`` et non ``95%`` — Fix A détecte l'unité
    via le caractère qui suit immédiatement le match dans le source."""
    mod = _load_extract()
    src = "### Résultat : précision **95%** sur le jeu de test"
    values = [c["value"] for c in mod.extract_markdown_claims(src)["numeric_claims"]]
    assert "95" in values, f"'95' (claim 95% on header) should be kept, got {values}"


# === Fix B : viz Python exclue du litmus 4 sur kernel .NET ===


def test_fix_B_dotnet_excludes_matplotlib_from_not_imported(tmp_path):
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "dotnet.ipynb",
        cells=[
            _md("# Mini .NET\nEn Python on aurait utilisé **matplotlib** ; ici Plotly."),
            _code('#r "nuget:Microsoft.ML,4.0.0"\nusing Microsoft.ML;'),
        ],
        kernel_name=".net-csharp",
    )
    res = mod.audit_notebook(nb)
    assert "matplotlib" in res["sota_tools_mentioned"], "matplotlib should still be detected as mentioned"
    assert "matplotlib" not in res["sota_tools_mentioned_not_imported"], (
        f"Fix B: matplotlib must NOT be flagged not-imported on .NET kernel, got {res['sota_tools_mentioned_not_imported']}"
    )


def test_fix_B_dotnet_kernelless_detected_via_nuget_directive(tmp_path):
    """Heuristique de secours : .NET détecté via #r nuget même si kernelspec est générique."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "generic-kernel.ipynb",
        cells=[
            _md("# Mini\nComparaison avec **seaborn** (Python)."),
            _code('#r "nuget:Microsoft.ML,4.0.0"\nusing Microsoft.ML;'),
        ],
        kernel_name="python3",  # kernelspec mal étiqueté
    )
    res = mod.audit_notebook(nb)
    assert "seaborn" not in res["sota_tools_mentioned_not_imported"], (
        "Fix B fallback: seaborn must be excluded when .NET detected via #r nuget directive"
    )


def test_fix_B_python_kernel_still_flags_unimported_viz(tmp_path):
    """Contrôle : sur un vrai notebook Python, le litmus 4 DOIT continuer à signaler
    matplotlib mentionné mais non importé (Fix B ne s'applique pas hors .NET)."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "python.ipynb",
        cells=[
            _md("# Mini Python\nOn visualise avec **matplotlib**."),
            _code("import numpy as np\nprint(np.array([1,2,3])"),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert "matplotlib" in res["sota_tools_mentioned_not_imported"], (
        "Regression guard: on Python, matplotlib-mentioned-not-imported must still fire"
    )
