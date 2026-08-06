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


# === Fix C (FP-c.1228) : stream outputs must contribute numbers ===


def test_fix_C_stream_output_numbers_are_extracted(tmp_path):
    """FP-c.1228 : les notebooks dont les outputs sont du stdout (output_type 'stream',
    ex PyPhi/IIT imprime TPM/matrices/Φ via print()) n'avaient AUCUN numeric_values
    extrait — le ``CLAIM_NUMERIC_RE.finditer`` n'était appliqué qu'à ``data['text/plain']``
    des display_data. Résultat : 0% de match -> 125+ faux MAJOR
    ``numeric_claim_not_in_outputs`` qui masquaient les vrais findings sur IIT-1/2/3.

    Fix : on extrait aussi les nombres du texte des outputs stream (miroir display_data).
    Ce test vérifie qu'un markdown claim présent dans un output STREAM n'est plus flaggé."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "stream.ipynb",
        cells=[
            _md("# Computation\n\nLa matrice résultat est **0.5** et le rang **3**."),
            _code(
                "print('result: 0.5')\nprint('rank:', 3)",
                outputs=[{"output_type": "stream", "name": "stdout", "text": "result: 0.5\nrank: 3\n"}],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    # Before Fix C : stream numbers weren't extracted -> 0 matched -> 2 false MAJOR.
    # After  Fix C : "0.5" and "3" are extracted from the stream output -> both match.
    assert res["numeric_claims_matched"] >= 2, (
        f"stream output numbers must be extracted; matched={res['numeric_claims_matched']}, "
        f"unmatched={res['numeric_claims_unmatched']}"
    )
    assert res["numeric_claims_unmatched"] == 0, (
        f"markdown claims present in stream output must not be flagged; findings={res['findings']}"
    )


def test_fix_C_display_data_extraction_unchanged(tmp_path):
    """Contrôle : Fix C ajoute l'extraction stream SANS régresser l'extraction
    display_data (le chemin d'origine doit toujours extraire les nombres)."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "display.ipynb",
        cells=[
            _md("# Computation\nLa précision est **0.92**."),
            _code(
                "repr_res",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "0.92"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] == 0, (
        f"display_data extraction regression; findings={res['findings']}"
    )



# === Fix D (FP-c.1229) : .NET Interactive text/html outputs must contribute numbers ===


def test_fix_D_dotnet_html_output_numbers_are_extracted(tmp_path):
    """FP-c.1229 : .NET Interactive emet les affichages riches d'objets (metriques
    CV, contributions de features, matrices) en MIME ``text/html`` (tables
    ``dni-treeview`` avec des cellules ``<pre>...</pre>``) SANS fallback
    ``text/plain``. Le scanner n'extrait les nombres que de ``text/plain`` ->
    ``numeric_values_found`` vide pour ces outputs -> faux
    ``numeric_claim_not_in_outputs`` MAJOR sur chaque notebook .NET qui cite ses
    propres resultats (ML-4, Sudoku-DLX, GameTheory, Probas/Infer, Search/CSP).

    Ce test verifie qu'un markdown claim present dans un output ``text/html``
    n'est plus flagge (avant Fix D : 1 faux MAJOR ; apres : 0)."""
    mod = _load_extract()
    # .NET treeview-style HTML: metric value lives inside <pre>0.8884</pre>
    html_output = (
        '<table><thead><tr><th><i>index</i></th><th>value</th></tr></thead>'
        '<tbody><tr><td>0</td><td><details class="dni-treeview"><summary>'
        '<span class="dni-code-hint"><code>RegressionMetrics</code></span></summary>'
        '<div><table><tbody>'
        '<tr><td>RSquared</td><td><div class="dni-plaintext"><pre>0.8884018879298109</pre></div></td></tr>'
        '<tr><td>RootMeanSquaredError</td><td><div class="dni-plaintext"><pre>3.230644533283385</pre></div></td></tr>'
        '</tbody></table></div></details></td></tr></tbody></table>'
    )
    nb = _write_nb(
        tmp_path / "dotnet-html.ipynb",
        cells=[
            _md("# Evaluation\nLa validation croisée donne **R² ≈ 0,8884** et **RMSE ≈ 3,2306**."),
            _code(
                "cvResults.Select(x => x.Metrics)",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/html": html_output},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name=".net-csharp",
    )
    res = mod.audit_notebook(nb)
    # Before Fix D : text/html ignored -> numbers not extracted -> false MAJOR.
    # After  Fix D : "0.8884018879298109" and "3.230644533283385" extracted from
    # the <pre> cells -> the markdown claims (0,8884 / 3,2306, locale-rounded
    # prefixes) match via the Litmus-1 substring rule.
    assert res["numeric_claims_unmatched"] == 0, (
        f"markdown claims present in text/html output must not be flagged; "
        f"matched={res['numeric_claims_matched']}, findings={res['findings']}"
    )


def test_fix_D_html_extraction_does_not_regress_text_plain(tmp_path):
    """Contrôle : Fix D ajoute l'extraction text/html SANS régresser text/plain
    (le chemin d'origine doit toujours extraire les nombres d'un output text/plain,
    et un output mixte text/plain + text/html ne doit pas doubler le compte des
    matched — la règle Litmus-1 en substring + le set numeric_values gèrent la
    dédup)."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "plain.ipynb",
        cells=[
            _md("# Resultat\nLa précision est **0.92**."),
            _code(
                "metrics",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "0.92"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] == 0, (
        f"text/plain extraction regression; findings={res['findings']}"
    )



# === Fix E (FP-c.909) : tolérance d'arrondi prose↔output ===


def test_fix_E_rounded_claim_matches_full_precision_output(tmp_path):
    """FP-c.909 : la prose pédagogique arrondit les outputs (« **9.79** ») alors
    que la cellule affiche la pleine précision (« 9.785 »). Le substring échoue
    sur la troncature -> faux MAJOR ``numeric_claim_not_in_outputs``. La famille
    Probas (Infer-101) était FULLY CLEAN mais apparaissait sale à cause de ça.

    Fix E : après l'échec du substring, si la claim a des décimales, on compare
    en float à la précision de la claim (±0.005 pour 2 décimales). Ce test
    vérifie qu'un markdown claim arrondi présent (en pleine précision) dans un
    output n'est plus flaggé."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "rounding.ipynb",
        cells=[
            _md("# Évaluation\nLa MAE est **9.79** et le biais **-45.80**."),
            _code(
                "metrics",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "MAE=9.785, bias=-45.79730358385471"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] == 0, (
        f"rounded claims (9.79 / -45.80) must match full-precision outputs "
        f"(9.785 / -45.797...) via Fix E tolerance; "
        f"matched={res['numeric_claims_matched']}, findings={res['findings']}"
    )


def test_fix_E_fr_comma_claim_matches_dot_output(tmp_path):
    """La claim FR à virgule (« **9,79** ») doit matcher l'output à point
    (« 9.785 ») via la même tolérance d'arrondi (la normalisation virgule→point
    s'applique avant le calcul float)."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "fr-rounding.ipynb",
        cells=[
            _md("# Évaluation\nLa MAE est **9,79**."),
            _code(
                "metrics",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "9.785"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] == 0, (
        f"FR comma claim (9,79) must match dot output (9.785) via Fix E; "
        f"findings={res['findings']}"
    )


def test_fix_E_genuine_mismatch_still_flagged(tmp_path):
    """Contrôle anti-complaisance : Fix E ne doit PAS absorber un VRAI écart.
    Une claim « **0.95** » contre un output « 0.85 » = |0.85−0.95| = 0.10,
    très supérieur au ±0.005 de tolérance (2 décimales) -> doit rester signalé
    comme ``numeric_claim_not_in_outputs`` MAJOR. Sans ce garde-fou, Fix E
    masquerait des claims exagérées (le vrai objectif du Litmus 1)."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "genuine-mismatch.ipynb",
        cells=[
            _md("# Évaluation\nLa précision est **0.95**."),
            _code(
                "metrics",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "0.85"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] >= 1, (
        f"genuine mismatch (0.95 vs 0.85) must stay flagged; Fix E must not "
        f"absorb real exaggerations; findings={res['findings']}"
    )


def test_fix_E_integer_claim_requires_exact_match(tmp_path):
    """Contrôle : une claim entière (« **10** ») garde une tolérance nulle
    (ndec=0 -> tol=None -> match exact substring requis uniquement). Une claim
    « 10 » ne doit pas absorber un output « 12 » (|12−10|=2) — et ne doit pas
    non plus matcher « 10 » au sein d'un grand nombre par tolérance float."""
    mod = _load_extract()
    nb = _write_nb(
        tmp_path / "integer.ipynb",
        cells=[
            _md("# Décompte\nIl y a **10** clusters."),
            _code(
                "count",
                outputs=[
                    {
                        "output_type": "execute_result",
                        "execution_count": 1,
                        "data": {"text/plain": "12"},
                        "metadata": {},
                    }
                ],
            ),
        ],
        kernel_name="python3",
    )
    res = mod.audit_notebook(nb)
    assert res["numeric_claims_unmatched"] >= 1, (
        f"integer claim (10 vs 12) must stay flagged — Fix E tolerance is "
        f"disabled for integer claims; findings={res['findings']}"
    )
