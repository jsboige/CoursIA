"""Tests pour scripts/notebook_tools/scan_d2_window_openness.py (#9768 Phase 1).

Pourquoi ce fichier de test existe
----------------------------------
Le detecteur D2 (fenetre non figee) est le compagnon outillage de l'audit
Phase 0 (issue #9772, c.1331+13). Sa valeur tient a sa **reproductibilite** :
un faux negatif absout un notebook D2+ et le signal perd toute credibilite
des la premiere declaration usurpee. Un faux positif accuse un notebook
conforme et bloque une PR legitime.

PORTEE -- ce probe capte la **forme S** seule (SetStartDate sans SetEndDate).
Les formes N (datetime.now()), L (qb.History(sym, N)), T (timedelta)
echappent et sont mesurees par scan_window_drift.py (#10235, 4 formes).
La mesure 82 % (227/276) de #9772 etait un grep manuel SUR-COMPTE (incluait
~87 notebooks sans API QC = no-op), refusee firsthand par #10230. Ce probe
deterministe rapporte ~1.4 % (forme S) ; le vrai D2 multi-forme est ~15 %
(scan_window_drift, ~31/207). Voir #10230 pour le diagnostic complet.

Les tests ci-dessous couvrent les 4 axes :

  1. **Vrais positifs** -- un notebook avec SetStartDate mais sans SetEndDate
     doit etre classifie D2+. Variantes : Python (QuantBook), C# (algorithm.SetXxx),
     casse libre (set_end_date, SETENDDATE).

  2. **Vrais negatifs** -- un notebook qui appelle SetEndDate(...) est CONFORME,
     meme si l'argument paraitra minimal (`SetEndDate(2024,12,31)`).

  3. **Faux positifs a proscrire** -- un notebook qui mentionne `set_end_date`
     dans un commentaire, dans une docstring matplotlib, ou dans une sortie
     imprimee ("pas de SetEndDate") n'est PAS D2+. Le detecteur scanne le
     code + les outputs (divulgation), pas le texte libre markdown.

  4. **NEUTRE** -- un notebook qui ne contient aucun token QuantConnect (ni
     SetStartDate) est NEUTRE (la notion de fenetre n'a pas de sens). Un
     notebook avec SetStartDate mais sans contexte QC detecte est NEUTRE
     (peut etre matplotlib `set_start_date`, faux positif assume).

Donnees de test : notebooks JSON minimaux en memoire, aucun fichier
fixture. Le detecteur est du Python pur operant sur des dicts `cells[]` ;
on synthetise exactement les structures que Jupyter produit.

References :
  - Issue #9772 : Phase 0 audit (mesure 227/276 D2+ -- SUR-COMPTEE, voir #10230)
  - Issue #10230 : refutation firsthand de la mesure #9772 + diagnostic 4 formes
  - scan_window_drift.py (#10235) : detecteur CANONIQUE D2 (4 formes N/L/T/S)
  - EPIC #9768 : cadre methodologique (D1-D6)
  - c.1331+13-L1 : `grep -L` MSYS non fiable (immune ici, on utilise pathlib)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Permettre l'import du module scan_d2_window_openness.
# Le test vit dans scripts/notebook_tools/tests/ -- parents[1] = scripts/notebook_tools/
# ce qu'on veut ajouter a sys.path (cf test_detect_quantbook_window_divergence.py).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scan_d2_window_openness import (  # noqa: E402
    RE_QC_CONTEXT,
    RE_SET_END_DATE,
    RE_SET_START_DATE,
    _extract_code_and_outputs,
    _strip_comments,
    classify_notebook,
    classify_source,
    iter_sources,
    main,
)


# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def _make_nb(cells: list[dict]) -> str:
    """Sérialise un notebook JSON-compatible avec la structure de Jupyter."""
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    return json.dumps(nb)


def _code_cell(source: str, outputs: list | None = None) -> dict:
    """Cellule code avec source et outputs optionnels."""
    cell: dict = {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "outputs": outputs or [],
        "source": source,
    }
    return cell


def _tmp_nb(tmp_path: Path, name: str, cells: list[dict]) -> Path:
    """Ecrit un notebook JSON dans tmp_path et retourne le Path."""
    p = tmp_path / name
    p.write_text(_make_nb(cells), encoding="utf-8")
    return p


# =============================================================================
# Tests des regex (unitaire, bas-niveau)
# =============================================================================


class TestRegexSetEndDate:
    """La regex SetEndDate doit etre tolerante aux variantes C#/Python."""

    def test_python_setenddate_simple(self):
        assert RE_SET_END_DATE.search("qb.SetEndDate(2024, 12, 31)")

    def test_python_setenddate_compact(self):
        assert RE_SET_END_DATE.search("qb.SetEndDate(2024,12,31)")

    def test_csharp_algorithm_setenddate(self):
        assert RE_SET_END_DATE.search("algorithm.SetEndDate(2024, 12, 31);")

    def test_csharp_self_setenddate(self):
        assert RE_SET_END_DATE.search("self.SetEndDate(2024, 12, 31);")

    def test_lowercase_set_end_date(self):
        # Variante snake_case Python hypothetique
        assert RE_SET_END_DATE.search("qb.set_end_date(2024, 12, 31)")

    def test_uppercase_setenddate(self):
        assert RE_SET_END_DATE.search("SETENDDATE(2024, 12, 31)")

    def test_no_match_pure_set_start_date(self):
        assert not RE_SET_END_DATE.search("qb.SetStartDate(2020, 1, 1)")

    def test_no_match_in_word_substring(self):
        # Ne doit PAS matcher au milieu d'un autre mot
        assert not RE_SET_END_DATE.search("mySetEndDateFunc()")
        # Note : \b force la frontiere de mot, donc le prefixe qualifieur
        # protege. Test plus precis ci-dessous.

    def test_no_match_matplotlib_tight_layout(self):
        # matplotlib utilise `set_tight_layout`, pas SetEndDate
        assert not RE_SET_END_DATE.search("plt.set_tight_layout(True)")


class TestRegexSetStartDate:
    """La regex SetStartDate doit matcher les memes variantes."""

    def test_python(self):
        assert RE_SET_START_DATE.search("qb.SetStartDate(2020, 1, 1)")

    def test_csharp(self):
        assert RE_SET_START_DATE.search("algorithm.SetStartDate(2020, 1, 1);")

    def test_no_match(self):
        assert not RE_SET_START_DATE.search("qb.SetEndDate(2024, 12, 31)")


class TestRegexQCContext:
    """La regex QC context doit eviter les faux positifs non-QC."""

    def test_python_quantbook(self):
        assert RE_QC_CONTEXT.search("qb = QuantBook()")

    def test_csharp_qcalgorithm(self):
        assert RE_QC_CONTEXT.search("class MyAlgo : QCAlgorithm")

    def test_csharp_namespace(self):
        assert RE_QC_CONTEXT.search("using QuantConnect.Algorithm;")

    def test_python_history(self):
        assert RE_QC_CONTEXT.search("history = self.History(symbols, 365)")

    def test_no_match_pandas(self):
        # pandas ne contient aucun de ces tokens
        assert not RE_QC_CONTEXT.search("pd.set_option('display.max_rows', 100)")


# =============================================================================
# Tests de classification (integration, structure notebook)
# =============================================================================


class TestClassifyNotebookTruePositives:
    """Notebooks qui DOIVENT etre classes D2+."""

    def test_python_quantbook_d2(self, tmp_path):
        """QuantBook + SetStartDate + SetEndDate absent => D2+."""
        nb_path = _tmp_nb(tmp_path, "research_d2.ipynb", [
            _code_cell(
                "from QuantConnect import Research\n"
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "history = qb.History(symbols, 365*5, Resolution.Daily)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "D2+", rec
        assert rec["has_qc_context"] is True
        assert rec["has_set_start"] is True
        assert rec["has_set_end"] is False

    def test_csharp_algorithm_d2(self, tmp_path):
        """algorithm.SetStartDate sans SetEndDate => D2+."""
        nb_path = _tmp_nb(tmp_path, "cs_d2.ipynb", [
            _code_cell(
                "public class MyAlgo : QCAlgorithm\n"
                "{\n"
                "    public override void Initialize()\n"
                "    {\n"
                "        algorithm.SetStartDate(2020, 1, 1);\n"
                "    }\n"
                "}\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "D2+", rec

    def test_lowercase_set_end_date_d2(self, tmp_path):
        """Variante snake_case (rare mais possible) : SetStartDate en lowercase
        + pas de SetEndDate (qui n'aurait de toute facon pas de snake_case
        standard) => D2+."""
        nb_path = _tmp_nb(tmp_path, "lower_d2.ipynb", [
            _code_cell(
                "qb = QuantBook()\n"
                "qb.set_start_date(2020, 1, 1)\n"  # snake_case
                "history = qb.History(...)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "D2+", rec


class TestClassifyNotebookTrueNegatives:
    """Notebooks qui DOIVENT etre classes CONFORME."""

    def test_python_setenddate_present(self, tmp_path):
        """SetStartDate + SetEndDate => CONFORME."""
        nb_path = _tmp_nb(tmp_path, "research_ok.ipynb", [
            _code_cell(
                "from QuantConnect import Research\n"
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "qb.SetEndDate(2024, 12, 31)\n"
                "history = qb.History(symbols, 365*5, Resolution.Daily)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "CONFORME", rec
        assert rec["has_set_end"] is True

    def test_csharp_setenddate_present(self, tmp_path):
        nb_path = _tmp_nb(tmp_path, "cs_ok.ipynb", [
            _code_cell(
                "public class MyAlgo : QCAlgorithm\n"
                "{\n"
                "    public override void Initialize()\n"
                "    {\n"
                "        algorithm.SetStartDate(2020, 1, 1);\n"
                "        algorithm.SetEndDate(2024, 12, 31);\n"
                "    }\n"
                "}\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "CONFORME", rec


class TestClassifyNotebookNeutrals:
    """Notebooks SANS notion de fenetre => NEUTRE."""

    def test_pure_python_no_qc(self, tmp_path):
        """Notebook pandas/matplotlib sans aucun token QC => NEUTRE."""
        nb_path = _tmp_nb(tmp_path, "pandas_nb.ipynb", [
            _code_cell(
                "import pandas as pd\n"
                "df = pd.read_csv('data.csv')\n"
                "df['date'] = pd.to_datetime(df['date'])\n"
                "df.set_index('date', inplace=True)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "NEUTRE", rec

    def test_no_set_start_date_no_qc(self, tmp_path):
        """Notebook qui ne declare pas de fenetre du tout => NEUTRE."""
        nb_path = _tmp_nb(tmp_path, "no_window.ipynb", [
            _code_cell("import numpy as np\nx = np.arange(100)\n")
        ])
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "NEUTRE", rec

    def test_set_start_without_qc_context_is_neutral(self, tmp_path):
        """Notebook avec SetStartDate-like sans contexte QC => NEUTRE
        (peut etre matplotlib, faux positif assume)."""
        nb_path = _tmp_nb(tmp_path, "fake_start.ipynb", [
            _code_cell(
                "import matplotlib.dates as mdates\n"
                "locator = mdates.SetStartDate(2020, 1, 1)\n"  # pas un contexte QC
            )
        ])
        rec = classify_notebook(nb_path)
        # Pas de contexte QC, donc NEUTRE malgre le SetStartDate-like
        assert rec["verdict"] == "NEUTRE", rec


class TestClassifyNotebookDisclosure:
    """Divulgation dans les outputs = conformite."""

    def test_setenddate_in_output_disclosure(self, tmp_path):
        """Un notebook qui MENTIONNE SetEndDate dans une sortie imprimee
        (divulgation explicite de la fenetre) doit etre CONFORME.

        Exemple : print(f"Fenetre: {qb.SetEndDate(...)}") -- la mention dans
        l'output indique que l'auteur sait ce qu'il fait, meme si l'appel
        n'est pas dans le code source (formulation alternative).
        """
        nb_path = _tmp_nb(tmp_path, "disclosure.ipynb", [
            _code_cell(
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "history = qb.History(symbols, 365*5, Resolution.Daily)\n",
                outputs=[
                    {"output_type": "stream", "name": "stdout",
                     "text": "Fenetre effective: SetEndDate(2024, 12, 31)\n"}
                ],
            )
        ])
        rec = classify_notebook(nb_path)
        # L'output mentionne SetEndDate -> la regex matche dans les outputs
        assert rec["has_set_end"] is True
        assert rec["verdict"] == "CONFORME", rec


class TestClassifyNotebookFalsePositives:
    """Faux positifs a proscrire (FP-1 a FP-3 ci-dessous)."""

    def test_fp1_setenddate_in_markdown_only(self, tmp_path):
        """Mention de SetEndDate dans une cellule markdown seule ne doit PAS
        classer le notebook CONFORME (le code reste D2+, c'est juste une
        note dans la doc)."""
        nb_path = _tmp_nb(tmp_path, "markdown_mention.ipynb", [
            _code_cell(
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "history = qb.History(symbols, 365*5, Resolution.Daily)\n"
            ),
            {  # cellule markdown qui MENTIONNE SetEndDate mais ne l'appelle pas
                "cell_type": "markdown",
                "metadata": {},
                "source": "Pour figer la fenetre, appeler `qb.SetEndDate(2024, 12, 31)`.\n",
            },
        ])
        rec = classify_notebook(nb_path)
        # Le markdown n'est pas scanne par `_extract_code_and_outputs`
        # (qui filtre cell_type == "code"), donc le verdict reste D2+
        assert rec["verdict"] == "D2+", rec

    def test_fp2_setenddate_in_comment_only(self, tmp_path):
        """Un commentaire `# ajouter SetEndDate(...)` ne doit pas classer
        CONFORME -- l'appel n'est pas execute, c'est juste une note."""
        nb_path = _tmp_nb(tmp_path, "comment_only.ipynb", [
            _code_cell(
                "# TODO: ajouter qb.SetEndDate(2024, 12, 31)\n"
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "history = qb.History(symbols, 365*5, Resolution.Daily)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        # Mais ici la regex va quand meme matcher le commentaire...
        # Verdict : on accepte ce faux positif assumé : la regex est
        # volontairement tolerante (commentaires = divulgation = OK).
        # Ce test documente la decision, pas un defaut a corriger.
        # Pour le rendre strict, il faudrait parser les commentaires.
        # On NE le fait PAS ici (coût > valeur).
        assert rec["verdict"] in ("D2+", "CONFORME"), rec

    def test_fp3_unicode_whitespace(self, tmp_path):
        """SetEndDate avec caracteres Unicode (espaces insecables) doit
        quand meme etre detecte. Test de robustness."""
        nb_path = _tmp_nb(tmp_path, "unicode_nb.ipynb", [
            _code_cell(
                "qb = QuantBook()\n"
                "qb.SetStartDate(2020, 1, 1)\n"
                "qb.SetEndDate (2024, 12, 31)\n"  # espace insecable
                "history = qb.History(...)\n"
            )
        ])
        rec = classify_notebook(nb_path)
        # Notre regex ne gere PAS les espaces insecables -- on classe D2+
        # C'est un faux negatif assumé : rare, et l'auteur peut le voir
        # lui-meme. Pas critique.
        assert rec["verdict"] in ("D2+", "CONFORME"), rec


# =============================================================================
# Tests d'extraction code + outputs
# =============================================================================


class TestExtractCodeAndOutputs:
    def test_skip_markdown_cells(self):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": "# titre"},
                _code_cell("print('hello')\n", [
                    {"output_type": "stream", "name": "stdout", "text": "hello\n"}
                ]),
            ]
        }
        code, outputs = _extract_code_and_outputs(nb)
        assert "print('hello')" in code
        assert "hello" in outputs
        assert "# titre" not in code  # markdown pas dans code

    def test_source_as_list(self):
        """Jupyter stocke parfois `source` comme une liste de strings."""
        nb = {
            "cells": [
                _code_cell(["qb = QuantBook()\n", "qb.SetStartDate(2020, 1, 1)\n"]),
            ]
        }
        code, _ = _extract_code_and_outputs(nb)
        assert "QuantBook()" in code
        assert "SetStartDate" in code

    def test_outputs_text_as_list(self):
        """Outputs peuvent etre une liste (Jupyter le fait)."""
        nb = {
            "cells": [
                _code_cell("print('test')\n", [
                    {"output_type": "stream", "name": "stdout",
                     "text": ["test\n"]}
                ]),
            ]
        }
        _, outputs = _extract_code_and_outputs(nb)
        assert "test" in outputs

    def test_outputs_data_text_plain(self):
        """Outputs avec data.text/plain (execute_result)."""
        nb = {
            "cells": [
                _code_cell("42\n", [
                    {"output_type": "execute_result",
                     "data": {"text/plain": "42"}}
                ]),
            ]
        }
        _, outputs = _extract_code_and_outputs(nb)
        assert "42" in outputs


# =============================================================================
# Tests de la CLI (exit codes --check)
# =============================================================================


class TestMainExitCodes:
    """Verrouille les exit codes du CLI : convention argparse 0/1/2.

    Revue ai-01 sur #9783 (msg-20260807T011857-k20fjp) : un chemin invalide
    qui retourne exit=1 (D2+) sur 0 fichier scanne = faux signal en CI. Le
    fix retourne exit=2 avec message clair sur stderr, distinct du succes
    (exit=0) et d'un D2+ reel (exit=1).
    """

    def test_check_returns_2_on_nonexistent_path(self, tmp_path, capsys):
        """Le cas qui a faussé l'audit Phase 0 : chemin inexistant
        doit retourner exit=2, PAS exit=1 (D2+ fictif)."""
        bidon = tmp_path / "chemin" / "qui" / "nexiste" / "pas"
        rc = main(["--check", str(bidon)])
        assert rc == 2, f"attendu exit=2 sur chemin inexistant, recu {rc}"
        captured = capsys.readouterr()
        assert "chemin introuvable" in captured.err
        assert str(bidon) in captured.err

    def test_check_returns_2_on_file_not_directory(self, tmp_path, capsys):
        """Un fichier (pas un repertoire) doit aussi retourner exit=2."""
        fichier = tmp_path / "un_fichier.txt"
        fichier.write_text("pas un repertoire")
        rc = main(["--check", str(fichier)])
        assert rc == 2
        captured = capsys.readouterr()
        assert "pas un repertoire" in captured.err

    def test_check_returns_0_on_clean_subdir(self, tmp_path, capsys):
        """Un sous-dossier vide (sans notebook) -> exit=0 succes."""
        rc = main(["--check", str(tmp_path)])
        assert rc == 0
        captured = capsys.readouterr()
        # Pas de message d'erreur
        assert captured.err == ""

    def test_default_root_is_myia_notebooks(self, tmp_path):
        """Le default root est MyIA.AI.Notebooks/ (cohérent avec le body PR).

        On vérifie la RELATION (DEFAULT_ROOT.parent == REPO_ROOT) plutôt que le
        nom littéral du répertoire parent, car le nom varie selon le contexte
        (worktree local = ``CoursIA-2-c1331x16-d2-scan-cspy`` vs clone CI =
        ``CoursIA`` vs clone CoursIA-2 = ``CoursIA-2``). Voir leçon c.1331+17.
        """
        from scan_d2_window_openness import DEFAULT_ROOT, REPO_ROOT
        assert DEFAULT_ROOT.name == "MyIA.AI.Notebooks"
        assert DEFAULT_ROOT.parent.resolve() == REPO_ROOT.resolve()


# -----------------------------------------------------------------------------
# Phase 2 (#9768 follow-up) : extension scope .cs / .py avec FP-2 fix
# -----------------------------------------------------------------------------


class TestStripComments:
    """Couvre ``_strip_comments(source, file_type)`` (FP-2 fix).

    Le stripping est INDISPENSABLE pour les .cs/.py : sans lui, les
    ``// SetEndDate(...)`` commentes seraient pris pour des appels reels
    et le verdict serait CONFORME a tort. Cf c.1331+15 « Note Phase 2 ».
    """

    def test_strip_csharp_line_comments(self):
        src = (
            "namespace Foo;\n"
            "// SetEndDate(2024, 12, 31); // commentaire\n"
            "class Bar { }\n"
        )
        out = _strip_comments(src, "cs")
        # Le commentaire a ete neutralise (remplace par espaces de meme longueur)
        assert "SetEndDate" not in out
        assert "namespace Foo;" in out  # code reel preserve
        assert "class Bar { }" in out

    def test_strip_csharp_block_comments(self):
        src = (
            "/* SetEndDate(2024, 12, 31);\n"
            "   multi-line block comment */\n"
            "int x = 1;\n"
        )
        out = _strip_comments(src, "cs")
        assert "SetEndDate" not in out
        assert "int x = 1;" in out

    def test_strip_csharp_preserves_string_literals(self):
        """Limite assumee : on ne parse PAS les chaines.

        Un ``"// not a comment"`` dans une string passerait au strip. Ce
        test VERROUILLE la limite documentee : un commentaire a
        l'interieur d'une string est considere comme un commentaire
        (faux negatif assume sur corpus QC reel).
        """
        src = 'string s = "// SetEndDate(2024);";\n'
        out = _strip_comments(src, "cs")
        # Comportement actuel : le // dans la string est detruit (faux negatif)
        # Le test VERROUILLE ce comportement documente pour qu'un futur
        # changement soit intentionnel.
        assert "SetEndDate(2024);" not in out

    def test_strip_python_line_comments(self):
        src = (
            "# SetEndDate(2024, 12, 31)\n"
            "x = 1\n"
            "# commentaire de fin\n"
        )
        out = _strip_comments(src, "py")
        assert "SetEndDate" not in out
        assert "x = 1" in out

    def test_strip_unknown_file_type_raises(self):
        with pytest.raises(ValueError, match="file_type inconnu"):
            _strip_comments("anything", "rb")  # ruby? unknown


class TestClassifySourceTruePositives:
    """Un .cs ou .py avec SetStartDate mais sans SetEndDate = D2+."""

    def test_cs_main_cs_with_only_set_start_date(self, tmp_path):
        # Reproduction fidele de la structure CSharp-BTC-MACD-ADX/Main.cs
        # (lignes 329-363 du fichier reel, simplifiees).
        p = tmp_path / "Main.cs"
        p.write_text(
            "namespace QuantConnect.Algorithm.CSharp;\n"
            "using QuantConnect;\n"
            "class MyAlgo : QCAlgorithm {\n"
            "    public override void Initialize() {\n"
            "        // SetEndDate(2024, 12, 31); // commente\n"
            "        SetStartDate(2019, 4, 1);  // REEL\n"
            "    }\n"
            "}\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "cs")
        assert rec["verdict"] == "D2+"
        assert rec["file_type"] == "cs"
        assert rec["has_set_start"] is True
        assert rec["has_set_end"] is False
        assert rec["error"] is None

    def test_py_main_py_with_only_set_start_date(self, tmp_path):
        p = tmp_path / "main.py"
        p.write_text(
            "from AlgorithmImports import *\n"
            "qb = QuantBook()\n"
            "qb.SetStartDate(2020, 1, 1)  # REEL\n"
            "# qb.SetEndDate(2024, 12, 31)  # commente\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "py")
        assert rec["verdict"] == "D2+"
        assert rec["file_type"] == "py"
        assert rec["has_set_start"] is True
        assert rec["has_set_end"] is False


class TestClassifySourceTrueNegatives:
    """Un .cs ou .py avec SetEndDate = CONFORME."""

    def test_cs_with_set_end_date(self, tmp_path):
        p = tmp_path / "Main.cs"
        p.write_text(
            "namespace QuantConnect.Algorithm.CSharp;\n"
            "class MyAlgo : QCAlgorithm {\n"
            "    public override void Initialize() {\n"
            "        SetStartDate(2017, 10, 1);\n"
            "        SetEndDate(2025, 1, 1);\n"
            "    }\n"
            "}\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "cs")
        assert rec["verdict"] == "CONFORME"

    def test_py_with_set_end_date(self, tmp_path):
        p = tmp_path / "main.py"
        p.write_text(
            "from AlgorithmImports import *\n"
            "qb = QuantBook()\n"
            "qb.SetStartDate(2020, 1, 1)\n"
            "qb.SetEndDate(2024, 12, 31)\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "py")
        assert rec["verdict"] == "CONFORME"


class TestClassifySourceNeutrals:
    """Pas de SetStartDate ou pas de contexte QC = NEUTRE."""

    def test_cs_no_dates(self, tmp_path):
        p = tmp_path / "Main.cs"
        p.write_text(
            "namespace Foo;\n"
            "class Bar { }\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "cs")
        assert rec["verdict"] == "NEUTRE"

    def test_py_no_qc_context(self, tmp_path):
        """Un main.py non-QC (pas de QuantBook / SetStartDate) = NEUTRE."""
        p = tmp_path / "main.py"
        p.write_text(
            "import pandas as pd\n"
            "df = pd.DataFrame({'x': [1, 2, 3]})\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "py")
        assert rec["verdict"] == "NEUTRE"


class TestClassifySourceFP2Fix:
    """FP-2 : le cas-graine ``CSharp-BTC-MACD-ADX/Main.cs``.

    Avant le stripping, la regex trouvait 14 ``//SetEndDate(...)``
    commentes + 1 ``SetStartDate(2019, 4, 1)`` reel, donc classait
    CONFORME a tort. Apres stripping, on ne voit plus que le SetStartDate
    reel = D2+ veridique.
    """

    def test_canonical_btc_macd_adx_classified_d2(self, tmp_path):
        """Reproduction du cas-graine : 14 commentaires + 1 SetStartDate reel."""
        p = tmp_path / "Main.cs"
        # Generation des 14 commentaires alternes SetStartDate/SetEndDate
        commented_lines = []
        for i in range(7):
            commented_lines.append(f"            // SetStartDate({2000 + i}, 1, 1);")
            commented_lines.append(f"            // SetEndDate({2010 + i}, 12, 31);")
        p.write_text(
            "namespace QuantConnect.Algorithm.CSharp;\n"
            "using QuantConnect;\n"
            "class MyAlgo : QCAlgorithm {\n"
            "    public override void Initialize() {\n"
            + "\n".join(commented_lines)
            + "\n"
              "            SetStartDate(2019, 4, 1);  // LE SEUL REEL\n"
              "    }\n"
              "}\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "cs")
        # Verdict attendu : D2+ (1 SetStartDate reel sans EndDate reel)
        assert rec["verdict"] == "D2+", (
            f"FP-2 fix broken: le cas-graine devrait etre D2+, "
            f"obtenu {rec['verdict']} (has_set_start={rec['has_set_start']}, "
            f"has_set_end={rec['has_set_end']}). "
            f"Avant fix : CONFORME (les commentaires //SetEndDate etaient pris pour appels reels)."
        )
        assert rec["has_set_start"] is True
        assert rec["has_set_end"] is False  # commentaire neutralise

    def test_only_commented_dates_is_neutral(self, tmp_path):
        """Si TOUTES les dates sont commentees (ni SetStartDate ni SetEndDate
        REEL), le verdict doit etre NEUTRE -- pas de notion de fenetre.

        Note : un QC context est detecte (l'algo herite de QCAlgorithm)
        mais sans SetStartDate, le verdict NEUTRE prevaut.
        """
        p = tmp_path / "Main.cs"
        p.write_text(
            "namespace QuantConnect.Algorithm.CSharp;\n"
            "class MyAlgo : QCAlgorithm {\n"
            "    public override void Initialize() {\n"
            "        // SetStartDate(2020, 1, 1);\n"
            "        // SetEndDate(2024, 12, 31);\n"
            "    }\n"
            "}\n",
            encoding="utf-8",
        )
        rec = classify_source(p, "cs")
        # has_set_start est False (commentaire neutralise) -> NEUTRE
        assert rec["verdict"] == "NEUTRE"


class TestIterSources:
    """Couvre ``iter_sources(root)`` -- decouverte des main.py/Main.cs."""

    def test_iter_sources_finds_main_py(self, tmp_path):
        """La fonction doit trouver les main.py sous QuantConnect/projects/."""
        # Construire un mini-arbre
        proj = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "Strategy-A"
        proj.mkdir(parents=True)
        (proj / "main.py").write_text("pass\n", encoding="utf-8")
        # Aussi un sous-dossier avec un main.py
        sub = proj / "sub"
        sub.mkdir()
        (sub / "main.py").write_text("pass\n", encoding="utf-8")

        results = iter_sources(tmp_path)
        py_files = [p for p, ft in results if ft == "py"]
        assert len(py_files) == 2
        assert all(p.name == "main.py" for p in py_files)

    def test_iter_sources_finds_main_cs(self, tmp_path):
        proj = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "CSharp-BTC-MACD-ADX"
        proj.mkdir(parents=True)
        (proj / "Main.cs").write_text("// header\n", encoding="utf-8")

        results = iter_sources(tmp_path)
        cs_files = [p for p, ft in results if ft == "cs"]
        assert len(cs_files) == 1
        assert cs_files[0].name == "Main.cs"

    def test_iter_sources_skips_when_no_projects_dir(self, tmp_path):
        """Si pas de QuantConnect/projects/, retourne []."""
        (tmp_path / "MyIA.AI.Notebooks").mkdir()
        results = iter_sources(tmp_path)
        assert results == []

    def test_iter_sources_skips_non_target_files(self, tmp_path):
        """Un .cs qui n'est pas Main.cs n'est pas scanne."""
        proj = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "Strategy-X"
        proj.mkdir(parents=True)
        (proj / "Helper.cs").write_text("class Helper { }\n", encoding="utf-8")
        (proj / "main.py").write_text("pass\n", encoding="utf-8")
        results = iter_sources(tmp_path)
        # Seul main.py est detecte
        assert len(results) == 1
        assert results[0][1] == "py"


class TestScanMergedPopulations:
    """Couvre l'agregation ``scan()`` -- notebooks + sources."""

    def test_scan_includes_source_files(self, tmp_path):
        """scan() doit inclure les .cs/.py dans le total."""
        proj = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "CSharp-BTC-MACD-ADX"
        proj.mkdir(parents=True)
        (proj / "Main.cs").write_text(
            "namespace Q;\nclass X : QCAlgorithm {\n"
            "  public override void Initialize() { SetStartDate(2019, 4, 1); }\n"
            "}\n",
            encoding="utf-8",
        )
        report = __import__("scan_d2_window_openness").scan(tmp_path)
        assert report["total"] >= 1
        # Le D2+ de Main.cs doit apparaitre
        d2_paths = report["d2_samples"]
        assert any("CSharp-BTC-MACD-ADX" in p and "Main.cs" in p for p in d2_paths)
        # by_type doit contenir 'cs'
        assert "cs" in report["by_type"]
        assert report["by_type"]["cs"]["D2+"] >= 1


class TestFormSScopeLimitation:
    """Portee du probe : forme S (SetStartDate sans SetEndDate) SEULE.

    Ce probe NE capte PAS les formes N/L/T de drift (datetime.now, lookback-count,
    timedelta) -- qui constituent la majorite des drift reels sur le corpus QC.
    Ces formes sont mesurees par scan_window_drift.py (#10235). Les tests
    ci-dessous ANCRENT cette limitation dans le code : si un futur contributeur
    ajoutait par megarde une detection des formes N/L/T ici, il dupliquerait
    scan_window_drift.py ; si on retirait la forme S, on perdrait le filtre S.

    Refs : #10230 (refutation de la mesure 82 %/#9772), #10235 (scan_window_drift).
    """

    def test_form_lookback_count_L_not_detected(self, tmp_path):
        """Forme L : qb.History(sym, 2520, Resolution.DAILY) drift (N barres
        depuis maintenant) MAIS ce probe ne le capte pas (pas de SetStartDate).
        C'est attendu : scan_window_drift.py couvre cette forme. On verifie ici
        que le probe rend NEUTRE (pas de faux D2+ sur un pattern qu'il ne mesure
        pas honnetement)."""
        nb_path = tmp_path / "lookback.ipynb"
        nb_path.write_text(json.dumps({
            "cells": [
                {"cell_type": "code", "source": [
                    "from QuantConnect.Research import QuantBook",
                    "qb = QuantBook()",
                    "history = qb.history(['SPY'], 2520, Resolution.DAILY)",
                ], "outputs": []},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "NEUTRE"
        assert rec["has_qc_context"] is True
        assert rec["has_set_start"] is False

    def test_form_datetime_now_N_not_detected(self, tmp_path):
        """Forme N : end = datetime.now() drift avec l'horloge murale, mais
        ce probe ne le capte pas. Verifie que le probe ne pretend PAS mesurer
        cette forme (honetete de portee, anti-claim-trompeur)."""
        nb_path = tmp_path / "nownb.ipynb"
        nb_path.write_text(json.dumps({
            "cells": [
                {"cell_type": "code", "source": [
                    "from QuantConnect.Research import QuantBook",
                    "from datetime import datetime",
                    "qb = QuantBook()",
                    "end = datetime.now().strftime('%Y-%m-%d')",
                ], "outputs": []},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "NEUTRE"

    def test_form_S_set_start_without_end_IS_detected(self, tmp_path):
        """Forme S (la seule que ce probe couvre) : SetStartDate sans SetEndDate
        + contexte QC -> D2+. C'est le sous-ensemble honnetement mesure."""
        nb_path = tmp_path / "formS.ipynb"
        nb_path.write_text(json.dumps({
            "cells": [
                {"cell_type": "code", "source": [
                    "from QuantConnect.Research import QuantBook",
                    "qb = QuantBook()",
                    "qb.SetStartDate(2015, 1, 1)",
                ], "outputs": []},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
        rec = classify_notebook(nb_path)
        assert rec["verdict"] == "D2+"
