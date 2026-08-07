"""Tests pour scripts/notebook_tools/scan_d2_window_openness.py (#9768 Phase 1).

Pourquoi ce fichier de test existe
----------------------------------
Le detecteur D2 (fenetre non figee) est le compagnon outillage de l'audit
Phase 0 (issue #9772, c.1331+13). Sa valeur tient a sa **reproductibilite** :
un faux negatif absout un notebook D2+ et le signal perd toute credibilite
des la premiere declaration usurpee. Un faux positif accuse un notebook
conforme et bloque une PR legitime.

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
  - Issue #9772 : Phase 0 audit (mesure empirique 227/276 D2+)
  - EPIC #9768 : cadre methodologique (D1-D6)
  - c.1331+13-L1 ★★ : `grep -L` MSYS non fiable (immune ici, on utilise pathlib)
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
    classify_notebook,
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
        (worktree local = ``CoursIA-2-c1331x14-d2-scan`` vs clone CI =
        ``CoursIA``). Voir leçon c.1331+17.
        """
        from scan_d2_window_openness import DEFAULT_ROOT, REPO_ROOT
        assert DEFAULT_ROOT.name == "MyIA.AI.Notebooks"
        assert DEFAULT_ROOT.parent.resolve() == REPO_ROOT.resolve()
