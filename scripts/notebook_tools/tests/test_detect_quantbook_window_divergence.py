"""Tests pour scripts/notebook_tools/detect_quantbook_window_divergence.py (#8772).

Pourquoi ce fichier de test existe
----------------------------------
Le detecteur cherche les quantbooks qui **annoncent une periode qu'ils ne
calculent pas** (#8772, classe doc-honesty #8052/#8364). Sa valeur tient
entierement a sa credibilite : un faux positif accuse un auteur conforme, et le
signal cesse d'etre cru des la premiere fausse accusation (lecon #8765). Ces
tests existent donc autant pour verrouiller ce que le detecteur **ne doit PAS**
flagger que ce qu'il doit attraper.

Les quatre classes de faux positifs ci-dessous ne sont pas theoriques : elles
ont ete **mesurees** pendant la mise au point, sur le depot reel, avant que le
detecteur ne soit livre. La premiere version rendait 42 hits sur 22 notebooks
la ou 5 seulement etaient reels.

  FP-1  Cellule de reference `class X(QCAlgorithm)`.
        Dans un QCAlgorithm, `self.History(symbol, N)` s'ancre sur l'heure
        COURANTE de la boucle de backtest : le lookback glissant y est l'effet
        VOULU. Seul `qb.Time`, fige a `StartDate` dans un QuantBook frais,
        produit la divergence. Mesure sur QC-Py-03-Data-Management.

  FP-2  Declaration confinee a une cellule de reference.
        QC-Py-04 ne declare aucune periode dans sa recherche ; son unique
        `SetStartDate(2015, 1, 1)` vit dans un snippet « code a copier dans
        main.py ». Le compter contaminait le verdict des cellules QuantBook
        voisines, qui n'annoncent pourtant rien.

  FP-3  Identifiant nu pris pour un entier.
        `self.History([sym], start, end, ...)` avec `start = datetime(2020,8,1)`
        etait lu comme un lookback entier. D'ou la regle stricte : un argument
        AMBIGU n'est jamais flagge (faux negatif assume, cf docstring detecteur).

  FP-4  Repli local annonce, sans periode declaree.
        Les trois `Research-Executor/research_*.ipynb` impriment « Local
        environment - using yfinance fallback » et ne declarent aucune periode :
        la donnee externe est legitime (#7066) et rien n'y diverge. Le defaut
        d'Alpha-Correlation-Analysis est la CONJONCTION -- un `SetStartDate`
        place dans le `try:` qui a echoue, annonce puis jamais applique.

Une limite est assumee et testee comme telle : ML-EnhancedPairs imprime bien sa
fenetre effective, sous un libelle `Periode:` identique a celui de la periode
declaree. Le detecteur le tient donc pour conforme. Ce residu est un defaut de
**libelle**, pas de divulgation ; il est porte par le critere 2 de #8772, pas
par cet outil, qui ne doit pas revendiquer plus qu'il ne mesure.

Donnees de test : notebooks JSON minimaux en memoire, aucun fichier fixture. Le
detecteur est du Python pur operant sur des dicts `cells[]` ; on synthetise donc
exactement les structures que Jupyter produit. Chaque test isole un conjoint de
la decision, pour qu'une regression sur l'un d'eux ressorte en un seul echec.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from detect_quantbook_window_divergence import (  # noqa: E402
    RE_INT_ARG,
    _split_call_args,
    find_int_lookback_calls,
    main,
    scan_notebook,
)


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def _code(source: str, outputs: list | None = None, execution_count: int | None = 1) -> dict:
    return {
        "cell_type": "code",
        "source": source.splitlines(keepends=True),
        "outputs": outputs or [],
        "execution_count": execution_count,
        "metadata": {},
    }


def _stream(text: str) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": [text]}


def _write_nb(tmp_path: Path, cells: list[dict], name: str = "quantbook.ipynb") -> Path:
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3", "language": "python"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path = tmp_path / name
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# 1. _split_call_args -- le scanner a parentheses equilibrees
# --------------------------------------------------------------------------

class TestSplitCallArgs:
    """Une regex `\\([^)]*\\)` casse sur les appels imbriques. C'est le faux
    negatif qui avait sous-compte le scan initial de 7 hits sur 9 (#8772)."""

    def test_nested_call_in_first_arg(self):
        src = "qb.History(list(symbols.values()), 365*5, Resolution.Daily)"
        args, close = _split_call_args(src, src.index("("))
        assert args == ["list(symbols.values())", "365*5", "Resolution.Daily"]
        assert src[close] == ")"

    def test_nested_brackets_and_braces(self):
        src = "qb.History([a, b], {'k': 1}, 252)"
        args, _ = _split_call_args(src, src.index("("))
        assert args == ["[a, b]", "{'k': 1}", "252"]

    def test_comma_inside_string_is_not_a_separator(self):
        src = 'qb.History("SPY,QQQ", 252, Resolution.Daily)'
        args, _ = _split_call_args(src, src.index("("))
        assert args == ['"SPY,QQQ"', "252", "Resolution.Daily"]

    def test_escaped_quote_inside_string(self):
        src = "qb.History('a\\'b', 252)"
        args, _ = _split_call_args(src, src.index("("))
        assert len(args) == 2
        assert args[1] == "252"

    def test_unclosed_call_returns_none(self):
        src = "qb.History(symbols, 365*5"
        assert _split_call_args(src, src.index("(")) is None

    def test_empty_call(self):
        src = "qb.History()"
        args, _ = _split_call_args(src, src.index("("))
        assert args == [""]


# --------------------------------------------------------------------------
# 2. RE_INT_ARG -- strict par choix : l'ambigu n'est jamais flagge
# --------------------------------------------------------------------------

class TestIntArgRegex:
    @pytest.mark.parametrize("arg", ["365*5", "252", "1825", "365 * 2", "(365*5)", "252*12/2"])
    def test_integer_lookbacks_match(self, arg):
        assert RE_INT_ARG.match(arg)

    @pytest.mark.parametrize(
        "arg",
        [
            "start",                      # FP-3 : identifiant nu portant un datetime
            "end",
            "lookback",                   # ambigu : peut valoir un timedelta
            "datetime(2020, 1, 1)",
            "timedelta(252 * 12)",        # forme Research-Executor : duree, pas entier
            "pd.Timestamp('2020-01-01')",
            "qb.StartDate",
            "",
        ],
    )
    def test_non_integer_arguments_do_not_match(self, arg):
        assert not RE_INT_ARG.match(arg)

    def test_operators_alone_do_not_match(self):
        """Le lookahead impose au moins un chiffre : `*` ou `-` seuls ne passent pas."""
        assert not RE_INT_ARG.match("*")
        assert not RE_INT_ARG.match(" - ")


# --------------------------------------------------------------------------
# 3. find_int_lookback_calls -- receveur + 2e argument
# --------------------------------------------------------------------------

class TestFindIntLookbackCalls:
    def test_quantbook_receiver_with_nested_first_arg(self):
        hits = find_int_lookback_calls(
            "history = qb.History(list(symbols.values()), 365*5, Resolution.Daily)"
        )
        assert len(hits) == 1
        assert hits[0] == {"receiver": "qb", "lookback": "365*5"}

    def test_self_receiver_is_skipped(self):
        """FP-1 : dans un QCAlgorithm l'ancrage glissant est l'effet voulu."""
        assert find_int_lookback_calls("bars = self.History(self.symbol, 252, Resolution.Daily)") == []

    def test_explicit_datetime_pair_is_not_a_lookback(self):
        """FP-3, forme mesuree sur QC-Py-03 cellule 19."""
        src = (
            "start = datetime(2020, 8, 1)\n"
            "end = datetime(2020, 9, 30)\n"
            "bars = qb.History([sym], start, end, Resolution.Daily)\n"
        )
        assert find_int_lookback_calls(src) == []

    def test_inline_datetime_arguments_are_not_flagged(self):
        src = "qb.History(sym, datetime(2020, 1, 1), datetime(2024, 12, 31), Resolution.Daily)"
        assert find_int_lookback_calls(src) == []

    def test_single_argument_call_is_ignored(self):
        assert find_int_lookback_calls("qb.History(symbols)") == []

    def test_multiple_calls_in_one_cell_are_all_reported(self):
        src = "a = qb.History(s1, 252, Resolution.Daily)\nb = qb.History(s2, 365*5, Resolution.Daily)\n"
        assert [h["lookback"] for h in find_int_lookback_calls(src)] == ["252", "365*5"]


# --------------------------------------------------------------------------
# 4. Signal A -- lookback entier non divulgue (trois conjoints)
# --------------------------------------------------------------------------

DECLARE = (
    "qb = QuantBook()\n"
    "qb.SetStartDate(2020, 1, 1)\n"
    "qb.SetEndDate(2024, 12, 31)\n"
    'print(f"Periode: {qb.StartDate} a {qb.EndDate}")\n'
)
LOOKBACK = "history = qb.History(list(symbols.values()), 365*5, Resolution.Daily)\n"
DISCLOSE = 'print(f"Fenetre effective: {closes.index[0].date()} a {closes.index[-1].date()}")\n'


class TestSignalA:
    def test_declared_lookback_undisclosed_is_flagged(self, tmp_path):
        """Le cas type mesure : ML-RandomForest / ML-SVM / ML-XGBoost."""
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK)])
        hits = scan_notebook(nb)["hits"]
        assert len(hits) == 1
        assert hits[0]["signal"] == "history_int_lookback_undisclosed"
        assert hits[0]["lookback"] == "365*5"
        assert hits[0]["cell_index"] == 1

    def test_disclosure_clears_the_notebook(self, tmp_path):
        """L'etat cible (#8770) : divulguer, pas re-fenetrer."""
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK + DISCLOSE)])
        assert scan_notebook(nb)["hits"] == []

    def test_disclosure_via_index_bounds_alone(self, tmp_path):
        """ML-EnhancedPairs imprime bien sa fenetre, sous un libelle `Periode:`
        ambigu. C'est un defaut de LIBELLE (critere 2 de #8772), pas de
        divulgation -- le detecteur ne doit pas revendiquer de l'attraper."""
        pairs = LOOKBACK + 'print(f"Periode: {closes.index[0].date()} a {closes.index[-1].date()}")\n'
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(pairs)])
        assert scan_notebook(nb)["hits"] == []

    def test_no_declared_period_is_not_a_divergence(self, tmp_path):
        """Sans annonce, rien ne diverge : un lookback nu est un choix, pas un defaut."""
        nb = _write_nb(tmp_path, [_code("qb = QuantBook()\n"), _code(LOOKBACK)])
        assert scan_notebook(nb)["hits"] == []

    def test_not_a_quantbook_notebook(self, tmp_path):
        nb = _write_nb(tmp_path, [_code("df.SetStartDate(2020, 1, 1)\n"), _code("df.History(x, 252)\n")])
        assert scan_notebook(nb)["hits"] == []

    def test_qcalgorithm_reference_cell_is_not_flagged(self, tmp_path):
        """FP-1, mesure sur QC-Py-03 : snippet `code a copier dans main.py`."""
        ref = (
            "# [REFERENCE QC] Code a copier dans main.py QC Lab (non executable ici)\n"
            "class DataExplorationAlgo(QCAlgorithm):\n"
            "    def Initialize(self):\n"
            "        self.SetStartDate(2020, 1, 1)\n"
            "    def OnData(self, data):\n"
            "        bars = self.History(self.symbol, 252, Resolution.Daily)\n"
        )
        nb = _write_nb(tmp_path, [_code("qb = QuantBook()\n"), _code(ref)])
        assert scan_notebook(nb)["hits"] == []

    def test_reference_cell_declaration_does_not_contaminate_research(self, tmp_path):
        """FP-2, mesure sur QC-Py-04 : l'unique `SetStartDate` vit dans un
        snippet de reference, la recherche n'annonce rien -- rien ne diverge."""
        ref = (
            "class SMACrossoverAlgorithm(QCAlgorithm):\n"
            "    def Initialize(self):\n"
            "        self.SetStartDate(2015, 1, 1)\n"
        )
        nb = _write_nb(tmp_path, [_code("qb = QuantBook()\n"), _code(LOOKBACK), _code(ref)])
        assert scan_notebook(nb)["hits"] == []


# --------------------------------------------------------------------------
# 5. Signal B -- periode declaree dans une branche morte
# --------------------------------------------------------------------------

FALLBACK_SRC = (
    "try:\n"
    "    qb = QuantBook()\n"
    "    qb.SetStartDate(2020, 1, 1)\n"
    "except NameError:\n"
    '    print("Local environment detected - yfinance will be used for data")\n'
)


class TestSignalB:
    def test_declared_period_never_applied_is_flagged(self, tmp_path):
        """Alpha-Correlation-Analysis : le SetStartDate vit dans le `try:` qui
        a echoue, la fenetre reelle s'ancre a l'heure d'execution."""
        nb = _write_nb(
            tmp_path,
            [_code(FALLBACK_SRC, [_stream("Local environment detected - yfinance will be used for data\n")])],
        )
        hits = scan_notebook(nb)["hits"]
        assert len(hits) == 1
        assert hits[0]["signal"] == "declared_period_in_dead_fallback_branch"

    def test_announced_fallback_without_declaration_is_clean(self, tmp_path):
        """FP-4 : forme `Research-Executor/research_*.ipynb`. Le repli yfinance
        est une donnee externe legitime (#7066) ; sans periode annoncee, rien
        ne diverge."""
        src = (
            "try:\n"
            "    qb = QuantBook()\n"
            "    QC_ENV = True\n"
            "except (ImportError, NameError):\n"
            "    QC_ENV = False\n"
        )
        nb = _write_nb(tmp_path, [_code(src, [_stream("Local environment - using yfinance fallback for data\n")])])
        assert scan_notebook(nb)["hits"] == []

    def test_fallback_marker_read_from_outputs_not_source(self, tmp_path):
        """Le fait est lu dans les `outputs` : la branche existe dans toutes ces
        cellules, seule la sortie committee dit laquelle a reellement tourne."""
        nb = _write_nb(tmp_path, [_code(FALLBACK_SRC, [_stream("Periode: 2020-01-01 a 2024-12-31\n")])])
        assert scan_notebook(nb)["hits"] == []

    def test_marker_in_display_data_is_read(self, tmp_path):
        out = {"output_type": "execute_result", "data": {"text/plain": ["(local environment)"]}, "metadata": {}}
        nb = _write_nb(tmp_path, [_code(FALLBACK_SRC, [out])])
        assert len(scan_notebook(nb)["hits"]) == 1

    def test_only_first_marker_qualifies_the_notebook(self, tmp_path):
        cells = [
            _code(FALLBACK_SRC, [_stream("Local environment detected\n")]),
            _code("x = 1\n", [_stream("Local environment detected\n")]),
        ]
        assert len(scan_notebook(_write_nb(tmp_path, cells))["hits"]) == 1


# --------------------------------------------------------------------------
# 6. scan_notebook -- contrat de sortie et robustesse
# --------------------------------------------------------------------------

class TestScanNotebookContract:
    def test_markdown_cells_are_ignored(self, tmp_path):
        md = {"cell_type": "markdown", "source": ["qb.History(x, 365*5)\n"], "metadata": {}}
        nb = _write_nb(tmp_path, [_code(DECLARE), md])
        assert scan_notebook(nb)["hits"] == []

    def test_unreadable_notebook_reports_error_not_crash(self, tmp_path):
        path = tmp_path / "broken.ipynb"
        path.write_text("{not json", encoding="utf-8")
        result = scan_notebook(path)
        assert result["error"] is not None
        assert result["hits"] == []

    def test_result_shape(self, tmp_path):
        result = scan_notebook(_write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK)]))
        assert set(result) == {"path", "hits", "error"}
        assert set(result["hits"][0]) == {"cell_index", "signal", "lookback", "detail"}


# --------------------------------------------------------------------------
# 7. CLI
# --------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_returns_1_on_divergence(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK)])
        assert main([str(nb), "--check"]) == 1
        assert "history_int_lookback_undisclosed" in capsys.readouterr().out

    def test_check_returns_0_when_clean(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK + DISCLOSE)])
        assert main([str(nb), "--check"]) == 0
        assert "No declared-vs-effective window divergence" in capsys.readouterr().out

    def test_json_output_is_machine_readable(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK)])
        assert main([str(nb), "--json"]) == 0
        payload = json.loads(capsys.readouterr().out)
        assert payload["total_hits"] == 1
        assert payload["results"][0]["hits"][0]["lookback"] == "365*5"

    def test_missing_notebook_returns_2(self, tmp_path, capsys):
        assert main([str(tmp_path / "nope.ipynb")]) == 2
        assert "notebook not found" in capsys.readouterr().err

    def test_unknown_family_returns_2(self, tmp_path, capsys):
        assert main(["--family", "NoSuchFamily", "--root", str(tmp_path)]) == 2
        assert "family not found" in capsys.readouterr().err

    def test_report_names_the_expected_fix(self, tmp_path, capsys):
        """Le rapport doit dire de DIVULGUER, jamais de re-fenetrer : re-fenetrer
        avant #8734 echangerait un defaut de doc contre un defaut de donnees."""
        nb = _write_nb(tmp_path, [_code(DECLARE), _code(LOOKBACK)])
        main([str(nb)])
        out = capsys.readouterr().out
        assert "Fenetre effective" in out
        assert "NE PAS re-fenetrer" in out
