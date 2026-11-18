"""Detecteur de sorties de flux sans fin de ligne (#22181).

Cinq cas distincts sont couverts :

1. le **defaut reel** : un rapport multiligne dont les fins de ligne ont ete
   perdues (l'executeur faisait ``text.split("\\n")``) ;
2. le **faux positif** que la mesure initiale de #22181 comptait : une barre
   de progression ``tqdm`` / ``yfinance``, dont les cadres se terminent par
   ``\\r`` -- c'est du texte legitime, pas un rapport aplati ;
3. le **controle negatif** : un flux correctement newline-terminé n'est
   jamais compté, et une sortie qui n'est pas un ``stream`` n'est jamais
   comptée ;
4. le **melange barre + rapport** : un seul cadre ``\\r`` ne blanchit plus un
   flux qui porte aussi un rapport aplati ;
5. les **etats non concluants** : carnet illisible et element non textuel
   sont distingues d'un zero sain.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.notebook_tools.scan_stream_newline_loss import (  # noqa: E402
    count_defects_in_notebook,
    is_defective_stream,
    is_inconclusive_stream,
    main,
    scan_path,
)


def _stream(text):
    return {"output_type": "stream", "name": "stdout", "text": text}


def test_flattened_report_is_a_defect():
    """Le cas de #21836 : les fins de ligne ont disparu."""
    out = _stream(["ligne 1", "ligne 2", "ligne 3"])
    assert is_defective_stream(out) is True


def test_progress_bar_is_not_a_defect():
    """Faux positif de la mesure initiale : une barre de progression \\r.

    Les cadres d'une barre se terminent par ``\\r`` (retour chariot) : le
    terminal les redessine sur place. Ce n'est pas un rapport aplati.
    """
    out = _stream(["\r", "[###   ] 27% completed\r", "[###   ] 27% completed"])
    assert is_defective_stream(out) is False


def test_newline_terminated_stream_is_not_a_defect():
    out = _stream(["ligne 1\n", "ligne 2\n", "ligne 3\n"])
    assert is_defective_stream(out) is False


def test_two_elements_are_never_a_defect():
    """Le seuil de la mesure : il faut plus de deux elements."""
    assert is_defective_stream(_stream(["ligne 1", "ligne 2"])) is False
    assert is_defective_stream(_stream("texte simple")) is False


def test_non_stream_output_is_never_a_defect():
    out = {"output_type": "execute_result", "data": {"text/plain": "42"},
           "execution_count": 1}
    assert is_defective_stream(out) is False


def test_mixed_output_endings_count_only_the_defective_ones():
    out = _stream(["a", "b", "c"])
    assert is_defective_stream(out) is True
    # une seule sortie avec un \n quelque part suffit a la blanchir
    out = _stream(["a\n", "b", "c"])
    assert is_defective_stream(out) is False


def test_progress_bar_followed_by_a_flattened_report_is_a_defect():
    """Un seul cadre ``\\r`` ne blanchit plus le flux entier.

    C'est le format ou un rapport est imprime dans la meme cellule qu'une
    barre de progression : la regle permissive (un seul ``\\r`` dans la liste
    suffit a blanchir) le laissait passer.
    """
    out = _stream(["[##  ] 40%\r", "[##  ] 80%\r", "rapport 1", "rapport 2"])
    assert is_defective_stream(out) is True


def test_a_single_cr_frame_does_not_whiten_a_flattened_report():
    """Un cadre ``\\r`` isole, suivi de cadres sans terminateur : defaut."""
    out = _stream(["[##  ] 40%\r", "rapport 1", "rapport 2"])
    assert is_defective_stream(out) is True


def test_inconclusive_text_element_does_not_raise():
    """Un element non textuel ne doit pas interrompre le parcours."""
    out = _stream(["ligne 1", 42, "ligne 3"])
    assert is_defective_stream(out) is False
    assert is_inconclusive_stream(out) is True


def _write_nb(path: Path, outputs):
    nb = {"cells": [{"cell_type": "code", "execution_count": 1,
                      "source": ["print('x')"], "outputs": outputs}],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")


def test_scan_path_reports_only_defective_notebooks(tmp_path):
    good = tmp_path / "good.ipynb"
    bad = tmp_path / "bad.ipynb"
    _write_nb(good, [_stream(["ligne 1\n", "ligne 2\n", "ligne 3\n"])])
    _write_nb(bad, [_stream(["ligne 1", "ligne 2", "ligne 3"]),
                     _stream(["\r", "[#] 27%\r", "[#] 27%"])])

    result = scan_path(tmp_path)
    assert list(result.defects) == ["bad.ipynb"]
    assert result.defects["bad.ipynb"] == 1
    assert result.unreadable == []
    assert result.complete is True


def test_scan_path_on_a_single_file(tmp_path):
    target = tmp_path / "one.ipynb"
    _write_nb(target, [_stream(["a", "b", "c"])])
    assert scan_path(target).defects == {"one.ipynb": 1}


def test_count_defects_ignores_markdown_cells():
    nb = {"cells": [
        {"cell_type": "markdown", "source": ["# titre"]},
        {"cell_type": "code", "execution_count": 1, "source": ["x"],
         "outputs": [_stream(["a", "b", "c"])]},
    ]}
    assert count_defects_in_notebook(nb) == 1


def test_unreadable_notebook_is_named_not_ignored(tmp_path):
    """Un carnet corrompu n'est plus saute en silence : il est compte.

    Sans cela, un balayage sur un depot peut rendre « zero defectueux » alors
    que des carnets n'ont pas ete lus du tout.
    """
    (tmp_path / "corrompu.ipynb").write_text("{ pas du json", encoding="utf-8")
    _write_nb(tmp_path / "ok.ipynb", [_stream(["a\n", "b\n", "c\n"])])

    result = scan_path(tmp_path)
    assert result.defects == {}
    assert result.unreadable == ["corrompu.ipynb"]
    assert result.scanned == 1
    assert result.complete is False


def test_inconclusive_notebook_is_counted_separately(tmp_path):
    _write_nb(tmp_path / "etrange.ipynb", [_stream(["a", 42, "c"])])

    result = scan_path(tmp_path)
    assert result.defects == {}
    assert result.inconclusive == {"etrange.ipynb": 1}
    assert result.complete is False


def test_cli_exit_codes_distinguish_clean_defect_and_incomplete(tmp_path, capsys):
    clean = tmp_path / "clean"
    clean.mkdir()
    _write_nb(clean / "ok.ipynb", [_stream(["a\n", "b\n", "c\n"])])
    assert main([str(clean)]) == 0

    broken = tmp_path / "broken"
    broken.mkdir()
    (broken / "corrompu.ipynb").write_text("{ pas du json", encoding="utf-8")
    # aucun defaut, mais la mesure n'a pas tout vu : code 3, pas 0
    assert main([str(broken)]) == 3

    defect = tmp_path / "defect"
    defect.mkdir()
    _write_nb(defect / "bad.ipynb", [_stream(["a", "b", "c"])])
    assert main([str(defect)]) == 1

    capsys.readouterr()
