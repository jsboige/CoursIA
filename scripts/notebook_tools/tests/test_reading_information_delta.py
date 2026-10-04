# -*- coding: utf-8 -*-
"""Tests du census #18411 (couverture + delta d'information des lectures).

Les deux premiers tests sont les **controles positifs** du critere : une
lecture qui ne fait que reprendre sa sortie doit rendre un delta nul, une
lecture qui apporte du vocabulaire propre un delta haut. Sans ces deux-la, un
instrument toujours "haut" (ou toujours "nul") passerait pour calibre.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from reading_information_delta import (  # noqa: E402
    MIN_OUTPUT_CHARS,
    census_notebook,
)


def md(text):
    return {"cell_type": "markdown", "source": [text]}


def code(text, out_text=None, exec_count=1):
    outputs = []
    if out_text is not None:
        outputs = [{"output_type": "stream", "name": "stdout", "text": [out_text]}]
    return {
        "cell_type": "code",
        "source": [text],
        "outputs": outputs,
        "execution_count": exec_count,
    }


def nb(cells):
    return {"cells": cells}


def test_reading_repeating_its_output_has_zero_delta():
    """Controle positif : la redite pure est vue comme redite."""
    out = "alpha beta gamma delta epsilon zeta eta theta"
    cells = [
        code("print('x')", out),
        md("### Lecture de la sortie\n\nalpha beta gamma delta epsilon zeta eta theta"),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.code_with_output == 1
    assert c.covered == 1
    assert len(c.readings) == 1
    assert c.readings[0].delta == 0.0
    assert c.readings[0].novel_sample == []


def test_reading_with_own_vocabulary_has_high_delta():
    """Controle positif : une lecture qui apporte son vocabulaire est vue haute."""
    out = "alpha beta gamma delta epsilon zeta eta theta"
    cells = [
        code("print('x')", out),
        md(
            "### Lecture de la sortie\n\n"
            "nuance perspective dialectique reification"
        ),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert len(c.readings) == 1
    assert c.readings[0].delta == 1.0
    assert c.readings[0].novel_words == 4


def test_small_output_is_not_demanded_a_reading():
    """Une sortie sous le plancher ne compte ni comme sortie ni comme couverte."""
    cells = [
        code("x = 1", "ok"),  # 2 chars < MIN_OUTPUT_CHARS
        md("### Lecture de la sortie\n\nrien a dire"),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert MIN_OUTPUT_CHARS > len("ok")
    assert c.code_with_output == 0
    assert c.covered == 0


def test_uncovered_output_is_counted_uncovered():
    """Une sortie substantielle sans lecture apres ni avant n'est pas couverte."""
    out = "valeur " * 20
    cells = [
        code("print('x')", out),
        code("print('y')", out),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.code_with_output == 2
    assert c.covered == 0


def test_reading_before_code_is_anchored_but_labelled():
    """Le repli 'before' compte comme couverture, mais se distingue du canonique."""
    out = "kappa lambda mu nu xi omicron pi rho sigma tau upsilon"
    cells = [
        md("### Lecture de la sortie\n\npreambule kappa lambda mu nu xi omicron"),
        code("print('x')", out),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.covered == 1
    assert c.readings[0].anchor == "before"


def test_two_outputs_sharing_one_reading_are_counted_once():
    """Une lecture unique ancree a deux sorties ne double pas le recensement."""
    out = "sigma tau upsilon phi chi psi omega " * 2
    cells = [
        code("print('x')", out),
        code("print('y')", out),
        md("### Lecture de la sortie\n\nsigma tau upsilon phi chi psi omega"),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.code_with_output == 2
    assert c.covered == 1  # seule la 2e sortie a une lecture adjacente
    assert len(c.readings) == 1


def test_reading_without_rare_words_reports_none():
    """Aucun mot rare (prose vide de contenu) : delta indefini, jamais 0 par defaut."""
    out = "alpha beta gamma delta epsilon zeta eta theta"
    cells = [
        code("print('x')", out),
        md("### Lecture de la sortie\n\nle la les de du 12 34"),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.covered == 1
    assert c.readings[0].rare_words == 0
    assert c.readings[0].delta is None


def test_neighbour_prose_vocabulary_is_not_counted_novel():
    """Un terme introduit par la prose voisine n'est pas un apport de la lecture."""
    out = "alpha beta gamma delta epsilon zeta eta theta"
    cells = [
        md("### Contexte\n\nreification dialectique"),
        code("print('x')", out),
        md("### Lecture de la sortie\n\nreification dialectique alpha beta"),
    ]
    c = census_notebook(nb(cells), "synthetic.ipynb")
    assert c.readings[0].delta == 0.0


def test_main_returns_zero_on_corpus_dir(tmp_path, capsys):
    """L'instrument est advisory : il rend toujours 0, meme sur un carnet illisible."""
    from reading_information_delta import main

    (tmp_path / "bad.ipynb").write_text("{not json", encoding="utf-8")
    good = tmp_path / "good.ipynb"
    good.write_text(
        json.dumps(
            nb([code("print('x')", "alpha beta gamma delta epsilon zeta eta theta")])
        ),
        encoding="utf-8",
    )
    rc = main([str(tmp_path), "--json"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert {p["path"].split("/")[-1] for p in payload} == {"bad.ipynb", "good.ipynb"}
    assert any(p.get("unreadable") for p in payload)