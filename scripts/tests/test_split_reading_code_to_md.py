# -*- coding: utf-8 -*-
"""Reproduction du faux positif code->md fence du cliquet split-reading.

Contexte (PR #18440, Lean-10-LeanDojo c.63) : quand une PR convertit une
cellule CODE avec sortie en cellule MARKDOWN (fence), la lecture legitime
qui suit (``### Interpretation : ...``) devient orpheline de SA sortie.
La remontee ``_output_key_above`` ne s'arrete pas a la fence (elle est du
markdown) : elle la rattache a la sortie de code PRECEDENTE. La lecture
legitime ET la fence gonflent le compte de lectures de cette sortie
precedente, le releve #17044 voit un deficit, et le cliquet poste un
``SECOND_READING`` sur une lecture qui n'a pas bouge.

Ecart avec la topologie minimale 3-cellules de la spec initiale (mesure,
scratchpad prealable) : SANS code execute au-dessus de la cellule
convertisie, ``detect_added_readings`` rend ``[]`` et
``readings_by_output(head)`` rend ``{}`` -- la lecture orpheline n'est
rattachee a aucune sortie, aucun deficit, le ratchet ne mord pas. Le
declencheur est le code au-dessus. Le carnet reel de la PR #18440 en porte
un : ``c.60`` (id ``1153046e``, execution_count=23, 1 sortie) juste avant
la fenetre c.61-c.65 (mesure sur ``1ad120705`` et ``1ad120705^``). Les
trois tests ci-dessous utilisent donc la topologie du carnet reel --
celle qui declenche.

Les assertions sont celles du comportement CORRECT attendu : elles
echouent tant que le bug est present. Ce fichier est une REPRODUCTION,
pas un fix -- ``check_split_reading_cells.py`` n'est pas modifie.

Origine : c.970 (livraison PR #18708). Le diagnostic a ete pose en c.968
sur #18440 narrow (Hermes 11:33Z), la reproduction en XFAIL est livree
en c.970 ; la mise a jour des assertions (NanoClaw review 17:35Z) est
livree en c.973.

Convention XFAIL : ``strict=True`` (defaut). Un XPASS inattendu = le
bug est corrige ou la repro n'est plus probante -> la CI force la
conversion en test de non-regression (par edition du fichier, pas en
silence). Un XFAIL persistant est attendu tant que le bug est present.
"""
import pytest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))
import check_split_reading_cells as mod  # noqa: E402


def md(src, cid):
    return {"cell_type": "markdown", "source": src, "id": cid}


def code(src, cid, output="42\n"):
    return {
        "cell_type": "code",
        "source": src,
        "id": cid,
        "execution_count": 1,
        "outputs": [{"output_type": "stream", "text": output}],
    }


@pytest.mark.xfail(reason="REPRODUCTION c.970 du bug split-reading code->md ; le cliquet signale a tort -- cf docstring", strict=True)
def test_code_to_md_conversion_not_second_reading():
    """Convertir un code avec sortie en fence markdown n'est pas une seconde
    lecture : la lecture legitime qui suit commentait la sortie du code
    original, elle n'a pas ete ajoutee."""
    base_nb = {
        "cells": [
            code("print(100)", "c0", output="100\n"),
            md("### Lecture\nLe cent.", "m1"),
            code("print(42)", "c1", output="42\n"),
            md("### Interpretation : resultat", "m2"),
        ]
    }
    # c1 devient une fence markdown, id conserve (geste reel de conversion).
    head_nb = {
        "cells": [
            code("print(100)", "c0", output="100\n"),
            md("### Lecture\nLe cent.", "m1"),
            md("```python\nprint(42)\n```", "c1"),
            md("### Interpretation : resultat", "m2"),
        ]
    }
    assert mod.detect_added_readings(head_nb, base_nb) == []


@pytest.mark.xfail(reason="REPRODUCTION c.970 du bug split-reading code->md ; le cliquet rattache a tort -- cf docstring", strict=True)
def test_code_to_md_keeps_legitimate_reading_count():
    """La conversion code->fence ne doit faire monter le compte de lectures
    d'AUCUNE sortie : la lecture legitime reste rattachee a la sortie du
    code converti (qui disparait avec lui), la fence n'est pas une lecture.

    Comportement observe du bug (NanoClaw review c.973 17:35Z, head
    e7719798) : en head, la lecture orpheline est ADOPTEE par la sortie
    precedente ``print(100)`` -- son compte passe de 1 a 3 (lecture
    legitime + fence + lecture du dessus rattachees par remontee), c'est
    ce deficit fabrique qui arme le SECOND_READING du test 1.

    Comportement correct apres fix : la lecture legitime ``m1`` reste
    rattachee a ``print(100)`` (compte 1, inchange par rapport a base).
    La sortie ``print(42)`` disparait avec le code, son compte passe de 1
    (base) a absent (head). Ni la fence ni la lecture du dessous ne sont
    comptabilisees.
    """
    base_nb = {
        "cells": [
            code("print(100)", "c0", output="100\n"),
            md("### Lecture\nLe cent.", "m1"),
            code("print(42)", "c1", output="42\n"),
            md("### Interpretation : resultat", "m2"),
        ]
    }
    head_nb = {
        "cells": [
            code("print(100)", "c0", output="100\n"),
            md("### Lecture\nLe cent.", "m1"),
            md("```python\nprint(42)\n```", "c1"),
            md("### Interpretation : resultat", "m2"),
        ]
    }
    assert mod.readings_by_output(head_nb) == {"print(100)": 1}
    assert mod.readings_by_output(base_nb) == {"print(100)": 1, "print(42)": 1}


@pytest.mark.xfail(reason="REPRODUCTION c.970 du bug split-reading code->md sur Lean-10 c.63 -- cf docstring", strict=True)
def test_minimal_repro_pr_18440():
    """Topologie Lean-10-LeanDojo c.60-c.65 mesuree sur la PR #18440
    (head = 1ad120705, base = 1ad120705^) : ids reels, memes positions.
    En base, c.63 est un code execute (id 3bd10c11, ec=24) ; en head il est
    devenu une fence markdown (id conserve). Aucune lecture n'est ajoutee
    par la PR : le cliquet ne doit rien signaler."""
    code_above = "prompt_llm = format_prompt(doc)\nprint(prompt_llm)"
    base_nb = {
        "cells": [
            code(code_above, "1153046e"),
            md("### Interpretation : Prompt LLM Formate", "ve2qg725my"),
            md("### Exemple Complet avec LLM (Pseudo-code)", "51a54161"),
            code("print(pattern_llm_pseudo)", "3bd10c11", output="<pattern>\n"),
            md("### Interpretation : Pattern d'Integration LLM", "pvi42j6do5"),
            md(
                "## Exercice 2 : Prompt LLM a partir de donnees LeanDojo",
                "95aqeoic87l",
            ),
        ]
    }
    head_nb = {
        "cells": [
            code(code_above, "1153046e"),
            md("### Interpretation : Prompt LLM Formate", "ve2qg725my"),
            md("### Exemple Complet avec LLM (Pseudo-code)", "51a54161"),
            md("```python\nprint(pattern_llm_pseudo)\n```", "3bd10c11"),
            md("### Interpretation : Pattern d'Integration LLM", "pvi42j6do5"),
            md(
                "## Exercice 2 : Prompt LLM a partir de donnees LeanDojo",
                "95aqeoic87l",
            ),
        ]
    }
    assert len(mod.detect_added_readings(head_nb, base_nb)) == 0
