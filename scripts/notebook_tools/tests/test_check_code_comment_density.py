"""Tests for check_code_comment_density.py (#26782).

Les quatre controles exigés par la spec (point 5 de l'issue) :

  1. controle POSITIF : le Z3-20 C# de #26613 (fixture vendored, sources
     seules -- outputs retires, la densite ne lit que les sources ; le
     carnet reel de la tete de PR rend la meme mesure au dixieme pres) doit
     tomber sous le seuil et rougir comme AJOUTE ;
  2. controle NEGATIF : un carnet a ~20 % de densite (>= 40 lignes de code)
     est vert ;
  3. cas du ``#`` dans une chaine (Python ET C#) : pas un commentaire ;
  4. cas du carnet de moins de 40 lignes de code : NON JUGE.

Plus les pings de conception que l'incident fondateur impose : un carnet
MODIFIE qui passe sous le seuil rougit, la dette heritee (deja sous le seuil
a la base) reste ADVISORY, les magies/directives sont exclues, l'interieur
d'une chaine multi-lignes n'est ni code ni commentaire.

La logique sous test est la classification et les verdicts -- pas de git,
pas de kernel.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_code_comment_density import (
    CODE,
    COMMENT,
    EXCLUDED,
    MIN_CODE_LINES,
    MIN_DENSITY,
    STRING_CONT,
    classify_csharp,
    classify_python,
    compare,
    diff_notebooks,
    notebook_stats,
    resolve_base,
    verdict,
)

FIXTURES = Path(__file__).resolve().parent / "fixtures"


def _nb(cells, kernel="python3"):
    return {
        "cells": [
            {"cell_type": "code", "execution_count": 1, "metadata": {},
             "outputs": [], "source": src.splitlines(True)}
            for src in cells
        ],
        "metadata": {"kernelspec": {"name": kernel,
                                    "display_name": kernel}},
        "nbformat": 4, "nbformat_minor": 5,
    }


def _cs_nb(cells):
    return _nb(cells, kernel=".net-csharp")


# ---------------------------------------------------------------------------
# Controle positif : Z3-20 C# de #26613 (fixture vendored, sources seules).
# ---------------------------------------------------------------------------

def test_positive_control_z3_20_csharp_26613():
    """Le carnet qui a motive le Concern user doit rougir comme ajoute.

    Mesure issue (regex premier passage) : 1,0 %. Mesure organe
    (tokenizer) : ~1,6 % -- meme ordre, meme verdict, et c'est le
    tokenizer qui fait foi (spec point 1).
    """
    nb = json.loads(
        (FIXTURES / "z3_20_csharp_26613_sources_only.nb.json")
        .read_text(encoding="utf-8"))
    stats = notebook_stats(nb)
    assert stats["code_lines"] >= MIN_CODE_LINES
    assert stats["density"] < MIN_DENSITY
    assert stats["per_language"], "langue non detectee"
    v = verdict(None, stats)
    assert v["verdict"] == "RED"


def test_negative_control_twenty_percent():
    """Un carnet a ~20 % de densite (>= 40 lignes) est OK."""
    lines = ["# Lecture du seuil : une ligne sur cinq environ"]
    for i in range(20):
        lines += [f"x{i} = {i}",
                  f"y{i} = x{i} + 1",
                  f"# etape {i} : somme cumulee sur la fenetre",
                  f"z{i} = y{i} * 2"]
    stats = notebook_stats(_nb(["\n".join(lines) + "\n"]))
    assert stats["code_lines"] >= MIN_CODE_LINES
    assert stats["density"] >= 0.15
    assert verdict(None, stats)["verdict"] == "OK"


# ---------------------------------------------------------------------------
# Cas du # dans une chaine (spec point 5, cas 3).
# ---------------------------------------------------------------------------

def test_hash_in_string_python():
    classes = classify_python('s = "cle # valeur"\nt = 1\n')
    assert classes[0] == CODE          # pas un commentaire
    assert classes[1] == CODE


def test_hash_in_string_csharp():
    classes = classify_csharp('var s = "# pas un commentaire";\nvar t = 1;\n')
    assert classes[0] == CODE
    assert classes[1] == CODE


def test_double_slash_in_string_csharp():
    classes = classify_csharp('var u = "https://exemple.fr";\n')
    assert classes[0] == CODE          # le // de l'URL n'est pas un commentaire


def test_trailing_comment_counts_both_sides():
    """Un commentaire de fin de ligne compte (spec #26782) : la ligne porte
    COMMENT meme si elle porte aussi du code."""
    classes = classify_python("x = 1  # invariant : x positif\n")
    assert classes[0] == COMMENT


# ---------------------------------------------------------------------------
# Cas du carnet de moins de 40 lignes (spec point 5, cas 4).
# ---------------------------------------------------------------------------

def test_small_notebook_not_judged():
    src = "\n".join(f"x{i} = {i}" for i in range(30)) + "\n"
    stats = notebook_stats(_nb([src]))
    assert stats["code_lines"] < MIN_CODE_LINES
    assert verdict(None, stats)["verdict"] == "NOT_JUDGED"


# ---------------------------------------------------------------------------
# Ratchet : ajouts, modifications, dette heritee (spec point 2).
# ---------------------------------------------------------------------------

def _stats(code, comm):
    return {"code_lines": code, "comment_lines": comm,
            "density": comm / code if code else None}


def test_added_below_threshold_red():
    assert verdict(None, _stats(100, 2))["verdict"] == "RED"


def test_added_above_threshold_ok():
    assert verdict(None, _stats(100, 8))["verdict"] == "OK"


def test_modified_drops_below_threshold_red():
    v = verdict(_stats(100, 10), _stats(100, 2))
    assert v["verdict"] == "RED"
    assert "sous le seuil" in v["reason"]


def test_modified_stays_above_ok():
    assert verdict(_stats(100, 10), _stats(100, 8))["verdict"] == "OK"


def test_inherited_debt_already_below_advisory():
    """Le stock de main n'est jamais juge : deja sous le seuil a la base,
    la modification qui y reste est ALREADY_BELOW (dette §I), pas RED."""
    v = verdict(_stats(100, 1), _stats(100, 2))
    assert v["verdict"] == "ALREADY_BELOW"


def test_modified_below_40_lines_not_judged():
    assert verdict(_stats(100, 10), _stats(30, 0))["verdict"] == "NOT_JUDGED"


# ---------------------------------------------------------------------------
# Classification : magies, directives, chaines multi-lignes.
# ---------------------------------------------------------------------------

def test_magics_and_directives_excluded_python():
    src = "%matplotlib inline\n!pip install x\n#!fsharp\n" \
          '#r "NuGet: X, 1.0"\nz = 1\n'
    classes = classify_python(src)
    assert classes[0] == EXCLUDED
    assert classes[1] == EXCLUDED
    assert classes[2] == EXCLUDED
    assert classes[3] == EXCLUDED
    assert classes[4] == CODE


def test_docstring_interior_neither_code_nor_comment():
    """La fermeture nue `\"\"\"` fait partie du token chaine : ni code ni
    commentaire (une fermeture suivie de code sur la meme ligne redevient
    CODE -- voir test_csharp_verbatim_interior)."""
    classes = classify_python('"""\ninterieur de docstring\n"""\n')
    assert classes[0] == CODE           # la ligne qui ouvre porte le token
    assert classes[1] == STRING_CONT
    assert classes[2] == STRING_CONT    # fermeture nue : interieur du token


def test_csharp_verbatim_interior():
    classes = classify_csharp('var q = @"verbatim\ninterieur\n";\n'
                              'var z = q.Length;\n')
    assert classes[0] == CODE
    assert classes[1] == STRING_CONT
    assert classes[2] == STRING_CONT      # queue de ponctuation seule
    assert classes[3] == CODE


def test_csharp_block_comment_interior_counts():
    classes = classify_csharp('/* bloc\nsuite */ var a = 1;\n')
    assert classes[0] == COMMENT
    assert classes[1] == COMMENT          # ferme le bloc puis du code


def test_csharp_preprocessor_directive_excluded():
    classes = classify_csharp("#region Calcul\n#endregion\n")
    assert classes[0] == EXCLUDED
    assert classes[1] == EXCLUDED


def test_fsharp_line_comment():
    classes = classify_csharp("let x = 1 // commentaire F#\n", fsharp=True)
    assert classes[0] == COMMENT


def test_interpolated_string_csharp():
    classes = classify_csharp('var m = $"total: {a + b} sur {n}";\n')
    assert classes[0] == CODE            # contenu entre {} n'est pas du code


# ---------------------------------------------------------------------------
# Axe lisibilite (advisory, spec point 3).
# ---------------------------------------------------------------------------

def test_long_line_counted():
    src = "x = 1  # " + "a" * 130 + "\n"
    stats = notebook_stats(_nb([src]))
    assert stats["readability"]["long_lines"] == 1


def test_long_block_counted():
    src = "\n".join(["v = 1"] + [f"w{i} = {i}" for i in range(80)])
    stats = notebook_stats(_nb([src]))
    assert stats["readability"]["long_blocks"] >= 1


def test_one_letter_outside_loop_counted():
    src = "q = f(w)\nfor i in range(3):\n    acc = i\n"
    from check_code_comment_density import _one_letter_count
    assert _one_letter_count(src, "python") >= 1   # q, w -- pas i


def test_loop_index_exempt():
    from check_code_comment_density import _one_letter_count
    assert _one_letter_count(
        "for i in range(3):\n    acc = i\n", "python") == 0


def test_readability_never_gates():
    """L'axe lisibilite est rapporte, jamais bloquant : un carnet charge en
    findings lisibilite mais au-dessus du seuil de densite reste OK."""
    src = "\n".join(["# entete"] +
                    [f"x{i} = {i}  # " + "b" * 130 for i in range(45)])
    stats = notebook_stats(_nb([src]))
    assert stats["readability"]["long_lines"] >= 45
    assert verdict(None, stats)["verdict"] == "OK"


# ---------------------------------------------------------------------------
# Language detection.
# ---------------------------------------------------------------------------

def test_kernel_language_python_vs_csharp():
    assert notebook_stats(_nb(["z = 1\n"]))["per_language"].get("python")
    assert notebook_stats(_cs_nb(["var z = 1;\n"]))["per_language"] \
        .get("csharp")


def test_polyglot_magic_first_line():
    nb = _nb(["#!csharp\nvar z = 1;\n"], kernel=".net-polyglot")
    assert notebook_stats(nb)["per_language"].get("csharp")


# ---------------------------------------------------------------------------
# Correctifs de review #26788 (tete 953d355). Chacun reproduit le defaut
# mesure par le coordinateur avant de le couvrir.
# ---------------------------------------------------------------------------

_GIT_ID = ["-c", "user.email=test@example.invalid", "-c", "user.name=test",
           "-c", "commit.gpgsign=false"]


def _git(cwd, *args):
    subprocess.run(["git", *_GIT_ID, *args], cwd=cwd, check=True,
                   capture_output=True, encoding="utf-8", errors="replace")


def _write_nb(path, src):
    path.write_text(json.dumps(_nb([src])), encoding="utf-8")


def test_rename_reads_base_at_origin_not_as_addition(tmp_path):
    """Un `git mv` pur n'ajoute rien : la base se lit a l'ORIGINE.

    Defaut mesure (review #26788) : `--name-only --diff-filter=ACMR` ne
    rend que le nouveau chemin, la base s'y lit absente -> « carnet
    ajoute » -> RED. Un renommage de carnet de dette (0 %, 45 lignes)
    rougissait : chaque PR de renumerotation ICT aurait ete bloquee.
    """
    src = "\n".join(["import math"] +
                    [f"v{i} = math.sqrt({i}) + {i} * 2"
                     for i in range(44)]) + "\n"
    _git(tmp_path, "init", "-q")
    _write_nb(tmp_path / "vieux.ipynb", src)
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-qm", "base")
    _git(tmp_path, "mv", "vieux.ipynb", "neuf.ipynb")
    _git(tmp_path, "commit", "-qm", "renommage")

    base = resolve_base("HEAD~1", cwd=tmp_path)
    pairs = diff_notebooks(base, "HEAD", cwd=tmp_path)
    assert pairs == [("neuf.ipynb", "vieux.ipynb")], pairs

    rows = compare(base, None, pairs, cwd=tmp_path)
    assert rows[0]["added"] is False, rows[0]
    assert rows[0]["verdict"] == "ALREADY_BELOW", rows[0]


def test_base_without_code_is_red_not_typeerror():
    """Base sans ligne de code + tete sous le seuil : RED, pas TypeError.

    Defaut mesure (review #26788) : `f"{base_dens:.1%}"` sur None levait
    un TypeError, exit 1 SANS JSON -- le garde tombait au lieu de conclure.
    """
    v = verdict(_stats(0, 0), _stats(100, 2))
    assert v["verdict"] == "RED"
    assert v["base_density"] is None
    assert "introduit" in v["reason"]


def test_naive_fallback_ignores_hash_in_string():
    """Repli (tokenize en echec) : un `#` dans une chaine reste du CODE."""
    src = 'verbeux = 1 if (else 0\ns = "cle # valeur"\n'
    classes = classify_python(src)
    assert classes[1] == CODE, classes


def test_naive_fallback_docstring_interior_is_string_cont():
    """Repli : l'interieur d'une docstring n'est ni code ni commentaire."""
    src = 'x = (1,\n"""\ndocstring\n"""\n'
    classes = classify_python(src)
    assert classes[1] == CODE, classes           # ouverture : token chaine
    assert classes[2] == STRING_CONT, classes
    assert classes[3] == STRING_CONT, classes     # fermeture nue


def test_py_degraded_reported_when_fallback_used():
    """Le repli S'ANNONCE : `py_degraded` est publie, plus seulement nomme."""
    assert notebook_stats(_nb(["y = (2,\nz = 1\n"]))["py_degraded"] == 1
    assert notebook_stats(_nb(["z = 1\n"]))["py_degraded"] == 0


def test_py_degraded_propagates_to_compare_rows(tmp_path):
    """`compare()` recopie `py_degraded` dans les rows (review #26788 pt 2).

    Defaut mesure : `notebook_stats` le calculait mais `compare()` ne le
    recopiait pas -- ni le JSON ni la sortie texte ne montraient la mesure
    approchee, le garde publiait une densite degradee sans le dire.
    """
    src = "y = (2,\nz = 1\n"          # parenthese ouverte -> repli
    _git(tmp_path, "init", "-q")
    _write_nb(tmp_path / "carnet.ipynb", "x = 1\n")
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-qm", "base")
    _write_nb(tmp_path / "carnet.ipynb", src)
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-qm", "degrade")

    base = resolve_base("HEAD~1", cwd=tmp_path)
    pairs = diff_notebooks(base, "HEAD", cwd=tmp_path)
    rows = compare(base, None, pairs, cwd=tmp_path)
    assert rows, "aucun carnet vu par le garde"
    assert rows[0]["py_degraded"] == 1, rows[0]
