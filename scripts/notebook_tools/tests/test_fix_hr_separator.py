"""Tests de `fix_hr_separator` — chaque cas dangereux a son controle.

Le risque de cet outil n'est pas de rater une conversion (le notebook reste
simplement hors du render) mais d'en faire une de trop : convertir un
soulignement setext ou un vrai frontmatter changerait le rendu ou casserait
les metadonnees. Les tests sont donc majoritairement des controles NEGATIFS.
"""
import importlib.util
import json
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "fix_hr_separator", Path(__file__).resolve().parents[1] / "fix_hr_separator.py"
)
fix = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(fix)


def conv(text, first=False):
    return fix.convert_cell(text, first)


def test_separateur_apres_ligne_vide_converti():
    src = "Du texte.\n\n---\n\nAutre texte."
    out, n = conv(src)
    assert n == 1
    assert "***" in out and "\n---\n" not in out


def test_separateur_en_tete_de_cellule_converti():
    src = "---\n\n## Titre\n\nProse."
    out, n = conv(src)
    assert n == 1
    assert out.startswith("***")


def test_soulignement_setext_non_touche():
    """`---` colle a du texte = titre H2, pas un separateur."""
    src = "Un titre de section\n---\n\nProse."
    out, n = conv(src)
    assert n == 0
    assert out == src


def test_bloc_de_code_non_touche():
    src = "Exemple :\n\n```yaml\n\n---\n\n```\n\nFin."
    out, n = conv(src)
    assert n == 0
    assert out == src


def test_vrai_frontmatter_de_tete_non_touche():
    src = '---\ntitle: "Mon notebook"\nauthor: Moi\n---\n'
    out, n = conv(src, first=True)
    assert n == 0
    assert out == src


def test_frontmatter_hors_premiere_cellule_est_converti():
    """Seule la PREMIERE cellule markdown peut porter un frontmatter legitime."""
    src = '---\ntitle: "pas un frontmatter ici"\n---\n'
    out, n = conv(src, first=False)
    assert n >= 1


def test_source_liste_reste_une_liste_avec_newlines():
    src = ["Du texte.\n", "\n", "---\n", "\n", "Suite."]
    out, n = conv(src)
    assert n == 1
    assert isinstance(out, list)
    assert "".join(out) == "Du texte.\n\n***\n\nSuite."


def test_plusieurs_separateurs_dans_une_cellule():
    src = "A\n\n---\n\nB\n\n---\n\nC"
    out, n = conv(src)
    assert n == 2
    assert out.count("***") == 2


def test_process_ecrit_et_reste_idempotent(tmp_path):
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": "# Titre\n"},
            {"cell_type": "markdown", "source": "Prose.\n\n---\n\nSuite.\n"},
            {"cell_type": "code", "source": "x = 1\n", "outputs": [],
             "execution_count": 1, "metadata": {}},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "n.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")

    assert fix.process(p, apply=False) == 1          # detecte
    assert fix.process(p, apply=True) == 1           # convertit
    assert fix.process(p, apply=False) == 0          # idempotent
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "***" in after["cells"][1]["source"]
    assert after["cells"][2]["source"] == "x = 1\n"  # code intact


def test_controle_positif_le_notebook_de_l_incident(tmp_path):
    """Controle POSITIF : la forme exacte qui a fait tomber le site #11451.

    Sans lui, un `0 a convertir` serait indiscernable d'un detecteur casse.
    """
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": "# SL-8\n"},
            {"cell_type": "markdown",
             "source": "---\n\n## 3. Extraction des donnees\n\nAvant de miner.\n"},
            {"cell_type": "markdown",
             "source": "---\n\n### Interpretation : Extraction\n\nL'extraction convertit.\n"},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "sl8.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    assert fix.process(p, apply=False) == 2, (
        "controle positif ECHOUE : la forme de l'incident #11451 n'est pas "
        "detectee -> l'outil est casse, son 'rien a convertir' est sans valeur"
    )


def _byte_diff_regions(a, b):
    """Rend les plages bytes ou ``a`` et ``b`` different, en supposant des tailles egales."""
    n = len(a)
    out = []
    i = 0
    while i < n:
        if a[i] != b[i]:
            j = i
            while j < n and a[j] != b[j]:
                j += 1
            out.append((i, j))
            i = j
        else:
            i += 1
    return out


def test_apply_byte_preserving_avec_output_text_html(tmp_path):
    """Regression #15230 : `--apply` ne doit changer que `---` en `***` dans la source.

    Le notebook .NET porte dans un output `text/html` une ligne whitespace-only
    (du decor JSON entre deux elements d'un tableau) que l'ancienne ecriture
    ``json.dumps(indent=1)`` supprimait. Le fixer byte-preserving doit la garder
    et ne modifier aucune autre surface (source code, outputs, execution_count,
    metadata, blanc interne).
    """
    raw = (
        '{"cells":['
        '{"cell_type":"markdown","source":["Prose.\\n","\\n","---\\n","\\n","Suite.\\n"]},'
        '{"cell_type":"code","execution_count":3,"metadata":{},"outputs":['
        '{"output_type":"display_data","data":{"text/html":['
        '"<div>\\r\\n",'
        '   \n'
        '"</div>\\r\\n"]},"metadata":{}}]}'
        '],"metadata":{},"nbformat":4,"nbformat_minor":5}\n'
    )
    p = tmp_path / "n.ipynb"
    p.write_bytes(raw.encode("utf-8"))
    before = p.read_bytes()

    assert fix.process(p, apply=False) == 1
    assert fix.process(p, apply=True) == 1
    after = p.read_bytes()

    # seule difference : la ligne de separateur markdown `---` devient `***`
    assert after == before.replace(b'"---\\n"', b'"***\\n"')
    # le decor whitespace-only entre les elements text/html est byte-preserve
    assert b'   \n' in after
    # aucune autre surface ne change (surfaces non ciblees)
    assert len(_byte_diff_regions(before, after)) >= 1
    for (s, e) in _byte_diff_regions(before, after):
        assert (before[s:e], after[s:e]) == (b"---", b"***")

    # les objets JSON non source restent semantiquement egaux
    before_nb = json.loads(before)
    after_nb = json.loads(after)
    assert before_nb["cells"][1]["outputs"] == after_nb["cells"][1]["outputs"]
    assert before_nb["cells"][1]["execution_count"] == after_nb["cells"][1]["execution_count"]
    assert before_nb["cells"][1]["metadata"] == after_nb["cells"][1]["metadata"]

    # idempotence : second --apply = 0 changement, fichier byte-identique
    assert fix.process(p, apply=True) == 0
    assert p.read_bytes() == after


def test_apply_preserve_code_outputs_execution_count(tmp_path):
    """Controle byte-à-byte : code, execution_count et outputs restent intacts."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": "# T\n"},
            {"cell_type": "markdown", "source": "A.\n\n---\n\nB.\n"},
            {"cell_type": "code", "source": "for (var i = 0; i < 3; i++) { }\n",
             "execution_count": 7, "metadata": {"tags": []},
             "outputs": [{"output_type": "display_data", "metadata": {},
                          "data": {"text/plain": ["hello\n"]}}]},
        ],
        "metadata": {"kernelspec": {"name": ".net-csharp", "display_name": ".NET (C#)"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "n.ipynb"
    p.write_bytes(json.dumps(nb).encode("utf-8"))
    before = p.read_bytes()

    assert fix.process(p, apply=True) == 1
    after = p.read_bytes()

    before_nb = json.loads(before)
    after_nb = json.loads(after)
    # source markdown convertie, le reste byte-identique au niveau objet
    assert after_nb["cells"][1]["source"] == "A.\n\n***\n\nB.\n"
    assert after_nb["cells"][2]["source"] == "for (var i = 0; i < 3; i++) { }\n"
    assert after_nb["cells"][2]["execution_count"] == 7
    assert after_nb["cells"][2]["outputs"] == before_nb["cells"][2]["outputs"]
    assert after_nb["metadata"] == before_nb["metadata"]
    # la source code n'a pas change au niveau bytes non plus
    assert b'for (var i = 0; i < 3; i++) { }' in after
    assert b'7' in after  # execution_count reste


def test_reconciliation_echoue_sans_ecrire(tmp_path):
    """Si les mutations textuelles ne se reconcilient pas, `--apply` echoue sans ecrire.

    Source markdown dont le separateur est encode en `-` (escape unicode) :
    la classification voit `---` (decode), mais le texte brut ne porte pas `---`,
    donc la mutation ne se reconcilie pas -> RuntimeError, aucun octet ecrit.
    """
    raw = (
        '{"cells":[{"cell_type":"markdown","source":['
        '"\\u002d\\u002d\\u002d\\n"]}],"metadata":{},"nbformat":4,"nbformat_minor":5}'
    )
    p = tmp_path / "n.ipynb"
    p.write_bytes(raw.encode("utf-8"))
    before = p.read_bytes()

    import pytest
    with pytest.raises(RuntimeError):
        fix.process(p, apply=True)
    assert p.read_bytes() == before  # rien n'a ete ecrit
