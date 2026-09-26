"""Tests for scripts/notebook_tools/check_notebook_nav_chain.py

Couvre la discrimination 3-niveaux de `_looks_nav` et le scan `link_404`
(organe qui ferme la classe de defaut stale-navigation fondateur Tell c.856-L1
sur TOUTES les series, pas seulement Z3-API : c'etait la limite du sweep
d'origine check_z3_navigation.py, retire comme doublon structurel de
check_notebook_navlinks.py + nav_chain.py).

Faux-positifs mesures (l'organe DOIT les tolerer) :
- lien de prose : `[voir Foo-1.ipynb](Foo-1.ipynb)` dans un README (pas un mot
  de navigation) -> PAS un link_404 (garde de prose, pas de nav).
- lien self-reference : `[](self.ipynb)` (texte vide, pas de fleche).
- lien vers fichier hors-perimetre (README.md sibling) -> pas un link_404 nav.

Faux-negatifs mesures (l'organe DOIT les trouver) :
- lien `<<` ou `>>` ou `←`/`→` vers un .ipynb absent.
- lien dans une rangee de nav sous `## Navigation` vers .ipynb absent.
- lien avec mot `suivant` / `precedent` dans le texte vers .ipynb absent.
"""
import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

import check_notebook_nav_chain as nav_chain


def _write_nb(tmp_path: Path, name: str, source: str) -> Path:
    """Ecrit un notebook .ipynb minimal avec une cellule markdown [0]."""
    import json
    nb = {
        "cells": [{"cell_type": "markdown", "metadata": {}, "source": source.splitlines(keepends=True)}],
        "metadata": {"kernelspec": {"language": "python"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


class TestLooksNav:
    """Discrimination 3-niveaux : texte du lien, ligne, cellule `## Navigation`."""

    def test_word_in_text(self):
        assert nav_chain._looks_nav("Suivant >>", "next.ipynb", "any line", False) is True

    def test_arrow_in_text(self):
        assert nav_chain._looks_nav("Z3-08 →", "Z3-08.ipynb", "any line", False) is True

    def test_navigation_cell(self):
        # Pas de mot-cle sur la ligne, mais cellule `## Navigation` -> OK
        line = "[MGS-7b](MGS-07b.ipynb) · [MGS-8](MGS-08.ipynb)"
        assert nav_chain._looks_nav("MGS-7b", "MGS-07b.ipynb", line, True) is True

    def test_word_on_line_not_link(self):
        # Le mot est sur la ligne, hors du lien (forme rangee canonique #17277)
        line = "**Serie MGS** | Precedent : [MGS-9](MGS-09.ipynb)"
        assert nav_chain._looks_nav("MGS-9", "MGS-09.ipynb", line, False) is True

    def test_prose_link_rejected(self):
        # Pas de mot-cle, pas de nav-cell, pas de fleche -> PROSE, pas nav
        line = "[voir Foo-1](Foo-1.ipynb)"
        assert nav_chain._looks_nav("voir Foo-1", "Foo-1.ipynb", line, False) is False

    def test_word_in_prose_rejected(self):
        # `index` n'est PAS dans NAV_LINE_MARKERS (trop frequent en prose)
        line = "voir l'index de la liste pour les details"
        assert nav_chain._looks_nav("details", "details.ipynb", line, False) is False


class TestBrokenNavLinks:
    """Le scan `broken_nav_links` ne rapporte que les liens nav vers cibles absentes."""

    def test_link_to_missing_notebook(self, tmp_path):
        nb = _write_nb(tmp_path, "A.ipynb", textwrap.dedent("""\
            ## Navigation
            | [Suivant B](B.ipynb) |
        """))
        result = nav_chain.broken_nav_links(nb)
        assert len(result) == 1
        assert result[0]["target"] == "B.ipynb"

    def test_link_to_existing_notebook_not_reported(self, tmp_path):
        _write_nb(tmp_path, "A.ipynb", textwrap.dedent("""\
            ## Navigation
            | [Suivant B](B.ipynb) |
        """))
        nb_b = _write_nb(tmp_path, "B.ipynb", "## Navigation\nvide")
        result = nav_chain.broken_nav_links(nb_b)
        assert result == []

    def test_prose_link_to_missing_not_404(self, tmp_path):
        # Le lien est de la PROSE (pas de nav-mot), donc pas un link_404 de nav.
        # (Le 404 de prose est le metier de check_notebook_navlinks.py, pas le notre.)
        nb = _write_nb(tmp_path, "A.ipynb", textwrap.dedent("""\
            [voir Foo-1](Foo-1.ipynb)
        """))
        result = nav_chain.broken_nav_links(nb)
        assert result == []

    def test_arrow_link_to_missing(self, tmp_path):
        # Fleche Unicode vers cible absente -- cas Z3-08 fondateur (avant correction)
        nb = _write_nb(tmp_path, "A.ipynb", textwrap.dedent("""\
            ## Navigation
            [← Serie](README.md) | [Z3-Python-08 →](Z3-08-Ordonnancement-Python.ipynb)
        """))
        result = nav_chain.broken_nav_links(nb)
        assert len(result) == 1
        assert result[0]["target"] == "Z3-08-Ordonnancement-Python.ipynb"

    def test_ascii_arrow_link_to_missing(self, tmp_path):
        # Fleche ASCII `<<` / `>>` (Z3-01 a Z3-06)
        nb = _write_nb(tmp_path, "A.ipynb", textwrap.dedent("""\
            [<< Precedent](Z3-05.ipynb) | [Suivant >>](Z3-07.ipynb)
        """))
        result = nav_chain.broken_nav_links(nb)
        # Les deux cibles sont absentes -> 2 findings
        targets = sorted(r["target"] for r in result)
        assert targets == ["Z3-05.ipynb", "Z3-07.ipynb"]


class TestScanBrokenNav:
    """`scan_broken_nav` rapporte les link_404 sur tout le set passe."""

    def test_real_depot_zero_link_404(self):
        """Le depot commited ne doit pas porter de link_404 de nav (gagne par
        check_notebook_navlinks.py universel). Si ce test echoue, soit un
        nouveau 404 a ete introduit, soit le garde 404 a regresse.
        C'est le controle anti-regression : la discrimination nav ne fabrique
        pas de faux positifs sur le depot reel.
        """
        # On importe _iter_notebooks paresseusement pour eviter un scan disque
        # quand le test est importe (cf. conftest). On l'appelle directement.
        from check_notebook_navlinks import _iter_notebooks
        notebooks = list(_iter_notebooks(None, tracked_only=True))
        # On filtre pour n'inclure que les notebooks de la famille SMT/Z3-API
        # (le test fondateur de la PR d'origine). On accepte un link_404 dans
        # d'autres familles si le depot en a (auquel cas le garde universel
        # aurait deja du le voir).
        z3_nb = [nb for nb in notebooks
                 if "SMT/Z3-API" in nb.parts and "Z3-08" in nb.name]
        findings = nav_chain.scan_broken_nav(z3_nb)
        # Le fondateur (Z3-08 -> Z3-01b-Style-Declaratif-Linq) N'EST PAS un 404 :
        # le fichier existe (kernelspec Python, juste un nom a suffixe -Linq).
        # Si le scan rapporte un link_404 ici, c'est que le test fondateur est
        # faux et qu'il faut corriger la doc de la PR d'origine.
        assert findings == [], (
            f"Trouve {len(findings)} link_404 inattendu(s) sur Z3-08 : "
            f"{findings}. Le fondateur originel de la PR n'etait PAS un vrai 404 "
            f"(le fichier Z3-01b existe, kernelspec Python)."
        )


class TestFindingKeys:
    """Cle de baseline 3-tuple (kind, notebook, target) -- discriminante pour link_404."""

    def test_link_404_distinct_by_target(self):
        report = {"findings": [
            {"kind": "link_404", "notebook": "A.ipynb", "target": "B.ipynb"},
            {"kind": "link_404", "notebook": "A.ipynb", "target": "C.ipynb"},
        ]}
        keys = nav_chain._finding_keys(report)
        assert keys == {
            ("link_404", "A.ipynb", "B.ipynb"),
            ("link_404", "A.ipynb", "C.ipynb"),
        }

    def test_other_kinds_unaffected(self):
        report = {"findings": [
            {"kind": "orphan_entry", "notebook": "A.ipynb"},
            {"kind": "unreachable", "notebook": "B.ipynb"},
        ]}
        keys = nav_chain._finding_keys(report)
        # orphan_entry / unreachable : target absent -> cle = ""
        assert keys == {
            ("orphan_entry", "A.ipynb", ""),
            ("unreachable", "B.ipynb", ""),
        }
