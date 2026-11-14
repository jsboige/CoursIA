#!/usr/bin/env python3
"""Tests de l'organe de recensement de l'écosystème Rust (#26513, Pli 1).

Un test par **fonction pure**, sur les cas limites que la doc de l'organe
revendique (docstrings de ``rust_ecosystem_census.py`` +
``docs/reference/rust-ecosystem-map.md``), plus un **contrôle par mutation**
qui prouve que la suite est *sensible* : une mutation plausible d'une logique
discriminante fait diverger la valeur rendue de l'attendu.

Les fonctions qui appellent ``git ls-files`` (``iter_notebooks``,
``local_module_names``, ``census``) ne sont pas testées ici : elles dépendent
de l'état de la machine. Le repli ``try/except`` ajouté à ``local_module_names``
garantit qu'un échec de ``git`` y rend l'ensemble vide (jamais une exception) —
même sémantique que le repli existant de ``iter_notebooks``.
"""

from collections import Counter

import rust_ecosystem_census as rec


# --- series_of -------------------------------------------------------------

def test_series_of_first_level_only():
    """``series_of`` rend le répertoire de PREMIER niveau, pas le chemin complet."""
    assert rec.series_of("MyIA.AI.Notebooks/Search/foo.ipynb") == "Search"
    # le préfixe est retiré, et SEUL le premier niveau reste (pas GenAI/Image)
    assert rec.series_of("MyIA.AI.Notebooks/GenAI/Image/foo.ipynb") == "GenAI"


def test_series_of_without_prefix():
    """Sans le préfixe, la première composante l'emporte telle quelle
    (docstring : « sinon TOUTES les séries s'appelleraient MyIA.AI.Notebooks »)."""
    assert rec.series_of("Search/foo.ipynb") == "Search"
    assert rec.series_of("foo.ipynb") == "foo.ipynb"


# --- python_imports --------------------------------------------------------

def test_python_imports_basic_and_as():
    assert rec.python_imports("import numpy") == {"numpy"}
    assert rec.python_imports("import numpy as np") == {"numpy"}


def test_python_imports_comma_list():
    assert rec.python_imports("import a, b, c") == {"a", "b", "c"}


def test_python_imports_dotted_reduces_to_toplevel():
    """``import numpy.linalg`` compte le niveau supérieur ``numpy``."""
    assert rec.python_imports("import numpy.linalg") == {"numpy"}


def test_python_imports_semicolon():
    """docstring : ``import traceback; print(x)`` ne doit pas rendre ``traceback;``."""
    assert rec.python_imports("import traceback; print(x)") == {"traceback"}


def test_python_imports_from():
    """``from X.Y import Z`` compte le module de niveau supérieur ``X``."""
    assert rec.python_imports("from os.path import join") == {"os"}
    assert rec.python_imports("from collections import Counter") == {"collections"}


def test_python_imports_skips_comments():
    assert rec.python_imports("# import numpy") == set()
    assert rec.python_imports("") == set()


# --- nuget_packages --------------------------------------------------------

def test_nuget_packages_basic():
    assert rec.nuget_packages('#r "nuget: Microsoft.SemanticKernel"') == {
        "Microsoft.SemanticKernel"
    }


def test_nuget_packages_strips_version():
    """la classe de caractères s'arrête à l'espace : la version ne compte pas."""
    assert rec.nuget_packages("#r 'nuget: Some.Pkg 1.2.3'") == {"Some.Pkg"}


def test_nuget_packages_none_and_case_insensitive():
    assert rec.nuget_packages("print('hi')") == set()
    assert rec.nuget_packages("#r 'NUGET: Foo'") == {"Foo"}


# --- cell_sources ----------------------------------------------------------

def test_cell_sources_code_only():
    """seules les cellules ``code`` sont rendues ; ``source`` liste => jointe."""
    doc = {"cells": [
        {"cell_type": "code", "source": ["import x\n", "import y"]},
        {"cell_type": "markdown", "source": ["# titre"]},
    ]}
    assert list(rec.cell_sources(doc)) == ["import x\nimport y"]


def test_cell_sources_missing_source_and_no_cells():
    """cellule code sans ``source`` => chaîne vide ; doc sans ``cells`` => rien."""
    assert list(rec.cell_sources({"cells": [{"cell_type": "code"}]})) == [""]
    assert list(rec.cell_sources({})) == []


# --- _md_table -------------------------------------------------------------

def test_md_table_ordering_and_limit():
    t = rec._md_table(Counter({"a": 2, "b": 3}))
    assert t == ["| nom | carnets |", "|---|---:|", "| `b` | 3 |", "| `a` | 2 |"]
    # ``limit`` borne la table au top-N
    assert rec._md_table(Counter({"a": 2, "b": 3}), limit=1) == [
        "| nom | carnets |", "|---|---:|", "| `b` | 3 |",
    ]


def test_md_table_empty():
    assert rec._md_table(Counter()) == ["| nom | carnets |", "|---|---:|"]


# --- contrôle par mutation -------------------------------------------------

def test_mutation_control(monkeypatch):
    """Contrôle par mutation — prouve que la suite est SENSIBLE à la logique
    discriminante de ``python_imports``.

    On mute la fonction (on retire la réduction ``.split(".")[0]`` au module de
    niveau supérieur) et on vérifie que la valeur rendue NE SATISFAIT PLUS le
    test discriminant ci-dessus (``test_python_imports_dotted_reduces_to_toplevel``,
    qui attend ``{"numpy"}``). Si la mutation n'avait aucun effet observable, la
    valeur mutée coïnciderait avec l'attendu : ce contrôle attraperait une suite
    aveugle.
    """
    def _mutated(source: str) -> set:
        found: set = set()
        for line in source.splitlines():
            s = line.strip()
            if s.startswith("#"):
                continue
            m = rec._IMPORT_RE.match(s)
            if m:
                for name in m.group(1).split(","):
                    name = name.split(" as ")[0].split(";")[0].strip()
                    if name:
                        found.add(name)  # mutation : pas de .split(".")[0]
        return found

    monkeypatch.setattr(rec, "python_imports", _mutated)
    assert rec.python_imports("import numpy.linalg") != {"numpy"}
