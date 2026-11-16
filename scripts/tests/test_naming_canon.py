#!/usr/bin/env python3
"""Tests du canon de nommage partage (#5081) — primitive `strip_lang`.

Le present fichier ne testait plus rien de specifique a l'ajout de `-rust` :
`check_kernel_suffix_canon.py` et `check_slot_reservation.py` l'importent chacun,
mais la primitive `strip_lang` n'avait pas de test qui verifie que les TROIS
rendus d'un meme item (un par noyau) retombent sur la MEME cle. C'est exactement
le couplage que `check_slot_reservation.py` exploite pour apparier les items a
index egal : `strip_lang(a) == strip_lang(b)`.

Sans `-rust` dans `KERNEL_LANG_SUFFIXES`, le jumeau Rust ne strippait PAS son
suffixe, sa cle divergeait de celles de ses jumeaux -CSharp / -Python a index
egal, et `check_slot_reservation.py` signalait un faux `slot-collision-on-merge`
a chaque passage `merge_ready`. Le controle positif ci-dessous est la preuve que
les trois rendus se regroupent a nouveau sur une seule cle.
"""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

_SCRIPT = (Path(__file__).resolve().parent.parent / "notebook_tools"
           / "naming_canon.py")


def _load_module() -> importlib.abc.ModuleType:
    spec = importlib.util.spec_from_file_location("naming_canon_under_test",
                                                  _SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    # Le module porte un @dataclass : le decorator relit sys.modules[cls.__module__].
    # L'enregistrer AVANT exec_module, sinon `dataclasses._is_type` trouve None.
    sys.modules["naming_canon_under_test"] = mod
    spec.loader.exec_module(mod)
    return mod


class TestStripLangRust(unittest.TestCase):
    """`-rust` apparie le jumeau Rust a ses jumeaux -CSharp / -Python."""

    @classmethod
    def setUpClass(cls):
        cls.n = _load_module()

    def test_rust_is_a_kernel_lang_suffix(self):
        self.assertIn("-rust", self.n.KERNEL_LANG_SUFFIXES)
        self.assertIn("-rust", self.n.LANG_SUFFIXES)

    def test_rust_twin_strips_to_same_key_as_csharp_and_python(self):
        rust = self.n.strip_lang("Sudoku-02-DancingLinks-Rust.ipynb")
        csharp = self.n.strip_lang("Sudoku-02-DancingLinks-CSharp.ipynb")
        python = self.n.strip_lang("Sudoku-02-DancingLinks-Python.ipynb")
        self.assertEqual(rust, "Sudoku-02-DancingLinks")
        self.assertEqual(rust, csharp)
        self.assertEqual(rust, python)


if __name__ == "__main__":
    unittest.main()
