"""Tests for scripts/notebook_tools/check_identifier_regression.py — identifier-regression guard.

Why this test file exists
--------------------------
`check_identifier_regression.py` (registre #2876) garde la classe de defect ou un
agent cure des accents mais depasse le scope markdown-only STRICT et accentue un
**identifiant de code** (variable, parametre, propriete, classe). Trois instances
reelles : #7094 (`Difference` -> `Différence` C# LINQ), #7143 (`for iteration` ->
`for itération` Python), #7154 (`préférences`/`itération`/`résultat`, 10 occ, 5
cellules). La verification NFD-accent-stripped qu'utilisent les agents est aveugle
par construction a ce defect (stripper les accents de `préférences` rend
`preferences`), d'ou la need d'un garde dedie.

Cinq clusters :
  1. TestStripPreserveLines — newline preservation (alignement des numeros de ligne)
  2. TestCodeIdentifiers — tokenisation hors chaines/commentaires (Python + C#)
  3. TestScan — regression vs suspect, multi-cellule, forme desaccentuee en base
  4. TestMainExitCodes — exit 0/1/2 contract (--check, ref absente)
  5. TestEdgeCases — accents legitimes pre-existants (faux positif evite)
"""
import json
import sys
from pathlib import Path

import pytest

# import du module sous test (depuis le dossier parent)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_identifier_regression as cir  # noqa: E402


def _nb(cells):
    """Notebook synthetique minimal avec une liste de cellules (type, source)."""
    return {"cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# ---------------------------------------------------------------------------
# 1. Strip + preservation des newlines
# ---------------------------------------------------------------------------
class TestStripPreserveLines:
    def test_line_comment_stripped_newline_preserved(self):
        src = "a = 1  # comment\nb = 2"
        assert cir._strip_preserve_lines(src).count("\n") == 1

    def test_triple_quoted_block_preserves_internal_newlines(self):
        src = 'x = """ligne1\nligne2\nligne3"""\ny = 1'
        stripped = cir._strip_preserve_lines(src)
        # source original = 3 newlines (2 internes au bloc + 1 apres """).
        # La preservation remplace le bloc par ses 2 NL internes + le NL de fin
        # reste -> 3 au total (pas de collapse vers 1).
        assert stripped.count("\n") == 3

    def test_cs_block_comment_preserves_newlines(self):
        src = "/* a\nb\nc */\nvar = 1"
        assert cir._strip_preserve_lines(src).count("\n") == 3

    def test_string_content_destroyed_but_lines_kept(self):
        src = 'x = "préférence"\ny = 1'
        stripped = cir._strip_preserve_lines(src)
        assert "préférence" not in stripped
        assert stripped.count("\n") == 1


# ---------------------------------------------------------------------------
# 2. Tokenisation des identifiants (hors chaines/commentaires)
# ---------------------------------------------------------------------------
class TestCodeIdentifiers:
    def test_python_excludes_line_comment(self):
        ids = cir.code_identifiers("x = 1  # préférence est un commentaire")
        assert "préférence" not in ids
        assert "x" in ids

    def test_python_excludes_string_literal(self):
        ids = cir.code_identifiers('msg = "résultat dans une chaine"')
        assert "résultat" not in ids
        assert "msg" in ids

    def test_python_excludes_triple_quoted(self):
        ids = cir.code_identifiers('doc = """itération\\nmulti"""')
        assert "itération" not in ids

    def test_cs_excludes_block_comment(self):
        ids = cir.code_identifiers("/* Différence */\nvar x = 1;")
        assert "Différence" not in ids

    def test_deaccent_form_returned(self):
        ids = cir.code_identifiers("préférences = 1")
        assert "preferences" in ids  # forme desaccentuee


# ---------------------------------------------------------------------------
# 3. Scan : regression vs suspect
# ---------------------------------------------------------------------------
class TestScan:
    def test_python_var_accented_in_head_is_regression(self):
        # Cas #7143 / #7154 : la head accentue un identifiant present (desaccentue) en base
        old = _nb([("code", "preferences = []\nfor p in preferences:\n    pass")])
        new = _nb([("code", "préférences = []\nfor p in préférences:\n    pass")])
        regs, susp = cir.scan(old, new)
        assert len(regs) == 2
        assert all(r[1] == "préférences" and r[2] == "preferences" for r in regs)

    def test_cs_property_accented_in_head_is_regression(self):
        # Cas #7094 : propriete anonyme LINQ C#
        old = _nb([("code", 'var q = xs.Select(x => new { Difference = x.a - x.b });')])
        new = _nb([("code", 'var q = xs.Select(x => new { Différence = x.a - x.b });')])
        regs, _ = cir.scan(old, new)
        assert len(regs) == 1
        assert regs[0][1] == "Différence" and regs[0][2] == "Difference"

    def test_loop_var_accented_is_regression(self):
        old = _nb([("code", "for iteration in range(10):\n    pass")])
        new = _nb([("code", "for itération in range(10):\n    pass")])
        regs, _ = cir.scan(old, new)
        assert len(regs) == 1 and regs[0][1] == "itération"

    def test_markdown_only_change_is_clean(self):
        # Cas nominal #2876 : seule une cellule markdown change -> 0 regression
        old = _nb([("code", "x = 1"), ("markdown", "Texte sans accent")])
        new = _nb([("code", "x = 1"), ("markdown", "Texte avec accents àéè")])
        regs, susp = cir.scan(old, new)
        assert regs == [] and susp == []

    def test_preexisting_accented_ident_is_not_new_regression(self):
        # Si la base AVOIT DEJA l'identifiant accentue (statut quo), la head ne
        # fait pas de regression (ce n'est pas un delta introduit par la PR).
        old = _nb([("code", "préférences = []")])
        new = _nb([("code", "préférences = []\nprint(préférences)")])
        regs, susp = cir.scan(old, new)
        # l'identifiant accentue n'est pas nouveau vs base -> ni regression (forme
        # desaccentuee 'preferences' absente de base) ni... en fait suspect car
        # forme desaccentuee absente. On verifie juste qu'il n'y a pas de FAUX
        # positif de regression.
        assert regs == []

    def test_cross_cell_base_definition_detected(self):
        # L'identifiant est defini dans la cell 0 (base) et accentue dans la cell 1 (head)
        old = _nb([("code", "resultat = 42"), ("code", "print(resultat)")])
        new = _nb([("code", "resultat = 42"), ("code", "print(résultat)")])
        regs, _ = cir.scan(old, new)
        assert len(regs) == 1
        assert regs[0][1] == "résultat"


# ---------------------------------------------------------------------------
# 4. main() exit codes
# ---------------------------------------------------------------------------
class TestMainExitCodes:
    def test_check_exit_1_on_regression(self, tmp_path, monkeypatch):
        # base propre, head avec regression, sur disque
        nb_path = tmp_path / "nb.ipynb"
        regressed = _nb([("code", "préférences = []")])
        nb_path.write_text(json.dumps(regressed), encoding="utf-8")

        # mock _git_show_notebook : base renvoie l'unaccented, head = disque
        def fake_show(ref, path):
            if ref == "origin/main":
                return _nb([("code", "preferences = []")])
            return None
        monkeypatch.setattr(cir, "_git_show_notebook", fake_show)
        # head = None -> lit le disque (le notebook regressed)
        rc = cir.main([str(nb_path), "--base", "origin/main", "--check"])
        assert rc == 1

    def test_check_exit_0_when_clean(self, tmp_path, monkeypatch):
        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(_nb([("code", "x = 1")])), encoding="utf-8")
        monkeypatch.setattr(cir, "_git_show_notebook",
                            lambda ref, path: _nb([("code", "x = 1")]))
        rc = cir.main([str(nb_path), "--base", "origin/main", "--check"])
        assert rc == 0

    def test_exit_2_when_base_ref_missing(self, tmp_path, monkeypatch):
        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text("{}", encoding="utf-8")
        monkeypatch.setattr(cir, "_git_show_notebook", lambda ref, path: None)
        rc = cir.main([str(nb_path), "--base", "origin/ghost"])
        assert rc == 2
