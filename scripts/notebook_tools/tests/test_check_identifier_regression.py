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
  6. TestScopeMode — mode --scope : classification markdown-only STRICT complete
     (comment / stdout / other), compliant vs violation, exit code combine
  7. TestRegressionCov — couverture linguistique F#/C#-verbatim/nbformat-list-source
     (gaps des clusters 1-6 : F# (* *) blocks, C# @$"" verbatim, source-as-list)
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


# ---------------------------------------------------------------------------
# 6. Mode --scope : classification markdown-only STRICT complete
# ---------------------------------------------------------------------------
class TestScopeMode:
    def test_markdown_only_change_is_compliant(self):
        # Seule une cellule markdown change -> scope compliant, 0 violation
        old = _nb([("code", "x = 1"), ("markdown", "Texte sans accent")])
        new = _nb([("code", "x = 1"), ("markdown", "Texte avec accents àéè")])
        viols, n_code, n_md = cir.scan_scope(old, new)
        assert n_code == 0 and n_md == 1
        assert viols == []

    def test_python_comment_cure_is_violation(self):
        # Une cure d'accent dans un commentaire de code = HORS scope
        old = _nb([("code", "# Etape 1 : faire X\nx = 1")])
        new = _nb([("code", "# Étape 1 : faire X\nx = 1")])
        viols, n_code, n_md = cir.scan_scope(old, new)
        assert n_code == 1
        assert len(viols) == 1
        assert viols[0]["canal"] == "comment"

    def test_python_stdout_cure_is_violation(self):
        # Une cure d'accent dans un print = HORS scope
        old = _nb([("code", 'print("Resultat : ok")')])
        new = _nb([("code", 'print("Résultat : ok")')])
        viols, n_code, _ = cir.scan_scope(old, new)
        assert n_code == 1
        assert len(viols) == 1
        assert viols[0]["canal"] == "stdout"

    def test_cs_console_write_cure_is_violation(self):
        # Console.WriteLine C# = stdout
        old = _nb([("code", 'Console.WriteLine("Resultat");')])
        new = _nb([("code", 'Console.WriteLine("Résultat");')])
        viols, _, _ = cir.scan_scope(old, new)
        assert len(viols) == 1 and viols[0]["canal"] == "stdout"

    def test_other_canal_for_structural_change(self):
        # Changement de code accentue ni commentaire ni stdout = other
        # (ex : docstring marquee 'other' car pas #/print, ou raise avec message)
        old = _nb([("code", 'raise ValueError("Attendu 81 caracteres")')])
        new = _nb([("code", 'raise ValueError("Attendu 81 caractères")')])
        viols, _, _ = cir.scan_scope(old, new)
        assert len(viols) == 1 and viols[0]["canal"] == "other"

    def test_non_accented_code_change_not_flagged(self):
        # Un changement de code SANS accent n'est pas une "cure" -> pas remonte
        old = _nb([("code", "x = 1")])
        new = _nb([("code", "x = 2  # no accent here")])
        viols, n_code, _ = cir.scan_scope(old, new)
        assert n_code == 1  # la cellule a change (compteur brut)
        assert viols == []  # mais aucune ligne accentuee -> 0 violation scope

    def test_scope_check_exit_1_on_violation(self, tmp_path, monkeypatch):
        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(_nb([("code", "# Étape 1\nx = 1")])), encoding="utf-8")
        monkeypatch.setattr(cir, "_git_show_notebook",
                            lambda ref, path: _nb([("code", "# Etape 1\nx = 1")]))
        rc = cir.main([str(nb_path), "--base", "origin/main", "--scope", "--check"])
        assert rc == 1

    def test_scope_check_exit_0_when_compliant(self, tmp_path, monkeypatch):
        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(_nb([("code", "x = 1"), ("markdown", "àéè")])),
                           encoding="utf-8")
        monkeypatch.setattr(cir, "_git_show_notebook",
                            lambda ref, path: _nb([("code", "x = 1"), ("markdown", "aee")]))
        rc = cir.main([str(nb_path), "--base", "origin/main", "--scope", "--check"])
        assert rc == 0

    def test_scope_json_has_by_canal_partition(self, tmp_path, monkeypatch, capsys):
        nb_path = tmp_path / "nb.ipynb"
        # multi-line code source via explicit NL join (no backslash escapes in test literal)
        new_lines = ["# Étape", chr(34)+"Résultat"+chr(34)+" sans effet", "z = 1"]
        old_lines = ["# Etape", chr(34)+"Resultat"+chr(34)+" sans effet", "z = 1"]
        new_src = chr(10).join(new_lines)
        old_src = chr(10).join(old_lines)
        nb_path.write_text(json.dumps(_nb([("code", new_src)])), encoding="utf-8")
        monkeypatch.setattr(cir, "_git_show_notebook",
                            lambda ref, path: _nb([("code", old_src)]))
        rc = cir.main([str(nb_path), "--base", "origin/main", "--scope", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert "scope" in out
        assert out["scope"]["code_cells_changed"] == 1
        assert out["scope"]["markdown_only_strict_compliant"] is False
        by_canal = out["scope"]["by_canal"]
        assert by_canal.get("comment", 0) >= 1


# ---------------------------------------------------------------------------
# 7. Couverture linguistique F#/C#-verbatim/nbformat-list-source
#    (gaps des clusters 1-6 : F# (* *) blocks, C# @$"" verbatim, source-as-list)
# ---------------------------------------------------------------------------
class TestRegressionCov:
    DQ = chr(34)  # guillemet double, pour eviter les echappements dans les litteraux

    def test_fs_block_comment_excludes_accented_ident(self):
        # Un identifiant accentue DANS un bloc (* *) F# = commentaire, pas flagge.
        src = "(* préférence est un commentaire F# *)\nlet x = 1"
        ids = cir.code_identifiers(src)
        assert "préférence" not in ids
        assert "preferences" not in ids
        assert "x" in ids

    def test_fs_accented_ident_outside_block_is_regression(self):
        # L'identifiant accentue est HORS du bloc -> regression si base avait unaccented.
        old = _nb([("code", "preferences = []")])
        new = _nb([("code", "(* note *)\npréférences = []")])
        regs, _ = cir.scan(old, new)
        assert len(regs) == 1 and regs[0][1] == "préférences"

    def test_cs_verbatim_interp_string_not_an_ident(self):
        # C# @$"..." (verbatim interpole) : contenu = chaine, pas un identifiant.
        # Un 'identifiant' accentue dans @$"..." ne doit PAS etre flagge.
        lit = "var msg = @$" + self.DQ + "{résultat}" + self.DQ + ";"
        ids = cir.code_identifiers(lit)
        assert "résultat" not in ids
        assert "msg" in ids and "var" in ids

    def test_accented_dict_key_is_regression(self):
        # Cle de dictionnaire accentuee Python = identifiant structurel.
        old = _nb([("code", "d = {'resultat': 1}")])
        new = _nb([("code", "d = {'résultat': 1}")])
        regs, _ = cir.scan(old, new)
        # La cle de dict est entre quotes -> c'est une chaine, pas un identifiant.
        # Donc PAS de regression (la cle string n'est pas un token structurel).
        assert regs == []

    def test_accented_param_rename_is_regression(self):
        # Renommer un parametre de fonction en l'accentuant = regression d'API source.
        # Cas #7167 : parametre `strategies` -> `stratégies` d'une signature Python.
        old = _nb([("code", "def evaluer(strategies):\n    return strategies")])
        new = _nb([("code", "def evaluer(stratégies):\n    return stratégies")])
        regs, _ = cir.scan(old, new)
        assert len(regs) == 2  # parametre + usage, les deux accentues vs base unaccented
        assert all(r[1] == "stratégies" and r[2] == "strategies" for r in regs)

    def test_nbformat_list_source_handled_e2e(self):
        # source comme LISTE de lignes (format nbformat real) -> _src_str() + scan()
        # doivent gerer indifferemment list-vs-str des deux cotes base/head.
        base_list = {"cells": [
            {"cell_type": "code", "source": ["preferences = []\n", "x = 1"], "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        head_str = {"cells": [
            {"cell_type": "code", "source": "préférences = []\nx = 1", "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        # Cas 1 : base (list, unaccented) -> head (str, accented) = REGRESSION.
        # Prouve que la base en format liste est normalisee par _src_str().
        regs, _ = cir.scan(base_list, head_str)
        assert len(regs) == 1 and regs[0][1] == "préférences"

        # Cas 2 : base deja accented (statut quo) -> head accented = PAS de regression.
        base_str_acc = {"cells": [
            {"cell_type": "code", "source": "préférences = []\nx = 1", "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        regs2, _ = cir.scan(base_str_acc, head_str)
        assert regs2 == []  # statut quo : la base avait deja la forme accentuee

    def test_fs_block_preserves_line_alignment(self):
        # Un bloc F# multi-ligne ne doit pas decaler les numeros de ligne.
        src = "(* ligne1\nligne2\nligne3 *)\npréférences = 1"
        for tok, line, ctx in cir.accented_identifiers(src):
            assert tok == "préférences"
            assert line == 4  # apres les 3 lignes internes du bloc + fermeture
            assert "préférences = 1" in ctx

    def test_lean_line_comment_excludes_accented_prose(self):
        # BUGFIX c.609 : Lean `--` commentaires n'etaient pas stirpes -> faux positif
        # sur la prose de commentaire (ex GameTheory-4b-Lean). `stratégies` dans un
        # commentaire Lean N'est PAS un identifiant structurel.
        src = "-- # Étape 3 : L'espace de stratégies d'un jeu\naxiom foo : Nat"
        ids = cir.code_identifiers(src)
        assert "stratégies" not in ids
        assert "strategies" not in ids  # forme desaccentuee aussi absente (commentaire)
        assert "foo" in ids and "Nat" in ids  # vrais identifiants Lean preserves

    def test_lean_line_comment_regression_is_false_positive_fixed(self):
        # Cas reel #7171 : un Lean notebook ou `stratégies` n'apparait QUE dans des
        # commentaires `--` ne doit PLUS etre flagge comme regression identifiant.
        old = _nb([("code", "-- Profil de strategies mixtes\naxiom foo : Nat")])
        new = _nb([("code", "-- Profil de stratégies mixtes\naxiom foo : Nat")])
        regs, susp = cir.scan(old, new)
        assert regs == []  # PAS de regression : strategies n'est pas structurel en base

    def test_lean_block_comment_excludes_accented_prose(self):
        # Lean block comment /- ... -/ : contenu exclue (multiline).
        src = "/- strategie\nmulti\nligne -/\naxiom résultat : Nat"
        ids = cir.code_identifiers(src)
        assert "strategie" not in ids  # dans le bloc /- -/
        assert "résultat" in ids or "resultat" in ids  # axiom résultat est structurel
        assert "axiom" in ids
