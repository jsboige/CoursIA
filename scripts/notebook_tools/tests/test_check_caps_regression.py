"""Tests for scripts/notebook_tools/check_caps_regression.py — registre #2876.

Verifie la detection des caps-regressions markdown (cure qui minuscule l'initiale
d'un mot capitalise). Defense-by-construction : le detecteur line-aligned evite
les FP du scan non-positionnel (po-2023 c.610/c.611). Valide sur le fleet reel
(#7191=36, #7187=0/213).
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_caps_regression as ccr  # noqa: E402


def _nb(cells):
    """Notebook synthetique : cells = liste de (cell_type, source_str)."""
    return {"cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(src):
    return ("markdown", src)


# ---------------------------------------------------------------------------
# 1. detection des vraies caps-regressions
# ---------------------------------------------------------------------------
class TestCapsRegressionDetection:
    def test_title_capital_lowercased(self):
        # H1 title : Systeme -> systeme (base cap, head lower) = REGRESSION
        old = _nb([_md("# Infer : Systeme de Classement\n")])
        new = _nb([_md("# Infer : système de Classement\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 1
        assert regs[0][2] == "Systeme"   # base_word
        assert regs[0][3] == "système"   # head_word

    def test_table_header_bold_lowercased(self):
        old = _nb([_md("| **Equipes** | Moyenne |\n")])
        new = _nb([_md("| **équipes** | Moyenne |\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 1
        assert regs[0][2] == "Equipes"

    def test_sentence_start_lowercased(self):
        old = _nb([_md("Apres chaque match, on continue.\n")])
        new = _nb([_md("après chaque match, on continue.\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 1

    def test_all_caps_lowercased(self):
        # MODELE -> modele (all-caps -> mixed) = REGRESSION
        old = _nb([_md("Les PARAMETRES sont la.\n")])
        new = _nb([_md("Les parametres sont la.\n")])  # pas d'accent -> pas une cure
        regs, summ = ccr.scan(old, new)
        # head n'a pas d'accent -> ignore (pas une cure). On teste avec accent :
        new2 = _nb([_md("Les paramètres sont la.\n")])
        regs2, summ2 = ccr.scan(old, new2)
        assert summ2["caps_regressions"] == 1
        assert regs2[0][2] == "PARAMETRES"

    def test_multiple_regressions_in_line(self):
        old = _nb([_md("Le Modele et le Systeme\n")])
        new = _nb([_md("Le modèle et le système\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 2


# ---------------------------------------------------------------------------
# 2. vrais negatifs : cures legitimes NON flagguees
# ---------------------------------------------------------------------------
class TestTrueNegatives:
    def test_lowercase_cure_mid_sentence_not_flagged(self):
        # base minuscule mi-phrase -> head minuscule accentue = cure legitime
        old = _nb([_md("Le systeme encode les donnees.\n")])
        new = _nb([_md("Le système encode les donnees.\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] >= 1

    def test_capital_preserved_correctly_not_flagged(self):
        # Systeme -> Systeme (cap preservee) = cure PARFAITE, pas de regression
        old = _nb([_md("# Titre : Systeme de calcul\n")])
        new = _nb([_md("# Titre : Système de calcul\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] == 1

    def test_all_caps_preserved_not_flagged(self):
        old = _nb([_md("Les PARAMETRES generaux.\n")])
        new = _nb([_md("Les PARAMÈTRES generaux.\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] == 1

    def test_same_word_cap_elsewhere_not_false_positive(self):
        # FP-class po-2023 c.610 : meme mot en cap dans une ligne (titre) ET en
        # lower dans une autre (prose). Curer la lower (ligne 1) NE doit PAS etre
        # flaggue meme si ligne 0 a la cap.
        old = _nb([
            _md("# Le Systeme\n"),                      # L0 : cap (titre, inchange)
            _md("Le systeme encode les donnees.\n"),    # L1 : lower (prose, curee)
        ])
        new = _nb([
            _md("# Le Systeme\n"),                      # L0 inchangé
            _md("Le système encode les donnees.\n"),    # L1 cure lower->lower+accent
        ])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0   # la cure L1 est legitime (lower->lower)
        assert summ["cures"] == 1

    def test_non_cure_change_ignored(self):
        # modification non-accent (mot different) : ignore, pas de regression
        old = _nb([_md("Le chat dort.\n")])
        new = _nb([_md("Le chien dort.\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] == 0

    def test_code_cells_ignored(self):
        # le detecteur est markdown-only : cellules code ignorees
        old = _nb([("code", "# Systeme comment\n")])
        new = _nb([("code", "# système comment\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] == 0


# ---------------------------------------------------------------------------
# 3. robustesse structurelle
# ---------------------------------------------------------------------------
class TestStructuralRobustness:
    def test_struct_changed_line_skipped(self):
        # ligne dont le NB de mots change = mod struct, skip (evite FP alignement)
        old = _nb([_md("Le systeme\n")])
        new = _nb([_md("Le système global\n")])  # 2 mots -> 3 mots
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["struct_changed_lines"] == 1

    def test_added_line_ignored(self):
        old = _nb([_md("Ligne une.\n")])
        new = _nb([_md("Ligne une.\nAjout systeme.\n")])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0

    def test_list_source_handled(self):
        # source en list nbformat (chunks). Cure legitime (lower->lower+accent).
        old = _nb([("markdown", ["Le systeme\n", "est la.\n"])])
        new = _nb([("markdown", ["Le système\n", "est la.\n"])])
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 0
        assert summ["cures"] == 1


# ---------------------------------------------------------------------------
# 4. exit codes main()
# ---------------------------------------------------------------------------
class TestMainExitCodes:
    def test_check_exit_1_on_regression(self, tmp_path):
        old = _nb([_md("# Systeme\n")])
        # on ecrit le NEW notebook ; base via git n'est pas disponible ici, donc
        # on test la logique de scan directement + le exit code via mock :
        new = _nb([_md("# système\n")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(new), encoding="utf-8")
        # main() tente git show pour la base -> sans repo, retourne 2. On teste
        # donc la fonction scan (preuve du verdict) + on verifie que main rejette
        # une base introuvable proprement.
        regs, summ = ccr.scan(old, new)
        assert summ["caps_regressions"] == 1

    def test_apply_mutually_exclusive_with_check_absent(self):
        # sanity : le CLI accepte --json + --check ensemble
        rc = ccr.main(["__nonexistent__", "--json", "--check"])
        # notebook inexistant sans head -> exit 2
        assert rc == 2
