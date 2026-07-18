"""Tests for scripts/notebook_tools/restore_accents_canonical.py — cure canonique #2876.

Verifie les 4 bright-lines defense-by-construction du registre #2876 (markdown-only
STRICT, adjudication ai-01 17/07 + raffinement link-target 18/07) :
  1. markdown-cell-source ONLY (code cells intouches)
  2. skip link targets ]( ... ) (defect #7135/#7145 : lien casse)
  3. skip code (consequence de 1)
  4. skip outputs / execution_count (seule la cle source est re-ecrite)
+ preservation casse + dictionnaire conservateur (non-ambigu) + structure nbformat.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import restore_accents_canonical as rac  # noqa: E402


def _nb(cells):
    """Notebook synthetique : cells = liste de (cell_type, source_str)."""
    return {"cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# ---------------------------------------------------------------------------
# 1. markdown-cell-source ONLY : les cellules code sont intouches
# ---------------------------------------------------------------------------
class TestMarkdownOnly:
    def test_code_cell_never_touched(self, tmp_path):
        # un identifiant accentuable 'parametre' dans une cellule CODE ne doit
        # JAMAIS etre cure (defect #7094/#7143/#7154 : over-reach code).
        nb = _nb([("code", "parametre = 1\nprint(parametre)"),
                  ("markdown", "Le parametre est important.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        # la cellule code reste byte-identique
        assert cured["cells"][0]["source"] == "parametre = 1\nprint(parametre)"
        # la cellule markdown est curee
        assert "paramètre" in cured["cells"][1]["source"]
        assert res["cures"] == 1

    def test_outputs_and_execution_count_preserved(self, tmp_path):
        # seule la cle 'source' d'une cellule markdown est re-ecrite ; une cellule
        # code avoisinante garde ses outputs + execution_count intacts (defect
        # #7105/#7124/#7132 : re-exec / regen outputs).
        nb = {"cells": [
            {"cell_type": "code", "source": "x = 1", "outputs": [{"data": "KEEP"}],
             "execution_count": 42, "metadata": {}},
            {"cell_type": "markdown", "source": "Le resultat est pret."},
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert cured["cells"][0]["outputs"] == [{"data": "KEEP"}]
        assert cured["cells"][0]["execution_count"] == 42
        assert cured["cells"][0]["source"] == "x = 1"  # code intact


# ---------------------------------------------------------------------------
# 2. skip link targets : defect #7135/#7145 (lien casse)
# ---------------------------------------------------------------------------
class TestLinkTargetProtection:
    def test_link_target_not_accented(self):
        # la cible du lien doit matcher le fichier reel sur disque (sans accent).
        line = "Voir [le modele de selection](Infer-10-Model-Selection.ipynb)."
        cured, n = rac._cure_line(line)
        assert "](Infer-10-Model-Selection.ipynb)" in cured  # cible intacte
        assert "sélection.ipynb" not in cured  # cible NON accentuee
        assert "modèle" in cured  # prose accented

    def test_multiple_links_protected(self):
        line = ("| [Model-Selection](Model-Selection.ipynb) | "
                "[Modeles-Hierarchiques](Modeles-Hierarchiques.ipynb) |")
        cured, n = rac._cure_line(line)
        assert "](Model-Selection.ipynb)" in cured
        assert "](Modeles-Hierarchiques.ipynb)" in cured
        assert "sélection.ipynb" not in cured and "modèles-Hierarchiques.ipynb" not in cured

    def test_image_src_protected(self):
        # ![alt](src.png) : la source image aussi
        line = "![schema du modele de parametres](assets/parametres.png)"
        cured, n = rac._cure_line(line)
        assert "](assets/parametres.png)" in cured  # src intact
        assert "parametres.png" in cured  # NON accente

    def test_link_with_title_protected(self):
        line = '[modele](Model-Selection.ipynb "titre du modele")'
        cured, n = rac._cure_line(line)
        # le ](...) "title" ) entier est un span ; la cible reste intacte
        assert "Model-Selection.ipynb" in cured


# ---------------------------------------------------------------------------
# 3. preservation casse + dictionnaire conservateur
# ---------------------------------------------------------------------------
class TestCaseAndDictionary:
    def test_capitalized_preserved(self):
        cured, n = rac._cure_line("Le Parametre general.")
        assert "Paramètre" in cured  # majuscule preservee

    def test_all_caps_preserved(self):
        cured, n = rac._cure_line("Les PARAMETRES sont la.")
        # tout-majuscule preserve
        assert "PARAMÈTRES" in cured

    def test_ambiguous_words_not_cured(self):
        # 'a', 'ou', 'la', 'complete' sont des mots FR valides sans accent
        # (a/ou/la) ou des mots EN (complete) -> le dictionnaire conservateur ne
        # les inclu PAS (restauration ambigue). On verifie qu'ils ne sont pas
        # dans le dictionnaire. (NB: 'tres' EST inclus car le mot FR reel = très,
        # la forme 'tres' n'est pas un mot FR valide.)
        for w in ("a", "ou", "la", "complete", "valeur", "the"):
            assert w not in rac.ACCENT_PAIRS, "{} should not be in dictionary".format(w)

    def test_word_boundary_not_partial(self):
        # 'parametrez' (verbe, pas dans le dict) ne doit pas matcher 'parametre'
        cured, n = rac._cure_line("parametrez la valeur")
        assert n == 0  # pas de cure partielle


# ---------------------------------------------------------------------------
# 4. structure nbformat preservee (list source + str source)
# ---------------------------------------------------------------------------
class TestNbformatStructure:
    def test_list_source_preserved_as_list(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["Le parametre\n", "est utile."], "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        assert isinstance(src, list)  # type preserve
        assert len(src) == 2  # nombre de chunks preserve
        assert "paramètre" in "".join(src)

    def test_paragraph_break_preserved_list_source(self, tmp_path):
        # Regression : bug blank-line collapse firsthand sur Infer-14 (28/33 cellules,
        # po-2024 c.634). Un chunk standalone "\n" (separateur de paragraphe) ne doit
        # JAMAIS etre absorbe par un join->split->re-chunk. La cure per-chunk preserve
        # byte-pour-byte le paragraph break markdown ("\n\n").
        nb = {"cells": [
            {"cell_type": "markdown",
             "source": ["# Infer : Systeme de Classement\n", "\n", "**Serie** : Parametres\n"],
             "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        joined = "".join(src) if isinstance(src, list) else src
        # le paragraphe break \n\n entre le titre H1 et le bloc Serie doit survivre
        assert "\n\n" in joined, "paragraph break collapsed by cure"
        # le chunk count doit etre preserve (3 chunks : titre, blank, serie)
        assert isinstance(src, list) and len(src) == 3, f"chunk count drift: {src}"
        # les accents sont quand meme appliques + casse preservee
        assert "Système" in joined and "Paramètres" in joined

    def test_str_source_preserved_as_str(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "markdown", "source": "Le parametre est utile.", "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert isinstance(cured["cells"][0]["source"], str)
        assert "paramètre" in cured["cells"][0]["source"]

    def test_idempotent(self, tmp_path):
        # curer 2x = meme resultat que 1x (pas de double-cure)
        nb = _nb([("markdown", "Le parametre et le resultat.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        once = p.read_text(encoding="utf-8")
        rac.cure_notebook(p, write=True)
        twice = p.read_text(encoding="utf-8")
        assert once == twice


# ---------------------------------------------------------------------------
# 5. main() exit codes (--check, --apply, --scope)
# ---------------------------------------------------------------------------
class TestMainExitCodes:
    def test_check_exit_1_when_cures_available(self, tmp_path):
        nb = _nb([("markdown", "Le parametre est pret.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check"])
        assert rc == 1

    def test_check_exit_0_when_clean(self, tmp_path):
        nb = _nb([("markdown", "Le paramètre est prêt.")])  # deja accente
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check"])
        assert rc == 0

    def test_apply_and_check_mutually_exclusive(self, tmp_path):
        nb = _nb([("markdown", "parametre")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--apply", "--check"])
        assert rc == 2

    def test_scope_flags_code_residue(self, tmp_path):
        # mode --scope : une cellule code avec 'parametre' = residue de script ad-hoc
        nb = _nb([("code", "parametre = 1"), ("markdown", "deja accente prêt")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check", "--scope"])
        assert rc == 1  # flagge le code residue

    def test_dry_run_does_not_write(self, tmp_path):
        nb = _nb([("markdown", "Le parametre.")])
        p = tmp_path / "nb.ipynb"
        original = json.dumps(nb)
        p.write_text(original, encoding="utf-8")
        rac.main([str(p), "--dry-run"])
        assert p.read_text(encoding="utf-8") == original  # inchange

    def test_apply_writes_and_cures(self, tmp_path):
        nb = _nb([("markdown", "Le parametre.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.main([str(p), "--apply"])
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert "paramètre" in cured["cells"][0]["source"]
