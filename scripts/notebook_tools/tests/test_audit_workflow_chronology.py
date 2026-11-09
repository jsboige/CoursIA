"""Tests for scripts/notebook_tools/audit_workflow_chronology.py.

Issue #14442 (défaut 3) : détecter la chronologie de livraison Git dans la prose
des carnets (renvois à un EPIC / une PR / une issue, un numéro en parenthèse, le
past-participe « livré »). Le test verifie la détection et la distinction cruciale
que fait l'organe : un pointeur de carnet SANS numéro (« voir GT-3b ») et une prose
française courante (« promesse livrée à Colonne ») ne sont PAS des marqueurs, alors
qu'un renvoi de livraison (« GT-3b (#12213) », « livré sur main par #13350 ») l'est.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import audit_workflow_chronology as mod  # noqa: E402


def _nb(cells):
    return {
        "cells": [
            {"cell_type": ct, "source": [src] if isinstance(src, str) else src,
             "metadata": {}, "outputs": [] if ct == "code" else None}
            for ct, src in cells
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }


def _write(tmp_path, name, cells):
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    return p


class TestScanNotebook:
    def test_epic_and_pr_paren_detected(self, tmp_path):
        p = _write(tmp_path, "a.ipynb", [
            ("markdown", "la forme d'itération que l'EPIC #12205 prescrit ; "
                          "Bruns-Kimmich via GT-3b (#12213)."),
        ])
        names = sorted(n for _, n, _ in mod.scan_notebook(str(p)))
        assert "epic" in names
        assert "pr_paren" in names

    def test_livre_sur_main_detected(self, tmp_path):
        p = _write(tmp_path, "b.ipynb", [
            ("markdown", "le twin C# est livré sur main par #13350."),
        ])
        names = sorted(n for _, n, _ in mod.scan_notebook(str(p)))
        assert "livre" in names

    def test_bare_notebook_pointer_not_flagged(self, tmp_path):
        # Pointeur pédagogique SANS numéro : pas un marqueur de livraison.
        p = _write(tmp_path, "c.ipynb", [
            ("markdown", "Représentation héritée de GT-3b ; les murs de GT-3b "
                          "ne sont pas des tunnels."),
        ])
        assert mod.scan_notebook(str(p)) == []

    def test_french_prose_livree_not_flagged(self, tmp_path):
        # « livrée » dans la prose courante, sans numéro accolé : pas un marqueur.
        p = _write(tmp_path, "d.ipynb", [
            ("markdown", "la promesse livrée à Colonne ne vaut que le rang 1,4."),
        ])
        assert mod.scan_notebook(str(p)) == []

    def test_provenance_with_number_is_flagged(self, tmp_path):
        # Un numéro en parenthèse est signalé, même si la lecture le classera
        # PROVENANCE_UTILE : l'organe rend le candidat, la classe est humaine.
        p = _write(tmp_path, "e.ipynb", [
            ("markdown", "Verdict SOTA-OK (#10459) : l'annexe ci-dessous."),
        ])
        assert len(mod.scan_notebook(str(p))) == 1

    def test_code_cell_ignored(self, tmp_path):
        # Seules les cellules markdown sont scannées.
        p = _write(tmp_path, "f.ipynb", [
            ("code", 'x = "EPIC #12205"  # dans du code, pas scanné'),
        ])
        assert mod.scan_notebook(str(p)) == []

    def test_paren_reference_followed_by_a_comment_is_detected(self, tmp_path):
        # Cécité de regex mesurée par la review Hermes sur #22658 : la forme
        # exacte « (#NNNN) » laissait passer un renvoi suivi d'un commentaire
        # (« (#15399, clos COMPLETED) », « (#10382, axe 5) »).
        p = _write(tmp_path, "g1.ipynb", [
            ("markdown", "le pilote (#15399, clos COMPLETED) et la Proposition 6 "
                          "(#12343, §1.1 du 16e)."),
        ])
        names = [n for _, n, _ in mod.scan_notebook(str(p))]
        assert names.count("pr_paren") == 2

    def test_unclosed_paren_reference_is_detected(self, tmp_path):
        # Renvoi sans parenthèse fermante : même classe de chronologie.
        p = _write(tmp_path, "g2.ipynb", [
            ("markdown", "la formalisation de la proposition (#15399"),
        ])
        names = [n for _, n, _ in mod.scan_notebook(str(p))]
        assert "pr_paren" in names

    def test_number_not_glued_to_the_paren_is_not_flagged(self, tmp_path):
        # Un numéro cité sans la parenthèse collée n'est pas la forme
        # canonique du renvoi de livraison (« PR #N » a son propre marqueur).
        p = _write(tmp_path, "g3.ipynb", [
            ("markdown", "voir (# 15399) ou (voir #15399) : pas la forme canonique."),
        ])
        assert mod.scan_notebook(str(p)) == []

    def test_three_digit_paren_is_not_flagged(self, tmp_path):
        # Frontière de nombre conservée : 3 chiffres ne sont pas un numéro de
        # PR/issue de ce dépôt.
        p = _write(tmp_path, "g4.ipynb", [
            ("markdown", "l'équation (#123) reste vraie."),
        ])
        assert mod.scan_notebook(str(p)) == []


class TestMainExitCodes:
    def test_clean_returns_0(self, tmp_path, capsys):
        p = _write(tmp_path, "clean.ipynb", [("markdown", "une prose sans numéro.")])
        assert mod.main([str(p)]) == 0

    def test_marker_returns_1(self, tmp_path, capsys):
        p = _write(tmp_path, "dirty.ipynb", [("markdown", "EPIC #12205.")])
        assert mod.main([str(p)]) == 1

    def test_missing_path_returns_2(self, tmp_path, capsys):
        assert mod.main([str(tmp_path / "absent.ipynb")]) == 2

    def test_json_output(self, tmp_path, capsys):
        p = _write(tmp_path, "j.ipynb", [("markdown", "PR #12648.")])
        assert mod.main([str(p), "--json"]) == 1
        data = json.loads(capsys.readouterr().out)
        assert data["n_notebooks_flagged"] == 1


class TestUtf8Emission:
    """Le rapport doit rester lisible par un consommateur UTF-8 sous redirection.

    Sous Windows, un stdout redirige encode en cp1252 : un accent du corpus
    (« la ou » avec accent grave) sort en octet 0xe0 et ``json.load`` leve
    ``UnicodeDecodeError`` au premier accent. Mesure du 2026-11-05 sur
    ``MyIA.AI.Notebooks/RL`` : octet 0xe0 en position 241, rapport entier perdu.
    """

    @pytest.mark.parametrize("extra", [["--json"], []], ids=["json", "humain"])
    def test_redirected_stdout_is_utf8_decodable(self, tmp_path, extra):
        """Les DEUX branches d'emission (``--json`` et humaine) doivent survivre
        a un stdout cp1252 redirige -- le mutant qui reveindrait la branche humaine
        a ``print()`` est tue par la variante ``extra == []``."""
        import io
        p = _write(tmp_path, "accent.ipynb", [("markdown", "l'EPIC #12205 là où le pli passe.")])
        raw = io.BytesIO()
        wrapper = io.TextIOWrapper(raw, encoding="cp1252")
        original, sys.stdout = sys.stdout, wrapper
        try:
            assert mod.main([str(p)] + extra) == 1
            wrapper.flush()
        finally:
            sys.stdout = original
        text = raw.getvalue().decode("utf-8")
        if "--json" in extra:
            assert json.loads(text)["n_notebooks_flagged"] == 1
        else:
            # Branche humaine : l'accent du snippet doit sortir en octets UTF-8
            # reels, pas en cp1252 (0xe0) ni en echappement backslashreplace.
            assert "là où" in text

    def test_stream_without_reconfigure_falls_back_to_ascii(self, tmp_path):
        p = _write(tmp_path, "accent2.ipynb", [("markdown", "l'EPIC #12205 là où le pli passe.")])

        class AsciiOnly:
            """Flux sans `reconfigure`, qui refuse tout caractere non-ASCII."""

            def __init__(self):
                self.chunks = []

            def write(self, text):
                non_ascii = [c for c in text if ord(c) > 127]
                if non_ascii:
                    raise UnicodeEncodeError("ascii", text, 0, len(text), "ordinal not in range(128)")
                self.chunks.append(text)

            def flush(self):
                pass

        fake = AsciiOnly()
        original, sys.stdout = sys.stdout, fake
        try:
            assert mod.main([str(p), "--json"]) == 1
        finally:
            sys.stdout = original
        text = "".join(fake.chunks)
        assert text.isascii(), "le repli doit emettre des octets ASCII"
        data = json.loads(text)
        assert data["n_notebooks_flagged"] == 1
        # Les accents survivent au repli : ils sont echappes dans le JSON, pas perdus.
        assert any("là où" in hit[2] for hit in data["notebooks"][0]["hits"])
