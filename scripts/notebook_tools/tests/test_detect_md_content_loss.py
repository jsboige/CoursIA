"""Tests for scripts/notebook_tools/detect_md_content_loss.py (issue #8655).

Couvre les 4 scenarios d'acceptation + le comportement de normalisation :
  - cellule tronquee (signal)
  - cellules fusionnees (PAS de signal -- FP interdit, design #1)
  - scission de cellule (PAS de signal -- FP interdit, design #1)
  - reformulation neutre (PAS de signal -- design #4)
  - demotion legitime titre -> callout (PAS de signal -- c'est la transformation
    #3966 saine, doit etre invisible apres normalisation)
  - perte de motif structurant (signal independant du seuil de caracteres)
"""
import json
import sys
from pathlib import Path
from unittest import mock

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import detect_md_content_loss as dml  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def _md(src):
    """Cellule markdown avec source (str ou list)."""
    return {"cell_type": "markdown", "source": src, "metadata": {}}


def _nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# Une cellule pedagogique substantielle (~700c normalises, au-dessus de MIN_ORIG_CHARS).
EXERCISE_BODY = (
    "## Exercice : Verifier qu'une grille est valide\n\n"
    "### Enonce\n\n"
    "Apres avoir resolu un Sudoku avec le backtracking, il est essentiel de "
    "verifier que la solution obtenue est bien valide. Implementez une fonction "
    "qui verifie les contraintes suivantes :\n\n"
    "1. Chaque ligne contient les chiffres 1 a 9 sans repetition.\n"
    "2. Chaque colonne contient les chiffres 1 a 9 sans repetition.\n"
    "3. Chaque bloc 3x3 contient les chiffres 1 a 9 sans repetition.\n\n"
    "**Indices gradues** :\n\n"
    "- Indice 1 : pensez a utiliser des ensembles pour detecter les doublons.\n"
    "- Indice 2 : decoupez la verification en trois sous-fonctions.\n"
    "- Indice 3 : la contrainte de bloc utilise des coordonnees en blocs de 3.\n"
)


# ---------------------------------------------------------------------------
# 1. Normalisation -- la demotion legitime (titre -> callout) est invisible
# ---------------------------------------------------------------------------
class TestNormalize:
    def test_heading_stripped(self):
        # "## Foo" et "Foo" normalisent identiquement.
        assert dml._normalize("## Foo bar") == dml._normalize("Foo bar")

    def test_callout_stripped(self):
        # Une LIGNE entiere qui n'est qu'un callout #3966 `> **X :**` disparait
        # a la normalisation (c'est la transformation legitime titre->callout).
        # NB : une ligne avec du contenu APRES le callout n'est pas un callout
        # pur et n'est pas retiree (le contenu reste).
        pure_callout = "> **Navigation :**"
        assert dml._normalize(pure_callout) == ""

    def test_legit_demotion_is_invisible(self):
        # La transformation SAINE du rollout #3966 : titre H1 -> callout blockquote.
        # Apres normalisation, le VOLUME de contenu doit etre identique -> pas de
        # signal de perte (c'est le coeur de l'anti-FP).
        before = "# 11. Quantization des LLMs\n\n" + ("Objectif general. " * 20)
        after = "## 11. Quantization des LLMs\n\n" + ("Objectif general. " * 20)
        assert dml._norm_len(before) == dml._norm_len(after)

    def test_whitespace_collapsed(self):
        assert dml._normalize("a  b\n\n  c") == dml._normalize("abc")


# ---------------------------------------------------------------------------
# 2. Cellule tronquee (signal) -- le defaut reel de #8654/#8630
# ---------------------------------------------------------------------------
class TestTruncatedCell:
    def test_massive_truncation_signals(self):
        # Cas reel #8654 cell 9 : 941c -> 16c (seul le callout d'indices reste).
        base = _nb(_md(EXERCISE_BODY))
        head = _nb(_md("> **Indices :**"))
        findings = dml._compare_cells(dml.extract_md_cells(base), dml.extract_md_cells(head))
        assert len(findings) == 1
        f = findings[0]
        assert f["kind"] == "TRUNCATED_CELL"
        assert f["ratio"] < dml.DROP_THRESHOLD
        assert f["before_chars"] >= dml.MIN_ORIG_CHARS

    def test_tiny_original_not_flagged(self):
        # Une cellule d'origine trop courte (< MIN_ORIG_CHARS) n'est pas signalee
        # meme si elle est tronquee -> evite le bruit sur les cellules triviales.
        short = "## Titre court\n"  # ~10c normalises < 100
        base = _nb(_md(short))
        head = _nb(_md("> **Titre :**"))
        findings = dml._compare_cells(dml.extract_md_cells(base), dml.extract_md_cells(head))
        assert findings == []


# ---------------------------------------------------------------------------
# 3. Cellules fusionnees (FAUX POSITIF a NE PAS lever, design #1)
# ---------------------------------------------------------------------------
class TestMergedCellsNoFalsePositive:
    def test_merge_preserves_content_no_signal(self):
        # Deux cellules base fusionnees en une seule head : le compte change
        # (2 -> 1), la comparaison cellule-par-cellule est court-circuitee, et le
        # contenu total est preserve -> 0 signal.
        part1 = "## Section A\n\n" + ("Contenu A. " * 20)
        part2 = "## Section B\n\n" + ("Contenu B. " * 20)
        merged = part1 + "\n\n" + part2  # tout est la, juste fusionne
        base = _nb(_md(part1), _md(part2))
        head = _nb(_md(merged))
        findings = dml._compare_cells(dml.extract_md_cells(base), dml.extract_md_cells(head))
        assert findings == [], "une fusion qui preserve le contenu ne doit PAS etre signalee"


# ---------------------------------------------------------------------------
# 4. Scission de cellule (FAUX POSITIF a NE PAS lever, design #1)
# ---------------------------------------------------------------------------
class TestSplitCellNoFalsePositive:
    def test_split_preserves_content_no_signal(self):
        # Une cellule base scindee en deux head : le compte change (1 -> 2),
        # court-circuit, contenu total preserve -> 0 signal.
        whole = "## Section\n\n" + ("Contenu. " * 40)
        base = _nb(_md(whole))
        head = _nb(_md("## Section\n"), _md(("Contenu. " * 40)))
        findings = dml._compare_cells(dml.extract_md_cells(base), dml.extract_md_cells(head))
        assert findings == [], "une scission qui preserve le contenu ne doit PAS etre signalee"


# ---------------------------------------------------------------------------
# 5. Reformulation neutre (PAS de signal, design #4)
# ---------------------------------------------------------------------------
class TestNeutralRephraseNoSignal:
    def test_minor_tightening_below_threshold(self):
        # Une reformulation qui resserre le texte de ~15 % reste au-dessus du
        # seuil de 75 % -> pas de signal. (Seul un effondrement est signale.)
        long_body = ("Phrase pedagogique assez longue pour rester substantielle. " * 12)
        base = _nb(_md("## Titre\n\n" + long_body))
        # On retire ~10 % du contenu (une phrase sur dix), reste > 75 %.
        trimmed = "## Titre\n\n" + ("Phrase pedagogique assez longue pour rester substantielle. " * 11)
        head = _nb(_md(trimmed))
        findings = dml._compare_cells(dml.extract_md_cells(base), dml.extract_md_cells(head))
        assert findings == []


# ---------------------------------------------------------------------------
# 6. Motifs structurants (signal independant du seuil de caracteres)
# ---------------------------------------------------------------------------
class TestLostMotifs:
    def test_lost_navigation_motif_signals(self):
        # La disparition du bloc **Navigation** est signalee meme si la chute de
        # caracteres est borderline. NB : le mot-cle est matche case-insensitive,
        # donc le head ne doit PAS contenir "navigation" pour que la perte soit vue.
        base = _nb(_md("**Navigation** : [Index](README.md) | [Suivant](11.ipynb)"))
        head = _nb(_md("Titre simple."))
        findings = dml._compare_motifs(dml._collect_motifs(base), dml._collect_motifs(head))
        labels = [f["motif"] for f in findings]
        assert "Navigation" in labels

    def test_partial_nav_link_loss_signals(self):
        # Perte PARTIELLE de liens de navigation (4 -> 2) -> LOST_NAV_LINKS.
        base = _nb(_md("[a](1.ipynb) [b](2.ipynb) [c](3.ipynb) [d](4.ipynb)"))
        head = _nb(_md("[a](1.ipynb) [b](2.ipynb)"))
        findings = dml._compare_motifs(dml._collect_motifs(base), dml._collect_motifs(head))
        kinds = [(f["kind"], f["delta"]) for f in findings]
        assert ("LOST_NAV_LINKS", 2) in kinds

    def test_motif_preserved_no_signal(self):
        # Le motif survit -> pas de signal.
        base = _nb(_md("**Navigation** : [Index](README.md)"))
        head = _nb(_md("**Navigation** : [Index](README.md) | [Suivant](2.ipynb)"))
        findings = dml._compare_motifs(dml._collect_motifs(base), dml._collect_motifs(head))
        assert all(f["kind"] != "LOST_MOTIF" for f in findings)


# ---------------------------------------------------------------------------
# 7. scan_notebook end-to-end (base via mock, head = working tree tmp file)
# ---------------------------------------------------------------------------
class TestScanNotebook:
    def _scan(self, tmp_path, base_nb, head_nb, nb_name="x.ipynb"):
        p = tmp_path / nb_name
        p.write_text(json.dumps(head_nb), encoding="utf-8")
        # Mock aussi ref_resolves (True) et path_exists_at_ref (True) : un
        # notebook EXISTANT a la base atteint la comparaison (follow-up #8662).
        with mock.patch.object(dml, "read_notebook_at_ref", return_value=base_nb), \
             mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=True):
            return dml.scan_notebook(p, base_ref="MOCK_BASE", head_ref=None)

    def test_truncation_end_to_end(self, tmp_path):
        r = self._scan(tmp_path, _nb(_md(EXERCISE_BODY)), _nb(_md("> **Indices :**")))
        assert r["stats"]["findings_count"] >= 1
        assert any(f["kind"] == "TRUNCATED_CELL" for f in r["findings"])

    def test_clean_demotion_end_to_end(self, tmp_path):
        # Demotion legitime (titre -> callout, contenu preserve) -> 0 finding.
        before = "# Titre\n\n" + ("Contenu pedagogique substantiel. " * 15)
        after = "## Titre\n\n" + ("Contenu pedagogique substantiel. " * 15)
        r = self._scan(tmp_path, _nb(_md(before)), _nb(_md(after)))
        assert r["stats"]["findings_count"] == 0


# ---------------------------------------------------------------------------
# 8. main() exit codes
# ---------------------------------------------------------------------------
class TestMainExitCodes:
    def _run(self, tmp_path, base_nb, head_nb):
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(head_nb), encoding="utf-8")
        # Mock ref_resolves (True) et path_exists_at_ref (True) : notebook
        # EXISTANT a la base -> la comparaison s'execute (follow-up #8662).
        with mock.patch.object(dml, "read_notebook_at_ref", return_value=base_nb), \
             mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=True):
            return dml.main([str(p), "--base", "MOCK", "--check"])

    def test_exit_1_on_truncation(self, tmp_path):
        assert self._run(tmp_path, _nb(_md(EXERCISE_BODY)), _nb(_md("> **Indices :**"))) == 1

    def test_exit_0_on_clean(self, tmp_path):
        before = "# Titre\n\n" + ("Contenu. " * 20)
        after = "## Titre\n\n" + ("Contenu. " * 20)
        assert self._run(tmp_path, _nb(_md(before)), _nb(_md(after))) == 0

    def test_exit_2_on_missing_base_ref(self, tmp_path):
        # Notebook EXISTANT mais illisible (ref valide, path presente, contenu
        # illisible) -> erreur -> exit 2 (garde anti-auto-desarmement preserve).
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(_nb(_md("ok"))), encoding="utf-8")
        with mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=True), \
             mock.patch.object(dml, "read_notebook_at_ref", return_value=None):
            assert dml.main([str(p), "--base", "BAD_REF", "--check"]) == 2


# ---------------------------------------------------------------------------
# 9. New-file exemption + invalid-ref guard (follow-up #8655/#8662)
# ---------------------------------------------------------------------------
class TestNewFileExemptionAndRefGuard:
    """Un notebook NOUVEAU (absent a la base) est exempt de content-loss ; un
    ref de base invalide reste rc=2 (garde anti-auto-desarmement preserve)."""

    def test_new_file_exempt_no_findings(self, tmp_path):
        # Notebook absent a la base (nouveau) -> exempt, 0 findings, new_file=True.
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(_nb(_md(EXERCISE_BODY))), encoding="utf-8")
        with mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=False), \
             mock.patch.object(dml, "read_notebook_at_ref", return_value=None):
            r = dml.scan_notebook(p, base_ref="MOCK_BASE", head_ref=None)
        assert r.get("new_file") is True
        assert r["stats"]["findings_count"] == 0
        assert "error" not in r

    def test_new_file_main_exits_0(self, tmp_path):
        # main() renvoie 0 pour un nouveau fichier (rien a perdre, tout est ajoute).
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(_nb(_md(EXERCISE_BODY))), encoding="utf-8")
        with mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=False), \
             mock.patch.object(dml, "read_notebook_at_ref", return_value=None):
            assert dml.main([str(p), "--base", "MOCK", "--check"]) == 0

    def test_invalid_ref_exits_2_disarm_preserved(self, tmp_path):
        # Ref de base invalide -> rc=2 : le garde anti-auto-desarmement (#8662)
        # reste arme. Sans ref_resolves, un BASE casse ferait passer tous les
        # chemins pour "nouveaux" (path_exists_at_ref False) -> desarmement silencieux.
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(_nb(_md("ok"))), encoding="utf-8")
        with mock.patch.object(dml, "ref_resolves", return_value=False):
            assert dml.main([str(p), "--base", "BAD_REF", "--check"]) == 2
