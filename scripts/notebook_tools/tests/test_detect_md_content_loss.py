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
def _md(src, cell_id=None):
    """Cellule markdown avec source (str ou list) et id nbformat optionnel."""
    cell = {"cell_type": "markdown", "source": src, "metadata": {}}
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


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
# 4b. Reorder SAFE par ID (c.8254, anti-FP detecteur)
# ---------------------------------------------------------------------------
class TestReorderSafeByCellID:
    """Bug fondateur (c.8254) : un reorder pur qui preserve le count et le multiset
    d'IDs nbformat 4.5+ etait confondu avec une perte de contenu (l'appariement
    par index croisait des cellules differentes apres decalage). Le multiset
    d'IDs identique est un signal fort "reorder sans modif de contenu" et
    merite appariement par ID, pas par index.

    Fix #10873 : l'appariement par ID porte sur le **sous-ensemble id-e stable**
    (cellules exposant un ``id``) ; les cellules sans id (residu) restent
    appariees par index. L'ancienne politique all-or-nothing basculait le
    notebook entier en mode index des qu'une cellule md etait sans id
    (150/1017 notebooks exposes, FP #10725).
    """

    def test_reorder_with_stable_ids_no_signal(self):
        # 3 cellules substantielles, reorder pur (memes contenus, ordre
        # different), multiset d'IDs preserve. L'ancienne politique par index
        # aurait signale la cellule 1 comme "tronquee de 100% a 0%" (elle
        # n'existait plus a la position 1, donc zip ramenait le contenu de la
        # cellule 0 a comparer). Avec l'appariement par ID, 0 signal.
        body_long_a = "## Section A\n\n" + ("Phrase A substantielle. " * 25)
        body_long_b = "## Section B\n\n" + ("Phrase B substantielle. " * 25)
        body_long_c = "## Section C\n\n" + ("Phrase C substantielle. " * 25)
        base = _nb(_md(body_long_a, cell_id="alpha"),
                   _md(body_long_b, cell_id="bravo"),
                   _md(body_long_c, cell_id="charlie"))
        head = _nb(_md(body_long_a, cell_id="alpha"),
                   _md(body_long_c, cell_id="charlie"),  # deplace de la fin au milieu
                   _md(body_long_b, cell_id="bravo"))    # deplace du milieu a la fin
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert findings == [], (
            "un reorder pur preservant les IDs ne doit PAS signaler de perte "
            f"(trouve: {findings!r})"
        )

    def test_truncation_with_stable_ids_still_signals(self):
        # Le multiset d'IDs est preserve MAIS une cellule est reellement
        # tronquee -- le garde doit continuer a signaler (ID matching n'est
        # pas un blanc-seing).
        body_long = "## Section\n\n" + ("Phrase substantielle. " * 30)
        base = _nb(_md(body_long, cell_id="alpha"),
                   _md(body_long, cell_id="bravo"))
        head = _nb(_md(body_long, cell_id="alpha"),
                   _md("> **Titre :**", cell_id="bravo"))  # cellule bravo reellement tronquee
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert len(findings) == 1
        assert findings[0]["kind"] == "TRUNCATED_CELL"
        assert findings[0]["cell_idx"] == 1  # position dans le head

    def test_reorder_with_single_missing_id_no_signal(self):
        # #10873 : une SEULE cellule md sans id (residu) ne doit plus basculer
        # le notebook entier en mode index. L'ancienne politique all-or-nothing
        # (`ids_available` exigeait que TOUTES les cellules aient un id)
        # retombait en index : la position 0 pairerait la LONGUE cellule A
        # (base) avec la COURTE cellule B (head, remontee en tete par le
        # reorder) -> faux positif TRUNCATED_CELL. Le fix apparie le
        # sous-ensemble id-e (alpha, charlie) par id et le residu (b, sans
        # id) par index -> 0 finding.
        a = "## Section A\n\n" + ("Phrase A substantielle. " * 30)   # ~730c normalises
        b = "## Bref rappel\n\n" + ("Rappel bref. " * 6)             # ~90c, sans id
        c = "## Section C\n\n" + ("Phrase C substantielle. " * 30)   # ~730c
        base = _nb(_md(a, cell_id="alpha"),
                   _md(b),                     # residu sans id
                   _md(c, cell_id="charlie"))
        head = _nb(_md(b),                     # reorder pur : B remonte en tete
                   _md(a, cell_id="alpha"),
                   _md(c, cell_id="charlie"))
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert findings == [], (
            "un reorder pur avec 1 cellule md sans id ne doit PAS signaler "
            f"(trouve: {findings!r})"
        )

    def test_partial_id_truncation_still_signals(self):
        # #10873 : le sous-ensemble id-e est apparie par id, mais une vraie
        # troncature sur une cellule id-e doit continuer a signaler (le fix
        # n'est pas un blanc-seing pour la cellule id-e elle-meme).
        body_long = "## Section\n\n" + ("Phrase substantielle. " * 30)
        base = _nb(_md(body_long, cell_id="alpha"),
                   _md(body_long))                # residu sans id
        head = _nb(_md("> **Titre :**", cell_id="alpha"),  # alpha reellement tronquee
                   _md(body_long))
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert len(findings) == 1
        assert findings[0]["kind"] == "TRUNCATED_CELL"
        assert findings[0]["cell_idx"] == 0  # position dans le head

    def test_zero_id_pure_reorder_no_signal(self):
        # #10873 court-circuit multiset : un notebook AUCUNE cellule md id-ee
        # (classe QC-Py-07/08/10, 0/52 et 0/50 ids) + reorder pur doit rendre
        # 0 finding. Les longuetres tres differentes garantissent que le code
        # PRE-court-circuit produisait bien un FP index (long base[0] paire
        # avec court head[0]) -- ce test echoue contre le code post-#10885
        # sans le court-circuit.
        body_long = "## Section A\n\n" + ("Phrase A substantielle. " * 30)   # ~730c
        body_short = "## Section B\n\n" + ("Phrase B plus courte. " * 12)     # ~280c
        base = _nb(_md(body_long), _md(body_short))
        head = _nb(_md(body_short), _md(body_long))  # reorder pur sans ids
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert findings == [], (
            "un reorder pur sur un notebook zero-id ne doit PAS signaler "
            f"(court-circuit multiset, trouve: {findings!r})"
        )

    def test_zero_id_real_truncation_still_signals(self):
        # #10873 non-blanc-seing : le court-circuit multiset ne desarme pas le
        # gate sur une VRAIE troncature en notebook zero-id -- la chaine
        # tronquee differe, le multiset differe, le court-circuit ne s'arme
        # pas et l'appariement index legacy signale.
        body_long = "## Section\n\n" + ("Phrase substantielle. " * 30)
        base = _nb(_md(body_long), _md(body_long))
        head = _nb(_md(body_long), _md("> **Titre :**"))  # vraie troncature
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert len(findings) == 1
        assert findings[0]["kind"] == "TRUNCATED_CELL"
        assert findings[0]["cell_idx"] == 1

    def test_zero_id_same_length_substitution_still_signals(self):
        # #10873 garde anti-blanc-seing des TOTAUX : substitution + reorder.
        # base = [X (L), Y (S)], head = [Y (S), X' (L)] ou X' est DISTINCT de
        # X mais de MEME longueur normalisee (mots de meme longueur). Les
        # TOTAUX sont egaux au caractere pres -- un critere sur les totaux
        # disculperait a tort (blanc-seing). Le critere implemente est le
        # MULTISET des chaines : il differe, le court-circuit ne s'arme pas,
        # l'appariement index signale le desalignement (X perdu, X' apparu).
        x = "## Analyse technique\n\n" + ("Regarder la volatilite. " * 20)
        x_prime = "## Analyse technique\n\n" + ("Analyser la volatilite. " * 20)
        y = "## Section breve\n\n" + ("Rappel court. " * 12)
        assert len(dml._normalize(x)) == len(dml._normalize(x_prime)), (
            "fixtures: X et X' doivent totaliser la meme longueur normalisee "
            "pour que ce test prouve multiset != totaux"
        )
        base = _nb(_md(x), _md(y))
        head = _nb(_md(y), _md(x_prime))  # X substitue par X' + reorder
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert len(findings) >= 1, (
            "une substitution meme-longueur + reorder doit signaler (multiset "
            f"different, totaux egaux -- trouve: {findings!r})"
        )
        assert findings[0]["kind"] == "TRUNCATED_CELL"

    def test_partial_ids_use_subset_matching(self):
        # #10873 : si seulement certaines cellules ont un id (cas mixte),
        # l'appariement par ID porte sur le sous-ensemble id-e (alpha),
        # l'index sur le residu sans id. Notebooks identiques -> 0 finding
        # (l'ancienne politique all-or-nothing retombait en mode index).
        body_long = "## Section\n\n" + ("Phrase. " * 25)
        base = _nb(_md(body_long, cell_id="alpha"), _md(body_long))
        head = _nb(_md(body_long, cell_id="alpha"), _md(body_long))
        # IDs partiels : alpha en base[0] et head[0], mais base[1]/head[1] = None.
        findings = dml._compare_cells(dml.extract_md_cells(base),
                                      dml.extract_md_cells(head))
        assert findings == [], (
            "un notebook mixte identique ne doit PAS signaler avec le subset "
            f"matching (trouve: {findings!r})"
        )


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


# ---------------------------------------------------------------------------
# 10. Frontmatter cost -> metadata.cost migration (#8919)
# ---------------------------------------------------------------------------
# Un bloc frontmatter YAML `cost:` retire d'une cellule alors que ses champs
# sont migres dans nb['metadata']['cost'] est une transformation LEGITIME (cas
# #8916) : le gate ne doit PAS la signaler. Mais une suppression seche, ou une
# migration laissant un metadata.cost DIVERGENT (cpu_min 0 au lieu de 20/45,
# reduced_pedagogical None au lieu d'un chemin -- piege #8908/#8912/#8914), doit
# rester ROUGE. Le detecteur reste mordant sur cette classe.
FRONTMATTER_COST_BLOCK = """---
title: Foo/quantbook
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 15
  gpu_required: false
  network: true
  external_account: quantconnect-organization
  free_alternative: null
  reduced_pedagogical: path/to/free-nb.ipynb
  reproducibility: HIGH
  metadata_written: 2026-07-23T08:00Z
  validator: qc_cloud
---
"""
FAITHFUL_COST = {
    "api_usd_est": 0.0, "api_provider": "none", "cpu_min": 15,
    "gpu_required": False, "network": True,
    "external_account": "quantconnect-organization", "free_alternative": None,
    "reduced_pedagogical": "path/to/free-nb.ipynb", "reproducibility": "HIGH",
    "metadata_written": "2026-07-23T08:00Z", "validator": "qc_cloud",
}


def _nb_with_cost(cost, *cells):
    nb = _nb(*cells)
    nb["metadata"]["cost"] = cost
    return nb


class TestFrontmatterCostMigration:
    """La migration frontmatter cost -> metadata.cost equivalente est invisible ;
    une migration divergente ou absente reste signaler (#8919)."""

    def _scan(self, tmp_path, base_nb, head_nb, nb_name="x.ipynb"):
        p = tmp_path / nb_name
        p.write_text(json.dumps(head_nb), encoding="utf-8")
        with mock.patch.object(dml, "read_notebook_at_ref", return_value=base_nb), \
             mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=True):
            return dml.scan_notebook(p, base_ref="MOCK_BASE", head_ref=None)

    # --- unit : parsing + equivalence ---
    def test_parse_frontmatter_cost_extracts_keys(self):
        cost = dml._parse_frontmatter_cost(FRONTMATTER_COST_BLOCK + "# H1\n")
        assert cost is not None
        assert set(cost) == set(FAITHFUL_COST)
        assert cost["cpu_min"] == "15"
        assert cost["free_alternative"] == "null"

    def test_parse_returns_none_without_frontmatter(self):
        assert dml._parse_frontmatter_cost("# Plain H1\n\nprose") is None
        assert dml._parse_frontmatter_cost("---\ntitle: x\n---\n# no cost block") is None

    def test_cost_equivalent_faithful(self):
        equiv, div = dml._cost_equivalent(
            dml._parse_frontmatter_cost(FRONTMATTER_COST_BLOCK), FAITHFUL_COST)
        assert equiv is True and div == []

    def test_cost_equivalent_flags_divergent_field(self):
        # cpu_min 15 -> 0, reduced_pedagogical path -> None (le piege #8908).
        base_cost = dml._parse_frontmatter_cost(FRONTMATTER_COST_BLOCK)
        divergent = dict(FAITHFUL_COST, cpu_min=0, reduced_pedagogical=None)
        equiv, div = dml._cost_equivalent(base_cost, divergent)
        assert equiv is False
        assert "cpu_min" in div and "reduced_pedagogical" in div

    def test_normalize_cost_value_yaml_json_parity(self):
        # YAML str "null" == JSON None ; "true"==True ; "0.0"==0.0 ; "HIGH"=="high"
        assert dml._normalize_cost_value("null") == dml._normalize_cost_value(None)
        assert dml._normalize_cost_value("true") == dml._normalize_cost_value(True)
        assert dml._normalize_cost_value("0.0") == dml._normalize_cost_value(0.0)
        assert dml._normalize_cost_value("HIGH") == dml._normalize_cost_value("high")

    # --- end-to-end : le gate dit VERT/ROUGE correctement ---
    def test_faithful_migration_no_finding(self, tmp_path):
        # #8916 : frontmatter migre verbatim dans metadata.cost -> VERT.
        body = "# Research QuantBook: Foo\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(FRONTMATTER_COST_BLOCK + body))
        head = _nb_with_cost(FAITHFUL_COST, _md(body))
        r = self._scan(tmp_path, base, head)
        assert r["stats"]["findings_count"] == 0, r["findings"]

    def test_divergent_cost_migration_signals(self, tmp_path):
        # #8908 skeleton : frontmatter retire mais metadata.cost diverge
        # (cpu_min 0 au lieu de 15) -> ROUGE + nomme le champ divergent.
        body = "# Research QuantBook: Foo\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(FRONTMATTER_COST_BLOCK + body))
        divergent = dict(FAITHFUL_COST, cpu_min=0, reduced_pedagogical=None)
        head = _nb_with_cost(divergent, _md(body))
        r = self._scan(tmp_path, base, head)
        kinds = {f["kind"] for f in r["findings"]}
        assert "FRONTMATTER_COST_DIVERGENCE" in kinds, r["findings"]
        div = [f for f in r["findings"] if f["kind"] == "FRONTMATTER_COST_DIVERGENCE"][0]
        assert "cpu_min" in div["divergent_fields"]
        assert "reduced_pedagogical" in div["divergent_fields"]

    def test_frontmatter_stripped_no_head_cost_signals(self, tmp_path):
        # Suppression seche : frontmatter retire, AUCUN metadata.cost -> ROUGE.
        body = "# Research QuantBook: Foo\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(FRONTMATTER_COST_BLOCK + body))
        head = _nb(_md(body))  # metadata.cost absent
        r = self._scan(tmp_path, base, head)
        assert any(f["kind"] == "FRONTMATTER_COST_DIVERGENCE" for f in r["findings"])

    def test_migration_plus_prose_truncation_still_signals(self, tmp_path):
        # Le strip du frontmatter ne doit PAS devenir un permis de tronquer la
        # prose : migration equivalente MAIS prose massivement coupee -> ROUGE.
        body = "# Research QuantBook: Foo\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(FRONTMATTER_COST_BLOCK + body))
        truncated = "# Research QuantBook: Foo\n"  # toute la prose perdue
        head = _nb_with_cost(FAITHFUL_COST, _md(truncated))
        r = self._scan(tmp_path, base, head)
        assert any(f["kind"] == "TRUNCATED_CELL" for f in r["findings"])


# ---------------------------------------------------------------------------
# 11. Review #8921 : cas REELS (SK-1 commente, Claudish notes non migrees)
# ---------------------------------------------------------------------------
# Les frontmatters reels portent leur justification en commentaire YAML inline et
# colocquent parfois une cle informative (notes:). La fonction d'equivalence doit
# (1) ignorer les commentaires, (2) comparer numeriquement (0.10 == 0.1),
# (3) accepter none -> valeur et metadata_written rafraichi comme des progres,
# (4) signaler une cle colocataire (notes:) perdue faute de migration.
SK1_FRONTMATTER = """---
title: GenAI/SemanticKernel-Intro
notes: |
  Raisonnement sur le cout (migre vers metadata.cost.notes, c.945).
cost:
  api_usd_est: 0.10           # ~5 appels kernel.invoke gpt-4o (~800 tokens/call)
  api_provider: openai        # openai_api_key + openai_chat_model_id=gpt-4o
  cpu_min: 1                  # cpu-only (pure api client, pas de gpu)
  gpu_required: false         # inference cote serveur openai
  network: true               # appels api openai obligatoires
  external_account: openai    # cle openai_api_key requise
  reproducibility: HIGH
  validator: openai_key
  free_alternative: null
  metadata_written: 2026-07-24
---
"""
# Head : valeurs PROPRES (sans commentaires) + free_alternative enrichi (null ->
# chemin reel = gain) + metadata_written rafraichi + notes migrees (c.945).
SK1_HEAD_COST = {
    "api_usd_est": 0.1, "api_provider": "openai", "cpu_min": 1,
    "gpu_required": False, "network": True, "external_account": "openai",
    "reproducibility": "HIGH", "validator": "openai_key",
    "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
    "metadata_written": "2026-07-28",
    "notes": "Raisonnement sur le cout migre (c.945).",
}

# Claudish : 5 lignes de notes (routage 3 tiers, alternative gratuite) NON migrees.
CLAUDISH_FRONTMATTER = """---
title: GenAI/Vibe-Coding/Claudish/notebooks/01-Intro
notes: |
  Routage 3 tiers (Claude/GPT/Gemini) selon le contexte.
  CE notebook EST l'alternative gratuite (endpoint public communal).
  Raisonnement humain sur le cout : 0 USD cote serveur.
cost:
  api_usd_est: 0.0
  cpu_min: 1
---
"""


class TestFrontmatterCostReviewFixes:
    """Review #8921 : equivalence robuste aux commentaires, numerique, aux progres
    (none -> valeur, date) et aux cles colocataires (notes:) non migrees."""

    def _scan(self, tmp_path, base_nb, head_nb, nb_name="x.ipynb"):
        p = tmp_path / nb_name
        p.write_text(json.dumps(head_nb), encoding="utf-8")
        with mock.patch.object(dml, "read_notebook_at_ref", return_value=base_nb), \
             mock.patch.object(dml, "ref_resolves", return_value=True), \
             mock.patch.object(dml, "path_exists_at_ref", return_value=True):
            return dml.scan_notebook(p, base_ref="MOCK_BASE", head_ref=None)

    # --- #8921-1 : commentaires YAML inline ignores ---
    def test_inline_comment_stripped(self):
        # `1  # cpu-only` == `1` ; `openai  # cle requise` == `openai`.
        assert dml._normalize_cost_value("1                  # cpu-only") == "1.0"
        assert dml._normalize_cost_value("openai        # openai_api_key") == "openai"
        # Un `#` colle a un caractere (URL) n'est PAS un commentaire -> preserve.
        assert "h#frag" in dml._normalize_cost_value("http://h#frag")

    # --- #8921-2 : comparaison numerique (0.10 == 0.1) ---
    def test_numeric_comparison(self):
        assert dml._normalize_cost_value("0.10") == dml._normalize_cost_value(0.1)
        assert dml._normalize_cost_value("0.10") == dml._normalize_cost_value("0.1")
        assert dml._normalize_cost_value(1) == dml._normalize_cost_value("1.0")

    # --- #8921-3 : none -> valeur = gain ; metadata_written exclu ---
    def test_none_to_value_is_gain_not_divergence(self):
        # free_alternative null -> chemin reel : ne doit PAS etre divergent.
        equiv, div = dml._cost_equivalent(
            {"free_alternative": "null"}, {"free_alternative": "path/to/nb.ipynb"})
        assert equiv is True and div == []

    def test_metadata_written_excluded(self):
        # Une date rafraichie a la migration n'est pas une divergence.
        equiv, div = dml._cost_equivalent(
            {"metadata_written": "2026-07-24"}, {"metadata_written": "2026-07-28"})
        assert equiv is True and div == []

    def test_value_to_none_is_loss_still_divergent(self):
        # Symetrie : valeur -> none EST une perte (reduced_pedagogical path -> None).
        equiv, div = dml._cost_equivalent(
            {"reduced_pedagogical": "path/to/nb.ipynb"}, {"reduced_pedagogical": None})
        assert equiv is False and "reduced_pedagogical" in div

    # --- #8921-4 : cle colocataire (notes:) non migree ---
    def test_frontmatter_non_cost_keys_detected(self):
        # SK-1 porte une cle notes: hors cost: -> detectee.
        assert "notes" in dml._frontmatter_non_cost_keys(SK1_FRONTMATTER)
        # Le bloc QC de reference n'a que title + cost -> aucune cle extra.
        assert dml._frontmatter_non_cost_keys(FRONTMATTER_COST_BLOCK) == []

    # --- end-to-end : SK-1 VERT (commentaires + head plus riche + notes migrees) ---
    def test_sk1_commented_frontmatter_richer_head_is_green(self, tmp_path):
        body = "# SemanticKernel Intro\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(SK1_FRONTMATTER + body))
        head = _nb_with_cost(SK1_HEAD_COST, _md(body))  # frontmatter migre, notes aussi
        r = self._scan(tmp_path, base, head)
        assert r["stats"]["findings_count"] == 0, r["findings"]

    # --- end-to-end : Claudish ROUGE (notes non migrees -> perte signalee) ---
    def test_claudish_unmigrated_notes_signals(self, tmp_path):
        body = "# Claudish Intro\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(CLAUDISH_FRONTMATTER + body))
        # cost migre mais metadata.cost SANS notes -> notes perdues -> ROUGE.
        head = _nb_with_cost({"api_usd_est": 0.0, "cpu_min": 1}, _md(body))
        r = self._scan(tmp_path, base, head)
        kinds = {f["kind"] for f in r["findings"]}
        assert "FRONTMATTER_COST_DIVERGENCE" in kinds, r["findings"]
        div = [f for f in r["findings"] if f["kind"] == "FRONTMATTER_COST_DIVERGENCE"][0]
        assert "notes" in div["divergent_fields"]  # la cle perdue est nommee

    def test_claudish_no_metadata_cost_at_all_signals(self, tmp_path):
        # metadata.cost = null (rien migre, ni cost ni notes) -> ROUGE.
        body = "# Claudish Intro\n\n" + ("Substantive prose. " * 15)
        base = _nb(_md(CLAUDISH_FRONTMATTER + body))
        head = _nb(_md(body))  # aucun metadata.cost
        r = self._scan(tmp_path, base, head)
        assert any(f["kind"] == "FRONTMATTER_COST_DIVERGENCE" for f in r["findings"])
