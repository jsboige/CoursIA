#!/usr/bin/env python3
"""Tests pour ``scripts/translation/render_notebook.py`` — T4 du pipeline i18n
(Epic #4957 / #10038 / #10039). Re-importe un notebook traduit à partir d'un
CSV par-cellule : markdown substitué, code byte-pour-byte, structure préservée.

Couvre les 6 critères d'acceptance du ticket #10039 :

1. Round-trip nominal : CSV rempli + nb FR → *_en.ipynb avec substitutions
   effectives et compte de cellules inchangé.
2. Falsification 1 : si le CSV modifie le source d'une cellule code (ce qui ne
   devrait jamais arriver), la cellule code reste byte-identique à la source.
3. Falsification 2 : CSV vide (aucune traduction) → *_en.ipynb identique à
   la source pour les champs traduisibles, structure préservée.
4. Orphelines : cellule dans le CSV mais pas dans le notebook → refus
   inconditionnel (``ValueError``, aucun fichier écrit) depuis #13544 §3 ;
   le contrat historique WARN + sidecar ``.stale`` (opt-in ``--fail-on-stale``
   de #13546) est supersedé.
5. ``--dry-run`` : aucun fichier écrit ; stats et diagnostics calculés.
6. Déterminisme : deux exécutions successives produisent un output byte-
   identique (json.dumps + indent=1 stable).

Helpers : notebooks synthétiques via ``_nb`` (mêmes conventions que
``test_extract_cells_to_csv.py``).
"""

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import render_notebook as r  # noqa: E402


# --------------------------------------------------------------------------
# Helpers — synthetic notebooks + CSV
# --------------------------------------------------------------------------

def _nb(cells, **meta):
    """Construit un notebook minimal. cells = liste de dicts {id,type,source,...}."""
    out_cells = []
    for c in cells:
        cell = {"id": c["id"], "cell_type": c["type"],
                "source": c["source"], "metadata": {}}
        if c["type"] == "code":
            cell["outputs"] = c.get("outputs", [])
            cell["execution_count"] = c.get("execution_count", None)
        out_cells.append(cell)
    return {
        "cells": out_cells,
        "metadata": meta,
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write_nb(tmp_path, name, cells, **meta):
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells, **meta)), encoding="utf-8")
    return p


def _write_csv(tmp_path, name, rows):
    """CSV minimal avec colonnes : notebook, cell_id, cell_type, src_lang,
    src_hash, text_fr, text_en. rows = liste de dicts."""
    p = tmp_path / name
    fieldnames = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
                  "text_fr", "text_en"]
    with p.open("w", encoding="utf-8", newline="") as fh:
        w = csv_DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        for row in rows:
            w.writerow(row)
    return p


# Petit wrapper pour éviter l'import csv en haut (juste pour les tests).
import csv as _csv


def csv_DictWriter(fh, fieldnames):
    return _csv.DictWriter(fh, fieldnames=fieldnames, quoting=_csv.QUOTE_MINIMAL,
                           lineterminator="\n")


# --------------------------------------------------------------------------
# Gate 1 — Round-trip nominal : substitutions effectives + structure préservée
# --------------------------------------------------------------------------

def test_render_substitutes_markdown_cells(tmp_path):
    """Round-trip nominal : 2 cellules markdown substituées depuis text_en."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
        {"id": "c1", "type": "code",
         "source": ["import torch"], "execution_count": 1,
         "outputs": [{"output_type": "stream", "name": "stdout", "text": ["ok"]}]},
        {"id": "m2", "type": "markdown", "source": ["## Section FR"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "aaa", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
        {"notebook": str(nb), "cell_id": "m2", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "bbb", "text_fr": "## Section FR",
         "text_en": "## Section EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out)
    # Invariant 3 (structure préservée) : nb de cellules identique.
    assert result.nb_cells_out == 3
    assert result.stats.n_md_cells == 2
    assert result.stats.n_code_cells == 1
    assert result.stats.n_translated == 2
    assert result.stats.n_fallback == 0
    # Sortie : vérifier les substitutions.
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    src_md = ["".join(c["source"]) for c in out_nb["cells"]
              if c["cell_type"] == "markdown"]
    assert src_md[0] == "# Title EN"
    assert src_md[1] == "## Section EN"


def test_render_preserves_code_byte_for_byte(tmp_path):
    """Round-trip : cellule code reste byte-identique (source + outputs + exec_count)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "code",
         "source": ["import torch\n", "x = 42\n"],
         "execution_count": 7,
         "outputs": [{"output_type": "stream", "name": "stdout",
                      "text": ["42"]}]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])  # CSV vide
    out = tmp_path / "out_en.ipynb"
    r.render(nb, csv_p, "en", out)
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    code = out_nb["cells"][0]
    assert code["source"] == ["import torch\n", "x = 42\n"]
    assert code["execution_count"] == 7
    assert code["outputs"] == [{"output_type": "stream", "name": "stdout",
                                "text": ["42"]}]


def test_render_preserves_cell_count_and_order(tmp_path):
    """Invariant 3 : count et ordre identiques à la source."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["a"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
        {"id": "m2", "type": "markdown", "source": ["b"]},
        {"id": "c2", "type": "code", "source": ["y"], "execution_count": None},
        {"id": "m3", "type": "markdown", "source": ["c"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "a", "text_en": "A"},
        {"notebook": str(nb), "cell_id": "m2", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "2", "text_fr": "b", "text_en": "B"},
        {"notebook": str(nb), "cell_id": "m3", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "3", "text_fr": "c", "text_en": "C"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out)
    assert result.nb_cells_out == 5
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    ids = [c["id"] for c in out_nb["cells"]]
    assert ids == ["m1", "c1", "m2", "c2", "m3"]


# --------------------------------------------------------------------------
# Gate 2 — Falsification 1 : CSV modifie le source code → cellule code intouchée
# --------------------------------------------------------------------------

def test_render_csv_text_en_for_code_cell_does_not_affect_code(tmp_path):
    """Le CSV ne peut pas modifier une cellule code (invariant #2 dur)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "code", "source": ["print(1)"],
         "execution_count": 5,
         "outputs": [{"output_type": "stream", "name": "stdout",
                      "text": ["1"]}]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        # Tentation : le CSV contient une "traduction" pour la cellule code.
        {"notebook": str(nb), "cell_id": "c1", "cell_type": "code",
         "src_lang": "fr", "src_hash": "x", "text_fr": "print(1)",
         "text_en": "print(2)  # SHOULD NOT BE USED"},
    ])
    out = tmp_path / "out_en.ipynb"
    r.render(nb, csv_p, "en", out)
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    code = out_nb["cells"][0]
    # Source byte-identique au FR, JAMAIS le contenu de text_en.
    assert code["source"] == ["print(1)"]
    assert "SHOULD NOT BE USED" not in "".join(code["source"])
    # Outputs et execution_count byte-identiques aussi.
    assert code["outputs"] == [{"output_type": "stream", "name": "stdout",
                                "text": ["1"]}]
    assert code["execution_count"] == 5


# --------------------------------------------------------------------------
# Gate 3 — Falsification 2 : CSV vide → tout en fallback FR, structure préservée
# --------------------------------------------------------------------------

def test_render_empty_csv_falls_back_to_fr(tmp_path):
    """Aucun texte_en dans le CSV → tous les markdown en fallback FR.
    (min_coverage=0.0 explicite : depuis #13557, 0% de couverture sans demande
    explicite est refusé par le fail-closed par défaut.)"""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
        {"id": "m2", "type": "markdown", "source": ["para"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])  # 0 lignes (pas de row, header seul)
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, min_coverage=0.0)
    assert result.stats.n_md_cells == 2
    assert result.stats.n_translated == 0
    assert result.stats.n_fallback == 2
    # Markdown conserve le texte FR exact.
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    md = [c for c in out_nb["cells"] if c["cell_type"] == "markdown"]
    assert md[0]["source"] == ["# Titre"]
    assert md[1]["source"] == ["para"]


# --------------------------------------------------------------------------
# Gate 3b — --require-translated guardrail (#10349) : refuse FR-clone renders
# --------------------------------------------------------------------------

def test_require_translated_raises_on_zero_translated(tmp_path):
    """require_translated=True + CSV vide (0 traduit) → ValueError (refus clone FR)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
        {"id": "m2", "type": "markdown", "source": ["para"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])  # 0 traduction
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="0 cellule markdown traduite"):
        r.render(nb, csv_p, "en", out, require_translated=True)


def test_require_translated_writes_no_file_on_refusal(tmp_path):
    """Le guardrail leve AVANT l'ecriture atomique : aucun fichier clone sur disque."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError):
        r.render(nb, csv_p, "en", out, require_translated=True)
    assert not out.exists()  # aucun clone FR ecrit


def test_require_translated_passes_when_cells_translated(tmp_path):
    """require_translated=True + CSV rempli (>=1 traduit) → rendu normal, pas d'erreur."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "a", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, require_translated=True)
    assert result.stats.n_translated == 1
    assert out.exists()  # rendu normal ecrit


def test_require_translated_noop_when_no_markdown_cells(tmp_path):
    """Notebook sans markdown (0 cellule traduisible) → guardrail se tait (pas de clone possible)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "code", "source": ["print(1)"], "execution_count": None},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    out = tmp_path / "out_en.ipynb"
    # Pas de raise : n_md_cells == 0, le guardrail ne s'applique pas.
    result = r.render(nb, csv_p, "en", out, require_translated=True)
    assert result.stats.n_md_cells == 0
    assert out.exists()


def test_default_render_preserves_criterion3_fr_placeholder(tmp_path):
    """Sans require_translated (defaut) → 0 traduit produit un clone FR (critere 3 #10039).
    Depuis #13557 la couverture 0% exige un min_coverage=0.0 explicite : le
    placeholder FR reste atteignable, mais declare."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])  # 0 traduction
    out = tmp_path / "out_en.ipynb"
    # defaut require_translated=False ; couverture partielle explicite.
    result = r.render(nb, csv_p, "en", out, min_coverage=0.0)
    assert result.stats.n_translated == 0
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    assert out_nb["cells"][0]["source"] == ["# Titre FR"]  # placeholder FR, pas d'erreur


def test_main_require_translated_returns_exit_2(tmp_path):
    """main() avec --require-translated + CSV vide → exit code 2 (ValueError catche)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    out = tmp_path / "out_en.ipynb"
    rc = r.main([
        "--csv", str(csv_p), "--notebook", str(nb),
        "--lang", "en", "--out", str(out), "--require-translated",
    ])
    assert rc == 2
    assert not out.exists()  # aucun clone FR ecrit


def test_render_partial_csv_translates_only_present_cells(tmp_path):
    """Cellule absente du CSV → fallback FR (jamais blank, jamais placeholder).
    (min_coverage=0.5 explicite : la couverture 50% serait refusee par defaut.)"""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
        {"id": "m2", "type": "markdown", "source": ["## Section FR"]},
    ])
    # CSV : SEUL m1 est traduit. m2 absent.
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "a", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, min_coverage=0.5)
    assert result.stats.n_translated == 1
    assert result.stats.n_fallback == 1
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    md = [c for c in out_nb["cells"] if c["cell_type"] == "markdown"]
    assert md[0]["source"] == ["# Title EN"]
    assert md[1]["source"] == ["## Section FR"]  # fallback, pas blanc


# --------------------------------------------------------------------------
# Gate 4 — Orphelines : CSV a une clé absente du notebook → capturée + non-crash
# --------------------------------------------------------------------------



# --------------------------------------------------------------------------
# Gate 5 — --dry-run : aucun fichier écrit, stats toujours calculées
# --------------------------------------------------------------------------

def test_render_dry_run_writes_nothing(tmp_path):
    """--dry-run : pas de fichier, mais stats cohérentes."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# Titre",
         "text_en": "# Title"},
    ])
    out = tmp_path / "out_en.ipynb"
    # Le caller passe dry_run=True mais le path est fourni pour les stats.
    result = r.render(nb, csv_p, "en", out, dry_run=True)
    assert result.out_path is None  # pas d'écriture
    assert not out.exists()  # preuve disque
    # Mais les stats sont calculées quand même.
    assert result.stats.n_md_cells == 1
    assert result.stats.n_translated == 1
    assert result.stats.n_code_cells == 1



# --------------------------------------------------------------------------
# Gate 6 — Déterminisme : deux exécutions successives → output byte-identique
# --------------------------------------------------------------------------

def test_render_deterministic_byte_identical_output(tmp_path):
    """Deux appels avec mêmes inputs → outputs byte-identiques."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# H"]},
        {"id": "c1", "type": "code",
         "source": ["print('ok')"], "execution_count": 1,
         "outputs": [{"output_type": "stream", "name": "stdout",
                      "text": ["ok"]}]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# H", "text_en": "# H EN"},
    ])
    out_a = tmp_path / "a_en.ipynb"
    out_b = tmp_path / "b_en.ipynb"
    r.render(nb, csv_p, "en", out_a)
    r.render(nb, csv_p, "en", out_b)
    assert out_a.read_bytes() == out_b.read_bytes()


def test_render_atomic_write_no_tmp_leftover(tmp_path):
    """Écriture atomique : pas de .tmp restant après succès."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    r.render(nb, csv_p, "en", out)
    tmp = out.with_suffix(out.suffix + ".tmp")
    assert out.exists()
    assert not tmp.exists()


# --------------------------------------------------------------------------
# Tests d'erreur explicites (FileNotFoundError, ValueError)
# --------------------------------------------------------------------------

def test_render_missing_notebook_raises(tmp_path):
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    with pytest.raises(FileNotFoundError):
        r.render(tmp_path / "absent.ipynb", csv_p, "en", tmp_path / "out.ipynb")


def test_render_missing_csv_raises(tmp_path):
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    with pytest.raises(FileNotFoundError):
        r.render(nb, tmp_path / "absent.csv", "en", tmp_path / "out.ipynb")


def test_render_csv_without_lang_col_raises(tmp_path):
    """CSV sans colonne text_<lang> → ValueError explicite."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = tmp_path / "no_en_col.csv"
    csv_p.write_text("notebook,cell_id,text_fr\nnb.ipynb,m1,fr only\n",
                     encoding="utf-8")
    with pytest.raises(ValueError, match="text_en"):
        r.render(nb, csv_p, "en", tmp_path / "out.ipynb")


# --------------------------------------------------------------------------
# #13546 (supersede par #13544 §3) : --fail-on-stale est un no-op deprecie --
# le refus orphelin est inconditionnel. Les tests ci-dessous verifient que le
# flag reste accepte (compat translation-sync.yml) et que le contrat est
# strictement plus fort qu'en #13546 : refus AVANT ecriture, sans sidecar.
# --------------------------------------------------------------------------

def test_render_fail_on_stale_raises_and_writes_nothing(tmp_path):
    """Orphelins -> ValueError AVANT toute ecriture, meme via le flag deprecie."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
        # ligne orpheline : cell_id absent du notebook (cellule supprimee)
        {"notebook": str(nb), "cell_id": "gone1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "2", "text_fr": "y", "text_en": "Y"},
    ])
    out = tmp_path / "out_en.ipynb"
    # Le flag est accepte (kwargs API + CLI) mais le refus vient de la gate
    # inconditionnelle : le message est celui de la gate, pas du flag.
    with pytest.raises(ValueError, match=r"orphelin\(s\) CSV : 1 cle\(s\) sans cellule"):
        r.render(nb, csv_p, "en", out, fail_on_stale=True)
    assert not out.exists()
    assert not out.with_suffix(out.suffix + ".stale").exists()


def test_render_fail_on_stale_passes_when_no_orphan(tmp_path):
    """Flag deprecie sans orphelin -> rendu normal, .stale absent."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    res = r.render(nb, csv_p, "en", out, fail_on_stale=True)
    assert out.exists()
    assert res.stats.n_orphan_keys == 0
    assert not out.with_suffix(out.suffix + ".stale").exists()


def test_render_dry_run_requires_out_path(tmp_path):
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    with pytest.raises(ValueError, match="--dry-run"):
        r.render(nb, csv_p, "en", None, dry_run=True)


# --------------------------------------------------------------------------
# Bonus : n_byte_identical comptabilise les traductions identiques au FR
# --------------------------------------------------------------------------

def test_render_counts_byte_identical_translations(tmp_path):
    """Si text_en == text_fr (ex. nom propre, nombre), compteur ++."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["FT-01"]},
        {"id": "m2", "type": "markdown", "source": ["# Titre FR"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "FT-01", "text_en": "FT-01"},
        {"notebook": str(nb), "cell_id": "m2", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "2", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out)
    assert result.stats.n_translated == 2
    assert result.stats.n_byte_identical == 1  # m1 : FT-01 == FT-01


# --------------------------------------------------------------------------
# diff_summary — utilitaire de spot-check
# --------------------------------------------------------------------------

def test_diff_summary_returns_no_diff_when_all_fallback(tmp_path):
    """CSV vide → output = source → diff_summary dit 'no markdown diffs'."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# A"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    out = tmp_path / "out_en.ipynb"
    r.render(nb, csv_p, "en", out, min_coverage=0.0)
    diff = r.diff_summary(nb, out, "en")
    assert diff == "(no markdown diffs)"


def test_diff_summary_returns_diff_when_substituted(tmp_path):
    """Avec substitutions effectives → diff_summary non vide."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    r.render(nb, csv_p, "en", out)
    diff = r.diff_summary(nb, out, "en")
    assert "Titre FR" in diff and "Title EN" in diff


# --------------------------------------------------------------------------
# Gate 7 — #13544 §3 — fail-closed par défaut (inversion preflight #13557)
# --------------------------------------------------------------------------

def test_default_render_refuses_orphans_no_artifact(tmp_path):
    """#13544 §3 — SANS aucun flag, un CSV avec orphelines est REFUSÉ.
    Le sidecar .stale a disparu avec l'opt-in : la correction est le CSV,
    pas une option."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# A"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# A", "text_en": "# A EN"},
        # 2 orphelines.
        {"notebook": str(nb), "cell_id": "ghost1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "x", "text_fr": "g1", "text_en": "G1"},
        {"notebook": str(nb), "cell_id": "ghost2", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "y", "text_fr": "g2", "text_en": "G2"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="orphelin"):
        r.render(nb, csv_p, "en", out)
    assert not out.exists()
    assert not out.with_suffix(out.suffix + ".stale").exists()


def test_default_render_refuses_sub_coverage(tmp_path):
    """#13544 §3 — SANS flag, le seuil par défaut (1.0) refuse une couverture
    partielle. Le rendu partiel doit être explicitement demandé."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
        {"id": "m2", "type": "markdown", "source": ["## Section FR"]},
        {"id": "m3", "type": "markdown", "source": ["para"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
    ])
    # CSV : SEUL m1 est traduit (1/3 = 33% de couverture markdown).
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="--min-coverage"):
        r.render(nb, csv_p, "en", out)
    assert not out.exists()


def test_explicit_partial_coverage_accepted(tmp_path):
    """#13544 §2 — couverture partielle EXPLICITE : --min-coverage 0.3 + 33%
    de couverture → rendu écrit, fallbacks FR assumés et comptés."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre FR"]},
        {"id": "m2", "type": "markdown", "source": ["## Section FR"]},
        {"id": "m3", "type": "markdown", "source": ["para"]},
        {"id": "c1", "type": "code", "source": ["x"], "execution_count": None},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# Titre FR",
         "text_en": "# Title EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, min_coverage=0.3)
    assert result.stats.n_translated == 1
    assert result.stats.n_fallback == 2
    assert out.exists()
    out_nb = json.loads(out.read_text(encoding="utf-8"))
    md = [c for c in out_nb["cells"] if c["cell_type"] == "markdown"]
    assert md[0]["source"] == ["# Title EN"]
    assert md[1]["source"] == ["## Section FR"]  # fallback FR assumé, déclaré
    assert md[2]["source"] == ["para"]


# --------------------------------------------------------------------------
# Gate 8 — #13544 §3 — refus dur (seuil explicite, bornes)
# --------------------------------------------------------------------------

def test_min_coverage_refuses_below_threshold(tmp_path):
    """min_coverage=0.8 + couverture 1/3 (33%) → ValueError."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# Titre"]},
        {"id": "m2", "type": "markdown", "source": ["## Section"]},
        {"id": "m3", "type": "markdown", "source": ["para"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# Titre",
         "text_en": "# Title"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="--min-coverage"):
        r.render(nb, csv_p, "en", out, min_coverage=0.8)
    assert not out.exists()  # refus dur AVANT ecriture


def test_min_coverage_writes_no_file_on_refusal(tmp_path):
    """Le refus min_coverage leve AVANT l'ecriture atomique : aucun clone
    sous le seuil ne doit atteindre le disque."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    # Couverture 1/2 = 50% < 0.8 → refuse.
    with pytest.raises(ValueError):
        r.render(nb, csv_p, "en", out, min_coverage=0.8)
    assert not out.exists()
    assert not out.with_suffix(out.suffix + ".stale").exists()


def test_min_coverage_passes_when_at_or_above_threshold(tmp_path):
    """min_coverage=0.5 + couverture 1/2 (50%) → passe."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, min_coverage=0.5)
    assert result.stats.n_translated == 1
    assert result.stats.n_fallback == 1
    assert out.exists()


def test_full_coverage_passes_with_default_threshold(tmp_path):
    """Défaut 1.0 + couverture complète (2/2) → passe sans aucun flag :
    le chemin sain de main n'est pas pénalisé par le fail-closed."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
        {"notebook": str(nb), "cell_id": "m2", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "2", "text_fr": "y", "text_en": "Y"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out)
    assert result.stats.n_fallback == 0
    assert result.stats.n_orphan_keys == 0
    assert out.exists()


def test_min_coverage_bypassed_when_no_markdown_cells(tmp_path):
    """Notebook sans markdown (0 cellule traduisible) → min_coverage se tait
    (couverture traitée comme 1.0, pas de défaut à enforce)."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "code", "source": ["print(1)"],
         "execution_count": None},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out, min_coverage=0.99)
    assert result.stats.n_md_cells == 0
    assert out.exists()


def test_min_coverage_rejects_out_of_range(tmp_path):
    """min_coverage hors [0.0, 1.0] → ValueError explicite, fichier non ecrit."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    for bad in (-0.1, 1.1, 2.0):
        with pytest.raises(ValueError, match="--min-coverage"):
            r.render(nb, csv_p, "en", out, min_coverage=bad)
        assert not out.exists()


# --------------------------------------------------------------------------
# Gate 9 — #13544 §3 — orphelins inconditionnels (plus d'opt-in)
# --------------------------------------------------------------------------

def test_orphans_refused_unconditionally(tmp_path):
    """1 orpheline, AUCUN flag → ValueError : rien ne désactive ce refus."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# A"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# A", "text_en": "# A EN"},
        {"notebook": str(nb), "cell_id": "ORPHAN", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "x", "text_fr": "fantome",
         "text_en": "ghost"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="orphelin"):
        r.render(nb, csv_p, "en", out)
    assert not out.exists()


def test_orphans_refused_even_with_lowered_coverage(tmp_path):
    """Abaisser --min-coverage ne rachète pas les orphelins : les deux gates
    sont indépendantes, aucune n'est l'échappatoire de l'autre."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
        {"notebook": str(nb), "cell_id": "ghost", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "y", "text_fr": "g", "text_en": "G"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="orphelin"):
        r.render(nb, csv_p, "en", out, min_coverage=0.0)
    assert not out.exists()


def test_no_orphans_renders_normally(tmp_path):
    """0 orpheline + couverture complète (défaut 1.0) → rendu normal."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["# A"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "# A", "text_en": "# A EN"},
    ])
    out = tmp_path / "out_en.ipynb"
    result = r.render(nb, csv_p, "en", out)
    assert result.stats.n_orphan_keys == 0
    assert out.exists()


def test_min_coverage_refusal_precedes_orphan_report(tmp_path):
    """Deux défauts à la fois : à seuil exigeant le refus couverture arrive
    en premier ; à seuil abaissé c'est l'orphelin qui refuse — chacun des
    deux défects est nommé selon la configuration."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        # Couverture 1/2 = 50% < 0.8.
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
        # Et 1 orpheline.
        {"notebook": str(nb), "cell_id": "ghost", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "y", "text_fr": "g", "text_en": "G"},
    ])
    out = tmp_path / "out_en.ipynb"
    with pytest.raises(ValueError, match="--min-coverage"):
        r.render(nb, csv_p, "en", out, min_coverage=0.8)
    assert not out.exists()
    with pytest.raises(ValueError, match="orphelin"):
        r.render(nb, csv_p, "en", out, min_coverage=0.3)
    assert not out.exists()


# --------------------------------------------------------------------------
# Gate 10 — CLI : exit codes du fail-closed
# --------------------------------------------------------------------------

def test_main_min_coverage_refuses_returns_exit_2(tmp_path):
    """main() avec --min-coverage + sous-couverture → exit code 2."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    rc = r.main([
        "--csv", str(csv_p), "--notebook", str(nb),
        "--lang", "en", "--out", str(out), "--min-coverage", "0.8",
    ])
    assert rc == 2
    assert not out.exists()


def test_main_default_refuses_sub_coverage_exit_2(tmp_path):
    """main() SANS flags + sous-couverture → exit 2 : le défaut est
    fail-closed, le refus ne dépend plus d'un flag oublié."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
        {"id": "m2", "type": "markdown", "source": ["y"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
    ])
    out = tmp_path / "out_en.ipynb"
    rc = r.main([
        "--csv", str(csv_p), "--notebook", str(nb),
        "--lang", "en", "--out", str(out),
    ])
    assert rc == 2
    assert not out.exists()


def test_main_orphans_refused_returns_exit_2(tmp_path):
    """main() SANS flags + orpheline → exit 2."""
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "m1", "type": "markdown", "source": ["x"]},
    ])
    csv_p = _write_csv(tmp_path, "tr.csv", [
        {"notebook": str(nb), "cell_id": "m1", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "1", "text_fr": "x", "text_en": "X"},
        {"notebook": str(nb), "cell_id": "ghost", "cell_type": "markdown",
         "src_lang": "fr", "src_hash": "y", "text_fr": "g", "text_en": "G"},
    ])
    out = tmp_path / "out_en.ipynb"
    rc = r.main([
        "--csv", str(csv_p), "--notebook", str(nb),
        "--lang", "en", "--out", str(out),
    ])
    assert rc == 2
    assert not out.exists()
