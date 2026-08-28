#!/usr/bin/env python3
"""Drift mode de scan_md_hierarchy (#11831) -- baseline per-notebook, delta>0 = flag.

Cas fondateur : PR #11823 a ajoute 6 headings-in-list dans un notebook ; le scan
census rendait `0/1 flagged` AVANT la regle (reglee par #11929), mais meme avec
la regle, une PR qui AMELIORORAIT un autre notebook aurait pu compenser au net.
Le drift gate est PER-NOTEBOOK : un delta>0 sur un (notebook, kind) est flagge
quels que soient les burndowns ailleurs -- le fix et le defaut sont deux reviews
differentes (acceptance #11831 : "PR qui AUGMENTE le compte => CHANGES_REQUESTED").

Contrat d'exit codes du mode diff (#11831) :
  0 = tout delta <= 0 (burndown pur, OK) ;
  2 = au moins un delta > 0 (regression) ;
  1 = entree cassee (baseline illisible, scan vacuous).

Ces tests ECHOIENT sur le RED d'avant le fix : argparse rejetait --baseline /
--diff (SystemExit 2), le mode n'existait pas.

Run:
    pytest scripts/notebook_tools/tests/test_scan_md_hierarchy_drift.py
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import scan_md_hierarchy as smh  # noqa: E402


# --- fixtures -----------------------------------------------------------------

def _nb(cells_md: list[str]) -> dict:
    return {
        "cells": [{"cell_type": "markdown", "source": [s],
                   "metadata": {}} for s in cells_md],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }


# Un notebook sain + un notebook a 2 findings connus :
#   HINT-AS-HEADING : heading nu `# Indice` (le stem hint sans titre).
#   HEADING-IN-LIST : `- # Astuce` (heading dans un item de liste, #11929).
CLEAN_CELLS = ["# Titre", "## Section", "Prose simple."]
FLAGGED_CELLS = ["# Titre", "# Indice", "- # Astuce de debug"]


def _corpus(tmp_path: Path) -> Path:
    """Corpus EN PLACE : les variants mutent les memes fichiers du meme
    repertoire (les cles de baseline dependent du chemin -- un corpus parallel
    dans un autre tmp matcherait jamais la baseline seeed)."""
    root = tmp_path / "corpus"
    root.mkdir(parents=True)
    (root / "clean.ipynb").write_text(
        json.dumps(_nb(CLEAN_CELLS), ensure_ascii=False), encoding="utf-8")
    (root / "flagged.ipynb").write_text(
        json.dumps(_nb(FLAGGED_CELLS), ensure_ascii=False), encoding="utf-8")
    return root


def _mutate(root: Path, name: str, cells: list[str]) -> None:
    (root / name).write_text(
        json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")


WORSE = FLAGGED_CELLS + ["- # Note importante", "## Astuce"]  # +1 IN-LIST, +1 HINT


def _key(root: Path, name: str) -> str:
    return smh.notebook_key(root / name)


def _seed_baseline(tmp_path: Path, root: Path) -> Path:
    bl = tmp_path / "md_hierarchy_baseline.json"
    counts = smh.compute_counts([str(root)])
    assert counts, "fixture cassée : le corpus doit produire des findings"
    smh.write_baseline(bl, counts)
    return bl


def _diff(root: Path, baseline: Path):
    """main() in-process sur le mode diff ; rend (rc, stdout+stderr capturés via capsys
    non disponible ici -- on capture par return value de main seulement)."""
    return smh.main([str(root), "--baseline", str(baseline), "--diff"])


# --- 1. compute_counts / write / load roundtrip -------------------------------

def test_compute_counts_aggregates_per_kind(tmp_path):
    root = _corpus(tmp_path)
    counts = smh.compute_counts([str(root)])
    entry = counts[_key(root, "flagged.ipynb")]
    assert entry.get("HINT-AS-HEADING") == 1
    assert entry.get("HEADING-IN-LIST") == 1
    assert _key(root, "clean.ipynb") not in counts  # 0 finding -> pas d'entree


def test_write_then_load_baseline_roundtrip(tmp_path):
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    loaded = smh.load_baseline(bl)
    assert loaded == smh.compute_counts([str(root)])
    # determinisme : deux ecritures avec la MÊME date PINNEE = bytes identiques
    # (une auto-timestamp rendrait deux writes non-reproductibles)
    smh.write_baseline(bl, smh.compute_counts([str(root)]),
                       generated_at="2026-08-24T00:00:00Z")
    first = bl.read_bytes()
    smh.write_baseline(bl, smh.compute_counts([str(root)]),
                       generated_at="2026-08-24T00:00:00Z")
    assert bl.read_bytes() == first
    # la date est bien dans la sortie (acceptance #12735)
    assert smh.baseline_generated_at(bl) == "2026-08-24T00:00:00Z"


def test_load_baseline_rejects_foreign_format(tmp_path):
    bad = tmp_path / "bad.json"
    bad.write_text('{"count": 1538, "hashes": []}', encoding="utf-8")
    with pytest.raises(ValueError):
        smh.load_baseline(bad)


# --- 2. le contrat d'exit codes du mode diff -----------------------------------

def test_no_drift_exits_0(tmp_path, capsys):
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    assert _diff(root, bl) == 0
    assert "drift: +0" in capsys.readouterr().out


def test_regression_exits_2_and_names_the_notebook(tmp_path, capsys):
    """LE falsifieur #11831 : un notebook qui gagne un finding -> exit 2."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", WORSE)
    assert _diff(root, bl) == 2
    out = capsys.readouterr().out
    assert "+1 HEADING-IN-LIST" in out
    assert "+1 HINT-AS-HEADING" in out
    assert "flagged.ipynb" in out


def test_burndown_only_exits_0_and_reports_improvement(tmp_path, capsys):
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", CLEAN_CELLS)  # tous les findings disparus
    assert _diff(root, bl) == 0
    out = capsys.readouterr().out
    assert "-1 HINT-AS-HEADING" in out and "(burndown)" in out


def test_new_defect_not_offset_by_fix_elsewhere(tmp_path, capsys):
    """Per-notebook, PAS net : fixer les 2 findings de flagged.ipynb ne rachete
    pas un +1 ailleurs -- le notebook avec le defaut neuf reste nomme."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", CLEAN_CELLS)  # 4 findings brules
    _mutate(root, "clean.ipynb", CLEAN_CELLS + ["# Indice supplementaire"])
    assert _diff(root, bl) == 2
    out = capsys.readouterr().out
    assert "clean.ipynb" in out and "+1 HINT-AS-HEADING" in out


def test_new_notebook_with_findings_is_regression(tmp_path, capsys):
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "fresh.ipynb", ["# Titre", "- # Note"])
    assert _diff(root, bl) == 2
    assert "fresh.ipynb" in capsys.readouterr().out


def test_unreadable_baseline_exits_1(tmp_path, capsys):
    root = _corpus(tmp_path)
    bl = tmp_path / "missing.json"
    assert _diff(root, bl) == 1
    assert "unreadable baseline" in capsys.readouterr().err


def test_vacuous_scan_in_diff_mode_exits_1(tmp_path, capsys):
    empty = tmp_path / "empty"
    empty.mkdir()
    bl = tmp_path / "bl.json"
    smh.write_baseline(bl, {})
    assert _diff(empty, bl) == 1  # pas de 0/0 muet, meme en drift


def test_clean_corpus_against_empty_baseline_exits_0(tmp_path):
    """Un corpus tout propre + baseline vide de findings = burndown stable, OK.
    (counts vide EST legitime -- la distinction vacuous se joue sur le nombre
    de notebooks designes, pas sur le nombre de findings.)"""
    cleanonly = tmp_path / "co"
    cleanonly.mkdir()
    (cleanonly / "clean.ipynb").write_text(
        json.dumps(_nb(CLEAN_CELLS), ensure_ascii=False), encoding="utf-8")
    bl = tmp_path / "bl.json"
    smh.write_baseline(bl, {})
    assert _diff(cleanonly, bl) == 0


# --- 3. garde structurel CLI ----------------------------------------------------

def test_baseline_without_action_is_error():
    with pytest.raises(SystemExit):
        smh.main(["whatever", "--baseline"])


def test_update_baseline_then_diff_is_green(tmp_path, capsys):
    """Le workflow de re-seed : --update-baseline ecrit, le diff qui suit
    rend 0 (auto-coherence scanner/baseline au meme commit)."""
    root = _corpus(tmp_path)
    _mutate(root, "flagged.ipynb", WORSE)
    bl = tmp_path / "bl.json"
    rc = smh.main([str(root), "--baseline", str(bl), "--update-baseline"])
    assert rc == 0
    assert "baseline updated" in capsys.readouterr().out
    assert _diff(root, bl) == 0


# --- 4. #12735 : veredict sur le NET intra-notebook, pas sur le +kind ---------

def test_within_notebook_migration_is_net_NOT_a_regression(tmp_path, capsys):
    """Cas PT_11 (#12735) : le meme notebook  migre d'une classe a l'autre
    (+1 HINT, -1 IN-LIST). Le verdict est le NET (0 ici), pas le '+1 HINT'.
    Un +1/-1 sur le meme fichier = burndown potentiel, jamais une regression."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)  # flagged.ipynb : {HINT:1, IN-LIST:1}
    _mutate(root, "flagged.ipynb", ["# Titre", "# Indice", "## Astuce"])
    rc = _diff(root, bl)
    assert rc == 0  # net 0 -> pas de regression a attribuer
    out = capsys.readouterr().out
    assert "(mixed, net 0)" in out
    assert "+1 HINT-AS-HEADING" in out  # le delta kind EST informe


def test_within_notebook_burndown_not_a_regression(tmp_path, capsys):
    """PT_11 (net -8) : le notebook GUERIT (IN-LIST tombe) mais garde un hint.
    Net negatif = burndown, exit 0. JAMAIS de '+1 nouveau defaut'."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", ["# Titre", "# Indice"])  # drop l'IN-LIST
    rc = _diff(root, bl)
    assert rc == 0
    out = capsys.readouterr().out
    assert "(burndown)" in out
    assert "-1 HEADING-IN-LIST" in out
    assert "+1" not in out.split("\n")[0]  # la ligne verdict n'est pas une augmentation


# --- 5. #12735 : attribution PR-scopee (--name-status) ------------------------

def _ns(tmp_path, *lines):
    p = tmp_path / "ns.txt"
    p.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return str(p)


def test_pr_scope_ignores_regression_outside_pr(tmp_path, capsys):
    """La CI scanne le CORPUS entier, pas le diff de la PR (#11831 invariant casse
    par #12735). Avec --name-status, un notebook qui a empiré mais N'EST PAS dans
    la PR ne doit PAS etre impute a cette PR."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", WORSE)  # +2, mais hors diff PR
    ns = _ns(tmp_path, f"M\t{_key(root, 'clean.ipynb')}")  # PR ne touche que clean
    assert smh.main([str(root), "--baseline", str(bl), "--diff", "--name-status", ns]) == 0
    out = capsys.readouterr().out
    assert "flagged.ipynb" not in out


def test_pr_scope_flags_regression_inside_pr(tmp_path, capsys):
    """Controle positif : une PR qui TOUCHE un notebook et y introduit des defauts
    est detectee, nommee, exit 2 (le garde redevient parlant)."""
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)
    _mutate(root, "flagged.ipynb", WORSE)  # +2, dans la PR
    ns = _ns(tmp_path, f"M\t{_key(root, 'flagged.ipynb')}")
    assert smh.main([str(root), "--baseline", str(bl), "--diff", "--name-status", ns]) == 2
    out = capsys.readouterr().out
    assert "flagged.ipynb" in out
    assert "+2" in out


def test_rename_resolution_no_phantom(tmp_path, capsys):
    """Zero-pad phantom (#12735) : baseline '4b.ipynb', PR renomme en '04b.ipynb'
    (git -M -> R100 old new). Le renommage resout l'entree baseline -> delta 0,
    pas de '+1' fantome."""
    root = _corpus(tmp_path)
    _mutate(root, "old.ipynb", ["# Titre", "# Indice"])  # {HINT:1}
    bl = _seed_baseline(tmp_path, root)
    old_key = _key(root, "old.ipynb")
    _mutate(root, "new.ipynb", ["# Titre", "# Indice"])  # meme contenu, 1 HINT
    new_key = _key(root, "new.ipynb")
    (root / "old.ipynb").unlink()
    ns = _ns(tmp_path, f"R100\t{old_key}\t{new_key}")
    assert smh.main([str(root), "--baseline", str(bl), "--diff", "--name-status", ns]) == 0
    out = capsys.readouterr().out
    assert "drift: +0" in out
    assert "+1" not in out


# --- 6. #12735 : baseline datee dans le rapport -------------------------------

def test_baseline_date_in_report(tmp_path, capsys):
    root = _corpus(tmp_path)
    bl = _seed_baseline(tmp_path, root)  # date "now"
    smh.write_baseline(bl, smh.compute_counts([str(root)]), generated_at="2026-08-24T00:00:00Z")
    _diff(root, bl)
    out = capsys.readouterr().out
    assert "generated 2026-08-24T00:00:00Z" in out
