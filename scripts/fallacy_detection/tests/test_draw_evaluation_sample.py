#!/usr/bin/env python3
"""Tests du tirage d'echantillon d'evaluation humaine (#20222, critere 1).

Couvre : determinisme graine, bornes de stratification, regle d'unite
(texte x noeud, dedup), exclusions par conception, exclusion NOT_FOUND,
integrite de la table de rollup contre le CSV d'alignement.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "scripts/fallacy_detection/draw_evaluation_sample.py"
ALIGNMENT_CSV = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic/logic_mafalda_to_argumentum.csv"


def _load_module():
    spec = importlib.util.spec_from_file_location("draw_evaluation_sample", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    sys.modules.setdefault("draw_evaluation_sample", mod)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def mod():
    return _load_module()


@pytest.fixture(scope="module")
def population(mod):
    pairs, _unjoinable, _unaligned = mod.build_pairs(mod.load_alignment())
    return pairs


def test_rollup_joinable_complet(mod):
    """Apres la correction case-insensitive + 'ad hominem', aucun libelle du
    corpus ne reste hors la table (les exclusions par conception mises a part).
    """
    _, unjoinable, _ = mod.build_pairs(mod.load_alignment())
    inattendus = {l for l in unjoinable if l not in mod.PAPER_L2_SANS_INVENTAIRE}
    assert not inattendus, f"libelles non joinables hors papier-L2 : {inattendus}"


def test_rollup_vers_csv(population, mod):
    """Chaque cible d'inventaire de la table de rollup existe dans le CSV
    d'alignement (aucune cle morte)."""
    import csv
    with open(ALIGNMENT_CSV, encoding="utf-8") as f:
        labels = {r["academic_label"] for r in csv.DictReader(f)}
    for _corpus, (inv, _src) in mod.CORPUS_TO_INVENTORY.items():
        assert inv in labels, f"{inv!r} absent du CSV d'alignement"


def test_unite_texte_noeud(population):
    """Une paire par (texte, noeud) : pas de doublon."""
    seen = [(p["source_file"], p["line_index"], p["node"]) for p in population]
    assert len(seen) == len(set(seen))


def test_exclusions_par_conception(population, mod):
    """'nothing' et 'to clean' ne produisent jamais de paire."""
    assert "nothing" in mod.EXCLUDED_LABELS and "to clean" in mod.EXCLUDED_LABELS
    assert all(p["corpus_label"] not in mod.EXCLUDED_LABELS for p in population)


def test_tirage_deterministe(mod, tmp_path):
    """Meme graine -> meme empreinte SHA-256 (protocole, critere 1)."""
    shas = []
    for i in range(2):
        sample = tmp_path / f"s{i}.jsonl"
        manifest = tmp_path / f"m{i}.json"
        rc = mod.main(["--seed", "7", "--out-sample", str(sample),
                       "--out-manifest", str(manifest)])
        assert rc == 0
        shas.append(json.loads(manifest.read_text(encoding="utf-8"))["echantillon_sha256"])
    assert shas[0] == shas[1]


def test_tirage_bornes_et_not_found(mod, tmp_path):
    """200 paires, plancher par famille tenu (population suffisante), et
    AUCUNE paire NOT_FOUND : leur etiquette n'est pas retrouvable par
    construction."""
    sample = tmp_path / "s.jsonl"
    manifest = tmp_path / "m.json"
    assert mod.main(["--seed", "42", "--out-sample", str(sample),
                     "--out-manifest", str(manifest)]) == 0
    rows = [json.loads(l) for l in sample.read_text(encoding="utf-8").splitlines()]
    m = json.loads(manifest.read_text(encoding="utf-8"))
    assert len(rows) == 200 == m["echantillon_taille"]
    familles = Counter(r["family"] for r in rows)
    for fam, n in familles.items():
        assert n >= 10, f"famille {fam} sous plancher : {n}"
    assert all(r["verdict"] in ("DIRECT", "PARTIAL") for r in rows)


def test_tirage_synthetic_bornes_serreess(mod):
    """Sur une population synthetique, une famille sous le plancher est prise
    en entier et la borne est signalee, jamais maquillee."""
    tiny = [
        {"source_file": "a.jsonl", "line_index": i, "corpus_label": "x",
         "inventory_label": "X", "node": f"n{i}", "family": "F",
         "verdict": "DIRECT"}
        for i in range(4)
    ]
    picked = mod.stratified_draw(tiny, seed=1, total=10, floor=10)
    assert len(picked) == 4  # toute la population, plancher inatteignable
