#!/usr/bin/env python3
"""Tests du tirage d'echantillon d'evaluation humaine (#20222, critere 1).

Depuis l'unification des populations : le tirage lit ``aligned_corpus.jsonl``
(l'artefait de reference produit par ``build_aligned_eval_corpus.py``) au lieu
de reconstruire le join. Le test cle epingle ``population ==
len(aligned_corpus.jsonl)`` -- sans lui, la derive deux-populations (257
contre 257 attendues vs 225 reelles, regles d'exclusion divergentes) revient
au prochain ajout de regle cote builder.

Couvre : epingle de population, determinisme graine, bornes de stratification,
unicite (texte x noeud, heritee du builder), absence de texte verbatim dans
les sorties (licence CC-BY-SA sous NOTICE), exclusions amont atteintes, lookup
verdict par identifiant d'artefact (exact + pont, insensible a la casse).
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
CORPUS = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic/aligned/aligned_corpus.jsonl"


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
    return mod.load_pairs(mod.ALIGNED_CORPUS, mod.load_alignment())


def test_population_egale_corpus_aligne(mod, population):
    """L'EPOINGLE : la population du tirage EST le corpus aligne commis --
    une ligne d'artefait, une paire. Si ce compte diverge, une seconde
    implementation du join est nee quelque part."""
    n_lignes = sum(1 for _ in CORPUS.open(encoding="utf-8"))
    assert len(population) == n_lignes


def test_aucun_texte_dans_les_sorties(mod, population, tmp_path):
    """Le texte verbatim (CC-BY-SA, sous NOTICE) ne sort JAMAIS du tirage :
    les paires ne portent que des references, l'echantillon non plus."""
    assert all("text" not in p for p in population)
    sample = tmp_path / "s.jsonl"
    manifest = tmp_path / "m.json"
    assert mod.main(["--seed", "42", "--out-sample", str(sample),
                     "--out-manifest", str(manifest)]) == 0
    # Un fragment distinctif du premier enregistrement du corpus ne doit se
    # retrouver nulle part dans l'echantillon.
    first_text = json.loads(CORPUS.open(encoding="utf-8").readline())["text"]
    fragment = first_text[:40]
    contenu = sample.read_text(encoding="utf-8")
    assert fragment not in contenu
    for line in contenu.splitlines():
        assert "text" not in json.loads(line)


def test_unite_texte_noeud_artefact():
    """Une paire par (TEXTE, noeud) -- la dedup est garantie a l'emission par
    le builder, au niveau du span. Témoin : (texte, noeud) unique dans
    l'artefact. NB (ligne gold, noeud) peut legitimement se repeter : deux
    spans d'un meme enregistrement peuvent porter le meme libelle (fragments
    distincts, memes noeud et ligne) -- 10 cas mesures sur les 225 paires."""
    seen = []
    for line in CORPUS.open(encoding="utf-8"):
        rec = json.loads(line)
        seen.append((rec["text"], rec["node"]))
    assert len(seen) == len(set(seen))


def test_exclusions_amont():
    """Les exclusions par conception du builder atteignent l'artefait : aucun
    libelle exclu ('nothing', 'to clean', L2 sans inventaire) n'y figure."""
    exclus = {"nothing", "to clean", "appeal to worse problems", "false dilemma"}
    labels = {json.loads(l)["source_label"].lower()
              for l in CORPUS.open(encoding="utf-8")}
    assert not (labels & exclus)


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


def test_lookup_verdict_insensible_casse_et_ponts(mod, tmp_path):
    """Le verdict est retrouve dans la table par l'identifiant que l'artefact
    porte : source_label pour 'exact' (casse quelconque), cible du pont pour
    'bridge:<L2>'. Aucune reimplementation des regles du builder."""
    corpus = tmp_path / "aligned_corpus.jsonl"
    corpus.write_text(
        json.dumps({"text": "t1", "node": "FamA/NodeA", "source_label": "Straw Man",
                    "match": "exact", "gold_line": 1}) + "\n" +
        json.dumps({"text": "t2", "node": "FamB/NodeB", "source_label": "ad populum",
                    "match": "bridge:Appeal to popularity", "gold_line": 2}) + "\n",
        encoding="utf-8",
    )
    align = {
        "Straw man": {"academic_label": "Straw man", "best_name": "NodeA",
                      "best_famille": "FamA", "verdict": "DIRECT"},
        "Appeal to popularity": {"academic_label": "Appeal to popularity",
                                 "best_name": "NodeB", "best_famille": "FamB",
                                 "verdict": "PARTIAL"},
    }
    pairs = mod.load_pairs(corpus, align)
    assert [(p["node"], p["family"], p["verdict"]) for p in pairs] == [
        ("NodeA", "FamA", "DIRECT"),   # 'Straw Man' -> 'Straw man', casse pliee
        ("NodeB", "FamB", "PARTIAL"),  # pont declare -> cle = cible du pont
    ]
    assert pairs[1]["inventory_label"] == "Appeal to popularity"


def test_completion_au_prorata_des_restes(mod):
    """Le complement au-dela du plancher suit le prorata des restes DIRECT,
    pas un remplissage sequentiel qui servirait la premiere famille triee."""
    def _famille(nom: str, n: int):
        return [
            {"source_file": "a.jsonl", "line_index": i, "corpus_label": "x",
             "inventory_label": "X", "node": f"{nom}{i}", "family": nom,
             "verdict": "DIRECT"}
            for i in range(n)
        ]

    # Restes apres plancher 10 : FamA=30, FamB=10 ; total 40 -> 20 sieges
    # complementaires, prorata exact 3:1 -> 15 pour FamA, 5 pour FamB.
    population = _famille("FamA", 40) + _famille("FamB", 20)
    picked = mod.stratified_draw(population, seed=3, total=40, floor=10)
    familles = Counter(p["family"] for p in picked)
    assert len(picked) == 40
    assert familles == {"FamA": 25, "FamB": 15}
    # Le remplissage sequentiel d'avant donnait FamA=30/FamB=10 : ce test
    # echoue sur ce comportement, c'est son role.
    picked2 = mod.stratified_draw(population, seed=3, total=40, floor=10)
    assert [(p["source_file"], p["node"]) for p in picked2] == \
        [(p["source_file"], p["node"]) for p in picked]  # deterministe
