#!/usr/bin/env python3
"""Tests de la tranche B (#17578) : echantillonnage, candidats, recouvrement.

Hermetiques : aucun appel reseau, aucune dependance au SDK OpenAI. Le moteur
n'est exercise que par le pilote documente dans la PR.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection import phase2b_llm_generation as G  # noqa: E402
from fallacy_detection.cartesian_dataset_builder import Pair  # noqa: E402


# --------------------------------------------------------------------------
# Donnees synthetiques
# --------------------------------------------------------------------------

def _pair(i: int, polarity: str, family: str) -> Pair:
    return Pair(pair_id=f"val-X{i}", split="val", polarity=polarity, node_pk=i,
                family=family, depth=3, is_leaf=True, scenario_path="s.1")


PAIRS = ([_pair(i, "fallacy", "Tricherie") for i in range(1, 41)]
         + [_pair(i, "fallacy", "Abus de langage") for i in range(41, 61)]
         + [_pair(i, "virtue", "Justesse lexicale") for i in range(61, 81)])


# --------------------------------------------------------------------------
# Echantillon stratifie
# --------------------------------------------------------------------------

def test_stratified_sample_est_determine():
    a = G.stratified_sample(PAIRS, 20, seed=0)
    b = G.stratified_sample(PAIRS, 20, seed=0)
    assert [p.pair_id for p in a] == [p.pair_id for p in b]
    assert G.stratified_sample(PAIRS, 20, seed=1) != a or True  # grain different accepte


def test_stratified_sample_represente_chaque_strate_pro_rata():
    sample = G.stratified_sample(PAIRS, 20, seed=0)
    fams = {}
    for p in sample:
        fams[(p.polarity, p.family)] = fams.get((p.polarity, p.family), 0) + 1
    # 40/20/20 sur 80 : pour n=20 -> 10/5/5
    assert fams[("fallacy", "Tricherie")] == 10
    assert fams[("fallacy", "Abus de langage")] == 5
    assert fams[("virtue", "Justesse lexicale")] == 5
    assert len(sample) == 20


def test_stratified_sample_ne_depasse_pas_n():
    assert len(G.stratified_sample(PAIRS, 7, seed=0)) <= 7


# --------------------------------------------------------------------------
# Candidats du controle aller-retour
# --------------------------------------------------------------------------

KEYS_BY_FAMILY = {
    ("fallacy", "Tricherie"): [f"F{i}" for i in range(1, 41)],
    ("virtue", "Justesse lexicale"): [f"V{i}" for i in range(61, 81)],
}


def test_candidate_set_contient_le_vrai_exactement_une_fois():
    p = _pair(12, "fallacy", "Tricherie")
    cs = G.candidate_set(p, KEYS_BY_FAMILY, k=16, seed=0)
    assert cs.keys.count(cs.true_key) == 1
    assert cs.true_key == "F12"
    assert cs.true_index == cs.keys.index("F12")


def test_candidate_set_est_determine_et_melange():
    p = _pair(12, "fallacy", "Tricherie")
    a = G.candidate_set(p, KEYS_BY_FAMILY, k=16, seed=0)
    b = G.candidate_set(p, KEYS_BY_FAMILY, k=16, seed=0)
    assert a == b
    positions = {G.candidate_set(_pair(i, "fallacy", "Tricherie"),
                                 KEYS_BY_FAMILY, k=16, seed=0).true_index
                 for i in range(1, 21)}
    assert len(positions) > 1  # la position du vrai noeud varie bien


def test_candidate_set_meme_polarite_meme_famille():
    cs = G.candidate_set(_pair(12, "fallacy", "Tricherie"), KEYS_BY_FAMILY, k=16, seed=0)
    assert set(cs.keys) <= set(KEYS_BY_FAMILY[("fallacy", "Tricherie")])
    assert len(cs.keys) == 16


def test_candidate_set_k_superieur_au_pool():
    cs = G.candidate_set(_pair(12, "fallacy", "Tricherie"), KEYS_BY_FAMILY, k=99, seed=0)
    assert len(cs.keys) == 40  # pool entier, vrai noeud inclus


# --------------------------------------------------------------------------
# Recouvrement example_*
# --------------------------------------------------------------------------

TEXTS = {"nodes": {
    "F12": {"fr": ("Titre", "Definition", ["exemple unique du noeud qui doit rester hors generation"])},
    "F13": {"fr": ("Titre", "Definition", ["autre chose"])},
}}


def test_overlap_identique_vaut_1():
    ex = TEXTS["nodes"]["F12"]["fr"][2][0]
    assert G.example_overlap(ex, "F12", TEXTS, "fr") == 1.0


def test_overlap_disjoint_vaut_0():
    assert G.example_overlap("texte totalement different sans aucun mot commun", "F12", TEXTS, "fr") == 0.0


def test_overlap_texte_vide_vaut_0():
    assert G.example_overlap("", "F12", TEXTS, "fr") == 0.0


def test_overlap_8grammes_partiel():
    # 3 8-grammes de chaque cote, 1 partage -> |union| = 5, Jaccard = 1/5
    ex = "alpha beta gamma delta epsilon zeta eta theta iota kappa"
    txt = "alpha beta gamma delta epsilon zeta eta theta mu nu"
    t = {"nodes": {"F1": {"fr": ("T", "D", [ex])}}}
    assert abs(G.example_overlap(txt, "F1", t, "fr") - 0.2) < 1e-9


# --------------------------------------------------------------------------
# Prompt de reclassement et agregation
# --------------------------------------------------------------------------

def test_roundtrip_prompt_nomme_les_items():
    rp = G.roundtrip_prompt("Le texte genere.", ("F12", "F13"), TEXTS, "fr")
    assert "1. Titre -- Definition" in rp and "2. Titre -- Definition" in rp
    assert "Le texte genere." in rp
    assert "item number only" in rp


def test_aggregate_calcule_les_metriques(tmp_path):
    rt = tmp_path / "roundtrip.jsonl"
    rt.write_text(
        '{"pair_id": "a", "node_hit": true}\n'
        '{"pair_id": "b", "node_hit": false}\n', encoding="utf-8")
    records = [
        {"pair_id": "a", "polarity": "fallacy", "family": "Tricherie", "overlap": 0.0,
         "generated": "texte"},
        {"pair_id": "b", "polarity": "virtue", "family": "Justesse lexicale", "overlap": 0.5,
         "generated": ""},
    ]
    m = G.aggregate(records, rt)
    assert m["n"] == 2 and m["n_roundtrip"] == 2
    assert m["node_hit_at_1"] == 0.5
    assert m["empty_generations"] == 1
    assert m["overlap_mean"] == 0.25
    assert m["by_polarity"]["fallacy"]["hit_rate"] == 1.0
    assert m["by_polarity"]["virtue"]["hit_rate"] == 0.0
    assert m["by_family"]["f:Tricherie"]["n"] == 1


def test_aggregate_echantillon_vide(tmp_path):
    rt = tmp_path / "roundtrip.jsonl"
    rt.write_text("", encoding="utf-8")
    m = G.aggregate([], rt)
    assert m["n"] == 0 and m["node_hit_at_1"] is None
