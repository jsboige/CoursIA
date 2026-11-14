"""Pytest suite for `argumentation_lib/_text_to_pl.py` — champ texte -> PL (#18392).

Le module vendorise le chemin texte -> belief set -> requetes du
PropositionalLogicAgent EPITA (SHA ecfd9b9c) : le LLM propose les formules,
Tweety dispose. Les contracts testes ici sont ceux qui PORTENT la garantie de
l'issue #18392, tous offline (ni LLM, ni JVM — les deux services sont injectes) :

- `extract_json_block` : fenced ```json d'abord, braces externes sinon (verbatim
  upstream) — une reponse bavarde du LLM ne casse pas le parse ;
- `filter_formulas` : une formule utilisant une proposition NON declaree est
  rejetee — le LLM ne peut pas faire entrer un atome inconnu par la bande ;
- `parse_translation_response` : reponse incomplete -> ValueError (echec
  visible, jamais une liste vide silencieuse) ;
- `validate_with_parser` : partition acceptees/rejetees SANS lever — le rejet
  par le parseur est l'information pedagogique, pas une panne ;
- `render_prompt` : les marqueurs {{$var}} (syntaxe SK conservee des prompts
  upstream) sont substitues une fois, exactement.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import pytest  # noqa: E402

from argumentation_lib import _text_to_pl as t2p  # noqa: E402


# ---------------------------------------------------------------------------
# extract_json_block (logique verbatim upstream)
# ---------------------------------------------------------------------------

def test_extract_json_block_prefere_le_bloc_fenced():
    raw = 'Voici ma traduction :\n```json\n{"propositions": ["a"], "formulas": ["a"]}\n```\nmerci.'
    assert t2p.extract_json_block(raw) == '{"propositions": ["a"], "formulas": ["a"]}'


def test_extract_json_block_replique_sur_les_braces():
    raw = 'texte avant {"query_ideas": ["a"]} texte apres'
    assert t2p.extract_json_block(raw) == '{"query_ideas": ["a"]}'


# ---------------------------------------------------------------------------
# filter_formulas (logique verbatim upstream)
# ---------------------------------------------------------------------------

def test_filter_formulas_rejette_les_atomes_non_declares():
    declared = ["rain", "wet", "picnic_inside"]
    formulas = [
        "rain => wet",               # que des declarees : gardee
        "rain => picnic_inside",     # idem : gardee
        "rain => storm",             # atome inconnu : rejetee
    ]
    assert t2p.filter_formulas(formulas, declared) == ["rain => wet", "rain => picnic_inside"]


def test_filter_formulas_ensemble_vide_tout_rejete():
    assert t2p.filter_formulas(["a => b"], []) == []


# ---------------------------------------------------------------------------
# parse_translation_response / parse_query_response
# ---------------------------------------------------------------------------

def test_parse_translation_response_ok():
    raw = '```json\n{"propositions": ["socrates_is_a_man"], "formulas": ["socrates_is_a_man"]}\n```'
    props, formulas = t2p.parse_translation_response(raw)
    assert props == ["socrates_is_a_man"]
    assert formulas == ["socrates_is_a_man"]


def test_parse_translation_response_incomplete_leve():
    # cle formulas absente : echec VISIBLE, pas une liste vide silencieuse
    with pytest.raises(ValueError, match="incomplete"):
        t2p.parse_translation_response('{"propositions": ["a"]}')


def test_parse_query_response_filtre_les_non_chaines():
    raw = '{"query_ideas": ["wet", 42, null]}'
    assert t2p.parse_query_response(raw) == ["wet"]


# ---------------------------------------------------------------------------
# validate_with_parser (partition sans lever)
# ---------------------------------------------------------------------------

def _fake_parse(formula: str):
    # simulate le contrat de PlParser.parseFormula : rejette l'operateur >>
    if ">>" in formula or formula.rstrip().endswith("=>"):
        raise ValueError("unexpected token")
    return formula


def test_validate_with_parser_partitionne_sans_lever():
    accepted, rejected = t2p.validate_with_parser(
        ["rain => wet", "rain >> wet", "rain =>"], _fake_parse
    )
    assert accepted == ["rain => wet"]
    assert [r["formula"] for r in rejected] == ["rain >> wet", "rain =>"]
    assert all(r["error"] for r in rejected)  # le motif du rejet est rapporte


def test_validate_with_parser_tout_valide():
    accepted, rejected = t2p.validate_with_parser(["a", "!a && b"], _fake_parse)
    assert accepted == ["a", "!a && b"] and rejected == []


# ---------------------------------------------------------------------------
# render_prompt + prompts (marqueurs {{$var}} conserves de l'upstream)
# ---------------------------------------------------------------------------

def test_render_prompt_substitue_les_marqueurs():
    out = t2p.render_prompt(t2p.PROMPT_TEXT_TO_PL, input="Socrate est un homme.")
    assert "{{$input}}" not in out
    assert "Socrate est un homme." in out


def test_render_prompt_queries_deux_variables():
    out = t2p.render_prompt(
        t2p.PROMPT_GEN_QUERIES, input="le texte", belief_set='{"propositions": []}'
    )
    assert "{{$input}}" not in out and "{{$belief_set}}" not in out


def test_prompts_exigent_le_json_strict():
    # les deux prompts portent le contrat de format (reponse JSON exploitable)
    assert '"propositions"' in t2p.PROMPT_TEXT_TO_PL
    assert '"formulas"' in t2p.PROMPT_TEXT_TO_PL
    assert '"query_ideas"' in t2p.PROMPT_GEN_QUERIES


def test_belief_set_summary():
    summary = t2p.belief_set_summary(["a"], ["a => b"])
    assert '"propositions"' in summary and '"formulas"' in summary
