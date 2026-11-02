# -*- coding: utf-8 -*-
# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : tests/unit/coursia/privacy_mining/test_privacy_mining_roundtrip.py
# Source SHA1 : 9752c075af56ec2de5be7c93b2a716ac1148cdcf (470L @ 2e2a1c3c)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/tests/test_privacy_mining_roundtrip.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# ADAPTATIONS DECLAREES (le corps de test amont est repris tel quel) :
#   1. prefixes d'import : `argumentation_analysis.evaluation.X` ->
#      `argumentation_lib._X` (les modules jumeaux sont en-tete de ce dossier,
#      voir `argumentation_lib/NOTICE-EPITA`) ;
#   2. chemins : la fixture amont `docs/coursia_contrib/privacy_mining_examples.json`
#      est portee en `data/privacy_mining_examples.json`, et le carnet amont
#      `docs/coursia_contrib/privacy_mining.ipynb` est le carnet livre
#      `Argumentation-10-Privacy-Export-Python.ipynb` ;
#   3. inventaire : l'inventaire amont compte les lignes des modules
#      `argumentation_analysis/...` ; on compare ici le CORPS (entete de
#      provenance exclu) des copies portees, qui doit avoir le meme nombre
#      de lignes que l'amont ;
#   4. `sys.path` : la racine de la serie est ajoutee au chemin (le depot
#      EPITA n'est pas installe sur cette machine).
#
# ADDITION COURSIA : `test_native_dung_prefix_rewrite` verifie que le module
# Dung (dependance LAZY du detecteur de topologie) est bien le port, et que
# `_pattern_mining.py` pointe vers lui -- sans ce port, le detecteur Dung
# rendait `{"error": 1.0}` au lieu de mesures reelles.
# =============================================================================
# -*- coding: utf-8 -*-
"""Round-trip guard for the #1961 Phase 6 CoursIA asset on privacy & mining.

Replays every case of docs/coursia_contrib/privacy_mining_examples.json against
the real evaluation modules (opaque_id, sanitize_state, pattern_mining) and
pins the structural claims the notebook teaches. Corpus-free, zero LLM, zero
JVM — synthetic fixtures only, synthetic salt.
"""

import copy
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

REPO = Path(__file__).resolve().parent.parent
EXAMPLES_PATH = REPO / "data" / "privacy_mining_examples.json"
NOTEBOOK_PATH = REPO / "Argumentation-10-Privacy-Export-Python.ipynb"

from argumentation_lib._opaque_id import opaque_id
from argumentation_lib._sanitize_state import sanitize_state
import argumentation_lib._pattern_mining as pm

SOURCE_FILES = {
    # chemin amont -> copie portee dans CoursIA
    "argumentation_analysis/evaluation/opaque_id.py": "argumentation_lib/_opaque_id.py",
    "argumentation_analysis/evaluation/sanitize_state.py": "argumentation_lib/_sanitize_state.py",
    "argumentation_analysis/evaluation/pattern_mining.py": "argumentation_lib/_pattern_mining.py",
}


def body_lines(path):
    """Lignes du corps, entete de provenance exclu.

    L'entete se termine par une ligne de separateur `# ====...` ; le corps
    commence apres le dernier separateur.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    seps = [
        i
        for i, line in enumerate(lines)
        if line.startswith("# ====") and set(line[2:].strip()) == {"="}
    ]
    return lines[(seps[-1] + 1) if seps else 0 :]

SALT = "synthetic-asset-salt"


@pytest.fixture(autouse=True)
def _salt(monkeypatch):
    monkeypatch.setenv("OPAQUE_ID_SALT", SALT)


@pytest.fixture(scope="module")
def examples():
    data = json.loads(EXAMPLES_PATH.read_text(encoding="utf-8"))
    assert data["asset"] == "privacy_mining"
    assert data["phase"] == 6
    return data


def case(section, name):
    match = [c for c in section if c["name"] == name]
    assert len(match) == 1, f"case {name!r} not found exactly once"
    return match[0]


def make_state():
    """The notebook's synthetic state fixture — same content, fresh copy."""
    return {
        "source_name": "Discours de synthèse (nom réel)",
        "author": "Auteur Réel",
        "url": "https://example.invalid/doc",
        "raw_text": "Texte brut long du document source.",
        "source_id": "doc_source_001",
        "source_metadata": {
            "genre": "discours",
            "title": "Titre réel du discours",
            "channel": "TV",
        },
        "identified_arguments": {
            "arg1": "Le premier argument en clair",
            "arg2": {"score": 3},
        },
        "identified_fallacies": {
            "f1": {
                "type": "ad_hominem",
                "justification": "cite le texte réel",
                "severity": 2,
            },
        },
        "argument_quality_scores": {
            "arg1": {"overall": 0.8, "llm_assessment": "narratif LLM citant l'argument"}
        },
        "dung_frameworks": {
            "fw1": {
                "name": "dung_grounded",
                "arguments": ["le premier argument en clair", "le second en clair"],
                "attacks": [["le premier argument en clair", "le second en clair"]],
                "extensions": {
                    "extensions": [["le premier argument en clair"]],
                    "count": 1,
                    "sizes": [1],
                    "all_members": ["le premier argument en clair"],
                },
                "formalism_specific": {
                    "contraries": {"atome_a": "contraire_a"},
                    "attack_weights": [
                        {"source": "atome_a", "target": "atome_b", "weight": 0.7}
                    ],
                    "criterion": "generalized_specificity",
                },
            }
        },
        "counter_arguments": [
            {
                "strategy": "reductio",
                "counter_content": "contre-argument en clair",
                "score": 0.5,
            }
        ],
        "extracts": [{"content": "extrait en clair", "claim_id": "c1"}],
        "probabilistic_results": [
            {
                "method": "ml",
                "arguments": ["argument en clair"],
                "acceptance_probabilities": {"argument en clair": 0.42},
            }
        ],
        "dialogue_results": [
            {
                "topic": "sujet en clair",
                "trace": [
                    {
                        "round": 1,
                        "speaker": "S1",
                        "argument": "texte en clair",
                        "target": "autre texte",
                    }
                ],
            }
        ],
        "debate_transcripts": [
            {
                "round": 1,
                "topic": "sujet débat",
                "exchanges": [
                    {
                        "point": "point en clair",
                        "rebuttal": "réponse en clair",
                        "scheme": "expert_opinion",
                    }
                ],
            }
        ],
        "nl_to_logic_translations": [
            {
                "source": "s",
                "logic": "P->Q",
                "original_text": "texte original",
                "variables": {"p": "signification en clair de p"},
            }
        ],
        "belief_revision_results": [
            {
                "method": "m",
                "original": ["croyance en clair"],
                "revised": [],
                "minimal_retraction": {
                    "options": [["croyance en clair"]],
                    "cardinality": 1,
                },
            }
        ],
        "narrative_synthesis": "Long texte narratif de synthèse.",
        "final_conclusion": "Conclusion finale narrative.",
        "stakes_and_stakeholders": {
            "stakes": ["enjeu en clair"],
            "stakeholders": ["acteur en clair"],
            "rhetorical_register": "délibératif",
        },
        "identified_metrics": {"n_args": 2, "score": 0.9},
        "unknown_new_container": [{"free": "texte d'un conteneur non classé"}],
    }


def make_sigs():
    return [
        {
            "metadata": {"cluster_id": "corpus_A"},
            "state": {
                "identified_fallacies": {
                    "f1": {"type": "ad_hominem", "source_arg": "arg1"},
                    "f2": {"type": "straw_man", "source_arg": "arg1"},
                    "f3": {"type": "cherry_picking", "source_arg": "arg2"},
                },
                "fol_analysis_results": [{"formula": "F", "valid": False}],
                "dung_frameworks": {"fw": {"attacks": [{"from": "a", "to": "b"}]}},
                "jtms_retraction_chain": [{"trigger": "x"}],
            },
        },
        {
            "metadata": {"cluster_id": "corpus_B"},
            "state": {
                "identified_fallacies": {
                    "f1": {"type": "appeal_to_authority", "source_arg": "arg1"},
                    "f2": {"type": "false_cause", "source_arg": "arg2"},
                },
                "dung_frameworks": {
                    "fw": {
                        "attacks": [{"from": "a", "to": "b"}, {"from": "b", "to": "c"}]
                    }
                },
            },
        },
    ]


# ---------------------------------------------------------------- inventory


def test_inventory_matches_head(examples):
    inv = examples["inventory"]
    assert set(inv) == set(SOURCE_FILES)
    for rel, copie in SOURCE_FILES.items():
        lines = len(body_lines(REPO / copie))
        assert lines == inv[rel], f"line count drifted for {rel}"


def test_notebook_ships_executed_outputs():
    nb = json.loads(NOTEBOOK_PATH.read_text(encoding="utf-8"))
    code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
    assert len(code_cells) >= 10
    counts = []
    for cell in code_cells:
        assert cell.get("execution_count"), "code cell without execution_count"
        assert cell.get("outputs"), "code cell without committed outputs"
        counts.append(cell["execution_count"])
    assert counts == sorted(counts), "execution_count must be sequential"


# ---------------------------------------------------------------- opaque_id


def test_opaque_id_deterministic_and_distinct(examples):
    stored = case(examples["opaque_cases"], "deterministic_and_distinct")
    assert opaque_id("Source A", salt="s1") == stored["id_a_1"] == stored["id_a_2"]
    assert opaque_id("Source B", salt="s1") == stored["id_b_same_salt"]
    assert opaque_id("Source A", salt="s2") == stored["id_a_other_salt"]
    assert (
        len({stored["id_a_1"], stored["id_b_same_salt"], stored["id_a_other_salt"]})
        == 3
    )
    for value in (
        stored["id_a_1"],
        stored["id_b_same_salt"],
        stored["id_a_other_salt"],
    ):
        assert len(value) == 8
        assert all(c in "0123456789abcdef" for c in value)


def test_opaque_id_requires_salt(examples, monkeypatch):
    stored = case(examples["opaque_cases"], "no_salt_raises")
    assert stored["raises"].startswith("RuntimeError")
    monkeypatch.delenv("OPAQUE_ID_SALT", raising=False)
    with pytest.raises(RuntimeError) as exc:
        opaque_id("Source A")
    assert "OPAQUE_ID_SALT is required" in str(exc.value)
    assert "public default" in str(
        exc.value
    )  # the #1973 rationale ships in the message


# ---------------------------------------------------------------- sanitize


def test_sanitize_top_level_and_identifiers(examples):
    stored = case(examples["sanitize_cases"], "top_level_stripped_and_source_opacified")
    san = sanitize_state(make_state())
    for gone in ("source_name", "author", "url", "raw_text"):
        assert gone not in san
    assert san["source_id"] == stored["source_id_after"]
    assert san["source_id"] == opaque_id("doc_source_001", salt=SALT)
    assert list(san["source_metadata"].keys()) == stored["metadata_keys_after"]
    assert list(san["source_metadata"].values()) == stored["metadata_values_after"]


def test_sanitize_text_vs_structure(examples):
    stored = case(examples["sanitize_cases"], "arguments_and_justifications")
    san = sanitize_state(make_state())
    assert san["identified_arguments"]["arg1"] == {"text_stripped": True}
    assert san["identified_arguments"]["arg2"] == {"score": 3}
    assert san["identified_fallacies"]["f1"] == {"type": "ad_hominem", "severity": 2}
    assert "llm_assessment" not in san["argument_quality_scores"]["arg1"]
    assert san["argument_quality_scores"]["arg1"]["overall"] == 0.8


def test_sanitize_topology_survives(examples):
    stored = case(examples["sanitize_cases"], "topology_survives_opacification")
    san = sanitize_state(make_state())
    fw = san["dung_frameworks"]["fw1"]
    assert len(fw["attacks"][0]) == 2
    assert fw["extensions"]["count"] == 1 and fw["extensions"]["sizes"] == [1]
    assert fw["name"] == "dung_grounded"
    assert fw["formalism_specific"]["criterion"] == "generalized_specificity"
    assert fw["formalism_specific"]["attack_weights"][0]["weight"] == 0.7
    # No plaintext claim text survives anywhere in the sanitized state
    assert "le premier argument en clair" not in json.dumps(san, ensure_ascii=False)


def test_sanitize_list_containers(examples):
    stored = case(examples["sanitize_cases"], "list_containers")
    san = sanitize_state(make_state())
    assert san["counter_arguments"][0] == {"strategy": "reductio", "score": 0.5}
    assert san["extracts"][0] == {"claim_id": "c1"}
    prob = san["probabilistic_results"][0]
    assert prob["method"] == "ml"
    assert list(prob["acceptance_probabilities"].values()) == [0.42]
    assert san["dialogue_results"][0]["trace"][0]["speaker"] == "S1"
    assert san["debate_transcripts"][0]["exchanges"][0]["scheme"] == "expert_opinion"
    assert san["belief_revision_results"][0]["minimal_retraction"]["cardinality"] == 1


def test_sanitize_narrative_struct_and_unknown(examples):
    ex = examples["sanitize_cases"]
    san = sanitize_state(make_state())
    s5 = case(ex, "narrative_and_struct_reductions")
    assert san["narrative_synthesis"] == s5["narrative_after"]
    assert san["narrative_synthesis"]["length"] == len(
        "Long texte narratif de synthèse."
    )
    assert san["stakes_and_stakeholders"] == s5["stakes_after"]
    assert san["stakes_and_stakeholders"]["has_rhetorical_register"] is True

    # Allowlist design: unknown container and unknown metrics traverse intact
    s6 = case(ex, "unknown_container_traverses_intact")
    assert san["unknown_new_container"] == s6["unknown_container_after"]
    assert san["identified_metrics"] == {"n_args": 2, "score": 0.9}


def test_sanitize_does_not_mutate_input(examples):
    state = make_state()
    original = copy.deepcopy(state)
    sanitize_state(state)
    assert state == original


def test_sanitize_salt_requirement_is_conditional(examples, monkeypatch):
    stored = case(examples["sanitize_cases"], "salt_requirement_is_conditional")
    monkeypatch.delenv("OPAQUE_ID_SALT", raising=False)
    # No opacifiable field -> no opaque_id call -> sanitizes fine
    assert (
        sanitize_state({"identified_metrics": {"n": 1}})
        == stored["state_without_opacifiable_fields"]
    )
    # source_id triggers opaque_id -> RuntimeError
    with pytest.raises(RuntimeError):
        sanitize_state({"source_id": "doc_x"})


# ---------------------------------------------------------------- mining


def test_mining_spectrum(examples):
    stored = case(examples["mining_cases"], "spectrum")
    spec = pm.fallacy_spectrum(make_sigs())
    assert spec == stored["result"]
    assert spec["corpus_A"] == {
        "ad_hominem": 0.3333,
        "straw_man": 0.3333,
        "cherry_picking": 0.3333,
    }


def test_mining_trick_vs_influence(examples):
    stored = case(examples["mining_cases"], "trick_vs_influence")
    tvi = pm.trick_vs_influence_ratio(make_sigs())
    assert tvi == stored["result"]
    assert tvi["corpus_A"]["asymmetry"] == 0.3333  # (2-1)/(2+1)
    assert tvi["corpus_B"]["asymmetry"] == 0.0  # 1 influence + 1 tricherie


def test_mining_trick_vs_influence_edges(examples):
    stored = case(examples["mining_cases"], "trick_vs_influence_edges")
    only_inf = pm.trick_vs_influence_ratio(
        [
            {
                "metadata": {"cluster_id": "only_influence"},
                "state": {
                    "identified_fallacies": {
                        "f": {"type": "bandwagon", "source_arg": "a"}
                    }
                },
            }
        ]
    )
    assert only_inf == stored["only_influence"]
    assert only_inf["only_influence"]["ratio"] == 1e9  # capped, no division by zero


def test_mining_cooccurrence(examples):
    stored_arg = case(examples["mining_cases"], "cooccurrence_argument_unit")
    co = pm.cooccurrence_matrix(make_sigs(), unit="argument")
    assert co == stored_arg["result"]
    pair = next(
        p for p in co["pairs"] if {p["a"], p["b"]} == {"ad_hominem", "straw_man"}
    )
    assert pair["support"] == 1 and pair["jaccard"] == 1.0  # perfectly co-occurring


def test_mining_cross_coverage(examples):
    stored = case(examples["mining_cases"], "cross_coverage")
    cc = pm.cross_coverage(make_sigs())
    assert cc == stored["result"]
    # corpus_A signature carries all three formal signals
    for signal in ("fol_invalid", "dung_unsupported", "jtms_retraction"):
        assert cc["ad_hominem"]["per_signature_rate"][signal] == 1.0
    # corpus_B signature: dung_unsupported only (c attacked, never attacking)
    assert cc["appeal_to_authority"]["per_signature_rate"]["dung_unsupported"] == 1.0
    assert cc["appeal_to_authority"]["per_signature_rate"]["fol_invalid"] == 0.0


def test_mining_formal_detectors_dict_attack_trap(examples):
    stored = case(examples["mining_cases"], "formal_detectors")
    det = pm.run_formal_detectors(make_sigs()[0])
    assert det == stored["result"]
    # Measured trap: dict-shaped attacks count as ONE entry — not one edge
    assert det["dung_topology"]["n_attacks"] == 1.0
    assert det["dung_topology"]["density"] == 1.0
    assert (
        det["jtms_retraction_rate"]["retraction_rate"] == 0.0
    )  # 0 beliefs -> 0.0, not a crash


def test_mining_dung_topology_directed_density(examples):
    stored = case(examples["mining_cases"], "dung_topology_directed_density")
    topo = pm.DungTopologyDetector().detect(
        {
            "state": {
                "dung_frameworks": {
                    "fw": {
                        "arguments": ["a", "b", "c"],
                        "attacks": [["a", "b"], ["b", "c"]],
                        "extensions": {
                            "grounded": ["a", "c"],
                            "preferred": [["a", "c"]],
                        },
                    }
                }
            }
        }
    )
    assert topo == stored["result"]
    assert topo["density"] == stored["density_value"] == 0.3333  # 2 / (3*2) directed


def test_mining_atms_three_state_contract(examples):
    stored = case(examples["mining_cases"], "atms_coherent_three_state_1650")
    atms = pm.AtmsBranchingDetector().detect(
        {
            "state": {
                "atms_contexts": [
                    {"assumptions": ["p", "q"], "coherent": True},
                    {"assumptions": ["r"], "coherent": False},
                    {
                        "assumptions": []
                    },  # absent key -> unclassified, NOT contradiction
                ]
            }
        }
    )
    assert atms == stored["result"]
    assert atms["contradiction_rate"] == 0.3333  # the unclassified context is excluded


def test_mining_detector_exception_is_error_flag(examples):
    stored = case(examples["mining_cases"], "detector_exception_is_error_flag")

    class Boom:
        name = "boom"

        def detect(self, signature):
            raise ValueError("kaboom")

    assert pm.run_formal_detectors({}, detectors=[Boom()]) == stored["result"]


# ---------------------------------------------- addition CoursIA (port Dung)


def test_native_dung_prefix_rewrite():
    """Le detecteur de topologie Dung doit viser le module PORT, pas l'amont.

    Sans `_native_dung.py`, l'import lazy de `_pattern_mining.py` echouait et
    le detecteur rendait `{"error": 1.0}` au lieu des mesures reelles.
    """
    from argumentation_lib import _native_dung

    assert isinstance(_native_dung.KEYED_SEMANTICS, tuple)
    assert callable(_native_dung.dung_reading)

    source = (REPO / "argumentation_lib" / "_pattern_mining.py").read_text(
        encoding="utf-8"
    )
    assert "from argumentation_lib._native_dung import" in source
    assert (
        "from argumentation_analysis.reporting.restitution.native_dung" not in source
    )


def test_cooccurrence_document_unit_measured():
    """Cas `cooccurrence_doc_unit` de la fixture : expectation INCOMPLETE.

    La fixture amont liste 3 paires de niveau document ; le code en produit 4
    sur les memes signatures (les 3 de `corpus_A` plus
    `appeal_to_authority + false_cause` de `corpus_B`), toutes de memes
    metriques (support 1, lift 2.0, jaccard 1.0). Ni le carnet amont ni le
    test round-trip amont n'exercent ce cas : l'ecart est donc dans la
    fixture, pas dans le code. On fige ici la valeur MESUREE pour que la
    derive soit visible si le comportement change.
    """
    co = pm.cooccurrence_matrix(make_sigs(), unit="doc")
    assert co["unit_count"] == 2
    assert len(co["pairs"]) == 4
    assert {frozenset((p["a"], p["b"])) for p in co["pairs"]} == {
        frozenset(("ad_hominem", "cherry_picking")),
        frozenset(("ad_hominem", "straw_man")),
        frozenset(("cherry_picking", "straw_man")),
        frozenset(("appeal_to_authority", "false_cause")),
    }
