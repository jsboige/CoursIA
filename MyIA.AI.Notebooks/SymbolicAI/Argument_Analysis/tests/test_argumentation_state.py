"""
Tests pour le shim `argumentation_lib` (Argumentum, #2137 Phase B).

`argumentation_lib` est la couche vendoree qui decouple les notebooks
Argument_Analysis des internals EPITA. Elle expose une API publique
(LibConfig, paths, JVM compat, RhetoricalAnalysisState, UnifiedAnalysisState)
et doit s'importer SANS JVM, SANS semantic_kernel, SANS le package EPITA
(lazy imports).

Ces tests assertent les **contrats de l'API publique** sur la surface
pure-Python (config, paths, etat collaboratif append-only, serialisation,
agregation des profils d'argument), pas seulement l'absence de crash :
  - Importabilite sans infra lourde (invariant HARD du shim).
  - Hygiene secrets : ZERO nom de modele, ZERO cle (le shim est explicitement
    "zero secrets, zero model names" — on verifie que ca reste vrai).
  - Generation d'IDs sequentiels et uniques.
  - Etats append-only (logs, erreurs, extraits accumulent).
  - Round-trip JSON (to_json/from_dict) preserve l'etat.
  - Designation d'agent one-shot (consommee puis None).
  - Profils agreges : get_argument_profile collecte sophismes/qualite/
    contre-arguments/JTMS ; get_weak_arguments / get_fallacious_arguments /
    get_enrichment_summary respectent leurs contrats de seuil/couverture.

Run with: pytest tests/test_argumentation_state.py -v
"""

import json
import sys
from pathlib import Path

import pytest

# Ajoute Argument_Analysis/ au path pour importer le package argumentation_lib.
sys.path.insert(0, str(Path(__file__).parent.parent))

import argumentation_lib as al  # noqa: E402
from argumentation_lib import (  # noqa: E402
    LibConfig,
    DEFAULT_CONFIG,
    get_config,
    RhetoricalAnalysisState,
    UnifiedAnalysisState,
    ArgumentProfile,
)


# ============================================================================
# Importabilite (HARD) : le shim s'importe SANS JVM / semantic_kernel / EPITA.
# ============================================================================

class TestImportability:
    """Le shim DOIT s'importer sans aucune infrastructure lourde."""

    def test_import_succeeds_without_heavy_deps(self):
        """L'import du package ne leve pas (pas de JVM/EPITA au module-level)."""
        import importlib
        # Re-import force pour verifier qu'aucun effet de bord ne casse.
        mod = importlib.reload(al)
        assert mod is al

    def test_public_api_surface(self):
        """La surface API documentee dans __init__ est bien exposee."""
        for name in [
            "LibConfig", "get_config", "DEFAULT_CONFIG",
            "RhetoricalAnalysisState", "UnifiedAnalysisState", "ArgumentProfile",
            "initialize_jvm", "is_jvm_started", "shutdown_jvm",
            "get_tweety_jar_dir", "ensure_output_dirs",
        ]:
            assert hasattr(al, name), f"API publique manquante : {name}"

    def test_version_string(self):
        assert isinstance(al.__version__, str) and al.__version__


# ============================================================================
# Hygiene secrets (HARD) : le shim est "zero secrets, zero model names".
# ============================================================================

class TestSecretsHygiene:
    """Le shim ne doit JAMAIS contenir de secret ni de nom de modele en clair."""

    def test_no_model_names_no_secrets(self):
        import inspect
        src = inspect.getsource(al)
        forbidden = [
            "gpt-4", "gpt-5", "claude-", "sk-proj", "sk-ant",
            "api_key=", "API_KEY = ", "ghp_", "AIza",
        ]
        for needle in forbidden:
            assert needle not in src, (
                f"Hygiene secrets violee : '{needle}' trouve dans le shim "
                f"(le shim doit etre zero-secret, zero-model-name)."
            )

    def test_config_has_no_secret_fields(self):
        """LibConfig n'expose AUCUN champ credential/model."""
        cfg = LibConfig()
        for field_name in cfg.__dataclass_fields__:
            low = field_name.lower()
            assert not any(s in low for s in ["key", "token", "secret", "model", "password"]), (
                f"Champ suspect dans LibConfig : {field_name}"
            )


# ============================================================================
# LibConfig (defaults statiques).
# ============================================================================

class TestLibConfig:
    def test_default_config_values(self):
        cfg = DEFAULT_CONFIG
        assert cfg.max_turns_per_phase == 5
        assert cfg.max_conversation_turns == 20
        assert cfg.enable_tracing is False
        assert cfg.enable_enhanced_reporting is False

    def test_default_config_is_singleton(self):
        """get_config() retourne le meme DEFAULT_CONFIG a chaque appel."""
        assert get_config() is DEFAULT_CONFIG
        assert get_config() is get_config()

    def test_libconfig_is_frozen(self):
        """LibConfig est immutable (dataclass frozen) : pas de mutation."""
        cfg = LibConfig()
        with pytest.raises((AttributeError, Exception)):
            cfg.max_turns_per_phase = 999  # type: ignore[misc]


# ============================================================================
# Paths (fonctions pures, pas d'effet de bord a l'import).
# ============================================================================

class TestPaths:
    def test_directory_hierarchy(self):
        """LIB_DIR < ARGUMENT_ANALYSIS_DIR < SYMBOLIC_AI_DIR (chaine des parents)."""
        from argumentation_lib import _paths as P
        assert P.LIB_DIR.parent == P.ARGUMENT_ANALYSIS_DIR
        assert P.ARGUMENT_ANALYSIS_DIR.parent == P.SYMBOLIC_AI_DIR

    def test_standard_subdirs_under_argument_analysis(self):
        from argumentation_lib import _paths as P
        for getter, name in [
            (P.get_ontology_dir, "ontologies"),
            (P.get_data_dir, "data"),
            (P.get_ext_tools_dir, "ext_tools"),
        ]:
            d = getter()
            assert d.parent == P.ARGUMENT_ANALYSIS_DIR
            assert d.name == name

    def test_get_tweety_jar_dir_returns_path_or_none(self):
        """Renvoie un Path (si JARs presents) ou None — pas d'exception."""
        from argumentation_lib import get_tweety_jar_dir
        result = get_tweety_jar_dir()
        assert result is None or isinstance(result, Path)

    def test_ensure_output_dirs_creates_and_returns(self, monkeypatch, tmp_path):
        """ensure_output_dirs cree les repertoires sous la racine et retourne
        un dict name->Path. On redirige la racine vers tmp_path pour ne pas
        muter le depot."""
        from argumentation_lib import _paths as P
        monkeypatch.setattr(P, "ARGUMENT_ANALYSIS_DIR", tmp_path)
        result = P.ensure_output_dirs("logs", "out")
        assert set(result.keys()) == {"logs", "out"}
        for name, p in result.items():
            assert p.exists() and p.is_dir()
            assert p.parent == tmp_path

    def test_ensure_output_dirs_idempotent(self, monkeypatch, tmp_path):
        """Appeler 2x ne leve pas (exist_ok=True)."""
        from argumentation_lib import _paths as P
        monkeypatch.setattr(P, "ARGUMENT_ANALYSIS_DIR", tmp_path)
        P.ensure_output_dirs("x")
        P.ensure_output_dirs("x")  # pas d'erreur
        assert (tmp_path / "x").exists()


# ============================================================================
# RhetoricalAnalysisState : IDs, append-only, cycle de vie.
# ============================================================================

class TestRhetoricalStateBasics:
    """Contrats de l'etat collaboratif de base."""

    def test_fresh_state_is_empty(self):
        s = RhetoricalAnalysisState("texte brut")
        assert s.raw_text == "texte brut"
        assert s.analysis_tasks == {}
        assert s.identified_arguments == {}
        assert s.identified_fallacies == {}
        assert s.belief_sets == {}
        assert s.query_log == []
        assert s.answers == {}
        assert s.final_conclusion is None

    def test_add_task_sequential_ids(self):
        s = RhetoricalAnalysisState("t")
        assert s.add_task("a") == "task_1"
        assert s.add_task("b") == "task_2"
        assert s.analysis_tasks == {"task_1": "a", "task_2": "b"}

    def test_add_argument_sequential_ids(self):
        s = RhetoricalAnalysisState("t")
        assert s.add_argument("x") == "arg_1"
        assert s.add_argument("y") == "arg_2"

    def test_add_fallacy_stores_entry_with_target(self):
        s = RhetoricalAnalysisState("t")
        s.add_argument("bob est fort")
        fid = s.add_fallacy("Ad Hominem", "attaque la personne", target_arg_id="arg_1",
                            family="relevance", taxonomy_path="ad_hominem/abusive")
        assert fid == "fallacy_1"
        entry = s.identified_fallacies["fallacy_1"]
        assert entry["type"] == "Ad Hominem"
        assert entry["target_argument_id"] == "arg_1"
        assert entry["family"] == "relevance"
        assert entry["taxonomy_path"] == "ad_hominem/abusive"

    def test_add_fallacy_optional_fields_omitted(self):
        """Sans family/taxonomy_path/target, l'entree ne contient que type+justification."""
        s = RhetoricalAnalysisState("t")
        s.add_fallacy("Strawman", "caricature")
        entry = s.identified_fallacies["fallacy_1"]
        assert "family" not in entry
        assert "target_argument_id" not in entry

    def test_add_belief_set_normalizes_logic_type_in_id(self):
        """Le prefixe d'ID normalise le logic_type (strip/lower/espaces->_)."""
        s = RhetoricalAnalysisState("t")
        bs_id = s.add_belief_set("Propositional Logic", "p => q")
        assert bs_id == "propositional_logic_bs_1"
        assert s.belief_sets[bs_id]["logic_type"] == "Propositional Logic"
        assert s.belief_sets[bs_id]["content"] == "p => q"

    def test_log_query_appends_to_log(self):
        s = RhetoricalAnalysisState("t")
        s.add_belief_set("PL", "p")
        lid = s.log_query("pl_bs_1", "entails(q)?", "yes")
        assert lid == "qlog_1"
        assert len(s.query_log) == 1
        entry = s.query_log[0]
        assert entry["log_id"] == "qlog_1"
        assert entry["query"] == "entails(q)?"
        assert entry["raw_result"] == "yes"

    def test_add_answer_stores_under_task_id(self):
        s = RhetoricalAnalysisState("t")
        s.add_task("que faire ?")
        s.add_answer("task_1", "agent_x", "reponse", ["arg_1"])
        assert s.answers["task_1"]["author_agent"] == "agent_x"
        assert s.answers["task_1"]["source_ids"] == ["arg_1"]

    def test_set_conclusion(self):
        s = RhetoricalAnalysisState("t")
        s.set_conclusion("donc X")
        assert s.final_conclusion == "donc X"

    def test_add_extract_sequential(self):
        s = RhetoricalAnalysisState("t")
        eid = s.add_extract("passage", "blah")
        assert eid == "extract_1"
        assert s.extracts[0]["name"] == "passage"

    def test_log_error_sequential_with_none_timestamp(self):
        s = RhetoricalAnalysisState("t")
        eid = s.log_error("agent_y", "boom")
        assert eid == "error_1"
        assert s.errors[0]["agent_name"] == "agent_y"
        assert s.errors[0]["timestamp"] is None


class TestAgentDesignation:
    """designate_next_agent / consume_next_agent_designation : one-shot."""

    def test_consume_returns_name_then_none(self):
        s = RhetoricalAnalysisState("t")
        assert s.consume_next_agent_designation() is None  # rien au depart
        s.designate_next_agent("sherlock")
        assert s.consume_next_agent_designation() == "sherlock"
        assert s.consume_next_agent_designation() is None  # consomme une fois

    def test_designate_overwrites_previous(self):
        s = RhetoricalAnalysisState("t")
        s.designate_next_agent("a")
        s.designate_next_agent("b")
        assert s.consume_next_agent_designation() == "b"


class TestTaskAnswered:
    def test_get_last_task_id_returns_unanswered(self):
        s = RhetoricalAnalysisState("t")
        s.add_task("t1")
        s.add_task("t2")
        s.add_answer("task_1", "a", "r", [])
        # task_2 est la derniere non repondue.
        assert s.get_last_task_id() == "task_2"

    def test_get_last_task_id_none_when_all_answered(self):
        s = RhetoricalAnalysisState("t")
        s.add_task("t1")
        s.add_answer("task_1", "a", "r", [])
        assert s.get_last_task_id() is None

    def test_mark_task_as_answered_unknown_task_is_noop(self):
        """Marquer une tache inexistante ne leve pas (warning only)."""
        s = RhetoricalAnalysisState("t")
        s.mark_task_as_answered("task_999", "reponse")  # ne leve pas
        assert "task_999" not in s.answers


class TestStateLifecycle:
    def test_reset_state_clears_everything_except_raw_text(self):
        s = RhetoricalAnalysisState("origine")
        s.add_task("t")
        s.add_argument("a")
        s.add_fallacy("F", "j")
        s.set_conclusion("c")
        s.add_extract("e", "c")
        s.reset_state()
        assert s.raw_text == "origine"  # preserve
        assert s.analysis_tasks == {}
        assert s.identified_arguments == {}
        assert s.identified_fallacies == {}
        assert s.final_conclusion is None
        assert s.extracts == []

    def test_snapshot_summarize_has_counts(self):
        s = RhetoricalAnalysisState("txt")
        s.add_task("t")
        s.add_argument("a")
        s.set_conclusion("c")
        snap = s.get_state_snapshot(summarize=True)
        assert snap["task_count"] == 1
        assert snap["argument_count"] == 1
        assert snap["conclusion_present"] is True
        assert "tasks_defined" in snap

    def test_snapshot_summarize_truncates_long_text(self):
        long = "x" * 300
        s = RhetoricalAnalysisState(long)
        snap = s.get_state_snapshot(summarize=True)
        assert len(snap["raw_text"]) < 300  # tronque
        assert snap["raw_text"].endswith("...")


# ============================================================================
# Round-trip JSON (to_json / from_dict) — invariant critique de persistence.
# ============================================================================

class TestJsonRoundTrip:
    def test_to_json_is_valid_json(self):
        s = RhetoricalAnalysisState("t")
        s.add_task("t1")
        s.add_argument("a1")
        data = json.loads(s.to_json())
        assert data["raw_text"] == "t"
        assert data["analysis_tasks"] == {"task_1": "t1"}

    def test_roundtrip_preserves_state(self):
        """to_json -> from_dict preserve l'etat (base class)."""
        s = RhetoricalAnalysisState("texte")
        s.add_task("t1")
        s.add_argument("a1")
        s.add_fallacy("F", "j", target_arg_id="arg_1")
        s.add_belief_set("PL", "p")
        s.add_answer("task_1", "agent", "rep", ["arg_1"])
        s.set_conclusion("conc")
        s.designate_next_agent("next_agent")

        data = json.loads(s.to_json())
        s2 = RhetoricalAnalysisState.from_dict(data)

        assert s2.raw_text == "texte"
        assert s2.analysis_tasks == s.analysis_tasks
        assert s2.identified_arguments == s.identified_arguments
        assert s2.identified_fallacies == s.identified_fallacies
        assert s2.belief_sets == s.belief_sets
        assert s2.answers == s.answers
        assert s2.final_conclusion == "conc"
        assert s2._next_agent_designated == "next_agent"

    def test_from_dict_handles_missing_keys(self):
        """from_dict sur dict minimal ne leve pas."""
        s = RhetoricalAnalysisState.from_dict({"raw_text": "only"})
        assert s.raw_text == "only"
        assert s.analysis_tasks == {}


# ============================================================================
# UnifiedAnalysisState : champs etendus + agregation des profils.
# ============================================================================

class TestUnifiedStateFields:
    def test_extended_fields_initialized_empty(self):
        u = UnifiedAnalysisState("t")
        assert u.counter_arguments == []
        assert u.argument_quality_scores == {}
        assert u.jtms_beliefs == {}
        assert u.dung_frameworks == {}
        assert u.governance_decisions == []
        assert u.debate_transcripts == []

    def test_inherits_base_add_methods(self):
        """UnifiedAnalysisState herite des methodes add_* de la base."""
        u = UnifiedAnalysisState("t")
        assert u.add_task("x") == "task_1"
        assert u.add_argument("a") == "arg_1"

    def test_add_counter_argument(self):
        u = UnifiedAnalysisState("t")
        ca_id = u.add_counter_argument("orig", "counter", "rebuttal", 0.8, target_arg_id="arg_1")
        assert ca_id == "ca_1"
        assert u.counter_arguments[0]["target_arg_id"] == "arg_1"
        assert u.counter_arguments[0]["score"] == 0.8

    def test_add_quality_score_stores_under_arg_id(self):
        u = UnifiedAnalysisState("t")
        u.add_quality_score("arg_1", {"clarity": 4.0}, overall=3.0)
        assert u.argument_quality_scores["arg_1"]["overall"] == 3.0

    def test_add_quality_score_resolved_id(self):
        """resolved_arg_id redirige le stockage vers l'ID canonique."""
        u = UnifiedAnalysisState("t")
        u.add_quality_score("llm_1", {"c": 4.0}, overall=7.0, resolved_arg_id="arg_1")
        assert "llm_1" not in u.argument_quality_scores
        assert u.argument_quality_scores["arg_1"]["overall"] == 7.0

    def test_add_jtms_belief(self):
        u = UnifiedAnalysisState("t")
        bid = u.add_jtms_belief("arg_1 is valid", True, ["justif"])
        assert bid == "jtms_1"
        assert u.jtms_beliefs["jtms_1"]["valid"] is True

    def test_add_dung_framework(self):
        u = UnifiedAnalysisState("t")
        did = u.add_dung_framework("AF1", ["a", "b"], [["a", "b"]])
        assert did == "dung_1"
        assert u.dung_frameworks["dung_1"]["attacks"] == [["a", "b"]]


class TestArgumentProfileAggregation:
    """get_argument_profile agrege sophismes/qualite/contre-args/JTMS pour 1 arg."""

    def test_profile_aggregates_fallacy_quality_counter_jtms(self):
        u = UnifiedAnalysisState("t")
        u.add_argument("L'argument principal")
        arg_id = "arg_1"
        u.add_fallacy("Ad Hominem", "attaque", target_arg_id=arg_id)
        u.add_quality_score(arg_id, {"clarity": 2.0}, overall=3.0)
        u.add_counter_argument("L'argument principal", "contre", "rebuttal", 0.9,
                               target_arg_id=arg_id)
        u.add_jtms_belief("arg_1 status", True, ["j"])

        profile = u.get_argument_profile(arg_id)
        assert isinstance(profile, ArgumentProfile)
        assert profile.arg_id == arg_id
        assert profile.description == "L'argument principal"
        assert len(profile.fallacies) == 1
        assert profile.quality_score is not None
        assert profile.quality_score["overall"] == 3.0
        assert len(profile.counter_arguments) == 1
        assert len(profile.jtms_beliefs) == 1

    def test_profile_for_unknown_arg_is_empty(self):
        u = UnifiedAnalysisState("t")
        profile = u.get_argument_profile("arg_999")
        assert profile.fallacies == []
        assert profile.quality_score is None
        assert profile.counter_arguments == []


class TestWeakAndFallacious:
    def test_get_weak_arguments_below_threshold(self):
        """Args dont quality overall < threshold sont faibles."""
        u = UnifiedAnalysisState("t")
        u.add_argument("faible")
        u.add_argument("fort")
        u.add_quality_score("arg_1", {}, overall=2.0)   # < 5.0 -> faible
        u.add_quality_score("arg_2", {}, overall=8.0)   # >= 5.0 -> ok
        weak = u.get_weak_arguments(threshold=5.0)
        weak_ids = [p.arg_id for p in weak]
        assert weak_ids == ["arg_1"]

    def test_get_weak_arguments_excludes_unscored(self):
        """Un arg sans score qualité n'est pas 'faible' (pas de score du tout)."""
        u = UnifiedAnalysisState("t")
        u.add_argument("no score")
        assert u.get_weak_arguments(threshold=5.0) == []

    def test_get_fallacious_arguments(self):
        """Args cibles d'au moins 1 sophisme (target valide)."""
        u = make_state_with_fallacies()
        ids = [p.arg_id for p in u.get_fallacious_arguments()]
        assert ids == ["arg_1"]  # arg_2 cible = arg inconnu -> exclu

    def test_get_fallacious_arguments_empty(self):
        u = UnifiedAnalysisState("t")
        assert u.get_fallacious_arguments() == []


def make_state_with_fallacies() -> UnifiedAnalysisState:
    """Helper : 2 args, 2 fallacies (1 cible valide arg_1, 1 cible inconnue)."""
    u = UnifiedAnalysisState("t")
    u.add_argument("cible valide")
    u.add_argument("autre")
    u.add_fallacy("F1", "j1", target_arg_id="arg_1")
    u.add_fallacy("F2", "j2", target_arg_id="arg_999")  # cible inexistante
    return u


class TestEnrichmentSummary:
    def test_summary_counts_and_gaps(self):
        u = UnifiedAnalysisState("t")
        u.add_argument("a1")
        u.add_argument("a2")
        u.add_fallacy("F", "j", target_arg_id="arg_1")
        u.add_quality_score("arg_1", {}, overall=4.0)
        # arg_2 : ni fallacie ni quality -> gaps attendus
        summary = u.get_enrichment_summary()
        assert summary["total_arguments"] == 2
        assert summary["with_fallacy_analysis"] == 1
        assert summary["with_quality_score"] == 1
        # gaps : arg_2 sans quality, arg_1 ET arg_2 sans formal verification
        gap_text = "\n".join(summary["gaps"])
        assert "arg_2 has no quality score" in gap_text
        assert "arg_1 has no formal verification" in gap_text
        assert "arg_2 has no formal verification" in gap_text

    def test_summary_empty_state(self):
        u = UnifiedAnalysisState("t")
        summary = u.get_enrichment_summary()
        assert summary["total_arguments"] == 0
        assert summary["gaps"] == []
