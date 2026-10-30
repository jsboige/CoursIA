# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/evaluation/sanitize_state.py
# Source SHA1 : 236f5290f869cc8f1e76f9b76a15e17cd2321fba (1131L @ 2e2a1c3c)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_sanitize_state.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# PREFIXE D'IMPORT SEUL : l'unique import `argumentation_analysis.*` du
# fichier (l.61) est reecrit en `argumentation_lib._opaque_id` (le module
# jumeau porte ci-contre) ; le reste du corps est byte-for-byte identique a
# l'amont aux fins de ligne pres. La divergence est declaree dans NOTICE-EPITA.
# Role porte : garde d'export : allowlist, opacification et agregats de l'etat d'analyse
# Fins de ligne : l'amont livre ce fichier en CRLF, le depot l'impose en LF
# (`.gitattributes` : `*.py text eol=lf`) ; le contenu est identique a l'amont
# aux fins de ligne pres (cf NOTICE-EPITA, section "Fins de ligne").
# =============================================================================
"""State sanitizer — the UNIQUE export guard for analysis state snapshots.

Produces a privacy-safe dict suitable for commits, dashboards, PRs, and
reports. All quantitative aggregates (counts, scores, structures) are
preserved; only nominative natural-language content is removed or opacified.

Epic #1258 Track 3 (#1261): the de-anonymized pipeline (Track 1/2) lets real
names and readable logic symbols live in the working state and in the
gitignored local artefacts (``evaluation/results/``). This function is the
single chokepoint through which a state snapshot must pass before reaching
git, a dashboard, a PR, or an API: it is where nominative content is scrubbed
at the boundary. Anti-penduple: this is the only guard for a *snapshot*, and a
catch-all scrub is not a substitute for it. One sibling policy survives, and it
is now one implementation instead of a scattered one: the SCDA export scrub
lives at ``evaluation.state_export_scrub._scrub_state_for_export`` and is shared
by both of its callers (#2143). It is deliberately **not** absorbed here — it is
a denylist + ``<scrubbed>`` + entity sweep, where this module is
allowlist-driven and aggregate-preserving; the two agree on all measured state
and diverge on ``extracts[*].name`` for a stated reason, documented at the
eighth pass of that module. ``appendix._strip_leak_keys`` remains a
consolidation target.

Coverage is ALLOWLIST-DRIVEN, and that is a deliberate design: a catch-all
"scrub every long string" pass would erase the structural aggregates
(identifiers, methods, framework types, extension topologies) this function
promises to preserve. The consequence is equally deliberate to state: a
container absent from every table below traverses this function **intact**.
Adding a state container is therefore not neutral — it must be classified
here, and "it carries no natural language" is a claim to be verified against
its producer, not assumed from its name. #1664 measured the cost of leaving
that implicit: ``dung_frameworks`` was covered (#1265, #1271) while six
sibling containers carrying the *same* claim text under the *same* sub-key
were not, for the simple reason that they are declared ``List[Dict]`` and the
passes written for Dung gate on ``isinstance(..., dict)``.

Known and deliberately NOT covered, each for a stated reason:
  * ``workflow_results`` — a free-form dict with no imposed schema, so the
    policy is the #3249 census, not a table entry: on the stored states the
    only ≥30-char leaf family is ``deep_synthesis_value_gates.
    vg1_citation_density.distinct_fields_cited`` — state container names
    (12 distinct values measured), a join vocabulary rather than prose.
  * ``restitution_acts_degraded`` — the degradation notes are a closed
    vocabulary at the producer (#3249 census: 14 templates with digits
    collapsed, every one a code literal of the act writers / readability
    gate, 0 source-text matches); the reading folder reads them from the raw
    local dump, never from a sanitized export.
  * ``formal_synthesis_reports[*].phase_results.*.formulas`` — symbolic, but
    Track 2 makes symbols readable (which is why ``variables`` IS opacified);
    the producer has to be read before deciding.
  * ``extracts[*].name``, ``semantic_index_refs[*].document_id`` — declared as
    names, yet structural in every artefact measured so far, and used as join
    keys downstream. Opacifying them on suspicion would trade a hypothetical
    leak for a certain breakage.
"""

from __future__ import annotations

import copy
from typing import Any

from argumentation_lib._opaque_id import opaque_id

# Fields to remove entirely from the top-level state snapshot.
_STRIP_TOP_LEVEL = {
    "raw_text",
    "full_text",
    "full_text_segment",
    "raw_text_snippet",
    "source_name",
    "document_name",
    "author",
    "date_iso",
    "url",
}

# Fields to replace with opaque IDs (key -> opaque_id(value)).
_OPAQUE_REPLACE = {"source_id"}

# Dict-valued fields whose *values* are nominative strings keyed by generic
# structural labels (key kept, value -> opaque_id). Track 1 (#1259) threads
# real ``source_metadata`` = ``{genre, speaker_role, channel, title, ...}``
# into the working state; the values are nominative (a ``title`` is a source
# name per CLAUDE.md privacy) but the keys are structural. Opacifying the
# values preserves "which metadata was present" without leaking content.
_OPAQUE_DICT_VALUES = {"source_metadata"}

# Dict-valued fields whose entries are nominative *strings*
# (e.g. ``{arg_id: description}``). The string is replaced by a placeholder;
# non-string (structured) values are preserved untouched.
_TEXT_STRIP_DICTS = {"identified_arguments", "arguments"}

# Dict-of-dicts fields: top-level field -> sub-keys whose string values are
# nominative and must be dropped (the rest of each entry is preserved).
#   e.g. identified_fallacies = {fid: {type, justification, family, ...}}
#        belief_sets          = {bs_id: {logic_type, content, propositions?}}
#        argument_quality_scores = {arg_id: {scores, overall, llm_assessment}}
# #1265 (Track 3 follow-up): ``llm_assessment`` is an LLM-written narrative
# that cites/paraphrases the real argument text (verify-the-verification,
# po-2023 finding) — pure narrative, 0 quantitative value, dropped.
_TEXT_STRIP_DICT_OF_DICTS = {
    # #3235: ``problematic_quote`` is a verbatim span of the argument text
    # (measured on the stored states: 557/557 NL strings equal to or
    # contained in an ``identified_arguments`` value on this seat, median
    # length 200 — a capped quote). No export reader reads it: the
    # fallacy→argument join is ``target_argument_id``, resolved at write
    # time (``resolve_fallacy_target_arg_id``) and already on the entry;
    # the text-match fallback joins the LIVE payload before the writer
    # runs. #3217's ``source_quote`` verdict on the fallacy axis: drop the
    # leaf, keep the record.
    "identified_fallacies": {"justification", "problematic_quote"},
    "belief_sets": {"content"},
    "argument_quality_scores": {"llm_assessment"},
    # #3217: ``add_argument`` stores the FULL verbatim quote in the provenance
    # entry (core/shared_state.py:355) — the writer truncates only the copy
    # embedded in the argument text (state_writers.py:1618). Measured: 360/360
    # non-empty quotes survived sanitize byte-identical while the argument
    # text beside them was stripped. ``producer``/``offset``/``offset_basis``
    # are closed-vocabulary/int and survive: drop the leaf, keep the record.
    "argument_provenance": {"source_quote"},
    # #3249 — the honest-absence ledger's free-form ``reason`` leaf. The
    # record is ``{capability, status, degraded, reason, extension_count}``
    # (``add_structured_arg_status``, shared_state.py:1846), written by the
    # six per-axis recorders of ``_record_structured_arg_status`` plus the
    # #3087 failure father. ``status`` is a closed vocabulary at every
    # producer (measured on the stored states: 5 literals); ``reason`` is
    # free-form producer prose, and the ``unavailable`` leg carries the
    # insight's ``refusal_detail`` / the output's ``message`` (docstring,
    # shared_state.py:1904-1913) — the ``errors[*].message`` class of #3261,
    # not declarable closed. The one export reader of the ledger
    # (``rederive_surplus_aggregate.py:142-147``) reads the capability keys
    # and the ``degraded`` boolean, never ``reason``. Drop the leaf, keep the
    # record — the #3239/#3261 gesture on the status axis.
    "structured_arg_status": {"reason"},
}

# Dict-of-dicts fields whose *list sub-keys* carry nominative text entries
# (verified nominative firsthand, #1265): top-level field -> {sub_key}.
# Each list is reduced by opacifying every string entry via ``opaque_id``
# (non-strings left as-is). The list *structure* survives (length, topology)
# so downstream quantitative aggregates (argument/attack counts, Dung extension
# membership) are preserved — only the content is opacified.
#   e.g. dung_frameworks = {df_id: {name, arguments: [claim_text, ...],
#                                   attacks: [[text_a, text_b], ...]}}
# _extract_arguments_from_context (invoke_callables.py:2617) puts the real
# claim text into ``arguments``; ``attacks`` are pairs of those same texts.
_OPAQUE_LIST_SUBKEYS = {
    "dung_frameworks": {"arguments", "attacks"},
    # PL atoms are named after the text they formalise (#2643).
    "belief_sets": {"propositions"},
    # #3235: ``jtms_beliefs`` — the belief name is ``{unit_id}:{text[:66]}``
    # (invoke_callables.py), nominative text with a structural prefix no
    # pass can split; the ATMS writer adds ``ATMS:{node}`` beliefs whose
    # bare-string justifications (``assumption_env:[…]``) embed the same
    # atoms. The name IS a join: the justification ``in_list`` entries
    # repeat it verbatim (measured on the stored states: 122 exact
    # overlaps), so it is opacified, not dropped — the same deterministic
    # ``opaque_id`` keeps the linkage. A scalar value and a bare-string
    # list both ride ``_opacify_list_values``; the dict-shaped
    # justifications' ``in_list``/``out_list`` leaves ride pass 5d.
    "jtms_beliefs": {"name", "justifications"},
}

# Dict-of-dicts whose entries carry a NESTED dict sub-key holding nominative
# list-valued leaves (#1271, po-2023 FB-39 follow-up to #1265): top-level field
# -> {nested_subkey -> {leaf_subkeys}}.
#   dung_frameworks[df_id]["extensions"] = {
#       "extensions":   [[claim_text, ...], ...],  # list of lists (the Dung
#                                                  #   extensions, each a set)
#       "count":        N,                         # structural — survives
#       "sizes":        [...],                     # structural — survives
#       "all_members":  [claim_text, ...],         # flat list (union of members)
#   }
# Tweety returns each extension as a set of the same ``arguments`` claim texts
# (invoke_callables.py:6188-6194); the writer stores them under ``extensions``
# (state_writers.py:903). Opacified recursively via ``_opacify_list_values``
# (handles both the nested list-of-lists and the flat ``all_members``) so set
# arity/topology survive — only the claim *content* is scrubbed. ``name`` is a
# structural label (verified non-nominative firsthand) and is left untouched.
_OPAQUE_NESTED_LIST_SUBKEYS = {
    "dung_frameworks": {"extensions": {"extensions", "all_members"}},
}

# Wave-2 ``formalism_specific`` sidecars on ``dung_frameworks`` entries (#1702).
# The six #1648 writers (ABA/SetAF/Weighted/EAF/DeLP, plus ADF which attaches no
# sidecar) attach a strictly-additive ``entry["formalism_specific"] = {...}`` dict
# to carry data the native Dung projection has no slot for. Each leaf was measured
# at its producer (the anti-pendule of #1702: "mesurer le producteur"), and the
# verdict split is nominative-source-atom vs closed-vocabulary/numeric-aggregate:
#
#   contraries        Dict[assumption_atom, contrary_atom]   — ABA l.968, BOTH
#                                                               keys+values source
#   set_attacks       List[{attackers:[atom], target:atom}]  — SetAF l.1482
#   attack_weights    List[{source, target, weight:float}]   — Weighted l.1541,
#                                                               weight KEPT (numeric)
#   epistemic_beliefs Dict[agent, List[arg_atom]]            — EAF l.1611
#   delp_arguments    str | List[str] (defeasible rule source over source
#                     predicates)                            — DeLP l.1658
#
# Deliberately NOT listed (survive untouched — closed vocab / pure numeric, the
# #1702 anti-pendule symmetrical to the scrubber's own l.156-163):
#   weight_statistics {min/max/avg_weight: float}            — Weighted l.1551
#   program_size      int                                     — DeLP l.1660
#   criterion         str (e.g. "generalized_specificity")   — DeLP l.1662, closed
#
# Parent 2 (``propositional_analysis_results[*].formalism_specific.qbf_quantifiers``)
# is ALSO not listed here and needs no scrub: the QBF writer docstring
# (state_writers.py:1683) measures its leaves as formal logical symbols
# (quantifier type + variable names like ``x``/``y``), not source-derived prose.
# "Covering both parents" (#1702 DoD) is therefore statuated by measurement on
# parent 2 (opaque by construction), not by a table entry.
#
# ``aspic_results.attacks`` (the other #1702 surface) is already covered by pass
# 5d via ``_OPAQUE_NESTED_ITEM_SUBKEYS`` (commit a9bcf516, #1649 follow-up).
#
# Leaf -> opacification mode:
#   "mapping"                 Dict keyed by a source atom -> opacify keys AND
#                             values (values may be a list of atoms).
#   ("dict_list", (fields,))  List[Dict] -> opacify the named string-leaves,
#                             keep the rest (e.g. the numeric ``weight``).
#   "atom_list"               A source-atom string OR list of them -> opacify.
_OPAQUE_FORMALISM_SPECIFIC = {
    "contraries": "mapping",
    "epistemic_beliefs": "mapping",
    "set_attacks": ("dict_list", ("attackers", "target")),
    "attack_weights": ("dict_list", ("source", "target")),
    "delp_arguments": "atom_list",
    # #1693: DL/CL provenance sidecars on fol_analysis_results (DL) and
    # propositional_analysis_results (CL). Each leaf is a list of source-derived
    # logical axioms/conditionals (NL→DL/CL translation of claim text) — same
    # nominative class as DeLP ``program``, so the ``atom_list`` mode applies.
    "tbox": "atom_list",
    "abox_concepts": "atom_list",
    "abox_roles": "atom_list",
    "conditionals": "atom_list",
}

# List-of-dicts fields: top-level field -> sub-keys whose values are
# nominative text to drop (the rest of each item is preserved).
_TEXT_STRIP_LISTS = {
    "counter_arguments": {"counter_content", "generated_text", "original_argument"},
    # #3242 — ``source_quote`` is the verbatim source span the fact-extraction
    # writer attaches to each claim (``_write_fact_extraction_to_state``,
    # state_writers.py:1592, which appends straight onto ``state.extracts``,
    # bypassing ``add_extract``). Measured on the stored states: a verbatim
    # span on essentially every state (the coordinator's replay counted 427
    # spans ≥ 30 chars on 81/81 states; 6 of 7 extracts on the latest doc_A
    # pass). No export reader reads it — the render's quality phase reads
    # ``source_quote`` from the LIVE extraction payload (the measure_1710
    # ``arguments[i]`` schema), never from a sanitized export. The #3217
    # ``argument_provenance`` verdict on the extracts axis: drop the leaf,
    # keep the record (``type`` survives, ``content`` already rides this pass).
    "extracts": {"content", "source_quote"},
    "debate_transcripts": {"proponent_move", "opponent_move", "topic"},
    "transcription_segments": {"text", "speaker"},
    "neural_fallacy_scores": {"text_segment"},
    "analysis_trace": {"summary"},
    "nl_to_logic_translations": {"original_text"},
    "semantic_index_refs": {"query", "snippet"},
    # #3229: ``add_formal_synthesis_report`` stores ``phase_results`` verbatim,
    # republishing every formal phase's output — the Dung extensions (the same
    # claim texts 4c opacifies under ``dung_frameworks``), argument text, and
    # source quotes under quote-named keys. Measured on a real state: 634 NL
    # paths / 1 695 strings survived sanitize under this one container. The
    # #1702 triage (deferred "who reads this?") is settled: NO script reads
    # phase_results from a sanitized export — the .analysis_kb consumers read
    # counts, the acts and structured_arg_status; the live readers (restitution,
    # synthesis) read the in-memory field, which this pass never touches.
    # Decision: drop phase_results from the export; the entry keeps its
    # structural aggregates (overall_validity...), summary stays pass-5-dropped.
    "formal_synthesis_reports": {"summary", "phase_results"},
    # #3235: the two ATMS belief lists no export reader names — the one
    # export reader (``pattern_mining.AtmsBranchingDetector``) reads
    # ``len(assumptions)`` and ``coherent`` only. The producer already
    # writes the quantitative signal as ints (``derivation_count`` /
    # ``contradiction_count``), which survive; the lists' only unique
    # content is the atom identities (measured: 207/21 NL strings, 4/0
    # matching argument text on this seat).
    "atms_contexts": {"derivable_beliefs", "contradicting_beliefs"},
    # #3239 — the formal-logic status messages. Producer census (every
    # ``message=`` site that reaches these three containers):
    # ``_write_propositional_to_state`` (state_writers.py:1678 copies
    # ``output["message"]``), ``_write_fol_to_state`` (:1713-1729 — the
    # ``unavailable:<reason>`` token or the prover's own message),
    # ``_write_modal_to_state`` (:1772-1783, same, including the parser/JVM
    # exception text of modal_handler.py:379-408), ``_write_sat_to_state``
    # (:2229, the backend's ``error`` string) and the external-solver writers
    # (:2994/:3044, ``external solver (<id>)[: msg]``). PL is closed
    # vocabulary (2 literals, pl_handler.py:200-204); FOL adds prover notes
    # and the Mace4 interpretation; modal and SAT can echo parser or JVM
    # text. Not declarable as closed vocabulary — the coordinator measured
    # 0/0/2 argument-text matches on 80 stored states (2 on modal), so drop.
    # Export readers: none. The axis readers (appendix, act2/act3, the
    # campaign render) read ``consistent``/``satisfiable``/``valid`` and
    # counts; ``pattern_mining`` reads ``valid``. The tri-state verdict
    # already attests degradation, so the leaf carries no export-only value.
    # Decision: drop the leaf, keep the record — the #3229/#3217 gesture on
    # the status axis. Not a catch-all: three named containers, one leaf.
    "fol_analysis_results": {"message"},
    "propositional_analysis_results": {"message"},
    "modal_analysis_results": {"message"},
    # #3261 — the top-level ``errors`` container. Producer census:
    # ``log_error`` (shared_state.py:584) appends
    # ``{id, agent_name, message, timestamp}`` and is the only writer, with
    # exactly three callers. ``invoke_callables.py:14581-14589`` builds
    # ``"stakes extraction {status}: {ExceptionType}: {e}"`` from the stakes
    # extractor's ``result["error"]`` (stakes_extractor.py:198/202): its
    # ``parse_error`` leg carries a ``JSONDecodeError``/``KeyError``/
    # ``IndexError`` string — a position, never the document; the model
    # output itself goes to ``stakes``/``stakeholders``/``register``, already
    # scrubbed above, never into the error. The ``llm_error`` leg, though,
    # is ``str(e)`` of a foreign API exception whose vocabulary no table can
    # promise closed. ``workflow_dsl.py:1218`` passes ``str(result.error)``
    # (the phase-error reason); ``sherlock_modern_orchestrator.py:131``
    # passes ``str(exception)``. Measured on the ai-01 states: 9 leaves ≥ 30
    # chars / 85 states, every sampled prefix technical — but the leaf is
    # not declarable technical-only, so it is not kept.
    # Export readers: one — the synthesis snapshot counts
    # ``len(errors)`` as ``error_count`` (shared_state.py:658); nothing
    # reads ``message`` from a sanitized export. Decision: drop the leaf,
    # keep the record — ``id``/``agent_name``/``timestamp`` and the arity
    # survive, the #3239 gesture on the errors axis. Not a catch-all: one
    # named container, one leaf.
    "errors": {"message"},
}

# #3239 rework — the NESTED twin of the formal-logic status leaf above:
# ``external_checks[*].message``. ``_attach_external_recheck``
# (state_writers.py:2918-2929) hangs one dict per re-check on the entry it
# re-ran, carrying ``solver`` / the verdict key / ``agrees`` / ``message``,
# and that ``message`` is the provenance string
# (``_external_provenance(output)``, the same free-form text the top-level
# leaf carries). Pass 5 drops the container's OWN ``message``; the re-check's
# leaf hangs one level deeper and traversed intact — a second NL surface the
# flat table cannot read, not a copy of the first: on this seat the two are
# never the same string (raw corpus: 229/131/229 top-level leaves, 28 FOL +
# 28 modal nested twins, **0 identical**), so dropping the outer leaf scrubs
# nothing of the inner one.
#
# Producer census — exactly TWO containers grow ``external_checks``:
# ``_write_external_fol_solver_to_state`` (:2976) and
# ``_write_external_modal_solver_to_state`` (:3028) are the only callers of
# the shared helper (verified by grep over the production tree; the PL leg
# has no external re-check writer and the raw corpus confirms it — 0 of 393
# ``propositional_analysis_results`` entries carries the key). The PL twin
# therefore does not exist and is not declared: no scrub rides suspicion
# (#1664).
#
# Same verdict as the outer leaf — drop the leaf, keep the record: the
# readers weigh ``solver``, the verdict key (``consistent``/``valid``) and
# the ``agrees`` tri-state; no export reader reads the provenance string
# (the axis readers take the verdict and the counts). Arity of
# ``external_checks`` survives with the leaf gone.
# field -> {sub_key: {nested leaf}}
_NESTED_TEXT_STRIP_SUBKEYS: dict[str, dict[str, set[str]]] = {
    "fol_analysis_results": {"external_checks": {"message"}},
    "modal_analysis_results": {"external_checks": {"message"}},
}

# #3249 — whole containers whose every string is a source-derived atom or
# signature line, with no structural sub-key worth distinguishing: the whole
# value rides ``_opacify_list_values`` so arity (and any cross-container atom
# join, the ``atms_contexts.assumptions`` gesture) survives.
#
#   ``atomic_propositions`` — ``Dict[source_key, List[str]]``
#   (shared_state.py:834), sole writer invoke_callables.py:9739-9744 storing
#   the LLM-extracted proposition atoms. Measured on the stored states: 1 473
#   NL strings on 71/90, atoms named after the text's entities. The only
#   export reader (``run_fp5_formal_matrix.py:115``) reads the count field;
#   the source keys survive untouched.
#
#   ``fol_signature`` — ``List[str]`` of FOL signature lines
#   (invoke_callables.py:1644-1646 / state_writers.py:1745-1750); the member
#   lists carry entity names (measured: 405 NL on 71/90). Export readers
#   count it (``run_spectacular_comparison.py:148`` reads ``len()``) and test
#   populated-ness (:101) — both survive the arity-preserving opacification.
#
# NOT here, decided by measurement on the same corpus: the
# ``restitution_acts_degraded`` notes are a closed vocabulary at the producer
# (14 templates with digits collapsed, every one a code literal of the act
# writers / readability gate; 0 source-text matches) and the only ≥30-char
# leaf family under ``workflow_results`` is
# ``deep_synthesis_value_gates.vg1_citation_density.distinct_fields_cited`` —
# state container names (12 distinct values measured), a join vocabulary, not
# prose. Both stay tolerated with that measurement beside their guard entry;
# no scrub rides a closed vocabulary (#1664).
_OPAQUE_WHOLE_CONTAINER_ATOMS: frozenset[str] = frozenset(
    {"atomic_propositions", "fol_signature"}
)

# LIST-of-dicts fields whose sub-keys carry the same nominative claim text that
# 4b/4c opacify for ``dung_frameworks`` (#1664): top-level field -> {sub_key}.
# Each sub-key is passed through ``_opacify_list_values``, which handles a bare
# string, a flat list and a nested list alike — so arity and topology survive
# and only the content is opacified, exactly as in 4b.
#
# Why these fields, measured rather than assumed: ``_extract_arguments_from_
# context`` (invoke_callables.py:3036) is the helper the 4b comment already
# cites as the one that "puts the real claim text into ``arguments``". It feeds
# 17 callables, not just Dung — ranking, probabilistic, bipolar, ASPIC+, belief
# revision and dialogue among them. Their writers store that list verbatim
# (shared_state.py:941-1032), so these carry claim text *by construction*:
#   bipolar_results[*].supports      = [[text_a, text_b], ...]  (cf. Dung attacks)
#   aspic_results[*].extensions      = [[text, ...], ...]       (cf. Dung extensions)
#   belief_revision_results[*].original/.revised = [text, ...]
#   dialogue_results[*].topic        = a claim text (the writer logs topic[:50])
#
# Anti-pendulum, also measured: the sibling label fields are NOT here.
# ``ranking_results.method``, ``aspic_results.reasoner_type``,
# ``bipolar_results.framework_type``, ``belief_revision_results.method`` are
# closed vocabularies at every producer, and the contract promises to preserve
# structural aggregates. Same verdict for ``dung_frameworks.name``: all ten
# call sites build it from a fixed vocabulary (``aba_preferred``,
# ``setaf_grounded``, ``social_af``, ``dung_arbitration``…), which confirms the
# #1271 firsthand reading — it stays untouched.
_OPAQUE_LIST_OF_DICTS_SUBKEYS = {
    "ranking_results": {"arguments"},
    "probabilistic_results": {"arguments"},
    "bipolar_results": {"arguments", "supports"},
    "aspic_results": {"extensions"},
    "belief_revision_results": {"original", "revised"},
    "dialogue_results": {"topic"},
    # #3235: ``atms_contexts[*].assumptions`` — the arg atoms (measured:
    # 790/790 NL strings equal to argument text on this seat). The export
    # reader counts them per context (``max_assumption_count`` /
    # ``avg_assumptions``), so the list must survive with its arity — the
    # ``dung_frameworks.arguments`` gesture. ``label`` is deliberately NOT
    # here: a closed vocabulary at the producer (six literals in
    # ``_generate_hypotheses``; 4 distinct values, 0 argument-text matches,
    # measured) — the ``dung_frameworks.name`` verdict, it stays untouched.
    "atms_contexts": {"assumptions"},
    # #3242 — the retraction cascade trace (``{trigger, retracted, cascaded,
    # reason}``, jtms_core.py:236 via ``session.jtms.get_retraction_chain()``,
    # invoke_callables.py:3618). ``trigger``/``retracted``/``cascaded`` all
    # carry belief names — the very ``{unit_id}:{text[:66]}`` names pass 4b
    # opacifies under ``jtms_beliefs`` one container over (measured on the
    # stored states: 412/412 cascaded items equal a raw ``jtms_beliefs`` name;
    # the coordinator's replay counted 661 on 78 states). The one export
    # reader (``pattern_mining.JtmsRetractionRateDetector``) reads
    # ``len(retraction_chain)`` only, which this pass never touches. Opacify,
    # not drop: the same deterministic ``opaque_id`` as pass 4b keeps the
    # cross-container join. ``reason`` is deliberately NOT listed — a closed
    # formula at the producer (``f"directly set to {validity}"``,
    # jtms_core.py:240), the ``dung_frameworks.name`` verdict.
    "jtms_retraction_chain": {"trigger", "retracted", "cascaded"},
}

# #3228: the display-label maps on the seven AF containers — sub-key
# ``argument_labels`` = ``{node: label}``, where the label IS the argument
# text (measured on the stored states: every label equals an
# ``identified_arguments`` value, 24 984/24 984 locally; the #3009/#3014 id
# move put the identity in the node ids and carried the text here). The
# KEYS are the raw ``arg_N`` join (``native_dung.rejected_by_arg`` reads
# them) and survive; the VALUES are opacified like ``source_metadata``'s
# (structural key, nominative value), preserving same-text linkage across
# containers. No production reader reads this map in a sanitized export
# (the census names the Act III render, which reads the live state).
# Seven writers in ``shared_state`` take the kwarg — the issue named four;
# the coordinator's replay of the stored states surfaced the three it
# under-counted (``add_dialogue_result``, ``add_probabilistic_result``,
# ``add_bipolar_result``), each keeping 2 143 verbatim labels on that seat.
# Covers both container shapes: ``dung_frameworks`` is dict-keyed, the
# other six are list-appended.
_OPAQUE_LABEL_MAP_SUBKEYS = {
    "dung_frameworks": {"argument_labels"},
    "ranking_results": {"argument_labels"},
    "aspic_results": {"argument_labels"},
    "belief_revision_results": {"argument_labels"},
    "dialogue_results": {"argument_labels"},
    "probabilistic_results": {"argument_labels"},
    "bipolar_results": {"argument_labels"},
}

# #3242 — dict-of-dicts fields whose sub-key is an ATOM MAP keyed by the
# source-derived constant identifiers of the FOL pass-1 signature
# (``state.fol_shared_signature[source_id] = {sorts, predicates,
# constants_raw, fol_solver}``, invoke_callables.py:10412). The FOL 2-pass
# pass 1 derives its constants from the text — the identifiers include
# personal names (the coordinator measured 1 588 keys / 1 208 NL values ≥ 30
# chars on 79 states; 1 115 / 912 on this seat's 49) — so BOTH halves of the
# map are nominative, the ``argument_labels`` lesson of #3228: a table that
# only opacifies values leaves the keys republishing the census in clear.
# Zero export readers name this container (census, #3242 comment), but the
# signature's own internal join is total and free to keep: ``sorts`` members
# ARE the ``constants_raw`` keys (``sorts = {"Thing": list(constants.keys())}``
# when the model gives none), so both ride the same deterministic
# ``opaque_id`` and the join survives the scrub.
# Leaf -> mode:
#   "keys_and_values"  keys are nominative atoms AND values their NL
#                      meaning — opacify both (the ``contraries`` mapping
#                      precedent of pass 4d).
#   "values"           keys are a CLOSED vocabulary (sort names: the pass-1
#                      prompt pins 'If unsure about sort, use "Thing"', and
#                      the fallback synthesises exactly that) — keys survive
#                      the ``dung_frameworks.name`` verdict, only the atom
#                      members are opacified.
# ``predicates`` (sort-typed signatures) and ``fol_solver`` (a solver id) are
# deliberately NOT listed: the issue measured and named the constants axis
# only, and no scrub rides suspicion (#1664).
_OPAQUE_ATOM_MAP_SUBKEYS: dict[str, dict[str, str]] = {
    "fol_shared_signature": {"constants_raw": "keys_and_values", "sorts": "values"},
    # #3252 crossing on #3242 — the sibling ``causes`` map the cascade
    # writer adds to each retraction-chain entry (invoke_callables.py:3697):
    # ``{belief name: "cascaded through justification <names>"}``. BOTH
    # halves are nominative — the keys are belief names, the values embed
    # justification names in a free string — so the ``constants_raw``
    # verdict applies: keys and values opacified, map arity (len()) intact.
    # The value is opacified whole: the embedded names ride one opaque id
    # with the string, the join that matters (belief name ↔ ``jtms_beliefs``
    # and the chain keys) lives in the KEYS.
    "jtms_retraction_chain": {"causes": "keys_and_values"},
}

# List-of-dicts fields with a dict sub-key whose *KEYS* are claim texts
# (#1664): top-level field -> {sub_key}. ``_invoke_probabilistic`` builds
# ``probs = {a: 0.5 for a in args}`` (invoke_callables.py:3896), so the
# acceptance map is indexed by the argument text itself. The keys are
# opacified and the numeric values kept, so the distribution survives intact.
_OPAQUE_LIST_OF_DICTS_MAPPING_KEYS = {
    "probabilistic_results": {"acceptance_probabilities"},
}

# List-of-dicts fields whose sub-key is ITSELF a list of dicts carrying
# nominative leaves (#1664): top-level field -> {sub_key -> {leaf_subkeys}}.
# One level deeper than pass 5.
#   dialogue_results[*].trace[*]      = {round, speaker, action, argument, target}
#       ``argument``/``target`` are claim texts (dialogue_handler.py:100-130);
#       ``speaker``/``action`` are closed vocabularies and survive.
#   debate_transcripts[*].exchanges[*] = {point, rebuttal, scheme, ...}
#       ``_write_debate_to_state`` stores point/rebuttal (the stored-layer
#       names, fed by the prompt's agent_a_point/agent_b_rebuttal — #2135).
#       The earlier proponent_move/opponent_move names were fabricated by no
#       producer, so the declaration had no target until the real names landed
#       here. ``scheme``/``scheme_key``/``critical_question`` are closed
#       vocabularies and are intentionally NOT listed — they survive.
_OPAQUE_NESTED_ITEM_SUBKEYS = {
    "dialogue_results": {"trace": {"argument", "target"}},
    "debate_transcripts": {"exchanges": {"point", "rebuttal"}},
    # #3252 crossing on #3242 — each retraction-chain entry gained
    # ``cascade_edges`` (invoke_callables.py:3691): a list of
    # ``{through_in: [belief names], conclusion: belief name}``, every name
    # the very ``{unit_id}:{text[:66]}`` shape ``trigger``/``retracted``/
    # ``cascaded`` already opacify in pass 5b. The edge count and each
    # edge's arity survive; the deterministic ``opaque_id`` keeps the join
    # with ``jtms_beliefs`` (pass 4b) and with the sibling chain keys.
    "jtms_retraction_chain": {"cascade_edges": {"through_in", "conclusion"}},
    # #1649 privacy follow-up: aspic_results[*].attacks = the qualified attacks
    # surfaced top-level by the #1681 writer (and now read by the #1699 reader).
    # Each attack dict = {target, attacker_premises, scope, attacker_rule}.
    # ``target``/``attacker_premises`` are source-derived PL atoms — ``_pl_atom``
    # (invoke_callables.py) keeps up to 24 leading chars of the argument text,
    # so they ARE nominative → opacify. ``scope`` (undercut/rebut/undermine/
    # unresolved) and ``attacker_rule`` (def_con_N / def_unc_N) are structural
    # closed vocabularies at every producer (measured: handler _qualify_attacks,
    # translator _validate_aspic_*) → preserved, exactly as dung_frameworks.name
    # is. Uses the same opacify_list_values path as dialogue_results.trace.
    "aspic_results": {"attacks": {"target", "attacker_premises"}},
    # #3235: ``jtms_beliefs`` is dict-keyed (``{jtms_N: {…}}``), so this
    # pass's list-only gate could never reach it — the same shape-blindness
    # 5b had before #1664. The justification items are dicts carrying the
    # belief names in ``in_list``/``out_list`` (truncated to 40 chars at
    # the producer); opacifying the leaves keeps the justification
    # topology (how many justifications, how many premises each) while the
    # names themselves ride pass 4b. Bare-string justifications (the ATMS
    # writer's ``assumption_env:[…]``) are already opacified by 4b.
    "jtms_beliefs": {"justifications": {"in_list", "out_list"}},
}

# List-of-dicts fields carrying a symbol-mapping sub-key: a ``Dict[str, str]``
# mapping an opaque atom (``p``, ``mp1``) to its NL meaning. Track 2 makes the
# NL meaning readable/potentially-nominative; the values are opacified with
# ``opaque_id`` so the mapping *structure* survives without leaking content.
_SYMBOL_MAPPING_LIST_FIELDS = {
    "nl_to_logic_translations": "variables",
}

# List-of-dicts fields whose sub-key is itself a DICT carrying nominative list
# leaves (#1646): top-level field -> {dict_subkey -> {leaf_subkeys}}. Unlike
# ``_OPAQUE_NESTED_ITEM_SUBKEYS`` (5d), the sub-key is a single dict, not a list
# of dicts — so the leaves hang directly off it.
#   belief_revision_results[*].minimal_retraction.options = [[belief, ...], ...]
#       ``options`` is a list-of-lists of belief labels (the argument text that
#       names the rupture point). The list topology + arity survive (how many
#       retraction options, how many beliefs each); only the nominative strings
#       are opacified. The sibling ``cardinality``/``base_size``/``touched_count``
#       are ints and are intentionally NOT listed, so they survive untouched.
_OPAQUE_DEEP_DICT_LEAVES: dict[str, dict[str, set[str]]] = {
    "belief_revision_results": {"minimal_retraction": {"options"}},
}

# Fields that are purely narrative text -> replaced with length + marker.
_NARRATIVE_FIELDS = {
    "narrative_synthesis",
    "act1_framing",
    "act2_narrative",
    "act3_conclusion",
    "final_conclusion",
}

# A single struct-valued field whose list sub-keys carry nominative NL.
# Reduced to a counts-only summary (aggregates preserved, all NL removed).
# Each value is (list_subkey_to_count, ...).
_STRUCT_LIST_SCRUB = {
    "stakes_and_stakeholders": ("stakes", "stakeholders"),
}


def _strip_text_from_dict(data: dict[str, Any], text_keys: set[str]) -> dict[str, Any]:
    """Remove text-bearing keys from a dict, keep everything else."""
    return {k: v for k, v in data.items() if k not in text_keys}


def _strip_text_from_list(items: list[Any], text_keys: set[str]) -> list[Any]:
    """Remove text-bearing keys from each dict in a list.

    #3254 — shape-tolerant on a measured old artefact: one stored state
    carries ``counter_arguments`` as bare strings (the field's original
    ``List[str]`` shape — no production writer emits it any more: the
    counter-argument writer filters non-dicts before the adder,
    state_writers.py:608, and the adder only ever appends dicts,
    shared_state.py:1283). A bare
    string IS the text leaf the dict form drops, so it takes the Dung
    ``arguments`` verdict instead: one ``opaque_id`` for the whole prose,
    the slot and the list arity preserved for the count readers
    (``counter_argument_count``, the appendix's « contre_arguments »
    count — the only export readers, both ``len()``). Anything else that
    is not a string carries no NL text by type and rides through
    unchanged — no scrub rides suspicion (#1664). Before this, the
    traversal called ``.items()`` on the string and the whole export
    aborted (fail-closed, but the chokepoint died for that state).
    """
    cleaned: list[Any] = []
    for item in items:
        if isinstance(item, dict):
            cleaned.append(_strip_text_from_dict(item, text_keys))
        elif isinstance(item, str):
            cleaned.append(opaque_id(item) if item else item)
        else:
            cleaned.append(item)
    return cleaned


def _opacify_mapping(mapping: Any) -> Any:
    """Opacify the NL-meaning values of a ``Dict[str, str]`` symbol mapping.

    Atom keys (``p``, ``mp1``) are kept; only the human-readable values are
    passed through ``opaque_id``. Non-string/empty values are left as-is.
    """
    if not isinstance(mapping, dict):
        return mapping
    return {
        k: (opaque_id(v) if isinstance(v, str) and v else v) for k, v in mapping.items()
    }


def _opacify_list_values(value: Any) -> Any:
    """Recursively opacify the strings inside a (possibly nested) list.

    Used for Dung ``arguments`` (flat list of claim texts) and ``attacks``
    (list of [attacker, target] pairs = nested list). The list topology and
    arity survive; only the nominative strings are replaced by ``opaque_id``.
    Non-strings are left as-is.
    """
    if isinstance(value, str):
        return opaque_id(value) if value else value
    if isinstance(value, list):
        return [_opacify_list_values(item) for item in value]
    return value


def _scrub_formalism_specific(sidecar: Any) -> Any:
    """Opacify the nominative leaves of a ``formalism_specific`` sidecar (#1702).

    The Wave-2 sidecar is a heterogeneous dict whose leaves mix source-derived
    PL atoms (the nominative payload — ``_pl_atom`` keeps up to 24 leading chars
    of argument text) with closed vocabularies and numeric aggregates the export
    contract promises to preserve. ``_OPAQUE_FORMALISM_SPECIFIC`` names the
    nominative leaves and their opacification mode; every key NOT in that table
    (``weight_statistics``, ``program_size``, ``criterion``) survives untouched.

    Topology is preserved everywhere: a list stays a list of the same arity, a
    mapping keeps its key count, and the numeric ``weight`` on each
    ``attack_weights`` entry survives — so downstream quantitative aggregates
    (joint-attack arity, weight distribution) are unaffected, exactly as passes
    4b/4c preserve Dung extension sizes.
    """
    if not isinstance(sidecar, dict):
        return sidecar
    out = dict(sidecar)  # shallow copy; untouched keys (criterion/stats) ride through
    for leaf, mode in _OPAQUE_FORMALISM_SPECIFIC.items():
        if leaf not in out:
            continue
        val = out[leaf]
        if mode == "mapping":
            # Dict keyed by a source atom; opacify keys AND values (values may be
            # a list of atoms — _opacify_list_values handles both str and list).
            if isinstance(val, dict):
                out[leaf] = {
                    (
                        opaque_id(k) if isinstance(k, str) and k else k
                    ): _opacify_list_values(v)
                    for k, v in val.items()
                }
        elif isinstance(mode, tuple) and mode[0] == "dict_list":
            fields = mode[1]
            if isinstance(val, list):
                scrubbed: list[Any] = []
                for entry in val:
                    if isinstance(entry, dict):
                        new_entry = dict(entry)
                        for f in fields:
                            if f in new_entry:
                                new_entry[f] = _opacify_list_values(new_entry[f])
                        scrubbed.append(new_entry)
                    else:
                        scrubbed.append(entry)
                out[leaf] = scrubbed
        elif mode == "atom_list":
            # A source-atom string OR a list of them (DeLP ``program`` can be
            # either); _opacify_list_values handles both shapes uniformly.
            out[leaf] = _opacify_list_values(val)
    return out


def _scrub_struct(value: Any, list_keys: tuple[str, ...]) -> dict[str, Any]:
    """Reduce a stakes/stakeholders struct to a counts-only summary."""
    if not isinstance(value, dict):
        return {"stripped": True}
    summary: dict[str, Any] = {"stripped": True}
    for key in list_keys:
        lst = value.get(key)
        summary[f"{key}_count"] = len(lst) if isinstance(lst, list) else 0
    # Short categorical labels are reduced to presence flags: they may carry
    # discursive context, so we keep only the boolean, not the string.
    for str_key in ("rhetorical_register", "discursive_arena"):
        summary[f"has_{str_key}"] = bool(value.get(str_key))
    return summary


def sanitize_state(state: dict[str, Any] | Any) -> dict[str, Any]:
    """Strip nominative fields, keep all quantitative aggregates.

    Args:
        state: A state dict (typically from ``state_snapshot`` in a golden
               fixture) or a ``UnifiedAnalysisState`` instance.  If an object
               with a ``model_dump`` or ``dict`` method is passed, it will be
               serialized first.

    Returns:
        A new dict with all sensitive text removed, opaque IDs substituted,
        symbol mappings opacified, and all counts/scores/structures preserved.
    """
    # Handle Pydantic models or objects with serialization.
    if hasattr(state, "model_dump"):
        data = state.model_dump()
    elif hasattr(state, "dict"):
        data = state.dict()
    elif isinstance(state, dict):
        data = copy.deepcopy(state)
    else:
        data = dict(state)

    # 1. Strip top-level sensitive fields.
    for field in _STRIP_TOP_LEVEL:
        data.pop(field, None)

    # 2. Replace identifying fields with opaque IDs.
    for field in _OPAQUE_REPLACE:
        if field in data and isinstance(data[field], str):
            data[field] = opaque_id(data[field])

    # 2b. Opacify the nominative values of dict-valued identifier fields
    #     (source_metadata = {genre, speaker_role, channel, title, ...}).
    for field in _OPAQUE_DICT_VALUES:
        if field in data and isinstance(data[field], dict):
            data[field] = _opacify_mapping(data[field])

    # 3. Strip text from dict-valued fields whose entries are strings
    #    (identified_arguments, arguments).
    for field in _TEXT_STRIP_DICTS:
        if field in data and isinstance(data[field], dict):
            data[field] = {
                k: {"text_stripped": True} if isinstance(v, str) else v
                for k, v in data[field].items()
            }

    # 4. Strip nominative sub-keys from dict-of-dicts fields
    #    (identified_fallacies.justification, belief_sets.content,
    #    argument_quality_scores.llm_assessment).
    for field, text_keys in _TEXT_STRIP_DICT_OF_DICTS.items():
        if field in data and isinstance(data[field], dict):
            data[field] = {
                key: (
                    _strip_text_from_dict(val, text_keys)
                    if isinstance(val, dict)
                    else val
                )
                for key, val in data[field].items()
            }

    # 4b. Opacify the nominative list-valued sub-keys of dict-of-dicts fields
    #     (dung_frameworks.arguments = [claim_text, ...],
    #      dung_frameworks.attacks = [[text_a, text_b], ...]).
    #     The list structure survives (length + attack topology preserved) so
    #     downstream Dung aggregates are unaffected; only the claim texts are
    #     opacified (#1265, po-2023 firsthand verdict).
    for field, subkeys in _OPAQUE_LIST_SUBKEYS.items():
        if field in data and isinstance(data[field], dict):
            new_entries: dict[str, Any] = {}
            for key, val in data[field].items():
                if isinstance(val, dict):
                    new_entry = dict(val)
                    for sk in subkeys:
                        if sk in new_entry:
                            new_entry[sk] = _opacify_list_values(new_entry[sk])
                    new_entries[key] = new_entry
                else:
                    new_entries[key] = val
            data[field] = new_entries

    # 4c. Opacify nominative list-valued leaves inside a NESTED dict sub-key
    #     of dict-of-dicts fields (dung_frameworks[*].extensions.extensions /
    #     .all_members — the Dung extensions, which are sets of the same claim
    #     texts that live in `arguments`). One level deeper than 4b; same
    #     recursive opacifier, so the nested list-of-lists (extensions) and the
    #     flat list (all_members) are both scrubbed while set arity/topology
    #     survive (#1271, po-2023 FB-39 follow-up to #1265).
    for field, nested_spec in _OPAQUE_NESTED_LIST_SUBKEYS.items():
        if field in data and isinstance(data[field], dict):
            nested_entries: dict[str, Any] = {}
            for key, val in data[field].items():
                if isinstance(val, dict):
                    new_entry = dict(val)
                    for subtree_key, leaf_subkeys in nested_spec.items():
                        subtree = new_entry.get(subtree_key)
                        if isinstance(subtree, dict):
                            new_subtree = dict(subtree)
                            for leaf in leaf_subkeys:
                                if leaf in new_subtree:
                                    new_subtree[leaf] = _opacify_list_values(
                                        new_subtree[leaf]
                                    )
                            new_entry[subtree_key] = new_subtree
                    nested_entries[key] = new_entry
                else:
                    nested_entries[key] = val
            data[field] = nested_entries

    # 4d. Opacify the Wave-2 ``formalism_specific`` sidecar on ``dung_frameworks``
    #     entries (#1702). The six #1648 writers attach this strictly-additive dict
    #     to carry formalism-specific data the native Dung projection has no slot
    #     for (ABA contraries, SetAF joint attacks, Weighted weights, EAF
    #     epistemic beliefs, DeLP program/criterion). Its nominative leaves are
    #     the same source-derived atoms passes 4b/4c opacify one level up, under a
    #     sibling key the dict-of-dicts sub-key passes never inspect. The closed-
    #     vocabulary / numeric-aggregate leaves (criterion, weight_statistics,
    #     program_size) survive by being absent from the spec table.
    if isinstance(data.get("dung_frameworks"), dict):
        for entry in data["dung_frameworks"].values():
            if isinstance(entry, dict) and "formalism_specific" in entry:
                entry["formalism_specific"] = _scrub_formalism_specific(
                    entry["formalism_specific"]
                )

    # 5. Strip nominative sub-keys from list-of-dicts fields.
    for field, text_keys in _TEXT_STRIP_LISTS.items():
        if field in data and isinstance(data[field], list) and text_keys:
            data[field] = _strip_text_from_list(data[field], text_keys)

    # 5b. Opacify the nominative sub-keys of LIST-of-dicts fields — the same
    #     claim text 4b opacifies for the dict-shaped ``dung_frameworks``
    #     (#1664). Four of the five formal-argumentation containers are
    #     declared ``List[Dict]`` and filled by ``append()``, so 4b's
    #     ``isinstance(data[field], dict)`` gate could never reach them.
    for field, subkeys in _OPAQUE_LIST_OF_DICTS_SUBKEYS.items():
        if field in data and isinstance(data[field], list):
            for item in data[field]:
                if not isinstance(item, dict):
                    continue
                for sk in subkeys:
                    if sk in item:
                        item[sk] = _opacify_list_values(item[sk])

    # 5c. Opacify the *keys* of mapping sub-keys inside list-of-dicts fields
    #     (probabilistic_results[*].acceptance_probabilities is indexed by the
    #     argument text). Values are numeric and survive, so the distribution
    #     is unaffected.
    for field, subkeys in _OPAQUE_LIST_OF_DICTS_MAPPING_KEYS.items():
        if field in data and isinstance(data[field], list):
            for item in data[field]:
                if not isinstance(item, dict):
                    continue
                for sk in subkeys:
                    mapping = item.get(sk)
                    if isinstance(mapping, dict):
                        item[sk] = {
                            (opaque_id(k) if isinstance(k, str) and k else k): v
                            for k, v in mapping.items()
                        }

    # 5d. Opacify nominative leaves one level deeper: a list-of-dicts field
    #     whose sub-key is itself a list of dicts (dialogue traces, debate
    #     exchanges). Entry count and turn structure survive. #3235: the
    #     gate reaches dict-keyed containers too (``jtms_beliefs`` is
    #     ``{jtms_N: {…}}``), mirroring 5g's both-shape gate — the existing
    #     entries are all list-shaped, so their behaviour is unchanged.
    for field, nested_spec in _OPAQUE_NESTED_ITEM_SUBKEYS.items():
        container = data.get(field)
        if not isinstance(container, (dict, list)):
            continue
        entries = container.values() if isinstance(container, dict) else container
        for item in entries:
            if not isinstance(item, dict):
                continue
            for subtree_key, leaf_subkeys in nested_spec.items():
                subtree = item.get(subtree_key)
                if not isinstance(subtree, list):
                    continue
                for leaf_item in subtree:
                    if not isinstance(leaf_item, dict):
                        continue
                    for leaf in leaf_subkeys:
                        if leaf in leaf_item:
                            leaf_item[leaf] = _opacify_list_values(leaf_item[leaf])

    # 5e. Opacify nominative leaves nested inside a DICT sub-key of a
    #     list-of-dicts field (#1646): the sub-key is a single dict (not a list
    #     of dicts), so the leaves hang directly off it. Mirrors 5d one level
    #     shallower on the subtree.
    for field, nested_spec in _OPAQUE_DEEP_DICT_LEAVES.items():
        if field in data and isinstance(data[field], list):
            for item in data[field]:
                if not isinstance(item, dict):
                    continue
                for dict_key, leaf_subkeys in nested_spec.items():
                    sub = item.get(dict_key)
                    if not isinstance(sub, dict):
                        continue
                    for leaf in leaf_subkeys:
                        if leaf in sub:
                            sub[leaf] = _opacify_list_values(sub[leaf])

    # 5f. Opacify the ``formalism_specific`` provenance sidecar on the FOL/PL
    #     list-of-dicts containers (#1693). DL attaches the sidecar to
    #     ``fol_analysis_results[*]`` (carrying the input TBox/ABox), CL to
    #     ``propositional_analysis_results[*]`` (carrying the input
    #     conditionals). These containers are not 4d scrub targets (4d covers
    #     ``dung_frameworks``), and the sidecar leaves are NL→DL/CL
    #     translations of source claim text — nominative, same class as the
    #     Wave-2 leaves 4d opacifies. Same ``_scrub_formalism_specific`` and
    #     the same ``_OPAQUE_FORMALISM_SPECIFIC`` table (extended with the
    #     DL/CL leaves); topology (list arity) survives, only the axiom text
    #     is opacified, so downstream counts (tbox_size etc.) are unaffected.
    for field in ("fol_analysis_results", "propositional_analysis_results"):
        if isinstance(data.get(field), list):
            for item in data[field]:
                if isinstance(item, dict) and "formalism_specific" in item:
                    item["formalism_specific"] = _scrub_formalism_specific(
                        item["formalism_specific"]
                    )

    # 5g. Opacify the display-label maps (``argument_labels``) on the four AF
    #     containers (#3228) — ``{node: label}`` where the label is the
    #     argument text itself, the exact text pass 3 strips in
    #     ``identified_arguments`` one field away. Keys (the raw ``arg_N``
    #     join) survive; values are opacified (``_opacify_mapping``, the
    #     ``source_metadata`` gesture). Handles both container shapes:
    #     dict-keyed (``dung_frameworks``) and list-appended (the other
    #     three).
    for field, subkeys in _OPAQUE_LABEL_MAP_SUBKEYS.items():
        container = data.get(field)
        if not isinstance(container, (dict, list)):
            continue
        entries = container.values() if isinstance(container, dict) else container
        for item in entries:
            if not isinstance(item, dict):
                continue
            for sk in subkeys:
                mapping = item.get(sk)
                if isinstance(mapping, dict):
                    item[sk] = _opacify_mapping(mapping)

    # 5h. #3242 — opacify the atom maps of the FOL pass-1 shared signature
    #     (``fol_shared_signature[*].constants_raw`` / ``.sorts``). The
    #     container is dict-keyed (``{source_id: {...}}``), so the 5b/5c
    #     list-of-dicts gates could never reach it — the same shape
    #     blindness 5d fixed for ``jtms_beliefs``. ``constants_raw`` is
    #     opacified keys AND values (both halves nominative); ``sorts`` keeps
    #     its closed-vocabulary sort names and opacifies the atom members.
    #     The deterministic ``opaque_id`` keeps the container's internal
    #     constants↔sorts join, and the map arity (len()) survives every
    #     reader. Untouched leaves (``predicates``, ``fol_solver``) ride
    #     through by being absent from the table. #3252 crossing: the gate
    #     takes both shapes now (5d's precedent) — ``jtms_retraction_chain``
    #     is list-shaped and its ``causes`` map rides ``keys_and_values``;
    #     the existing dict-shaped entry's behaviour is unchanged.
    for field, modes in _OPAQUE_ATOM_MAP_SUBKEYS.items():
        container = data.get(field)
        if not isinstance(container, (dict, list)):
            continue
        entries = container.values() if isinstance(container, dict) else container
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            for sk, mode in modes.items():
                val = entry.get(sk)
                if not isinstance(val, dict):
                    continue
                if mode == "keys_and_values":
                    entry[sk] = {
                        (
                            opaque_id(k) if isinstance(k, str) and k else k
                        ): _opacify_list_values(v)
                        for k, v in val.items()
                    }
                else:  # "values" — the sort names are a closed vocabulary
                    entry[sk] = {k: _opacify_list_values(v) for k, v in val.items()}

    # 5i. #3239 rework — drop the NESTED status leaf, one level under the
    #     container pass 5 already strips: ``external_checks[*].message``
    #     (the re-check provenance ``_attach_external_recheck`` attaches,
    #     state_writers.py:2921-2928). One level down is exactly where the
    #     flat table cannot reach it — the same shape blindness 5d/5h fixed
    #     for ``jtms_beliefs`` and ``fol_shared_signature``. Same verdict as
    #     the outer leaf: drop the leaf, keep the record, so ``solver``, the
    #     verdict key and the ``agrees`` tri-state survive with the list
    #     arity; no export reader reads the provenance string. Only the two
    #     containers that grow ``external_checks`` are declared (measured:
    #     the PL leg has no external re-check writer, 0/393 entries carry the
    #     key). A non-dict re-check entry rides through unchanged — no
    #     producer writes one and the stored corpus holds none, so declaring
    #     a branch for it would be a shape invented here (#1664).
    for field, nested_spec in _NESTED_TEXT_STRIP_SUBKEYS.items():
        entries = data.get(field)
        if not isinstance(entries, list):
            continue
        for item in entries:
            if not isinstance(item, dict):
                continue
            for subtree_key, leaf_keys in nested_spec.items():
                subtree = item.get(subtree_key)
                if not isinstance(subtree, list):
                    continue
                item[subtree_key] = [
                    (
                        _strip_text_from_dict(leaf_item, leaf_keys)
                        if isinstance(leaf_item, dict)
                        else leaf_item
                    )
                    for leaf_item in subtree
                ]

    # 5j. #3249 — opacify the whole-atom containers: every string inside
    #     ``atomic_propositions`` (dict of atom lists) and ``fol_signature``
    #     (list of signature lines) is a source-derived atom, so the entire
    #     value rides ``_opacify_list_values`` — the ``dung_frameworks.
    #     arguments`` gesture applied to the whole field. Arity survives for
    #     the ``len()`` readers; the deterministic ``opaque_id`` keeps any
    #     cross-container atom join. Handles both shapes (dict-keyed and
    #     list); non-string leaves pass through as everywhere else.
    for field in _OPAQUE_WHOLE_CONTAINER_ATOMS:
        container = data.get(field)
        if isinstance(container, dict):
            data[field] = {k: _opacify_list_values(v) for k, v in container.items()}
        elif isinstance(container, list):
            data[field] = _opacify_list_values(container)

    # 6. Opacify symbol-mapping sub-keys inside list-of-dicts fields
    #    (nl_to_logic_translations[*].variables).
    for field, subkey in _SYMBOL_MAPPING_LIST_FIELDS.items():
        if field in data and isinstance(data[field], list):
            for item in data[field]:
                if isinstance(item, dict) and subkey in item:
                    item[subkey] = _opacify_mapping(item[subkey])

    # 7. Replace narrative text with length info.
    for field in _NARRATIVE_FIELDS:
        if field in data and isinstance(data[field], str):
            original = data[field]
            data[field] = {
                "length": len(original),
                "stripped": True,
            }

    # 8. Reduce struct-valued NL fields to counts (stakes_and_stakeholders).
    for field, list_keys in _STRUCT_LIST_SCRUB.items():
        if field in data:
            data[field] = _scrub_struct(data[field], list_keys)

    # 9. #2298 — validate the zero-shot surplus projection's closed shape.
    #    The projection is privacy-safe by construction (natures + opaque
    #    anchors, no statements — a decisive statement can carry a source
    #    excerpt). This pass is the declared classification the allowlist
    #    contract demands: if the shape ever drifts (a statement sneaks in,
    #    an unexpected key), the field is replaced by a marker instead of
    #    traversing intact.
    if "zero_shot_surplus" in data:
        data["zero_shot_surplus"] = _validate_surplus_projection(
            data["zero_shot_surplus"]
        )

    return data


_SURPLUS_PROJECTION_KEYS = {
    "established_items",
    "established_by_nature",
    "procedural_items",
    "carries_non_procedural_surplus",
    "unavailable_reason",
}


def _validate_surplus_projection(value: Any) -> Any:
    """Closed-shape check for the persisted surplus projection (#2298)."""

    if not isinstance(value, dict) or not set(value) <= _SURPLUS_PROJECTION_KEYS:
        return {"scrubbed": "non-conform surplus projection (shape)"}
    items = value.get("established_items")
    if not isinstance(items, list):
        return {"scrubbed": "non-conform surplus projection (items)"}
    for item in items:
        if not isinstance(item, dict) or set(item) != {"nature", "cites"}:
            return {"scrubbed": "non-conform surplus projection (item keys)"}
        if not isinstance(item["nature"], str) or not isinstance(item["cites"], list):
            return {"scrubbed": "non-conform surplus projection (item types)"}
    by_nature = value.get("established_by_nature")
    if not isinstance(by_nature, dict) or not all(
        isinstance(k, str) and isinstance(v, int) for k, v in by_nature.items()
    ):
        return {"scrubbed": "non-conform surplus projection (ventilation)"}
    return value
