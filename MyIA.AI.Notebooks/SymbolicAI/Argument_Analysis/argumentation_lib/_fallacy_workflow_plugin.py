#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/plugins/fallacy_workflow_plugin.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: ecfd9b9c (2026-09-29).
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is identical to the upstream
# source at the cited commit, EXCEPT two documented deviations (#19204, on top
# of the portee-2 vendoring of #19287): (2) the taxonomy CSV is read as
# `utf-8-sig` -- the vendored CSV carries a UTF-8 BOM that plain `utf-8` keeps
# glued to the first header cell, silently voiding every PK lookup and
# degrading the funnel to the one_shot regime; (3) `_persist_trace` detaches
# the descent-trace FileHandler before its truncating write (else NUL padding).
# Measurements: NOTICE-EPITA, section "Entonnoir de sophismes".
#
# This module is a verbatim vendoring of the EPITA-IS tronc plugin set
# (FallacyWorkflowPlugin + ExplorationPlugin + TaxonomyNavigator) used by
# Argumentation-02-Fallacies-Detection. The Python package is renamed
# `argumentation_lib` here so that the upstream `from argumentation_analysis.X`
# imports are rewritten (via a conftest-time sys.path shim, see
# `_paths.py`) -- see NOTICE-EPITA.
#
# The vendoring covers portee 2 of issue #18391 (entonnoir taxonomique
# agentique). The Lexique (DETECTEUR_SOPHISMES, 38 entrees) shipped in
# #18506 is kept as the deterministic baseline; this file enables the
# agentic comparison path (run_guided_analysis + exploration_plugin).
"""FallacyWorkflowPlugin — hierarchical taxonomy-guided fallacy detection.

Rebuilt from commit d2fdd930 with improvements:
- Iterative deepening with double-selection pattern (confirm parent vs explore child)
- Parallel branch exploration via asyncio.gather
- One-shot fallback when iterative deepening fails
- Structured output via IdentifiedFallacy Pydantic model
- Full navigation trace for explainability

See docs/reports/issue_84_git_archaeology.md for architectural history.
"""

import asyncio
import csv
import json
import logging
import os
import time
from pathlib import Path
from typing import Annotated, Dict, List, Optional, Set, Tuple

from semantic_kernel.kernel import Kernel
from semantic_kernel.functions.kernel_function_decorator import kernel_function
from semantic_kernel.connectors.ai.open_ai import (
    OpenAIChatCompletion,
    OpenAIPromptExecutionSettings,
)
from semantic_kernel.connectors.ai.function_choice_behavior import (
    FunctionChoiceBehavior,
)
from semantic_kernel.connectors.ai.chat_completion_client_base import (
    ChatCompletionClientBase,
)
from semantic_kernel.contents import (
    ChatHistory,
    FunctionCallContent,
    FunctionResultContent,
)

from argumentation_analysis.agents.utils.taxonomy_navigator import TaxonomyNavigator
from argumentation_analysis.core.plaintext_destination import (
    PlaintextDestinationError,
    check_plaintext_destination,
)
from argumentation_analysis.plugins.exploration_plugin import ExplorationPlugin
from argumentation_analysis.utils.taxonomy_local_overrides import purge_rows
from argumentation_analysis.plugins.identification_models import (
    IdentifiedFallacy,
    FallacyAnalysisResult,
)

logger = logging.getLogger(__name__)


class FallacyWorkflowPlugin:
    """Plugin orchestrating hierarchical taxonomy-guided fallacy detection.

    Uses a master-slave kernel architecture:
    - Master: orchestrates the workflow phases
    - Slave: constrained LLM with only ExplorationPlugin tools available

    Detection algorithm:
    1. Present root categories + their children to the LLM
    2. LLM selects candidate branches via explore_branch calls
    3. For each candidate, iterative deepening with double-selection:
       - Show parent (confirm) + children (explore deeper)
       - LLM calls confirm_fallacy OR explores a child
    4. Parallel exploration of multiple branches
    5. Fallback to one-shot if iterative approach fails
    """

    MAX_BRANCHES = 4
    MAX_CANDIDATES = 20  # Wide-net Phase 1 cap (#578)
    MIN_CONFIRM_DEPTH = 2  # Don't accept confirmations at depth < 2 (too generic)

    # FB-30 (#1107): restored agentic taxonomy navigation by subtraction.
    # There is NO depth cap — the taxonomy leaves are the only cap (real
    # taxonomy depth ≤ 10). The previous MAX_DEPTH_PER_BRANCH=8 made the 12
    # leaf nodes at depth 9-10 structurally unreachable. Runaway protection
    # (#708) is preserved by a generous per-branch LLM-CALL budget (circuit
    # breaker), NOT a depth cap. One navigation iteration == one LLM call, so
    # this bounds total calls while letting the LLM descend freely to leaves.
    MAX_NAVIGATION_LLM_CALLS = 18
    # How many subtree levels the navigation prompt shows at each step (a
    # multi-level cluster, not just immediate children) so the LLM can jump
    # levels via explore_branch(any_pk) — the original summer-2025 design.
    NAV_CLUSTER_DEPTH = 2

    # RA-3 #1048 item 2: bounded recursive sub-branch fan-out.
    # At a fork the LLM may flag several promising children; the engine used to
    # keep one and silently drop the rest (recall loss — the fork prompt even
    # invites multi-child exploration the single-path loop ignored). When
    # enabled, the top child stays the primary path AND the next few are
    # explored as concurrent recursive sub-branches. The wall-clock bench
    # (PR #1067) shows Phase-2-style gather fan-out is ≥2x at realistic
    # wide-net widths, so the work overlaps rather than adding latency.
    # Bounded by a per-fork width + a shared global budget
    # (_BranchSupersessionTracker.try_consume_fanout) and pruned by
    # supersession — anti-pendule #1019, never "parallelize everything".
    ENABLE_SUBBRANCH_FANOUT = True
    SUBBRANCH_FANOUT_WIDTH = 2  # max extra children spawned per fork
    SUBBRANCH_FANOUT_BUDGET = 12  # max sub-branches spawned per analysis

    # FB-35 (#1121): global cost-based circuit breaker on the agentic descent.
    # MAX_NAVIGATION_LLM_CALLS bounds a SINGLE branch (≤18 calls) and the
    # fan-out budget bounds sub-branch SPAWNING (≤12) — but their PRODUCT
    # (~20 wide-net candidates × 18 calls × fan-out) is uncapped, which is
    # what explodes on a large/entity-dense corpus (the doc_A runaway). This
    # bounds the TOTAL descent LLM calls across ALL branches + sub-branches
    # of one run_guided_analysis — a cost-based breaker, NOT a depth cap
    # (anti-pendule: FB-30 subtracted the depth cap on purpose; this is
    # additive only on the call-count dimension, never on depth). Tunable via
    # env so a pathological corpus can be bounded without a code change.
    DESCENT_TOTAL_CALL_BUDGET = int(os.getenv("FALLACY_DESCENT_CALL_BUDGET", "240"))

    # #2157: wide-net Phase 1 wall-clock budget — the only one on the descent
    # chain that was not env-tunable. Default UNCHANGED at 60 s: raising it is
    # a measurement decision (issue #2157, piste 3), not a fix.
    WIDENET_PHASE1_TIMEOUT = float(os.getenv("FALLACY_WIDENET_PHASE1_TIMEOUT", "60.0"))

    class _BranchSupersessionTracker:
        """Track confirmed fallacies for branch supersession during parallel exploration.

        When a branch confirms a fallacy at depth D with confidence C, sibling
        branches exploring ancestor nodes at depth < D can abandon early — the
        confirmed match is strictly more specific.  This saves LLM calls by
        cutting exploration of branches that are superseded.

        Thread-safety: all mutation is done from the asyncio event loop, so
        no explicit locking is needed (single-threaded concurrency model).
        """

        def __init__(
            self,
            navigator: TaxonomyNavigator,
            fanout_budget: int = 0,
            descent_call_budget: int = 0,
        ):
            self._navigator = navigator
            # (pk, taxonomy_path, depth, confidence)
            self._confirmed: List[Tuple[str, str, int, float]] = []
            self.superseded_count = 0
            # RA-3 #1048 item 2: shared budget bounding recursive sub-branch
            # fan-out across ALL branches of one analysis. Mirrors the agentic
            # navigation's MAX_NAVIGATION_LLM_CALLS guardrail — fan-out is
            # capped, never unbounded (anti-pendule #1019). 0 ⇒ fan-out
            # disabled.
            self._fanout_budget = fanout_budget
            self.fanout_spawned = 0
            # FB-35 (#1121): shared global budget bounding the TOTAL number of
            # descent LLM calls across ALL branches + sub-branches of one
            # analysis. The per-branch MAX_NAVIGATION_LLM_CALLS bounds one
            # branch; the fan-out budget bounds spawning; THIS bounds their
            # product (the dimension that explodes on large corpora). One
            # descent iteration == one LLM call, so this counts cost, not
            # depth. 0 ⇒ disabled (no global cap, legacy behavior). When
            # exhausted the descent stops and run_guided_analysis surfaces a
            # fail-loud flag (anti-theater #1019: partial results + honest
            # marker, never a silent empty/truncated outcome).
            self._descent_call_budget = descent_call_budget
            self._descent_call_enabled = descent_call_budget > 0
            self._descent_calls_remaining = descent_call_budget
            self.descent_calls_made = 0
            self.descent_budget_exceeded = False

        def register(self, pk: str, depth: int, confidence: float) -> None:
            """Register a confirmed fallacy."""
            node = self._navigator.get_node(pk)
            path = node.get("path", "") if node else ""
            self._confirmed.append((pk, path, depth, confidence))

        def check_superseded(
            self, current_pk: str, current_depth: int
        ) -> Optional[str]:
            """Return the superseding PK if *current_pk* is an ancestor of a
            confirmed node that is strictly deeper.  ``None`` otherwise.
            """
            current_node = self._navigator.get_node(current_pk)
            if not current_node:
                return None
            current_path = current_node.get("path", "")
            if not current_path:
                return None

            for conf_pk, conf_path, conf_depth, conf_conf in self._confirmed:
                # Only supersede when confirmed node is strictly deeper
                if conf_depth <= current_depth:
                    continue
                # Same lineage: confirmed path descends from current path
                if conf_path.startswith(current_path + "."):
                    return conf_pk
            return None

        @property
        def confirmation_count(self) -> int:
            return len(self._confirmed)

        def try_consume_fanout(self) -> bool:
            """Consume one unit of the shared sub-branch fan-out budget.

            Returns True while budget remains (a sub-branch may be spawned),
            False once exhausted. Bounds total recursive fan-out across all
            branches of one analysis so concurrent token spend stays capped
            (anti-pendule #1019: bounded fan-out, never "explore everything").
            """
            if self._fanout_budget <= 0:
                return False
            self._fanout_budget -= 1
            self.fanout_spawned += 1
            return True

        def try_consume_descent_call(self) -> bool:
            """Consume one unit of the global descent LLM-call budget (FB-35 #1121).

            Returns True while budget remains (the calling branch may make its
            LLM call and continue descending), False once exhausted. Bounds the
            TOTAL descent LLM calls across all branches + recursive sub-branches
            of one analysis — the per-branch MAX_NAVIGATION_LLM_CALLS and the
            fan-out spawn budget each bound a single dimension, but their
            product (~candidates × calls × fan-out) is what explodes on a
            large/entity-dense corpus. This is a COST-based breaker (one
            iteration == one LLM call), never a depth cap. When it returns
            False the caller stops descending and the run surfaces a fail-loud
            flag. 0 ⇒ disabled (legacy unbounded-within-branch behavior).

            Thread-safety: single-threaded asyncio event loop, no locking
            needed (same model as try_consume_fanout above).
            """
            if not self._descent_call_enabled:
                return True  # no global cap configured (legacy behavior)
            if self._descent_calls_remaining <= 0:
                self.descent_budget_exceeded = True
                return False
            self._descent_calls_remaining -= 1
            self.descent_calls_made += 1
            return True

    def __init__(
        self,
        master_kernel: Kernel,
        llm_service: ChatCompletionClientBase,
        taxonomy_file_path: Optional[str] = None,
        taxonomy_data: Optional[list] = None,
        logger: Optional[logging.Logger] = None,
    ):
        self.master_kernel = master_kernel
        self.llm_service = llm_service
        self.logger = logger or logging.getLogger(__name__)
        self.language = "fr"

        # #2324: marche déterministe de la descente. En mode parallèle
        # (défaut, production inchangée), l'entrelacement des branches dans le
        # ``asyncio.gather`` du Phase 2 — et donc la supersession croisée et
        # l'ordre de consommation du budget — dépend des latences de réponse :
        # la forme de la marche est choisie par le LLM *et par le scheduler* à
        # chaque session d'enregistrement. Une seule session ne peut alors pas
        # produire des cassettes couvrant chaque marche possible. En mode
        # séquentiel, la marche devient une fonction pure des réponses
        # enregistrées : candidats dans l'ordre du wide-net, une branche après
        # l'autre — le rejeu suit exactement la marche enregistrée. La descente
        # a toujours LIEU (nœuds visités, LLM consulté) ; seule la
        # séquentialisation change.
        self.descent_sequential = os.getenv("FALLACY_DESCENT_SEQUENTIAL", "0") == "1"

        data = taxonomy_data or []
        load_error: Optional[str] = None
        if not data and taxonomy_file_path:
            try:
                # `utf-8-sig`, not `utf-8`: the vendored CSV carries a UTF-8 BOM
                # that plain `utf-8` keeps glued to the first header cell,
                # silently voiding every PK lookup (deviation #2, see header
                # and NOTICE-EPITA "Entonnoir de sophismes").
                with open(taxonomy_file_path, mode="r", encoding="utf-8-sig") as infile:
                    reader = csv.DictReader(infile)
                    data = purge_rows(list(reader))
            except FileNotFoundError:
                load_error = f"file not found at {taxonomy_file_path}"
            except Exception as e:
                load_error = f"read error: {e}"

        self.taxonomy_navigator = TaxonomyNavigator(taxonomy_data=data)
        self.exploration_plugin = ExplorationPlugin(
            self.taxonomy_navigator, language=self.language
        )

        # #2141: three degradation states, each said in its own words. The
        # previous single message ("loading failed **or** has no root nodes")
        # merged "tried and failed" with "never tried": a navigator that was
        # never handed a source was reported as a failed load, so nothing
        # distinguished a bypassed funnel from a broken one — and every neural
        # run bypassed it silently. self.taxonomy_state is the readable form.
        roots = self.taxonomy_navigator.get_root_nodes()
        if roots:
            self.taxonomy_state = "loaded"
            self.logger.info(
                f"Taxonomy loaded: {len(data)} nodes, {len(roots)} root categories"
            )
        elif load_error is not None:
            self.taxonomy_state = "load_failed"
            self.logger.error(
                f"Taxonomy source provided but the load failed ({load_error}) — "
                "the navigator is empty and the wide-net funnel will resolve no candidate."
            )
        elif not data and taxonomy_file_path is None and not taxonomy_data:
            self.taxonomy_state = "none"
            self.logger.warning(
                "Taxonomy: no source provided (neither taxonomy_file_path nor "
                "taxonomy_data) — no load was attempted, the navigator is empty by "
                "construction, and the wide-net funnel will fall back to one-shot."
            )
        else:
            self.taxonomy_state = "empty_roots"
            self.logger.warning(
                f"Taxonomy loaded {len(data)} rows but no root node (depth==1) — "
                "the navigator has no category and the wide-net funnel will resolve no candidate."
            )

    def _create_slave_kernel(self) -> Tuple[Kernel, OpenAIPromptExecutionSettings]:
        """Create a constrained kernel with only ExplorationPlugin available.

        The slave LLM can ONLY call explore_branch, confirm_fallacy, or
        conclude_no_fallacy. It cannot respond with free text.
        """
        slave_kernel = Kernel()
        slave_kernel.add_service(self.llm_service)
        slave_kernel.add_plugin(self.exploration_plugin, "Exploration")

        slave_settings = OpenAIPromptExecutionSettings(
            function_choice_behavior=FunctionChoiceBehavior.Auto(auto_invoke=False)
        )
        return slave_kernel, slave_settings

    def _mark_fallback(self, result_json: str) -> str:
        """#2141: make a bypassed funnel readable to a consumer.

        A one-shot result is reached by three routes — an explicit
        ``use_one_shot`` request, a wide-net that failed to parse, and a
        wide-net that ran but could resolve no candidate. Only the last means
        the master/slave funnel was bypassed *because its navigator had
        nothing to resolve against*. The marker names that case; when the
        navigator loaded (``taxonomy_state == "loaded"``) the one-shot is a
        genuine choice and no marker is added.
        """
        if self.taxonomy_state == "loaded":
            return result_json
        try:
            parsed = json.loads(result_json)
        except (json.JSONDecodeError, TypeError):
            return result_json
        if not isinstance(parsed, dict) or "fallacies" not in parsed:
            return result_json
        parsed["fallback_reason"] = "empty_taxonomy_navigator"
        parsed["taxonomy_state"] = self.taxonomy_state
        return json.dumps(parsed, indent=2, ensure_ascii=False)

    def _mark_regime(self, result_json: str, regime: str) -> str:
        """#2141 temps 2: name the regime the result was actually produced under.

        ``one_shot`` when a single full-taxonomy call produced it — whether that
        was requested outright or reached by a funnel that resolved nothing.
        ``funnel`` when the wide-net descent ran and produced it. A consumer can
        read which regime it got without re-deriving the call path, which is what
        makes the two regimes comparable instead of merely co-existing.
        """
        try:
            parsed = json.loads(result_json)
        except (json.JSONDecodeError, TypeError):
            return result_json
        if not isinstance(parsed, dict) or "fallacies" not in parsed:
            return result_json
        parsed["analysis_regime"] = regime
        return json.dumps(parsed, indent=2, ensure_ascii=False)

    def _create_one_shot_kernel(self) -> Tuple[Kernel, OpenAIPromptExecutionSettings]:
        """Create a kernel for one-shot fallback analysis."""
        kernel = Kernel()
        kernel.add_service(self.llm_service)
        settings = OpenAIPromptExecutionSettings(
            function_choice_behavior=FunctionChoiceBehavior.NoneInvoke()
        )
        return kernel, settings

    def _build_root_presentation(self) -> str:
        """Build a formatted presentation of root categories + their children."""
        roots = self.taxonomy_navigator.get_root_nodes()
        lines = []
        for root in roots:
            pk = root.get("PK", "")
            name = root.get(f"text_{self.language}", root.get("nom_vulgarisé", pk))
            desc = root.get(f"desc_{self.language}", "")
            lines.append(f"\n## {name} (ID: {pk})")
            if desc:
                lines.append(f"   {desc}")

            children = self.taxonomy_navigator.get_children(pk)
            for child in children:
                cpk = child.get("PK", "")
                cname = child.get(
                    f"text_{self.language}", child.get("nom_vulgarisé", cpk)
                )
                cdesc = child.get(f"desc_{self.language}", "")[:120]
                lines.append(f"   - {cname} (ID: {cpk}): {cdesc}")

        return "\n".join(lines)

    def _build_roots_index(self) -> Dict[str, str]:
        """Build a lookup: lowercase root name → root PK."""
        roots = self.taxonomy_navigator.get_root_nodes()
        index = {}
        for root in roots:
            pk = root.get("PK", "")
            name = root.get(f"text_{self.language}", root.get("nom_vulgarisé", ""))
            index[name.lower().strip()] = pk
        return index

    def _build_deep_index(self, max_depth: int = 3) -> Dict[str, str]:
        """Build a lookup: lowercase name → PK for nodes up to max_depth.

        FB-19 (#1040): gives wide-net Phase 1 a head start by mapping to
        depth-2/3 nodes instead of only depth-1 roots. This shaves 2-3
        levels off the descent and makes reaching depth-5+ nodes feasible.
        """
        index: Dict[str, str] = {}
        for node in self.taxonomy_navigator.taxonomy_data:
            try:
                depth = int(node.get("depth", 0))
            except (ValueError, TypeError):
                continue
            if depth < 1 or depth > max_depth:
                continue
            pk = node.get("PK", "")
            if not pk:
                continue
            name = node.get(f"text_{self.language}", node.get("nom_vulgarisé", ""))
            if name:
                index[name.lower().strip()] = pk
            # Also index by family / subfamily keywords for broader matching
            for field in ("Famille", "Sous-Famille", "Soussousfamille"):
                val = node.get(field, "")
                if val and val.lower().strip() not in index:
                    index[val.lower().strip()] = pk
        return index

    # German → English keyword bridge for multilingual support (#600)
    _DE_TO_EN_KEYWORDS: Dict[str, str] = {
        "strohmann": "straw man",
        "strohmann-argument": "straw man",
        "dammbruch": "slippery slope",
        "rückführung": "slippery slope",
        "gefühl": "emotion",
        "emotionale appellation": "emotion",
        "entweder-oder": "false dilemma",
        "schwarz-weiß": "false dilemma",
        "vorschnelle verallgemeinerung": "hasty generalization",
        "übergeneralisierung": "hasty generalization",
        "zirkelschluss": "circular reasoning",
        "zirkulär": "circular reasoning",
        "roter hering": "red herring",
        "nebenthema": "red herring",
        "ablenkung": "red herring",
        "heuchlerisch": "tu quoque",
        "schuld durch assoziation": "guilt by association",
        "mitläufereffekt": "bandwagon",
        "mehrheitsargument": "bandwagon",
        "traditionsargument": "tradition",
        "brunnenvergiftung": "poisoning the well",
        "wahrer schotte": "no true scotsman",
        "fehlschluss der ursache": "false cause",
        "suggestivfrage": "loaded question",
        "fangfrage": "loaded question",
        "angst": "appeal to fear",
        "mitleid": "appeal to pity",
        "rosinenpickerei": "cherry picking",
        "personenangriff": "ad hominem",
        "autorität": "authority",
        "berufung auf": "authority",
        "unzureichend": "insufficiency",
        "beeinflussung": "influence",
        "betrug": "cheating",
        "täuschung": "cheating",
        "behinderung": "obstruction",
        "blockade": "obstruction",
        "obstruktion": "obstruction",
    }

    def _map_fallacy_to_root_pk(
        self, fallacy_name: str, roots_index: Dict[str, str]
    ) -> Optional[str]:
        """Map a free-text fallacy name to the closest root PK via keyword matching.

        Supports FR/EN/DE keywords via a three-pass strategy:
        1. Direct lookup in roots_index
        2. German → English keyword bridge, then roots_index
        3. Pattern-based fuzzy matching (FR/EN/DE patterns)
        """
        name_lower = fallacy_name.lower().strip()
        if name_lower in roots_index:
            return roots_index[name_lower]

        # Pass 2: German bridge — translate DE keyword to EN, then lookup
        for de_keyword, en_keyword in self._DE_TO_EN_KEYWORDS.items():
            if de_keyword in name_lower and en_keyword in roots_index:
                return roots_index[en_keyword]

        root_keywords = {
            "authority": ["autorit", "autorität", "berufung auf"],
            "ad hominem": [
                "ad hominem",
                "attaque",
                "personne",
                "personenangriff",
                "ad-personam",
            ],
            "straw man": ["paille", "distortion", "strohmann", "strohmann-argument"],
            "slippery slope": ["pente glissante", "dammbruch", "rückführung"],
            "emotion": ["émotion", "sentiment", "gefühl", "emotionale appellation"],
            "false dilemma": [
                "faux dilemme",
                "dilemme",
                "entweder-oder",
                "schwarz-weiß",
            ],
            "hasty generalization": [
                "généralisation",
                "vorschnelle verallgemeinerung",
                "übergeneralisierung",
            ],
            "circular reasoning": [
                "circulaire",
                "pétition",
                "zirkelschluss",
                "zirkulär",
            ],
            "red herring": ["hareng", "diversion", "roter hering", "nebenthema"],
            "tu quoque": ["tu quoque", "hypocrisie", "heuchlerisch"],
            "guilt by association": [
                "association",
                "culpabilité",
                "schuld durch assoziation",
            ],
            "bandwagon": [
                "ad populum",
                "majeure",
                "mitläufereffekt",
                "mehrheitsargument",
            ],
            "tradition": ["tradition", "traditionsargument"],
            "non sequitur": ["non sequitur", "inconséquence", "nicht zwingend"],
            "poisoning the well": ["empoisonnement", "brunnenvergiftung"],
            "no true scotsman": ["vrai écossais", "wahrer schotte", "kein wahrer"],
            "false cause": [
                "fausse cause",
                "causalité",
                "fehlschluss der ursache",
                "post hoc",
            ],
            "loaded question": ["question chargée", "suggestivfrage", "fangfrage"],
            "manipulation": ["manipulation", "beeinflussung"],
            "appeal to fear": ["angst", "appell an die angst"],
            "appeal to pity": ["mitleid", "mitleidsappell"],
            "begging the question": ["implikation", "voraussetzung"],
            "cherry picking": ["rosinenpickerei", "auswahl"],
            "deflection": ["ablenkung", "themenwechsel"],
            "insufficiency": ["unzureichend", "mangelhaft", "insufficient"],
            "influence": ["beeinflussung", "manipulation"],
            "cheating": ["betrug", "trick", "täuschung"],
            "obstruction": ["behinderung", "blockade", "obstruktion"],
        }

        for keyword, patterns in root_keywords.items():
            if keyword in name_lower or any(p in name_lower for p in patterns):
                for root_name, pk in roots_index.items():
                    if any(p in root_name for p in patterns):
                        return pk

        for root_name, pk in roots_index.items():
            if root_name in name_lower or name_lower in root_name:
                return pk

        return None

    def _map_fallacy_to_deep_pk(
        self, fallacy_name: str, deep_index: Dict[str, str]
    ) -> Optional[str]:
        """Map a free-text fallacy name to the deepest matching PK.

        Tries the deep index (depth ≤ 3) first, giving the agentic navigation
        a head start. Falls back to None if no match.
        """
        name_lower = fallacy_name.lower().strip()

        # Direct match in deep index
        if name_lower in deep_index:
            return deep_index[name_lower]

        # Substring match: check if any deep index key is contained in the name
        for key, pk in deep_index.items():
            if key in name_lower or name_lower in key:
                return pk

        return None

    async def _wide_net_candidates(self, argument_text: str) -> List[str]:
        """Phase 1 wide-net: LLM lists all candidate fallacies 0-shot-style.

        Returns list of PKs (depth 1-3 via deep index), up to MAX_CANDIDATES.

        Tries deep index first (depth 2-3), falls back to root PKs. This gives
        the agentic navigation a 2-3 level head start; from there the LLM
        descends freely (multi-level cluster, no depth cap — FB-30 #1107).
        """
        kernel, settings = self._create_one_shot_kernel()
        roots = self.taxonomy_navigator.get_root_nodes()
        roots_text = "\n".join(
            f"- {r.get('text_fr', r.get('nom_vulgarisé', r.get('PK', '')))} (PK: {r.get('PK', '')})"
            for r in roots
        )

        prompt = (
            f"Analyze this text exhaustively for logical fallacies:\n\n"
            f"--- TEXT ---\n{argument_text[:8000]}\n--- END ---\n\n"
            "List EVERY fallacy you can find. For each, respond with a JSON object:\n"
            '{"fallacy_name": "...", "root_category": "...", "confidence": 0.0-1.0}\n\n'
            "Respond with a JSON array of objects. Be thorough — aim for 10-20 fallacies.\n"
            "Even borderline or arguable cases should be included.\n\n"
            f"Available root categories:\n{roots_text}"
        )

        history = ChatHistory(
            system_message="You are a fallacy detection expert. Be exhaustive. Respond ONLY with a JSON array."
        )
        history.add_user_message(prompt)

        try:
            response = await asyncio.wait_for(
                self.llm_service.get_chat_message_content(
                    chat_history=history, settings=settings, kernel=kernel
                ),
                timeout=self.WIDENET_PHASE1_TIMEOUT,
            )
            raw = str(response).strip()
        except asyncio.TimeoutError:
            # str(TimeoutError()) == "" — a catch-all here logged an empty
            # message, so a budget overrun silently degraded the funnel to
            # one-shot (#2157). Same shape as the two named handlers below.
            self.logger.warning(
                f"Wide-net Phase 1 timed out after {self.WIDENET_PHASE1_TIMEOUT}s "
                f"(FALLACY_WIDENET_PHASE1_TIMEOUT), falling back to one-shot"
            )
            return []
        except Exception as e:
            self.logger.warning(f"Wide-net Phase 1 failed: {type(e).__name__}: {e}")
            return []

        candidates_raw = []
        try:
            if "```json" in raw:
                raw = raw.split("```json")[1].split("```")[0]
            elif "```" in raw:
                raw = raw.split("```")[1].split("```")[0]
            start = raw.find("[")
            end = raw.rfind("]") + 1
            if start >= 0 and end > start:
                candidates_raw = json.loads(raw[start:end])
            elif raw.strip().startswith("{"):
                candidates_raw = [json.loads(raw)]
        except (json.JSONDecodeError, ValueError):
            self.logger.warning(f"Wide-net parse failed, raw: {raw[:200]}")
            return []

        if not isinstance(candidates_raw, list):
            candidates_raw = [candidates_raw]

        # FB-19: try deep index first (depth 2-3), then fall back to root PKs
        deep_index = self._build_deep_index(max_depth=3)
        roots_index = self._build_roots_index()
        candidate_pks = []
        for c in candidates_raw:
            if not isinstance(c, dict):
                continue
            root_cat = c.get("root_category", "")
            fallacy_name = c.get("fallacy_name", "")

            # Try deep index first (FB-19)
            pk = self._map_fallacy_to_deep_pk(fallacy_name, deep_index)
            if not pk:
                pk = self._map_fallacy_to_deep_pk(root_cat, deep_index)
            # Fall back to root mapping
            if not pk:
                pk = self._map_fallacy_to_root_pk(root_cat, roots_index)
            if not pk:
                pk = self._map_fallacy_to_root_pk(fallacy_name, roots_index)
            if pk and pk not in candidate_pks:
                candidate_pks.append(pk)

        candidate_pks = candidate_pks[: self.MAX_CANDIDATES]
        self.logger.info(
            f"Phase 1 wide-net (FB-19 deep): {len(candidates_raw)} candidates, "
            f"{len(candidate_pks)} unique PKs: {candidate_pks}"
        )
        return candidate_pks

    async def _execute_tool_calls(
        self,
        response_items: list,
        slave_kernel: Kernel,
        history: ChatHistory,
    ) -> List[Dict]:
        """Execute function calls from the LLM response and feed results back."""
        results = []
        for item in response_items:
            if not isinstance(item, FunctionCallContent):
                continue

            func_name = item.name or ""
            # Handle both "Exploration-explore_branch" and "explore_branch" formats
            short_name = func_name.split("-")[-1] if "-" in func_name else func_name
            arguments = item.arguments or {}

            # Parse arguments if they're a string
            if isinstance(arguments, str):
                try:
                    arguments = json.loads(arguments)
                except (json.JSONDecodeError, TypeError):
                    arguments = {}

            try:
                plugin = slave_kernel.plugins.get("Exploration")
                if plugin and short_name in plugin:
                    func = plugin[short_name]
                    # Call the underlying Python method directly to avoid
                    # SK 1.40's KernelFunction.__call__ requiring kernel arg
                    method = getattr(self.exploration_plugin, short_name, None)
                    if method is not None:
                        result_str = str(method(**arguments))
                    else:
                        result_str = str(func(slave_kernel, **arguments))
                else:
                    result_str = json.dumps({"error": f"Unknown function: {func_name}"})
            except Exception as e:
                self.logger.warning(f"Tool call {func_name} failed: {e}")
                result_str = json.dumps({"error": str(e)})

            # Feed result back to history
            history.add_message(
                FunctionResultContent(
                    id=item.id, result=result_str
                ).to_chat_message_content()
            )

            # Parse result for caller
            try:
                parsed = json.loads(result_str)
            except (json.JSONDecodeError, TypeError):
                parsed = {"raw": result_str}
            parsed["function_name"] = short_name
            results.append(parsed)

        return results

    def _render_subtree_cluster(self, root_pk: str, max_levels: int = 2) -> str:
        """Render a truncated multi-level subtree under ``root_pk``.

        FB-30 (#1107): the navigation prompt shows the LLM a cluster spanning
        ``max_levels`` below the current node (not just immediate children),
        so the LLM can jump levels by calling ``explore_branch`` on a deeper
        PK directly. Each line carries name + PK + short description so the
        LLM has enough signal to pick any node.

        Args:
            root_pk: the PK whose subtree to render (rendered as the root line).
            max_levels: how many levels of descendants to include below the
                root (1 = children only, 2 = children + grandchildren).

        Returns:
            A newline-separated, indented cluster string. Empty string if the
            root has no descendants.
        """
        lines: List[str] = []

        def walk(pk: str, level: int) -> None:
            if level > max_levels:
                return
            node = self.taxonomy_navigator.get_node(pk)
            if not node:
                return
            indent = "  " * level
            name = node.get(f"text_{self.language}", node.get("nom_vulgarisé", pk))
            desc = node.get(f"desc_{self.language}", "")
            # Keep the description short so the whole cluster fits the prompt.
            desc_short = desc[:120] + ("…" if len(desc) > 120 else "")
            depth = node.get("depth", "?")
            lines.append(f"{indent}- {name} (ID: {pk}, depth {depth}): {desc_short}")
            for child in self.taxonomy_navigator.get_children(pk):
                walk(child.get("PK", ""), level + 1)

        walk(root_pk, 0)
        return "\n".join(lines)

    async def _explore_single_branch(
        self,
        argument_text: str,
        start_pk: str,
        slave_kernel: Kernel,
        slave_settings: OpenAIPromptExecutionSettings,
        reasoning_history: Optional[List[str]] = None,
        supersession_tracker: Optional["_BranchSupersessionTracker"] = None,
        results_sink: Optional[List[IdentifiedFallacy]] = None,
    ) -> Optional[IdentifiedFallacy]:
        """Explore a single taxonomy branch using iterative deepening.

        At each level, the LLM sees:
        - The PARENT node (marked "CONFIRM this if it matches")
        - All CHILD nodes (marked "EXPLORE deeper")

        Memory of reasons: The LLM's justification at each level is captured
        and passed to the next level's prompt for context continuity.

        Double intention: After exploring to a node, the LLM sees BOTH the
        parent (to confirm/stop) AND children (to explore deeper).

        The LLM calls confirm_fallacy to stop, explore_branch to go deeper,
        or conclude_no_fallacy to abandon the branch.

        Args:
            supersession_tracker: Optional shared tracker. When a parallel
                branch confirms a deeper, more specific fallacy, this branch
                can abandon early if it is exploring an ancestor node.
        """
        current_pk = start_pk
        navigation_trace = [start_pk]
        reasoning_history = reasoning_history or []

        # FB-30 (#1107): no depth cap — the LLM descends until it reaches a
        # leaf (the only natural cap, depth ≤ 10). Bounded only by a generous
        # per-branch LLM-call budget (circuit breaker, preserves #708). One
        # iteration == one LLM call (either the leaf-confirmation call or the
        # navigation call), so this counts calls, not depth.
        llm_call_count = 0
        while llm_call_count < self.MAX_NAVIGATION_LLM_CALLS:
            # FB-35 (#1121): global cost-based circuit breaker. Consume one
            # unit of the shared descent-call budget BEFORE making this
            # iteration's LLM call. When the global budget (across all
            # concurrent branches + sub-branches) is exhausted, stop
            # descending — run_guided_analysis surfaces a fail-loud flag. This
            # is a COST cap (one iteration == one call), NOT a depth cap, so
            # the LLM still descends freely to leaves within the budget.
            if supersession_tracker is not None and not (
                supersession_tracker.try_consume_descent_call()
            ):
                self.logger.warning(
                    "  Global descent call budget exceeded at branch %s "
                    "(call #%d) — stopping descent (fail-loud, FB-35 #1121)",
                    start_pk,
                    supersession_tracker.descent_calls_made,
                )
                break
            llm_call_count += 1
            # --- Supersession check (RA-3 #1048) ---
            if supersession_tracker is not None:
                current_node = self.taxonomy_navigator.get_node(current_pk)
                current_depth = int(current_node.get("depth", 0)) if current_node else 0
                superseding_pk = supersession_tracker.check_superseded(
                    current_pk, current_depth
                )
                if superseding_pk:
                    supersession_tracker.superseded_count += 1
                    self.logger.info(
                        f"  Branch SUPERSeded at {current_pk} (depth {current_depth}) "
                        f"by confirmed {superseding_pk}"
                    )
                    return None
            current_node = self.taxonomy_navigator.get_node(current_pk)
            if not current_node:
                break

            children = self.taxonomy_navigator.get_children(current_pk)

            # Leaf node — ask LLM for confirmation instead of auto-confirm (#471)
            if not children:
                self.logger.info(
                    f"  Leaf node reached: {current_pk} "
                    f"({current_node.get(f'text_{self.language}', '')})"
                )
                leaf_name = current_node.get(
                    f"text_{self.language}",
                    current_node.get("nom_vulgarisé", current_pk),
                )
                leaf_desc = current_node.get(f"desc_{self.language}", "")
                leaf_example = current_node.get(f"example_{self.language}", "")

                reasoning_context = ""
                if reasoning_history:
                    reasoning_context = (
                        "\n--- PREVIOUS REASONING ---\n"
                        + "\n".join(
                            f"{i+1}. {r}" for i, r in enumerate(reasoning_history[-3:])
                        )
                        + "\n"
                    )

                leaf_prompt = (
                    f'Text to analyze: "{argument_text[:500]}"\n\n'
                    f"You reached a LEAF node in the fallacy taxonomy.\n"
                    f"Node: {leaf_name} (PK: {current_pk})\n"
                    f"Description: {leaf_desc}\n"
                    f"{'Example: ' + leaf_example[:200] if leaf_example else ''}\n"
                    f"{reasoning_context}\n"
                    "Does this leaf node correctly identify a fallacy in the text?\n"
                    "IMPORTANT: Only confirm if the reasoning in the text is genuinely fallacious.\n"
                    "Legitimate uses of authority, emotion, or tradition are NOT fallacies.\n\n"
                    "Choose ONE action:\n"
                    f"- confirm_fallacy(node_pk='{current_pk}', justification='...', confidence=0.0-1.0) "
                    "if this matches\n"
                    "- conclude_no_fallacy(reason='...') if no match"
                )

                leaf_history = ChatHistory(
                    system_message=(
                        "You are a fallacy classifier. You MUST call exactly one function. "
                        "Do NOT respond with text.\n"
                        "When evaluating circular reasoning: accept paraphrased/implicit forms "
                        "where the premise presupposes the conclusion.\n"
                        "When evaluating appeal to emotion: confirm only if emotion is the "
                        "primary persuasive operator, not merely illustrative."
                    )
                )
                leaf_history.add_user_message(leaf_prompt)

                try:
                    leaf_response = await asyncio.wait_for(
                        self.llm_service.get_chat_message_contents(
                            chat_history=leaf_history,
                            settings=slave_settings,
                            kernel=slave_kernel,
                        ),
                        timeout=30.0,
                    )
                except asyncio.TimeoutError:
                    self.logger.warning(
                        f"  Leaf confirmation timed out for {current_pk}"
                    )
                    break
                except Exception as e:
                    self.logger.warning(f"  Leaf confirmation LLM call failed: {e}")
                    break

                leaf_items = []
                if leaf_response:
                    for msg in leaf_response:
                        if hasattr(msg, "items"):
                            leaf_items.extend(msg.items)

                leaf_calls = [
                    i for i in leaf_items if isinstance(i, FunctionCallContent)
                ]
                if not leaf_calls:
                    self.logger.info("  No function call at leaf — branch abandoned")
                    break

                leaf_results = await self._execute_tool_calls(
                    leaf_calls, slave_kernel, leaf_history
                )

                for lr in leaf_results:
                    if lr.get("function_name") == "confirm_fallacy" and lr.get(
                        "confirmed"
                    ):
                        leaf_depth = int(current_node.get("depth", 0))
                        # Register leaf confirmation for supersession (RA-3 #1048)
                        if supersession_tracker is not None:
                            supersession_tracker.register(
                                current_pk,
                                leaf_depth,
                                lr.get("confidence", 0.7),
                            )
                        return IdentifiedFallacy(
                            fallacy_type=lr.get("name", lr.get("name_fr", leaf_name)),
                            taxonomy_pk=current_pk,
                            taxonomy_path=current_node.get("path", ""),
                            explanation=lr.get("justification", ""),
                            confidence=lr.get("confidence", 0.7),
                            navigation_trace=navigation_trace,
                            family=current_node.get("Famille", ""),
                            depth=leaf_depth,
                        )
                    elif lr.get("function_name") == "conclude_no_fallacy":
                        self.logger.info(
                            f"  Leaf not confirmed: {lr.get('reason', '')}"
                        )
                        return None

                break

            # Build double-selection prompt with memory of reasons
            parent_name = current_node.get(
                f"text_{self.language}", current_node.get("nom_vulgarisé", current_pk)
            )
            parent_desc = current_node.get(f"desc_{self.language}", "")
            parent_example = current_node.get(f"example_{self.language}", "")

            # Memory of reasons: include previous reasoning
            reasoning_context = ""
            if reasoning_history:
                reasoning_context = (
                    "\n--- PREVIOUS REASONING (for context) ---\n"
                    + "\n".join(
                        f"{i+1}. {r}" for i, r in enumerate(reasoning_history[-3:])
                    )
                    + "\n"
                )

            options_text = (
                f"\n--- OPTIONS at depth {current_node.get('depth', '?')} ---\n"
            )
            # Double intention: Parent can be re-selected to confirm
            options_text += (
                f"[CONFIRM] {parent_name} (ID: {current_pk})\n"
                f"  Description: {parent_desc}\n"
            )
            if parent_example:
                options_text += f"  Example: {parent_example[:200]}\n"
            options_text += (
                "  → Select this node AGAIN (confirm_fallacy with pk='{current_pk}') "
                "if this level matches and you want to STOP here.\n"
            )

            # FB-30 (#1107): multi-level cluster, not just immediate children.
            # The LLM sees a truncated subtree NAV_CLUSTER_DEPTH levels deep,
            # so it can jump levels by calling explore_branch on a grandchild
            # PK directly (the original summer-2025 agentic design), rather
            # than descending one level per iteration.
            options_text += (
                f"\n[EXPLORE DEEPER] — subtree under {parent_name} "
                f"(showing {self.NAV_CLUSTER_DEPTH + 1} levels; "
                "you may explore ANY listed node, not only the immediate children):\n"
            )
            options_text += self._render_subtree_cluster(
                current_pk, max_levels=self.NAV_CLUSTER_DEPTH
            )

            prompt = (
                f'Text to analyze: "{argument_text[:500]}"\n\n'
                f"You are navigating the fallacy taxonomy. Current position: {parent_name}\n"
                f"{reasoning_context}"
                f"{options_text}\n"
                "Choose ONE action:\n"
                "- Call explore_branch(node_pk='<any_listed_pk>') to explore a node — "
                "you may jump several levels deep by picking a grandchild/great-grandchild PK directly\n"
                f"- Call confirm_fallacy(node_pk='{current_pk}', ...) to confirm THIS level and stop\n"
                "- Call conclude_no_fallacy(reason='...') if no match in this branch\n"
                "You MUST call exactly one function."
            )

            history = ChatHistory(
                system_message=(
                    "You are a fallacy classifier navigating a taxonomy tree. "
                    "Your goal is to find the MOST SPECIFIC (deepest) matching fallacy. "
                    "You MUST call one of the available functions. "
                    "Do NOT respond with text — only function calls.\n\n"
                    "CRITICAL MULTI-BRANCH INSTRUCTION:\n"
                    "1. When selecting among children, PREFER exploring MULTIPLE children (call explore_branch "
                    "   multiple times) rather than confirming immediately at the current level.\n"
                    "2. Confirm at the current level when EITHER: (a) you are at a LEAF node, OR "
                    "   (b) NO child matches even partially, OR (c) every available child is a NARROWER "
                    "   SPECIALIZATION than the fallacy the text actually exhibits. For (c): if the "
                    "   current node correctly names the fallacy but its children each describe a "
                    "   more specific sub-case the argument does NOT instantiate (e.g. the current "
                    "   node is 'circular reasoning' but the only child is a specific named variant "
                    "   like a Cartesian circle that the text is not), confirm the current node rather "
                    "   than descending to a leaf that will not match. Descending to a non-matching "
                    "   leaf only to then conclude_no_fallacy loses a correct classification.\n"
                    "3. Do NOT call conclude_no_fallacy prematurely. The text likely contains "
                    "   fallacies in multiple branches. Abandon a branch only if you are CERTAIN "
                    "   there is no match at ANY descendant.\n\n"
                    "IMPORTANT: Only confirm a fallacy if the reasoning in the text is "
                    "genuinely fallacious. Legitimate uses of authority, emotion, "
                    "tradition are NOT fallacies.\n\n"
                    "DETECTION GUIDANCE — INDIRECT FORMS:\n"
                    "Circular reasoning (petitio principii): The conclusion may be "
                    "re-injected as a premise through PARAPHRASE, not literal repetition. "
                    "Watch for: restating the claim in different words as if it were new "
                    "evidence; using a synonym or reworded assertion as justification. "
                    "This includes implicit circularity where the premise presupposes "
                    "the conclusion without stating it outright.\n"
                    "Appeal to emotion: Distinguish between (a) an argument where emotion "
                    "is the PRIMARY OPERATOR — fear, indignation, pride, pity, loyalty "
                    "DRIVE the persuasion instead of reasons — and (b) an argument that "
                    "merely ILLUSTRATES with emotional language but provides substantive "
                    "reasoning. Only (a) is fallacious. Look for: arguments that would "
                    "collapse if the emotional charge were removed; moral-duty framing "
                    "that replaces logical justification; urgency appeals that bypass evidence."
                )
            )
            history.add_user_message(prompt)

            try:
                response = await asyncio.wait_for(
                    self.llm_service.get_chat_message_contents(
                        chat_history=history,
                        settings=slave_settings,
                        kernel=slave_kernel,
                    ),
                    timeout=30.0,
                )
            except asyncio.TimeoutError:
                self.logger.warning(
                    f"  LLM call timed out during branch exploration at {current_pk}"
                )
                break
            except Exception as e:
                self.logger.warning(f"  LLM call failed during branch exploration: {e}")
                break

            # Extract function calls from response
            all_items = []
            if response:
                for msg in response:
                    if hasattr(msg, "items"):
                        all_items.extend(msg.items)

            tool_calls = [i for i in all_items if isinstance(i, FunctionCallContent)]
            if not tool_calls:
                self.logger.info("  No function calls in response — branch exhausted")
                break

            # Execute tool calls
            tool_results = await self._execute_tool_calls(
                tool_calls, slave_kernel, history
            )

            # Classify the LLM's tool calls. Original behaviour: the first
            # confirm/conclude decides the branch; explore_branch advances the
            # path. RA-3 #1048 item 2: capture *all* explore targets so extra
            # promising children can be fanned out as bounded concurrent
            # sub-branches instead of being silently dropped.
            confirm_result = None
            conclude_result = None
            explore_targets: List[Tuple[str, dict]] = []  # (next_pk, node_info)
            for result in tool_results:
                func_name = result.get("function_name", "")
                if func_name == "confirm_fallacy" and result.get("confirmed"):
                    confirm_result = result
                    break
                elif func_name == "conclude_no_fallacy":
                    conclude_result = result
                    break
                elif func_name == "explore_branch":
                    node_info = result.get("node", {})
                    next_pk = node_info.get("pk", "")
                    if next_pk and next_pk != current_pk:
                        explore_targets.append((next_pk, node_info))

            # --- Decision, in priority order (preserves original semantics) ---
            if confirm_result is not None:
                confirmed_pk = confirm_result.get("pk", "")
                confirmed_node = self.taxonomy_navigator.get_node(confirmed_pk)
                confirmed_depth = (
                    int(confirmed_node.get("depth", 0)) if confirmed_node else 0
                )
                justification = confirm_result.get("justification", "")

                # Capture reasoning for memory
                reasoning_summary = (
                    f"Confirmed {current_node.get(f'text_{self.language}', current_pk)} "
                    f"at depth {confirmed_depth}: {justification}"
                )
                reasoning_history.append(reasoning_summary)

                # Reject too-shallow confirmations — force deeper exploration
                if confirmed_depth < self.MIN_CONFIRM_DEPTH and children:
                    self.logger.info(
                        f"  Confirmation at depth {confirmed_depth} rejected "
                        f"(min={self.MIN_CONFIRM_DEPTH}), forcing deeper exploration"
                    )
                    # Pick the first child as default deeper path
                    first_child = children[0]
                    current_pk = first_child.get("PK", "")
                    navigation_trace.append(current_pk)
                    continue  # re-iterate outer loop with new current_pk

                # Build full explanation with reasoning history
                full_explanation = justification
                if reasoning_history:
                    full_explanation += (
                        f" | Reasoning path: {'; '.join(reasoning_history)}"
                    )

                # Register confirmation for branch supersession (RA-3 #1048)
                if supersession_tracker is not None:
                    supersession_tracker.register(
                        confirmed_pk,
                        confirmed_depth,
                        confirm_result.get("confidence", 0.7),
                    )

                return IdentifiedFallacy(
                    fallacy_type=confirm_result.get(
                        "name",
                        confirm_result.get("name_fr", confirm_result.get("pk", "")),
                    ),
                    taxonomy_pk=confirmed_pk,
                    taxonomy_path=confirm_result.get("path", ""),
                    explanation=full_explanation,
                    confidence=confirm_result.get("confidence", 0.7),
                    navigation_trace=navigation_trace,
                    family=current_node.get("Famille", ""),
                    depth=confirmed_depth,
                )

            if conclude_result is not None:
                reason = conclude_result.get("reason", "no reason")
                # Capture reasoning for memory
                reasoning_summary = f"Abandoned {current_node.get(f'text_{self.language}', current_pk)}: {reason}"
                reasoning_history.append(reasoning_summary)
                self.logger.info(f"  Branch abandoned: {reason}")
                return None

            if not explore_targets:
                self.logger.info("  explore_branch returned same/empty node")
                break

            # RA-3 #1048 item 2: the top child stays the primary path; extra
            # promising children are fanned out as bounded concurrent
            # sub-branches (additive — the primary path is never regressed).
            primary_pk, primary_info = explore_targets[0]
            extras = explore_targets[1:]
            if (
                extras
                and self.ENABLE_SUBBRANCH_FANOUT
                and results_sink is not None
                and supersession_tracker is not None
            ):
                await self._fanout_subbranches(
                    extras,
                    argument_text,
                    slave_kernel,
                    slave_settings,
                    reasoning_history,
                    supersession_tracker,
                    results_sink,
                )

            # Capture reasoning for memory - why the primary branch was chosen
            primary_name = primary_info.get(
                "name", primary_info.get("name_fr", primary_pk)
            )
            reasoning_history.append(
                f"Explored {primary_name} from "
                f"{current_node.get(f'text_{self.language}', current_pk)}"
            )
            current_pk = primary_pk
            navigation_trace.append(current_pk)
            self.logger.info(
                f"  Exploring deeper: {primary_name} "
                f"(reasoning history: {len(reasoning_history)} steps)"
            )

        return None

    async def _fanout_subbranches(
        self,
        extras: List[Tuple[str, dict]],
        argument_text: str,
        slave_kernel: Kernel,
        slave_settings: OpenAIPromptExecutionSettings,
        reasoning_history: List[str],
        supersession_tracker: "_BranchSupersessionTracker",
        results_sink: List[IdentifiedFallacy],
    ) -> None:
        """Explore extra promising children as bounded concurrent sub-branches.

        RA-3 #1048 item 2. When a fork yields more than one promising child the
        primary path follows the top child (handled by the caller) and the next
        few are explored concurrently here. Results are appended to
        *results_sink* — additive, so the primary single-path descent is never
        regressed. Bounded by:

          - ``SUBBRANCH_FANOUT_WIDTH`` (extra children spawned per fork), and
          - the tracker's shared global fan-out budget (per analysis),

        and pruned by the supersession tracker (dead-end / superseded
        sub-branches abandon early). Anti-pendule #1019: fan-out is capped, not
        unbounded — it mirrors the agentic navigation's
        ``MAX_NAVIGATION_LLM_CALLS`` discipline.
        """
        tasks = []
        for sub_pk, sub_info in extras[: self.SUBBRANCH_FANOUT_WIDTH]:
            if not supersession_tracker.try_consume_fanout():
                self.logger.info("  Sub-branch fan-out budget exhausted")
                break
            sub_name = sub_info.get("name", sub_info.get("name_fr", sub_pk))
            self.logger.info(f"  Fan-out sub-branch: {sub_name} (PK: {sub_pk})")
            tasks.append(
                self._explore_single_branch(
                    argument_text,
                    sub_pk,
                    slave_kernel,
                    slave_settings,
                    reasoning_history=list(reasoning_history),
                    supersession_tracker=supersession_tracker,
                    results_sink=results_sink,
                )
            )
        if not tasks:
            return
        if self.descent_sequential:
            # #2324 : le fan-out suit la même discipline que le Phase 2 —
            # l'ordre d'arrivée dans ``results_sink`` devient déterministe.
            sub_results = []
            for task in tasks:
                try:
                    sub_results.append(await task)
                except Exception as exc:  # noqa: BLE001 — parité gather
                    sub_results.append(exc)
        else:
            sub_results = await asyncio.gather(*tasks, return_exceptions=True)
        for r in sub_results:
            if isinstance(r, IdentifiedFallacy):
                results_sink.append(r)
            elif isinstance(r, BaseException):
                self.logger.warning(f"  Sub-branch fan-out error: {r}")

    @kernel_function(
        name="run_guided_analysis",
        description=(
            "Analyze text for fallacies using hierarchical taxonomy navigation. "
            "Uses iterative deepening with parallel branch exploration, "
            "falling back to one-shot if needed."
        ),
    )
    async def run_guided_analysis(
        self,
        argument_text: Annotated[str, "The text to analyze for fallacies"],
        trace_log_path: Optional[str] = None,
        use_one_shot: bool = False,
    ) -> Annotated[str, "JSON result with identified fallacies"]:
        """Execute hierarchical fallacy detection with one-shot fallback.

        Algorithm:
        1. Present root categories to slave LLM
        2. Slave selects candidate branches (via explore_branch calls)
        3. For each candidate, iterative deepening with double-selection
        4. Parallel exploration of up to MAX_BRANCHES branches
        5. If no result, fall back to one-shot full-taxonomy approach

        FB-30 (#1107): the mechanical per-level beam descent is removed.
        Agentic navigation in step 3 now has no depth cap (taxonomy leaves are
        the only cap) and shows the LLM a multi-level cluster so it can jump
        levels — restoring the original summer-2025 design by subtraction.
        """
        file_handler = self._attach_trace_handler(trace_log_path)

        try:
            self.logger.info(f"--- Fallacy Analysis for: '{argument_text[:80]}...' ---")

            # Direct one-shot mode if requested
            if use_one_shot:
                return self._mark_regime(
                    await self._run_one_shot(argument_text), "one_shot"
                )

            # Phase 1: Wide-net candidate selection (#578)
            candidate_pks = await self._wide_net_candidates(argument_text)
            if not candidate_pks:
                self.logger.info(
                    "Wide-net produced no candidates — falling back to one-shot"
                )
                _fallback = self._mark_fallback(await self._run_one_shot(argument_text))
                return self._mark_regime(_fallback, "one_shot")

            self.logger.info(
                f"Phase 1: {len(candidate_pks)} wide-net candidates: {candidate_pks}"
            )

            # Phase 2: Parallel iterative deepening on ALL candidates
            slave_kernel, slave_settings = self._create_slave_kernel()
            # Branch supersession tracker (RA-3 #1048) — shared across branches.
            # The fan-out budget bounds recursive sub-branch exploration
            # (item 2) across the whole analysis.
            tracker = self._BranchSupersessionTracker(
                self.taxonomy_navigator,
                fanout_budget=(
                    self.SUBBRANCH_FANOUT_BUDGET if self.ENABLE_SUBBRANCH_FANOUT else 0
                ),
                descent_call_budget=self.DESCENT_TOTAL_CALL_BUDGET,
            )
            # Sink collecting fan-out sub-branch results (RA-3 #1048 item 2).
            # Additive: top-level branch primaries return via the gather below;
            # any extra promising children explored as sub-branches land here.
            fanout_sink: List[IdentifiedFallacy] = []
            exploration_tasks = [
                self._explore_single_branch(
                    argument_text,
                    pk,
                    slave_kernel,
                    slave_settings,
                    reasoning_history=None,
                    supersession_tracker=tracker,
                    results_sink=fanout_sink,
                )
                for pk in candidate_pks
            ]
            if self.descent_sequential:
                # #2324 : une branche après l'autre, dans l'ordre des candidats
                # — même exceptions que ``gather(return_exceptions=True)`` :
                # une branche qui échoue n'interrompt pas les suivantes.
                branch_results = []
                for task in exploration_tasks:
                    try:
                        branch_results.append(await task)
                    except Exception as exc:  # noqa: BLE001 — parité gather
                        branch_results.append(exc)
            else:
                branch_results = await asyncio.gather(
                    *exploration_tasks, return_exceptions=True
                )

            # Phase 3: Collect + dedup by leaf taxonomy_pk (keep highest confidence)
            identified = []
            seen_pks = {}
            total_iterations = 0
            if tracker.confirmation_count > 0 or tracker.superseded_count > 0:
                self.logger.info(
                    f"Branch supersession: {tracker.confirmation_count} confirmed, "
                    f"{tracker.superseded_count} branches superseded"
                )
            for result in branch_results:
                if isinstance(result, Exception):
                    self.logger.warning(f"Branch exploration error: {result}")
                    continue
                if isinstance(result, IdentifiedFallacy):
                    total_iterations += len(result.navigation_trace)
                    leaf_pk = result.fallacy_type
                    if (
                        leaf_pk in seen_pks
                        and seen_pks[leaf_pk].confidence >= result.confidence
                    ):
                        continue
                    seen_pks[leaf_pk] = result
                    identified = [r for r in identified if r.fallacy_type != leaf_pk]
                    identified.append(result)

            # Merge fan-out sub-branch results (RA-3 #1048 item 2) with the same
            # dedup-by-leaf rule (keep highest confidence per leaf PK).
            for result in fanout_sink:
                total_iterations += len(result.navigation_trace)
                leaf_pk = result.fallacy_type
                if (
                    leaf_pk in seen_pks
                    and seen_pks[leaf_pk].confidence >= result.confidence
                ):
                    continue
                seen_pks[leaf_pk] = result
                identified = [r for r in identified if r.fallacy_type != leaf_pk]
                identified.append(result)
            if tracker.fanout_spawned:
                self.logger.info(
                    f"Sub-branch fan-out explored {tracker.fanout_spawned} "
                    f"extra branch(es) (RA-3 #1048 item 2)"
                )

            if identified:
                identified.sort(key=lambda f: f.confidence, reverse=True)
                # FB-30 (#1107): the mechanical beam descent (_beam_descent,
                # Phase 3b) is removed — restored agentic navigation in
                # _explore_single_branch (no depth cap + multi-level cluster)
                # now reaches deep/lateral nodes directly. Method label no
                # longer carries the "_beam" suffix.
                method = "wide_net_parallel"
                analysis_result = FallacyAnalysisResult(
                    fallacies=identified,
                    exploration_method=method,
                    branches_explored=len(candidate_pks),
                    total_iterations=total_iterations,
                )
                self.logger.info(
                    f"--- Analysis complete: {len(identified)} fallacies identified "
                    f"via {method} ({len(candidate_pks)} branches) ---"
                )
                result_json = analysis_result.model_dump_json(indent=2)
                # FB-35 (#1121): surface the global descent-call diagnostic
                # always (calls made across all branches + sub-branches) and a
                # fail-loud marker when the budget was hit. When exceeded, the
                # fallacies above are PARTIAL (the descent was cut short) —
                # flagged honestly so the report/convergence layer marks the
                # phase degraded (anti-theater #1019).
                result_obj = json.loads(result_json)
                result_obj["descent_calls_made"] = tracker.descent_calls_made
                if tracker.descent_budget_exceeded:
                    result_obj["descent_budget_exceeded"] = True
                    result_obj["exploration_method"] = "wide_net_parallel_budget_capped"
                    result_json = json.dumps(result_obj, indent=2, ensure_ascii=False)
                else:
                    result_json = json.dumps(result_obj, indent=2, ensure_ascii=False)
                self._persist_trace(trace_log_path, analysis_result, argument_text)
                return self._mark_regime(result_json, "funnel")

            # Phase 4: Fallback to one-shot
            self.logger.info(
                "No fallacies found via iterative deepening — falling back to one-shot"
            )
            one_shot_result = await self._run_one_shot(argument_text)
            # FB-35 (#1121): surface the descent-call diagnostic on the one-shot
            # fallback too. ``descent_calls_made`` is always injected (it records
            # how many calls the iterative descent consumed before giving up),
            # and ``descent_budget_exceeded`` marks the degradation when the
            # descent was cost-capped (the one-shot itself is a single call —
            # unbounded-by-design — so the marker reflects that the ITERATIVE
            # descent was cut short).
            try:
                _os_obj = json.loads(one_shot_result)
                _os_obj["descent_calls_made"] = tracker.descent_calls_made
                if tracker.descent_budget_exceeded:
                    _os_obj["descent_budget_exceeded"] = True
                one_shot_result = json.dumps(_os_obj, indent=2, ensure_ascii=False)
            except (json.JSONDecodeError, TypeError):
                pass
            if trace_log_path:
                try:
                    parsed = json.loads(one_shot_result)
                    if "fallacies" in parsed:
                        parsed["trace_note"] = "one_shot_fallback"
                        parsed["argument_excerpt"] = argument_text[:200]
                        check_plaintext_destination(trace_log_path)
                        trace_path = Path(trace_log_path)
                        trace_path.parent.mkdir(parents=True, exist_ok=True)
                        trace_path.write_text(
                            json.dumps(parsed, indent=2, ensure_ascii=False),
                            encoding="utf-8",
                        )
                except PlaintextDestinationError as refused:
                    self.logger.warning("One-shot trace not written: %s", refused)
                except (json.JSONDecodeError, TypeError):
                    pass
            return self._mark_regime(one_shot_result, "one_shot")

        except Exception as e:
            self.logger.error(f"Analysis error: {e}", exc_info=True)
            return json.dumps({"error": str(e), "fallacies": []})
        finally:
            if file_handler:
                self.logger.removeHandler(file_handler)
                file_handler.close()

    def _attach_trace_handler(
        self, trace_log_path: Optional[str]
    ) -> Optional[logging.FileHandler]:
        """Build + attach the optional descent-trace FileHandler.

        Robust to a ``trace_log_path`` whose parent directory is missing or
        non-creatable (#1722). The caller — often the LLM via SK
        auto-function-invoke on the conversational path — may pass a POSIX path
        improvised on a Windows host; a non-creatable trace path must NOT kill
        the hierarchical taxonomy descent (#1019 family: a swallowed crash
        produces an invisible degradation). Creates the parent dir; on failure
        falls back to no handler with a WARNING. Returns the handler (or None)
        so ``run_guided_analysis`` can detach it in its ``finally`` block.
        """
        if not trace_log_path or str(trace_log_path).strip() in ("", "None", "null"):
            return None
        try:
            check_plaintext_destination(str(trace_log_path))
            Path(str(trace_log_path)).parent.mkdir(parents=True, exist_ok=True)
            handler = logging.FileHandler(trace_log_path, mode="w", encoding="utf-8")
            handler.setFormatter(
                logging.Formatter(
                    "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
                )
            )
            self.logger.addHandler(handler)
            return handler
        except (OSError, PermissionError, ValueError) as trace_exc:
            self.logger.warning(
                "trace_log_path '%s' unusable (%s); continuing without " "trace file",
                trace_log_path,
                trace_exc,
            )
            return None

    def _persist_trace(
        self,
        trace_log_path: Optional[str],
        result: "FallacyAnalysisResult",
        argument_text: str,
    ) -> None:
        """Persist structured taxonomy traversal trace to JSON file."""
        if not trace_log_path:
            return
        try:
            trace_entries = []
            for fallacy in result.fallacies:
                node = self.taxonomy_navigator.get_node(fallacy.taxonomy_pk)
                parent_chain = []
                if node and node.get("path"):
                    parent_chain = node["path"].split(" > ")
                trace_entries.append(
                    {
                        "taxonomy_node_id": fallacy.taxonomy_pk,
                        "fallacy_type": fallacy.fallacy_type,
                        "parent_chain": parent_chain,
                        "navigation_trace": fallacy.navigation_trace,
                        "decision_rationale": fallacy.explanation,
                        "citation_excerpt": argument_text[:200],
                        "confidence": fallacy.confidence,
                    }
                )

            trace_data = {
                "exploration_method": result.exploration_method,
                "branches_explored": result.branches_explored,
                "total_iterations": result.total_iterations,
                "traversal_paths": trace_entries,
            }

            check_plaintext_destination(trace_log_path)
            trace_path = Path(trace_log_path)
            trace_path.parent.mkdir(parents=True, exist_ok=True)
# Deviation #3: detach any FileHandler bound to this path BEFORE the
            # truncating write. The descent-trace handler was opened in mode "w"
            # at the start of the run and keeps its file offset; a write_text()
            # under it truncates the file, and the handler's next record is
            # emitted at the old offset, padding the JSON with NUL bytes.
            # Measured 2026-10-05: 8240 chars of JSON followed by 3624 NULs.
            # The caller's `finally` still re-detaches harmlessly.
            for _handler in list(self.logger.handlers):
                if isinstance(_handler, logging.FileHandler) and Path(
                    _handler.baseFilename
                ) == trace_path.resolve():
                    _handler.flush()
                    self.logger.removeHandler(_handler)
                    _handler.close()
            trace_path.write_text(
                json.dumps(trace_data, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            self.logger.info(f"Trace persisted to {trace_log_path}")
        except Exception as e:
            self.logger.warning(f"Failed to persist trace: {e}")

    def _match_taxonomy_name(self, text: str) -> str:
        """Try to find a taxonomy fallacy name within free-form LLM text (#655 Track KK).

        Returns the longest matching taxonomy name, or "" if nothing matches.
        """
        known_names: list[str] = []
        for node in self.taxonomy_navigator.taxonomy_data:
            for key in ("text_fr", "nom_vulgarisé"):
                name = node.get(key, "")
                if name and len(name) > 4:
                    known_names.append(name)
        # Also check common French fallacy names not in taxonomy
        known_names.extend(
            [
                "Ad hominem",
                "Appel à l'autorité",
                "Pente glissante",
                "Homme de paille",
                "Faux dilemme",
                "Pétition de principe",
                "Appel à la tradition",
                "Appel à la nouveauté",
                "Généralisation hâtive",
                "Fausse cause",
                "Appel aux émotions",
                "Changement de sujet",
                "Fausse équivalence",
                "Empoisonnement du puits",
                "Appel à l'ignorance",
            ]
        )
        text_lower = text.lower()
        best = ""
        for name in known_names:
            if name.lower() in text_lower and len(name) > len(best):
                best = name
        return best

    def _build_compact_taxonomy(self, max_depth: int = 4) -> str:
        """Build a compact taxonomy representation (PK + name + path) to fit in context."""
        lines = []
        for node in self.taxonomy_navigator.taxonomy_data:
            depth = int(node.get("depth", 0))
            if depth > max_depth:
                continue
            pk = node.get("PK", "")
            name = node.get("text_fr", node.get("nom_vulgarisé", ""))
            path = node.get("path", "")
            if name and pk:
                indent = "  " * depth
                lines.append(f"{indent}PK={pk} [{path}] {name}")
        return "\n".join(lines)

    async def _run_one_shot(self, argument_text: str) -> str:
        """Fallback one-shot analysis — sends compact taxonomy to LLM."""
        self.logger.info("Running one-shot fallback analysis")

        kernel, settings = self._create_one_shot_kernel()
        # Use compact taxonomy (depth ≤ 4) to stay within token limits
        compact_taxonomy = self._build_compact_taxonomy(max_depth=6)

        prompt = (
            f"Analyze the following text:\n--- TEXT ---\n{argument_text}\n--- END TEXT ---\n\n"
            "Identify the single most relevant fallacy from the taxonomy below. "
            "CRITICAL: Choose the MOST SPECIFIC (deepest) node that matches — "
            "generic labels like 'Ad hominem' or 'Appel à l'autorité' are too shallow. "
            "Prefer leaf nodes or deep sub-types (e.g., 'Empoisonnement du puits' instead of 'Culpabilité par association'). "
            "IMPORTANT: Use the exact fallacy name as it appears in the taxonomy (in French). "
            "Respond with ONLY a JSON object: "
            '{"fallacy_name": "...", "taxonomy_pk": "...", "explanation": "...", "confidence": 0.0-1.0}\n\n'
            f"--- TAXONOMY ---\n{compact_taxonomy}\n--- END ---"
        )

        history = ChatHistory(
            system_message=(
                "You are an expert in logical fallacies. Identify the most specific "
                "and relevant fallacy from the taxonomy. Respond with ONLY a JSON object."
            )
        )
        history.add_user_message(prompt)

        try:
            response = await self.llm_service.get_chat_message_content(
                chat_history=history, settings=settings, kernel=kernel
            )
            raw = str(response).strip()

            # Try to parse structured JSON response
            try:
                text_to_parse = raw
                if "```json" in text_to_parse:
                    text_to_parse = text_to_parse.split("```json")[1].split("```")[0]
                elif "```" in text_to_parse:
                    text_to_parse = text_to_parse.split("```")[1].split("```")[0]
                start = text_to_parse.find("{")
                end = text_to_parse.rfind("}") + 1
                if start >= 0 and end > start:
                    parsed = json.loads(text_to_parse[start:end])
                    fallacy_name = parsed.get("fallacy_name", "")
                    if fallacy_name:
                        fallacy = IdentifiedFallacy(
                            fallacy_type=fallacy_name,
                            taxonomy_pk=parsed.get("taxonomy_pk", ""),
                            explanation=parsed.get("explanation", ""),
                            confidence=float(parsed.get("confidence", 0.5)),
                            navigation_trace=[],
                        )
                        result = FallacyAnalysisResult(
                            fallacies=[fallacy],
                            exploration_method="one_shot",
                        )
                        return result.model_dump_json(indent=2)
            except (json.JSONDecodeError, ValueError, TypeError):
                pass

            # Fallback: try to match a taxonomy name in the raw text (#655 Track KK).
            matched_name = self._match_taxonomy_name(raw)
            if matched_name:
                fallacy = IdentifiedFallacy(
                    fallacy_type=matched_name,
                    taxonomy_pk="",
                    explanation="One-shot identification (taxonomy name extracted from response)",
                    confidence=0.35,
                    navigation_trace=[],
                )
                result = FallacyAnalysisResult(
                    fallacies=[fallacy], exploration_method="one_shot"
                )
                return result.model_dump_json(indent=2)

            # No usable fallacy found — return empty rather than garbage
            self.logger.warning(
                "One-shot: could not extract usable fallacy name from response"
            )
            return json.dumps(
                {"fallacies": [], "exploration_method": "one_shot_no_match"}
            )

        except Exception as e:
            self.logger.error(f"One-shot fallback failed: {e}")
            return json.dumps({"error": str(e), "fallacies": []})
