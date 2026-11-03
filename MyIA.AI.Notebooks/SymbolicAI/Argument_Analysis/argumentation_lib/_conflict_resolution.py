# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/services/jtms/conflict_resolution.py
# Source SHA1 : dd8a00391c2fe5fda77165e33a014fbb142e5d7e (305L @ 713927e1)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_conflict_resolution.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# VERBATIM SANS MODIFICATION : le fichier amont n'importe que la bibliotheque
# standard, donc aucun prefixe `argumentation_analysis.*` n'a a etre reecrit et
# le corps ci-dessous est **byte-for-byte** identique a l'amont. Seule cette
# entete de provenance est ajoutee -- convention des ports verbatim du
# dossier (cf `_belief_revision_handler.py`).
# Role porte : resolution de conflits entre agents -- 5 strategies
# Fins de ligne : l'amont livre ce fichier en CRLF, le depot l'impose en LF
# (`.gitattributes` : `*.py text eol=lf`) ; le contenu est identique a l'amont
# aux fins de ligne pres (cf NOTICE-EPITA, section "Fins de ligne").
# =============================================================================
"""
Conflict Resolution for JTMS multi-agent scenarios.

Extracted from agents/jtms_communication_hub.py for standalone use.
Works with belief dictionaries — no direct agent dependency.

5 resolution strategies:
- confidence_based: highest confidence wins
- evidence_based: evidence quality + justification count
- consensus: majority vote on ``valid`` among 3+ agents
- agent_expertise: domain-specific expertise mapping
- temporal: most recent belief wins

A strategy that cannot apply (no expert for the domain, no timestamp) falls
back to confidence and says so: ``strategy_used`` names what decided and
``fallback_from`` what was asked. A belief without a numeric ``confidence``
is not scored as 0.0: the comparison is reported unresolved, naming it
(``missing_confidence``). #2344.
"""

import logging
from datetime import datetime
from typing import Any, Dict, List, Optional

logger = logging.getLogger("ConflictResolver")


class ConflictResolver:
    """Resolve conflicts between competing beliefs from multiple agents.

    Operates on belief dictionaries, not agent objects — usable in both
    pipeline and conversational modes.

    Usage:
        resolver = ConflictResolver()
        conflict = {
            "belief_name": "hypothesis_X",
            "beliefs": {
                "agent_1": {"belief_name": "hypothesis_X", "confidence": 0.8, "valid": True},
                "agent_2": {"belief_name": "hypothesis_X", "confidence": 0.3, "valid": False},
            },
            "context": {"type": "hypothesis"},
        }
        result = resolver.resolve(conflict, strategy="confidence_based")
    """

    STRATEGIES = [
        "confidence_based",
        "evidence_based",
        "consensus",
        "agent_expertise",
        "temporal",
    ]

    # Domain expertise mapping: context type → preferred agent role
    EXPERTISE_MAP = {
        "hypothesis": "sherlock",
        "evidence": "sherlock",
        "deduction": "sherlock",
        "validation": "watson",
        "logical_proof": "watson",
        "consistency": "watson",
        "quality": "quality",
        "fallacy": "informal",
        "counter_argument": "counter",
    }

    def __init__(self):
        self.resolution_history: List[Dict[str, Any]] = []

    def resolve(
        self,
        conflict: Dict[str, Any],
        strategy: str = "confidence_based",
    ) -> Dict[str, Any]:
        """Resolve a conflict synchronously. Returns resolution dict.

        Raises:
            ValueError: an unknown ``strategy``, or a conflict without a
                ``beliefs`` mapping. Both come from the caller's code (#2344):
                a misspelt strategy used to become ``confidence_based``, and a
                conflict handed under another key resolved nobody, silently.
        """
        if strategy not in self.STRATEGIES:
            raise ValueError(
                f"Unknown conflict resolution strategy {strategy!r}; "
                f"known: {', '.join(self.STRATEGIES)}"
            )
        if not isinstance(conflict.get("beliefs"), dict):
            raise ValueError(
                "Conflict has no 'beliefs' mapping (agent -> belief dict); "
                f"got keys {sorted(conflict)}"
            )

        result = {
            "conflict_id": conflict.get(
                "conflict_id", f"conflict_{len(self.resolution_history)}"
            ),
            "strategy_used": strategy,
            "resolved": False,
            "chosen_belief": None,
            "chosen_agent": None,
            "reasoning": "",
            "timestamp": datetime.now().isoformat(),
        }

        try:
            resolver_fn = getattr(self, f"_resolve_by_{strategy.replace('_based', '')}")
            resolution = resolver_fn(conflict)
            result.update(resolution)
        except Exception as e:
            result["error"] = str(e)
            result["reasoning"] = f"Resolution error: {e}"

        self.resolution_history.append(result)
        return result

    @staticmethod
    def _missing_confidence(beliefs: Dict) -> Optional[Dict]:
        """Unresolved result naming the agents whose belief has no confidence.

        ``None`` when every belief carries a number. A missing confidence used
        to count as 0.0, so the other side won by default (#2344).
        """
        missing = [
            agent
            for agent, data in beliefs.items()
            if isinstance(data.get("confidence"), bool)
            or not isinstance(data.get("confidence"), (int, float))
        ]
        if not missing:
            return None
        return {
            "resolved": False,
            "missing_confidence": missing,
            "reasoning": f"No confidence for {', '.join(missing)}: "
            "the beliefs cannot be compared",
        }

    def _fallback_to_confidence(self, conflict: Dict, requested: str, why: str) -> Dict:
        """Resolve by confidence, naming the strategy that could not apply."""
        resolution = self._resolve_by_confidence(conflict)
        resolution["strategy_used"] = "confidence_based"
        resolution["fallback_from"] = requested
        resolution["reasoning"] = (
            f"{requested} not applicable ({why}); fell back to confidence. "
            f"{resolution['reasoning']}"
        )
        return resolution

    def _resolve_by_confidence(self, conflict: Dict) -> Dict:
        """Pick the belief with highest confidence."""
        beliefs = conflict.get("beliefs", {})
        missing = self._missing_confidence(beliefs)
        if missing:
            return missing
        best_belief = None
        best_confidence = -1.0
        best_agent = None

        for agent_name, data in beliefs.items():
            confidence = data["confidence"]
            if confidence > best_confidence:
                best_confidence = confidence
                best_belief = data.get("belief_name")
                best_agent = agent_name

        return {
            "resolved": best_belief is not None,
            "chosen_belief": best_belief,
            "chosen_agent": best_agent,
            "reasoning": f"Highest confidence: {best_confidence:.2f} by {best_agent}",
            "confidence_score": best_confidence,
        }

    def _resolve_by_evidence(self, conflict: Dict) -> Dict:
        """Pick the belief with best evidence score (justification count * confidence)."""
        beliefs = conflict.get("beliefs", {})
        missing = self._missing_confidence(beliefs)
        if missing:
            return missing
        best_belief = None
        best_score = -1.0
        best_agent = None

        for agent_name, data in beliefs.items():
            justification_count = data.get("justification_count", 1)
            score = justification_count * data["confidence"]

            if score > best_score:
                best_score = score
                best_belief = data.get("belief_name")
                best_agent = agent_name

        return {
            "resolved": best_belief is not None,
            "chosen_belief": best_belief,
            "chosen_agent": best_agent,
            "reasoning": f"Best evidence score: {best_score:.2f} by {best_agent}",
            "evidence_score": best_score,
        }

    def _resolve_by_consensus(self, conflict: Dict) -> Dict:
        """Majority vote among agents. Requires 3+ agents for meaningful result."""
        beliefs = conflict.get("beliefs", {})
        if len(beliefs) < 3:
            return {
                "resolved": False,
                "reasoning": "Consensus requires 3+ agents",
            }

        # Count votes for each truth value
        votes_true = sum(1 for d in beliefs.values() if d.get("valid") is True)
        votes_false = sum(1 for d in beliefs.values() if d.get("valid") is False)

        if votes_true > votes_false:
            winner = next(
                (a for a, d in beliefs.items() if d.get("valid") is True), None
            )
            return {
                "resolved": True,
                "chosen_agent": winner,
                "chosen_belief": beliefs[winner]["belief_name"] if winner else None,
                "reasoning": f"Consensus: {votes_true} for vs {votes_false} against",
            }
        elif votes_false > votes_true:
            winner = next(
                (a for a, d in beliefs.items() if d.get("valid") is False), None
            )
            return {
                "resolved": True,
                "chosen_agent": winner,
                "chosen_belief": beliefs[winner]["belief_name"] if winner else None,
                "reasoning": f"Consensus: {votes_false} against vs {votes_true} for",
            }
        return {"resolved": False, "reasoning": "Consensus tie"}

    def _resolve_by_agent_expertise(self, conflict: Dict) -> Dict:
        """Pick the belief from the agent with domain expertise."""
        beliefs = conflict.get("beliefs", {})
        context_type = conflict.get("context", {}).get("type", "unknown")
        # #2344: an unknown domain has no expert. It used to default to
        # "sherlock", which crowned Sherlock the expert of any domain.
        expert_role = self.EXPERTISE_MAP.get(context_type)
        if expert_role is None:
            return self._fallback_to_confidence(
                conflict, "agent_expertise", f"no expert mapped for {context_type!r}"
            )

        for agent_name, data in beliefs.items():
            if expert_role.lower() in agent_name.lower():
                return {
                    "resolved": True,
                    "chosen_belief": data.get("belief_name"),
                    "chosen_agent": agent_name,
                    "reasoning": f"Expert {expert_role} for domain {context_type}",
                    "expertise_domain": context_type,
                }

        return self._fallback_to_confidence(
            conflict, "agent_expertise", f"no {expert_role} agent among the beliefs"
        )

    def _resolve_by_temporal(self, conflict: Dict) -> Dict:
        """Pick the most recently updated belief."""
        beliefs = conflict.get("beliefs", {})
        latest_agent = None
        latest_ts = None

        for agent_name, data in beliefs.items():
            ts = data.get("timestamp")
            if ts and (latest_ts is None or ts > latest_ts):
                latest_ts = ts
                latest_agent = agent_name

        if latest_agent:
            return {
                "resolved": True,
                "chosen_belief": beliefs[latest_agent].get("belief_name"),
                "chosen_agent": latest_agent,
                "reasoning": f"Most recent: {latest_agent} at {latest_ts}",
            }

        return self._fallback_to_confidence(
            conflict, "temporal", "no belief carries a timestamp"
        )

    def get_history(self) -> List[Dict[str, Any]]:
        """Get resolution history."""
        return self.resolution_history

    def get_stats(self) -> Dict[str, Any]:
        """Get resolution statistics."""
        resolved = sum(1 for r in self.resolution_history if r.get("resolved"))
        by_strategy = {}
        for r in self.resolution_history:
            s = r.get("strategy_used", "unknown")
            by_strategy[s] = by_strategy.get(s, 0) + 1

        return {
            "total_conflicts": len(self.resolution_history),
            "resolved": resolved,
            "unresolved": len(self.resolution_history) - resolved,
            "by_strategy": by_strategy,
        }
