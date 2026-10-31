# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/services/jtms/atms_core.py
# Source SHA1 : 70651a707a7ff37e6cd7502796300907a90d9783 (242L @ 713927e1)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_atms_core.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# VERBATIM SANS MODIFICATION : le fichier amont n'importe que la bibliotheque
# standard, donc aucun prefixe `argumentation_analysis.*` n'a a etre reecrit et
# le corps ci-dessous est **byte-for-byte** identique a l'amont. Seule cette
# entete de provenance est ajoutee -- convention des ports verbatim du
# dossier (cf `_belief_revision_handler.py`).
# Role porte : ATMS -- etiquetage par environnements d'hypotheses
# Fins de ligne : l'amont livre ce fichier en CRLF, le depot l'impose en LF
# (`.gitattributes` : `*.py text eol=lf`) ; le contenu est identique a l'amont
# aux fins de ligne pres (cf NOTICE-EPITA, section "Fins de ligne").
# =============================================================================
"""
ATMS (Assumption-based Truth Maintenance System) core module.

Integrated from student project 1.4.1-JTMS (Zebic, Leguere, Shan, Breant).
Provides assumption-based reasoning via environment tracking.

Unlike JTMS which tracks a single truth value per belief, ATMS tracks
the set of minimal assumption environments under which each node can be derived.

Label contract (#2094, decision documented after re-measurement):
    Labels are computed only when a justification is inserted
    (`add_justification`) and are stripped only by an explicit
    `invalidate_environment`. There is no hypothesis-withdrawal API and no
    re-propagation: an environment removed by invalidation stays removed until
    a new justification re-derives it, and nothing restores labels on its own.
    `invalidate_environment` clears the contradiction node (⊥) too, so a
    nogood is NOT durably recorded — consumers needing durable contradiction
    memory keep their own registry (see `hypothesis_tracker._contradicted_by`).

Classes:
    ATMSNode — A node with a label (set of valid environments)
    ATMSJustification — A rule relating in-nodes and out-nodes to a conclusion
    ATMS — The assumption-based truth maintenance system
"""

import logging
from itertools import product
from typing import Dict, FrozenSet, List, Optional, Set

logger = logging.getLogger("ATMS")

CONTRADICTION_SYMBOL = "\u22a5"  # ⊥


class ATMSNode:
    """A node in the ATMS, representing a proposition.

    Each node has a label: a set of minimal environments (frozensets of
    assumption names) under which this node can be derived.
    """

    def __init__(self, name: str, is_assumption: bool = False) -> None:
        self.name = name
        self.label: Set[FrozenSet[str]] = set()
        self.justifications: List["ATMSJustification"] = []
        self.is_assumption = is_assumption
        if is_assumption:
            self.label.add(frozenset({name}))

    def add_env(self, env: FrozenSet[str]) -> bool:
        """Add an environment to this node's label. Returns True if new."""
        if env not in self.label:
            self.label.add(env)
            return True
        return False

    def __repr__(self) -> str:
        return self.name


class ATMSJustification:
    """A justification rule in the ATMS.

    A justification states: if all in_nodes are derivable AND none of the
    out_nodes are derivable (under the same environment), then the conclusion
    is derivable.
    """

    def __init__(
        self,
        in_nodes: List[ATMSNode],
        out_nodes: List[ATMSNode],
        conclusion: ATMSNode,
    ) -> None:
        self.in_nodes = in_nodes
        self.out_nodes = out_nodes
        self.conclusion = conclusion


class ATMS:
    """Assumption-based Truth Maintenance System.

    Tracks which combinations of assumptions (environments) support each node.
    Unlike JTMS, ATMS maintains all possible derivation paths simultaneously.

    Usage:
        atms = ATMS()
        atms.add_assumption("a")
        atms.add_assumption("b")
        atms.add_node("c")
        atms.add_justification(["a", "b"], [], "c")
        envs = atms.get_environments("c")  # {frozenset({"a", "b"})}
    """

    def __init__(self) -> None:
        self.nodes: Dict[str, ATMSNode] = {}
        self.contradiction_node = self.add_node(CONTRADICTION_SYMBOL)

    def add_node(self, name: str, is_assumption: bool = False) -> ATMSNode:
        """Add a node to the ATMS. Returns existing node if name already exists."""
        if name not in self.nodes:
            self.nodes[name] = ATMSNode(name, is_assumption)
            logger.debug(
                "Added %s node '%s'",
                "assumption" if is_assumption else "regular",
                name,
            )
        return self.nodes[name]

    def add_assumption(self, name: str) -> ATMSNode:
        """Add an assumption node (shorthand for add_node with is_assumption=True)."""
        return self.add_node(name, is_assumption=True)

    def add_justification(
        self,
        in_names: List[str],
        out_names: List[str],
        conclusion_name: str,
    ) -> None:
        """Add a justification rule and propagate environments.

        Computes the Cartesian product of in-node labels, merges environments,
        filters by out-node blocking and consistency, then adds valid
        environments to the conclusion's label. This is the only operation
        that grows labels — propagation happens at insertion time only
        (#2094 label contract).
        """
        for name in in_names + out_names + [conclusion_name]:
            if name not in self.nodes:
                raise KeyError(
                    f"Node '{name}' not found in ATMS. "
                    "Add it with add_node() or add_assumption() first."
                )

        in_nodes = [self.nodes[name] for name in in_names]
        out_nodes = [self.nodes[name] for name in out_names]
        conclusion = self.nodes[conclusion_name]

        justification = ATMSJustification(in_nodes, out_nodes, conclusion)
        conclusion.justifications.append(justification)

        # Empty in-list: conclusion derivable under empty environment
        if not in_nodes:
            empty_env = frozenset()
            blocked = any(
                any(env.issubset(empty_env) for env in out_node.label)
                for out_node in out_nodes
            )
            if not blocked and self.is_consistent(empty_env):
                conclusion.add_env(empty_env)
            return

        in_env_lists = [node.label for node in in_nodes]
        if any(len(envs) == 0 for envs in in_env_lists):
            return  # Some in-node has no valid environments

        for combination in product(*in_env_lists):
            merged_env = frozenset().union(*combination)

            # Out-node blocking: skip if any out-node is derivable under a
            # subset of the merged environment
            if any(
                any(env.issubset(merged_env) for env in out_node.label)
                for out_node in out_nodes
            ):
                continue

            if self.is_consistent(merged_env):
                conclusion.add_env(merged_env)
                if conclusion.name == CONTRADICTION_SYMBOL:
                    self.invalidate_environment(merged_env)

    def invalidate_environment(self, env: FrozenSet[str]) -> None:
        """Remove an inconsistent environment and all its supersets from all nodes.

        This includes ⊥ itself: the nogood is not durably recorded, and
        `is_consistent(env)` reads True again afterwards (#2094). Durability
        here is structural, not memorial — nothing re-propagates, so the
        stripped environments stay gone until a new justification re-derives
        them.
        """
        for node in self.nodes.values():
            node.label = {
                node_env for node_env in node.label if not env.issubset(node_env)
            }
        logger.debug("Invalidated environment %s and its supersets", set(env))

    def get_environments(self, node_name: str) -> Set[FrozenSet[str]]:
        """Get all valid environments for a node."""
        if node_name not in self.nodes:
            raise KeyError(f"Node '{node_name}' not found in ATMS.")
        return self.nodes[node_name].label

    def is_consistent(self, env: FrozenSet[str]) -> bool:
        """Check whether an environment is consistent (not contradictory)."""
        return frozenset(env) not in self.nodes[CONTRADICTION_SYMBOL].label

    def get_node(self, name: str) -> Optional[ATMSNode]:
        """Get a node by name, or None if not found."""
        return self.nodes.get(name)

    def get_assumptions(self) -> List[str]:
        """Get all assumption names."""
        return [
            name
            for name, node in self.nodes.items()
            if node.is_assumption and name != CONTRADICTION_SYMBOL
        ]

    def explain_node(self, node_name: str) -> Dict:
        """Explain why a node has its current environments.

        Returns a dict with the node's environments and the justifications
        that contribute to them.
        """
        if node_name not in self.nodes:
            raise KeyError(f"Node '{node_name}' not found in ATMS.")
        node = self.nodes[node_name]
        justification_info = []
        for j in node.justifications:
            justification_info.append(
                {
                    "in_nodes": [n.name for n in j.in_nodes],
                    "out_nodes": [n.name for n in j.out_nodes],
                }
            )
        return {
            "name": node_name,
            "is_assumption": node.is_assumption,
            "environments": [sorted(e) for e in node.label],
            "justifications": justification_info,
        }

    def show(self) -> str:
        """Return a string representation of all node labels."""
        lines = []
        for name, node in self.nodes.items():
            if name == CONTRADICTION_SYMBOL:
                continue
            envs = sorted([sorted(e) for e in node.label])
            lines.append(f"{name}: {envs}")
        return "\n".join(lines)
