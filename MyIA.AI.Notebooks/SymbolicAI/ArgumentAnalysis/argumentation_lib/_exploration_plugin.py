#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/plugins/exploration_plugin.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: ecfd9b9c (2026-09-29).
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification.
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
"""ExplorationPlugin — constrained kernel functions for taxonomy navigation.

This plugin provides the ONLY tools available to the 'slave' LLM during
hierarchical fallacy detection. The LLM must navigate the taxonomy tree
by calling these functions — it cannot respond freely.

Recovered from commit d2fdd930 and enhanced with structured output.
"""

import json
import logging
import math
from typing import Annotated, Optional, Tuple

from semantic_kernel.functions.kernel_function_decorator import kernel_function

from argumentation_analysis.agents.utils.taxonomy_navigator import TaxonomyNavigator

logger = logging.getLogger(__name__)

#: Scores des niveaux lexicaux historiques — acceptés, mais le contrat que le
#: prompt feuille énonce est un nombre (#2746).
_CONFIDENCE_LEVELS = {"high": 0.9, "medium": 0.7, "low": 0.4}

#: Ce qu'une confiance illisible dégrade : le défaut "medium" du paramètre,
#: même valeur que le lecteur aval (fallacy_workflow_plugin lit
#: ``lr.get("confidence", 0.7)``). L'entrée rejetée est nommée dans la note,
#: jamais silencieuse.
_UNREADABLE_CONFIDENCE_SCORE = 0.7


def _confidence_score(raw: object) -> Tuple[float, str]:
    """Le contrat unique de ``confirm_fallacy`` : un nombre dans ``[0, 1]``
    (ce que le prompt feuille demande) ou un nom de niveau.

    Rend ``(score, note)``. La note est vide quand l'entrée a été lue
    fidèlement ; sinon elle nomme l'entrée rejetée. Jamais d'exception — un
    appel de confirmation valide ne doit pas se perdre sur la forme de sa
    confiance (#2746).
    """
    rejected = (
        f"unreadable confidence {raw!r}, defaulted to "
        f"{_UNREADABLE_CONFIDENCE_SCORE}"
    )
    if isinstance(raw, bool) or raw is None:
        return _UNREADABLE_CONFIDENCE_SCORE, rejected
    if isinstance(raw, (int, float)):
        value = float(raw)
    elif isinstance(raw, str):
        text = raw.strip()
        level = _CONFIDENCE_LEVELS.get(text.lower())
        if level is not None:
            return level, ""
        try:
            value = float(text.replace(",", "."))
        except ValueError:
            return _UNREADABLE_CONFIDENCE_SCORE, rejected
    else:
        return _UNREADABLE_CONFIDENCE_SCORE, rejected
    if math.isnan(value) or math.isinf(value):
        return _UNREADABLE_CONFIDENCE_SCORE, rejected
    return min(max(value, 0.0), 1.0), ""


class ExplorationPlugin:
    """Plugin for constrained taxonomy navigation during fallacy detection.

    Provides 3 kernel functions:
    - explore_branch: Navigate to a taxonomy node and see its children
    - confirm_fallacy: Confirm a specific node as the identified fallacy
    - conclude_no_fallacy: Abandon exploration — no fallacy found in this branch
    """

    def __init__(self, taxonomy_navigator: TaxonomyNavigator, language: str = "fr"):
        self.taxonomy_navigator = taxonomy_navigator
        self.language = language
        self._alt_lang = "en" if language == "fr" else "fr"

    @kernel_function(
        name="explore_branch",
        description=(
            "Navigate to a taxonomy node to see its details and children. "
            "Use this to explore deeper into a branch that might contain "
            "the relevant fallacy. Returns the node info and its children."
        ),
    )
    def explore_branch(
        self,
        node_pk: Annotated[str, "The PK (ID) of the taxonomy node to explore"],
    ) -> Annotated[str, "JSON with node details and children"]:
        """Navigate to a taxonomy node and return its details + children."""
        node = self.taxonomy_navigator.get_node(node_pk)
        if not node:
            return json.dumps({"error": f"Node {node_pk} not found"})

        children = self.taxonomy_navigator.get_children(node_pk)
        lang = self.language
        branch_info = {
            "node": {
                "pk": node.get("PK", ""),
                "path": node.get("path", ""),
                "name": (
                    node.get(f"text_{lang}", "")
                    or node.get("nom_vulgarisé", "")
                    or node.get(f"text_{self._alt_lang}", "")
                ),
                "description": node.get(f"desc_{lang}", "")
                or node.get(f"desc_{self._alt_lang}", ""),
                "example": node.get(f"example_{lang}", "")
                or node.get(f"example_{self._alt_lang}", ""),
                "depth": node.get("depth", ""),
                "is_leaf": len(children) == 0,
            },
            "children": [
                {
                    "pk": c.get("PK", ""),
                    "name": (
                        c.get(f"text_{lang}", "")
                        or c.get("nom_vulgarisé", "")
                        or c.get(f"text_{self._alt_lang}", "")
                    ),
                    "description": c.get(f"desc_{lang}", "")
                    or c.get(f"desc_{self._alt_lang}", ""),
                    "example": (
                        c.get(f"example_{lang}", "")
                        or c.get(f"example_{self._alt_lang}", "")
                    )[:200],
                }
                for c in children
            ],
            "children_count": len(children),
        }
        return json.dumps(branch_info, ensure_ascii=False)

    @kernel_function(
        name="confirm_fallacy",
        description=(
            "Confirm that a specific taxonomy node is the identified fallacy. "
            "Call this when you are confident that the current node matches "
            "the fallacy in the analyzed text. Provide justification."
        ),
    )
    def confirm_fallacy(
        self,
        node_pk: Annotated[str, "The PK of the confirmed fallacy node"],
        confidence: Annotated[
            str,
            "Confidence: a number between 0.0 and 1.0 (as the leaf prompt "
            "specifies), or a level 'high'/'medium'/'low'",
        ] = "medium",
        justification: Annotated[str, "Why this fallacy matches the text"] = "",
    ) -> Annotated[str, "Confirmation result"]:
        """Confirm a fallacy identification with justification."""
        node = self.taxonomy_navigator.get_node(node_pk)
        if not node:
            return json.dumps({"error": f"Node {node_pk} not found"})

        confidence_score, confidence_note = _confidence_score(confidence)

        lang = self.language
        result = {
            "confirmed": True,
            "pk": node.get("PK", ""),
            "path": node.get("path", ""),
            "name": (
                node.get(f"text_{lang}", "")
                or node.get("nom_vulgarisé", "")
                or node.get(f"text_{self._alt_lang}", "")
            ),
            "name_fr": node.get("text_fr", ""),
            "confidence": confidence_score,
            "justification": justification,
        }
        if confidence_note:
            result["confidence_note"] = confidence_note
        return json.dumps(result, ensure_ascii=False)

    @kernel_function(
        name="conclude_no_fallacy",
        description=(
            "Conclude that no relevant fallacy was found in the current branch. "
            "Call this when you have explored the branch sufficiently and determined "
            "that none of the nodes match the analyzed text."
        ),
    )
    def conclude_no_fallacy(
        self,
        reason: Annotated[str, "Why no fallacy was found in this branch"],
    ) -> Annotated[str, "Conclusion recorded"]:
        """Conclude that no fallacy was found in this branch."""
        return json.dumps({"confirmed": False, "reason": reason}, ensure_ascii=False)
