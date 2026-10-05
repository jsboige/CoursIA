#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/agents/utils/taxonomy_navigator.py` from
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
import json
from typing import List, Dict, Any, Optional

from argumentation_analysis.utils.taxonomy_local_overrides import render_alias
from argumentation_analysis.utils.taxonomy_tree import (
    taxonomy_parent_path,
    taxonomy_root_path,
)


class TaxonomyNavigator:
    """
    Navigates an already-loaded taxonomy.

    The constructor takes loaded rows (`List[Dict[str, Any]]`), not a path —
    loading from CSV/JSON belongs to the caller (#2041).
    """

    def __init__(self, taxonomy_data: List[Dict[str, Any]]):
        if isinstance(taxonomy_data, str):
            # #2041: a path where loaded rows belong would crash on the
            # first character ('c'.get) — say what was wrong instead. An
            # empty navigator would be a silent false-negative on the whole
            # taxonomy, so refusing beats any lenient fallback.
            raise TypeError(
                "TaxonomyNavigator expects loaded rows (List[Dict[str, Any]]), "
                f"got a str — a path was passed where loaded rows belong: {taxonomy_data!r}"
            )
        self.taxonomy_data = taxonomy_data if taxonomy_data is not None else []
        self.node_map: Dict[str, Dict[str, Any]] = {}
        self.path_map: Dict[str, Dict[str, Any]] = {}  # New: For path-based lookup
        self._build_node_map()

    def _build_node_map(self):
        """Builds the node and path maps from the taxonomy data."""
        if not self.taxonomy_data:
            return
        for node in self.taxonomy_data:
            pk = node.get("PK")
            path = node.get("path")
            if pk:
                self.node_map[str(pk)] = node
            if path:
                self.path_map[str(path)] = node

    def get_node(self, node_id: str) -> Optional[Dict[str, Any]]:
        """
        Retrieves a node by its 'PK'.
        """
        return self.node_map.get(node_id)

    def get_node_by_path(self, path: str) -> Optional[Dict[str, Any]]:
        """
        Retrieves a node by its 'path'.
        """
        return self.path_map.get(path)

    def get_root_nodes(self) -> List[Dict[str, Any]]:
        """
        Returns all nodes at the root of the taxonomy (depth 1).
        """
        roots = []
        for node in self.taxonomy_data:
            try:
                if int(node.get("depth", -1)) == 1:
                    roots.append(node)
            except (ValueError, TypeError):
                continue
        return roots

    def get_children(self, node_id: str) -> List[Dict[str, Any]]:
        """
        Retrieves the direct children of a given node.
        """
        parent_node = self.get_node(node_id)
        if not parent_node:
            return []

        # #2401: the path is the relation. A depth cell is not consulted: one
        # row's depth disagrees with its path, and the root's children carry
        # bare segments no prefix rule reaches.
        parent_path = str(parent_node.get("path", ""))
        root = taxonomy_root_path(
            (node.get("path"), node.get("depth")) for node in self.taxonomy_data
        )
        return [
            node
            for node in self.taxonomy_data
            if taxonomy_parent_path(node.get("path"), root) == parent_path
        ]

    def get_parent(self, node_id: str) -> Optional[Dict[str, Any]]:
        """
        Retrieves the parent of a given node.
        """
        node = self.get_node(node_id)
        if not node:
            return None

        # #2401: a bare segment belongs to the depth-0 root when the taxonomy
        # carries one; without it, it is a top and has no parent.
        root = taxonomy_root_path(
            (row.get("path"), row.get("depth")) for row in self.taxonomy_data
        )
        parent_path = taxonomy_parent_path(node.get("path"), root)
        if parent_path is None:
            return None
        for parent_node in self.taxonomy_data:
            if parent_node.get("path") == parent_path:
                return parent_node
        return None

    def is_leaf(self, node_id: str) -> bool:
        """
        Checks if a node is a leaf (has no children).
        """
        return not self.get_children(node_id)

    def get_branch_as_str(self, node_id: str) -> str:
        """
        Returns a string representation of a branch, including the node
        and its direct children, formatted with indentation.
        """
        node = self.get_node(node_id)
        if not node:
            return "Node not found."

        branch_str = ""
        node_name = render_alias(
            node.get("PK"), node.get("nom_vulgarisé", node.get("PK"))
        )
        branch_str += f"- {node_name} (ID: {node['PK']})\n"

        children = self.get_children(node_id)
        for child in children:
            child_name = render_alias(
                child.get("PK"), child.get("nom_vulgarisé", child.get("PK"))
            )
            branch_str += f"  - {child_name} (ID: {child['PK']})\n"

        return branch_str.strip()

    def get_taxonomy_preview(
        self, depth: int = 2, language: str = "fr", details: bool = True
    ) -> str:
        """
        Generates a string preview of the taxonomy up to a specified depth,
        with an option to include details or just names.
        """
        if not self.taxonomy_data:
            return "Taxonomy data is not available."

        preview_lines = []

        def build_preview(node_id, current_depth):
            if current_depth > depth:
                return

            node = self.get_node(node_id)
            if not node:
                return

            indent = "  " * (current_depth - 1)
            node_name = render_alias(
                node.get("PK"), node.get(f"text_{language}", node.get("PK"))
            )

            if details:
                desc = node.get(f"desc_{language}", "").strip()
                preview_lines.append(
                    f"{indent}- {node_name} (ID: {node['PK']}): {desc}"
                )
            else:
                preview_lines.append(f"{indent}- {node_name}")

            children = self.get_children(node_id)
            for child in children:
                build_preview(child["PK"], current_depth + 1)

        root_nodes = self.get_root_nodes()
        for root in root_nodes:
            build_preview(root["PK"], 1)

        return "\n".join(preview_lines)

    def get_taxonomy_as_json(self) -> str:
        """
        Returns the entire taxonomy data as a JSON string.
        """
        if not self.taxonomy_data:
            return "[]"
        return json.dumps(self.taxonomy_data, indent=2, ensure_ascii=False)
