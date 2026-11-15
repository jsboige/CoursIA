#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/plugins/identification_models.py` from
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
"""Pydantic models for structured fallacy identification output."""

from typing import List, Optional
from pydantic import BaseModel, Field


class IdentifiedFallacy(BaseModel):
    """Structured result from hierarchical taxonomy-guided fallacy detection."""

    fallacy_type: str = Field(
        ..., description="The exact name of the identified fallacy from the taxonomy"
    )
    taxonomy_pk: str = Field(
        ..., description="The PK (primary key) of the fallacy in the taxonomy"
    )
    taxonomy_path: str = Field(
        default="", description="The full dot-separated path through the taxonomy"
    )
    explanation: str = Field(
        ..., description="Why this fallacy applies to the analyzed text"
    )
    problematic_quote: str = Field(
        default="",
        description="The exact quote from the text that exhibits the fallacy",
    )
    confidence: float = Field(
        default=0.0, ge=0.0, le=1.0, description="Confidence score (0.0 to 1.0)"
    )
    navigation_trace: List[str] = Field(
        default_factory=list,
        description="List of taxonomy node PKs visited during iterative deepening",
    )
    family: str = Field(
        default="",
        description="The CSV 'Famille' column value (one of the 7 French families)",
    )
    depth: Optional[int] = Field(
        default=None,
        description=(
            "Taxonomy depth of the confirmed node. None = not measured "
            "(one-shot regime, where no descent happened)"
        ),
    )


class FallacyAnalysisResult(BaseModel):
    """Complete result of a fallacy analysis run."""

    fallacies: List[IdentifiedFallacy] = Field(default_factory=list)
    exploration_method: str = Field(
        default="one_shot",
        description="Detection method used: 'iterative_deepening' or 'one_shot'",
    )
    branches_explored: int = Field(
        default=0, description="Number of taxonomy branches explored"
    )
    total_iterations: int = Field(
        default=0, description="Total iterations across all branches"
    )
