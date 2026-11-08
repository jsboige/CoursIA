# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/evaluation/pattern_mining.py
# Source SHA1 : 0176c88bfaf7c82184dd69e6fda85a0dae8c2e02 (512L @ 2e2a1c3c)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_pattern_mining.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# PREFIXE D'IMPORT SEUL : l'unique import `argumentation_analysis.*` du
# fichier (l.91, LAZY, a l'interieur de `DungTopologyDetector.detect`) est
# reecrit en `argumentation_lib._native_dung` (le module jumeau porte
# ci-contre, lui-meme verbatim) ; le reste du corps est byte-for-byte
# identique a l'amont aux fins de ligne pres. La divergence est declaree
# dans NOTICE-EPITA.
# Role porte : minage de motifs agreges (spectres, densites) sur les corpus de reanalyse
# Fins de ligne : l'amont livre ce fichier en CRLF, le depot l'impose en LF
# (`.gitattributes` : `*.py text eol=lf`) ; le contenu est identique a l'amont
# aux fins de ligne pres (cf NOTICE-EPITA, section "Fins de ligne").
# =============================================================================
"""Discourse pattern mining — aggregate signatures into corpus-level patterns.

Consumes ``signature_*.json`` files produced by the C.2 batch runner and
produces spectral, asymmetry, co-occurrence, formal detector, and
cross-coverage analyses.
"""

from __future__ import annotations

import json
import logging
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Protocol, Sequence, runtime_checkable

# ---------------------------------------------------------------------------
# Fallacy family mapping — Tricherie (8.x) vs Influence (2.x)
# ---------------------------------------------------------------------------

# Tricherie: self-bias fallacies (arranger les faits, changement de cap, pensée biaisée)
TRICHERIE_TYPES = frozenset(
    {
        "cherry_picking",
        "confirmation_bias",
        "rationalization",
        "moving_the_goalposts",
        "special_pleading",
        "biased_sampling",
        "false_cause",
        "hasty_generalization",
    }
)

# Influence: inductive fallacies (procédé rhétorique, émotion, manipulation mentale)
INFLUENCE_TYPES = frozenset(
    {
        "ad_hominem",
        "appeal_to_authority",
        "appeal_to_emotion",
        "appeal_to_fear",
        "bandwagon",
        "red_herring",
        "straw_man",
        "slippery_slope",
        "false_dilemma",
        "loaded_question",
        "circular_reasoning",
        "equivocation",
    }
)


# ---------------------------------------------------------------------------
# Formal pattern detector protocol
# ---------------------------------------------------------------------------


@runtime_checkable
class FormalPatternDetector(Protocol):
    """Extensible detector for formal logic patterns in a signature."""

    name: str

    def detect(self, signature: Dict[str, Any]) -> Dict[str, float]: ...


# ---------------------------------------------------------------------------
# Built-in detectors
# ---------------------------------------------------------------------------


class DungTopologyDetector:
    """Extract topological features from Dung argumentation frameworks."""

    name = "dung_topology"

    def detect(self, signature: Dict[str, Any]) -> Dict[str, float]:
        state = signature.get("state", signature)
        dung = state.get("dung_frameworks", {})
        if not dung:
            return {
                "n_args": 0.0,
                "n_attacks": 0.0,
                "density": 0.0,
                "n_extensions": 0.0,
                "max_extension_size": 0.0,
            }

        # #2672: the first entry is a formalism sidecar on pipeline runs (DeLP's,
        # with no arguments); the shared decoder finds the native framework.
        from argumentation_lib._native_dung import (
            KEYED_SEMANTICS,
            dung_reading,
        )

        fw, by_semantics = dung_reading(dung)
        if fw is None:
            fw = {}
        args = fw.get("arguments", [])
        attacks = fw.get("attacks", [])
        n = len(args)
        n_atk = len(attacks)
        max_ext = n * (n - 1) if n > 1 else 1
        # Directed-edge density (n*(n-1)), not undirected (n*(n-1)/2)
        density = n_atk / max_ext if max_ext > 0 else 0.0

        all_exts = [ext for sem in KEYED_SEMANTICS for ext in by_semantics.get(sem, [])]

        return {
            "n_args": float(n),
            "n_attacks": float(n_atk),
            "density": round(density, 4),
            "n_extensions": float(len(all_exts)),
            "max_extension_size": float(max((len(e) for e in all_exts), default=0)),
        }


class AtmsBranchingDetector:
    """Extract ATMS context branching features."""

    name = "atms_branching"

    def detect(self, signature: Dict[str, Any]) -> Dict[str, float]:
        state = signature.get("state", signature)
        contexts = state.get("atms_contexts", [])
        if not contexts:
            return {
                "max_assumption_count": 0.0,
                "avg_assumptions": 0.0,
                "contradiction_rate": 0.0,
            }

        n = len(contexts)
        assumption_counts = [len(c.get("assumptions", [])) for c in contexts]
        # #1650: the producer emits ``coherent`` (bool) per context, NOT a
        # ``status == "contradictory"`` string. The previous reader probed a
        # phantom key (gotcha #1636/#765) → ``contradictions`` was always 0
        # → ``contradiction_rate`` read 0.0 on every corpus, masking whether
        # the ATMS actually found any incoherent hypothesis. Three states,
        # never the boolean negation ``not c.get("coherent")`` (that would
        # fabricate a contradiction for every context lacking the key):
        #   - coherent present and False  → contradiction (incoherent env)
        #   - coherent present and True   → coherent
        #   - coherent absent             → unclassifiable (logged, not counted)
        contradictions = 0
        unclassified = 0
        for c in contexts:
            if "coherent" in c:
                if c["coherent"] is False:
                    contradictions += 1
            else:
                unclassified += 1
        if unclassified:
            _logger.warning(
                "atms_branching: %d/%d context(s) lack the 'coherent' key — "
                "contradiction_rate is a lower bound (unclassifiable contexts "
                "excluded from the count, not assumed contradictory).",
                unclassified,
                n,
            )

        return {
            "max_assumption_count": float(max(assumption_counts, default=0)),
            "avg_assumptions": round(sum(assumption_counts) / n if n > 0 else 0.0, 2),
            "contradiction_rate": round(contradictions / n if n > 0 else 0.0, 4),
        }


class JtmsRetractionRateDetector:
    """Extract JTMS retraction rate features."""

    name = "jtms_retraction_rate"

    def detect(self, signature: Dict[str, Any]) -> Dict[str, float]:
        state = signature.get("state", signature)
        beliefs = state.get("jtms_beliefs", {})
        retraction_chain = state.get("jtms_retraction_chain", [])

        n_beliefs = len(beliefs)
        n_retractions = len(retraction_chain)
        n_justifications = len(
            {b.get("justification") for b in beliefs.values() if isinstance(b, dict)}
        )

        return {
            "n_beliefs": float(n_beliefs),
            "n_justifications": float(n_justifications),
            "retraction_rate": round(
                n_retractions / n_beliefs if n_beliefs > 0 else 0.0, 4
            ),
        }


_logger = logging.getLogger(__name__)


# Default registry — extend by appending to this list
FORMAL_DETECTORS: List[FormalPatternDetector] = [
    DungTopologyDetector(),
    AtmsBranchingDetector(),
    JtmsRetractionRateDetector(),
]


# ---------------------------------------------------------------------------
# Spectral analysis
# ---------------------------------------------------------------------------


def fallacy_spectrum(
    signatures: Sequence[Dict[str, Any]],
    by: str = "cluster_id",
) -> Dict[str, Dict[str, float]]:
    """Compute relative fallacy frequency per cluster.

    Returns:
        ``{cluster_id: {fallacy_type: relative_freq}}``
    """
    clusters: Dict[str, Counter] = defaultdict(Counter)
    cluster_total: Dict[str, int] = defaultdict(int)

    for sig in signatures:
        state = sig.get("state", sig)
        metadata = sig.get("metadata", {})
        cluster_key = metadata.get(by, "unknown")

        fallacies = state.get("identified_fallacies", {})
        if isinstance(fallacies, dict):
            for f_data in fallacies.values():
                if isinstance(f_data, dict):
                    ftype = f_data.get("type", "unknown")
                    clusters[cluster_key][ftype] += 1
                    cluster_total[cluster_key] += 1

    result: Dict[str, Dict[str, float]] = {}
    for cid, counts in clusters.items():
        total = cluster_total[cid]
        result[cid] = {
            ftype: round(count / total, 4) if total > 0 else 0.0
            for ftype, count in counts.items()
        }

    return result


# ---------------------------------------------------------------------------
# Asymmetry Tricherie ↔ Influence
# ---------------------------------------------------------------------------


def trick_vs_influence_ratio(
    signatures: Sequence[Dict[str, Any]],
    by: str = "cluster_id",
) -> Dict[str, Dict[str, float]]:
    """Compute Tricherie/Influence asymmetry per cluster.

    Returns per cluster:
        - tricherie_share: proportion of Tricherie-family fallacies within this cluster
        - influence_share: proportion of Influence-family fallacies within this cluster
        - ratio: influence / tricherie (bounded to 1e9)
        - asymmetry: (influence - tricherie) / (influence + tricherie) ∈ [-1, 1]
    """
    clusters: Dict[str, Counter] = defaultdict(Counter)

    for sig in signatures:
        state = sig.get("state", sig)
        metadata = sig.get("metadata", {})
        cluster_key = metadata.get(by, "unknown")

        fallacies = state.get("identified_fallacies", {})
        if isinstance(fallacies, dict):
            for f_data in fallacies.values():
                if isinstance(f_data, dict):
                    ftype = f_data.get("type", "")
                    if ftype in TRICHERIE_TYPES:
                        clusters[cluster_key]["tricherie"] += 1
                    elif ftype in INFLUENCE_TYPES:
                        clusters[cluster_key]["influence"] += 1

    result: Dict[str, Dict[str, float]] = {}
    for cid, counts in clusters.items():
        t = counts.get("tricherie", 0)
        i = counts.get("influence", 0)
        total = t + i if (t + i) > 0 else 1

        t_share = round(t / total, 4)
        i_share = round(i / total, 4)
        ratio = round(min(i / t, 1e9), 4) if t > 0 else (1e9 if i > 0 else 0.0)
        asym = round((i - t) / (i + t), 4) if (i + t) > 0 else 0.0

        result[cid] = {
            "tricherie_share": t_share,
            "influence_share": i_share,
            "ratio": ratio,
            "asymmetry": asym,
        }

    return result


# ---------------------------------------------------------------------------
# Co-occurrence matrix
# ---------------------------------------------------------------------------


def cooccurrence_matrix(
    signatures: Sequence[Dict[str, Any]],
    unit: str = "argument",
    top_n: int = 20,
) -> Dict[str, Any]:
    """Compute fallacy co-occurrence matrix with support/confidence/lift/jaccard.

    Args:
        signatures: List of signature dicts from C.2.
        unit: "argument" (same extracted argument) or "doc" (same document).
        top_n: Number of top pairs to return by lift.

    Returns:
        ``{pairs: [{a, b, support, confidence, lift, jaccard}], unit_count}``
    """
    pair_counts: Counter = Counter()
    type_counts: Counter = Counter()
    total_units = 0

    for sig in signatures:
        state = sig.get("state", sig)
        fallacies = state.get("identified_fallacies", {})

        if unit == "argument":
            arg_fallacies: Dict[str, set] = defaultdict(set)
            if isinstance(fallacies, dict):
                for f_data in fallacies.values():
                    if isinstance(f_data, dict):
                        src = f_data.get("source_arg", "__none__")
                        ftype = f_data.get("type", "unknown")
                        arg_fallacies[src].add(ftype)

            for ftypes in arg_fallacies.values():
                total_units += 1
                for ft in ftypes:
                    type_counts[ft] += 1
                if len(ftypes) > 1:
                    for a in sorted(ftypes):
                        for b in sorted(ftypes):
                            if a < b:
                                pair_counts[(a, b)] += 1
        else:  # doc-level
            doc_types: set = set()
            if isinstance(fallacies, dict):
                for f_data in fallacies.values():
                    if isinstance(f_data, dict):
                        doc_types.add(f_data.get("type", "unknown"))

            total_units += 1
            for ft in doc_types:
                type_counts[ft] += 1
            if len(doc_types) > 1:
                for a in sorted(doc_types):
                    for b in sorted(doc_types):
                        if a < b:
                            pair_counts[(a, b)] += 1

    denominator = max(total_units, 1)
    pairs = []
    for (a, b), support in pair_counts.items():
        sa = type_counts[a]
        sb = type_counts[b]
        conf_ab = support / sa if sa > 0 else 0.0
        expected = (sa / denominator) * (sb / denominator)
        lift = support / (denominator * expected) if expected > 0 else 0.0
        jaccard = support / (sa + sb - support) if (sa + sb - support) > 0 else 0.0
        pairs.append(
            {
                "a": a,
                "b": b,
                "support": support,
                "confidence": round(conf_ab, 4),
                "lift": round(lift, 4),
                "jaccard": round(jaccard, 4),
            }
        )

    pairs.sort(key=lambda p: p["lift"], reverse=True)
    return {"pairs": pairs[:top_n], "unit_count": total_units}


# ---------------------------------------------------------------------------
# Cross-coverage informal ↔ formal
# ---------------------------------------------------------------------------


def cross_coverage(
    signatures: Sequence[Dict[str, Any]],
) -> Dict[str, Dict[str, Dict[str, float]]]:
    """Measure co-occurrence of informal fallacies with formal logic signals.

    For each fallacy type, reports two rate families:

      - ``per_signature_rate``: among signatures containing this fallacy type,
        what fraction also exhibit each formal signal. Counts each signature
        once regardless of how many times the fallacy occurs.
      - ``per_occurrence_rate``: among occurrences of this fallacy type, what
        fraction co-occur with each formal signal. A signature with 3
        fallacies + a formal signal counts 3 toward the numerator.

    Formal signals:
      - FOL invalidity
      - Dung edge without support (noisy heuristic — see docs)
      - JTMS retraction
    """
    # Track both counting modes
    sig_seen: Dict[str, set] = defaultdict(set)  # ftype -> set of sig indices
    sig_with_signal: Dict[str, Dict[str, set]] = defaultdict(lambda: defaultdict(set))
    occ_total: Dict[str, int] = defaultdict(int)
    occ_with_signal: Dict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))

    for idx, sig in enumerate(signatures):
        state = sig.get("state", sig)
        fallacies = state.get("identified_fallacies", {})

        has_fol_invalid = False
        fol_results = state.get("fol_analysis_results", [])
        if isinstance(fol_results, list):
            for r in fol_results:
                if isinstance(r, dict) and not r.get("valid", True):
                    has_fol_invalid = True

        # Noisy heuristic: arg attacked but not attacking others
        has_dung_unsupported = False
        dung = state.get("dung_frameworks", {})
        attacks = []
        if isinstance(dung, dict):
            for fw in dung.values():
                if isinstance(fw, dict):
                    attacks.extend(fw.get("attacks", []))
        if attacks:
            args_attacked = set()
            args_with_support = set()
            for atk in attacks:
                if isinstance(atk, dict):
                    args_attacked.add(atk.get("to", ""))
                    args_with_support.add(atk.get("from", ""))
            if args_attacked - args_with_support:
                has_dung_unsupported = True

        has_jtms_retraction = len(state.get("jtms_retraction_chain", [])) > 0

        formal_signals = {
            "fol_invalid": has_fol_invalid,
            "dung_unsupported": has_dung_unsupported,
            "jtms_retraction": has_jtms_retraction,
        }

        if isinstance(fallacies, dict):
            for f_data in fallacies.values():
                if isinstance(f_data, dict):
                    ftype = f_data.get("type", "unknown")
                    occ_total[ftype] += 1
                    sig_seen[ftype].add(idx)
                    for signal, present in formal_signals.items():
                        if present:
                            occ_with_signal[ftype][signal] += 1
                            sig_with_signal[ftype][signal].add(idx)

    result: Dict[str, Dict[str, Dict[str, float]]] = {}
    for ftype in sig_seen:
        n_occ = occ_total[ftype] if occ_total[ftype] > 0 else 1
        n_sig = len(sig_seen[ftype]) if len(sig_seen[ftype]) > 0 else 1
        result[ftype] = {
            "per_signature_rate": {},
            "per_occurrence_rate": {},
        }
        for signal in ["fol_invalid", "dung_unsupported", "jtms_retraction"]:
            result[ftype]["per_signature_rate"][signal] = round(
                len(sig_with_signal[ftype].get(signal, set())) / n_sig, 4
            )
            result[ftype]["per_occurrence_rate"][signal] = round(
                occ_with_signal[ftype].get(signal, 0) / n_occ, 4
            )

    return result


# ---------------------------------------------------------------------------
# Run all formal detectors on a signature
# ---------------------------------------------------------------------------


def run_formal_detectors(
    signature: Dict[str, Any],
    detectors: Optional[List[FormalPatternDetector]] = None,
) -> Dict[str, Dict[str, float]]:
    """Run all formal pattern detectors on a single signature.

    Args:
        signature: A single signature dict.
        detectors: Override detector list. Defaults to FORMAL_DETECTORS.

    Returns:
        ``{detector_name: {metric: value}}``
    """
    if detectors is None:
        detectors = FORMAL_DETECTORS

    results: Dict[str, Dict[str, float]] = {}
    for det in detectors:
        try:
            results[det.name] = det.detect(signature)
        except Exception as exc:
            _logger.warning("detector %s failed: %s", det.name, exc, exc_info=True)
            results[det.name] = {"error": 1.0}
    return results
