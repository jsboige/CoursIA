#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/utils/taxonomy_local_overrides.py` from
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
"""Code-level overrides applied to the vendored Argumentum taxonomy at load.

The vendored CSV (``argumentum_fallacies_taxonomy.csv``) is a byte-faithful
mirror of upstream ArgumentumGames/Argumentum @ c86b71ff — the integrity
guard (tests/unit/scripts/test_argumentum_taxonomy_integrity.py) pins that
mirror, and re-pulls must keep diffing cleanly against upstream. Local
fixes therefore NEVER edit the CSV: they live here, addressed by PK,
reviewable and revertible the day upstream fixes the same rows.

#2036 tranche 1 — purge of the two raw editorial notes in ``nom_vulgarisé``:

- PK 41 (path 1.1.2.1.5, text_fr « Je le sais quand je le vois »): the field
  carries a titling brainstorm (« Je n'aime aucun des titres. Chercher vers… »),
  not a name. ``taxonomy_sophism_detector`` echoes ``nom_vulgarisé`` on every
  detection, so a detection of this node would put the whole note in reader
  prose.
- PK 992 (path 6.2.2, text_fr « Vouloir le beurre et l'argent du beurre »):
  the field carries a column-swap question
  (« Versatilité: ON INVERSERAIT PAS LE TEXT_FR eT LE NOM VULGARISé? »).

Both are purged to the empty string — ``nom_vulgarisé`` is optional by
design (the field is empty on the vast majority of the 1408 rows), the
lexical matcher guards empty values (``if nom_vulgarise and …``), and no
replacement name is coined here: inventing taxonomy content is item 2 of
#2036, which needs an explicit register-policy decision.

#2036 item 2 — attested display aliases for broken-register ``text_fr``
names. Arbitration: display-only aliases are allowed ONLY where the French
term is *attested* (published title, reference glossary, established
proverb) — never forged. The four attestations live in
``RENDER_ALIAS_SOURCES`` and are machine-checked (a sourced-table/test pair
reddens on an unsourced alias).

The alias is display-ONLY. It must never ride the loaded data: the lexical
matcher reads ``nom_vulgarisé`` (substring) and ``text_fr`` (words > 4
chars) from the same loaded rows, so an alias in those fields would change
what matches. It applies at name-resolution-for-reader sites only —
detector state writes, benchmark name preference, navigator prompt renders
— via :func:`render_alias`.

Nodes left untouched because no attested French term was found (searched
2026-09-05): PK 41 « Je le sais quand je le vois », PK 980 « La science
s'est déjà trompée », PK 992 « Vouloir le beurre et l'argent du beurre »
(attested idiom, no alternative technical term), PK 1009 « Où est le mal ? ».
The 7 borderlines are deliberately untouched (established idioms).
"""

from __future__ import annotations

from typing import Dict, Iterable, Union

# PK -> {field: replacement}. Keys are ints; loaders normalise to str for
# DictReader rows.
EDITORIAL_NOTE_PURGES: Dict[int, Dict[str, str]] = {
    41: {"nom_vulgarisé": ""},
    992: {"nom_vulgarisé": ""},
}

# PK -> attested display alias (#2036 item 2). Every entry MUST have a
# citation in RENDER_ALIAS_SOURCES — an alias without a source is a forged
# name and fails the guard test.
RENDER_ALIASES: Dict[int, str] = {
    320: "Pensez aux enfants",
    328: "Sagesse du dégoût",
    449: "Mieux vaut peu que rien",
    1311: "Gros mensonge",
}

RENDER_ALIAS_SOURCES: Dict[int, str] = {
    320: "fr.wikipedia.org/wiki/Pensez_aux_enfants — nom rhétorique établi du cliché (argumentum ad misericordiam)",
    328: "fr.wikipedia.org/wiki/Sagesse_du_dégoût — titre français publié de la « wisdom of repugnance » (Kass, 1997)",
    449: "proverbe français attesté — linternaute.fr/proverbe/2008, dicocitations.com",
    1311: "rendu attesté de « big lie » — fr.wikipedia.org/wiki/Glossaire_de_la_langue_du_Troisième_Reich, Linguee/Reverso",
}


def render_alias(pk, default_name: str) -> str:
    """Return the attested display alias for a node, else the default name.

    Display-only: callers pass the name they resolved for a reader (state
    write, name preference, prompt render); the matching fields in the
    loaded taxonomy are never rewritten. A malformed PK is a passthrough —
    this helper must never be the reason a render crashes.
    """
    try:
        key = int(pk)
    except (TypeError, ValueError):
        return default_name
    return RENDER_ALIASES.get(key, default_name)


def purge_row(row: Dict[str, str]) -> Dict[str, str]:
    """Apply the editorial-note purges to one DictReader row, in place."""
    pk = str(row.get("PK", ""))
    overrides = EDITORIAL_NOTE_PURGES.get(int(pk)) if pk.isdigit() else None
    if overrides:
        for field, replacement in overrides.items():
            row[field] = replacement
    return row


def purge_rows(rows: Iterable[Dict[str, str]]) -> list:
    """Apply the editorial-note purges to DictReader rows, in place."""
    return [purge_row(row) for row in rows]


def purge_dataframe(df) -> None:
    """Apply the editorial-note purges to a pandas DataFrame in place.

    Addresses rows by the ``PK`` column (string-normalised comparison) and
    only rewrites columns the override table names, so a schema change
    upstream fails loudly at the missing-column access rather than purging
    the wrong cell.
    """
    if "PK" not in df.columns:
        return
    pk_column = df["PK"].astype(str)
    for pk, overrides in EDITORIAL_NOTE_PURGES.items():
        mask = pk_column == str(pk)
        if not mask.any():
            continue
        for field, replacement in overrides.items():
            df.loc[mask, field] = replacement
