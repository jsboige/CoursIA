# =============================================================================
# Verbatim port from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file: argumentation_analysis/agents/core/logic/modal_kb_identifier_normalizer.py
# Upstream commit: a8025f60 (2026-07-02) — blob d86761b9, 114 lignes
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
#
# Vendored for EPIC #4960 volet B etape 4 (branchement formel, 2026-11-14) :
# the verbatim `_modal_handler.py` imports this sibling at module level
# (`.modal_kb_identifier_normalizer import ModalIdentifierNormalizer`) and its
# sub-tranche had not landed it — the modal leg (listed FUNCTIONAL by the EPIC
# body: PL / FOL / Modal / AF-Dung / SAT) was unimportable for want of this
# stdlib-only module (re + typing, zero dependency).
# Delivered under the underscore name `_modal_kb_identifier_normalizer`;
# the alias `argumentation_lib.modal_kb_identifier_normalizer` is registered
# by `_logic_handlers_compat.py`, same re-routing as `tweety_initializer`.
#
# Verbatim integrity: body below this header is byte-for-byte identical to
# the upstream source at the cited commit.
# =============================================================================

"""Modal KB identifier normalization (#1326, builds on #1260/#1230).

Tweety's ``MlParser`` grammar is *stricter* than the propositional parser: a
predicate/sort declaration must match ``[a-zA-Z][a-zA-Z0-9]*`` — underscores and
other separators are rejected with::

    ParserException: Illegal characters in predicate definition 'joke_teleprompter';
                      declaration must conform to [a-z,A-Z]([a-z,A-Z,0-9])*

Several modal-KB producers emit underscored multi-word atoms (LLM-generated
identifiers such as ``joke_teleprompter``, the spectacular-path
``_construct_modal_kb_from_json``). Such a KB never parses, so consistency is
never decided and the modal axis degrades to honest ``None`` (the R519
firsthand-reproduced failure: 3/3 modal axes undecided).

This module maps every MlParser-illegal atom to a fresh legal identifier and is
applied at the parse point (``ModalHandler``, immediately *amont* de
``parseBeliefBase``) so EVERY caller is protected regardless of upstream
producer — defense-in-depth. The transform:

* PascalCase join on non-alphanumeric splits: ``joke_teleprompter`` →
  ``JokeTeleprompter`` (the semantic stem survives, only the separators drop).
* generic ``MpAtomN`` fallback when the stem is empty/illegal.
* applied **consistently** to declarations and bodies, and the collision set
  tracks *generated* candidates too — so two distinct source atoms that
  PascalCase to the same stem (``heavy_rain`` vs ``heavy-rain``) are
  disambiguated instead of collapsed. That soundness guard was absent from the
  original inline #1260 closure.

Anti-pendule: this normalizes the **syntax** of the sort-name for Tweety only;
it does not neutralize semantic content or variance. No heuristic masks a
parse-fail — a genuinely malformed KB is still rejected and the handler returns
honest ``None`` (#1019 fail-loud). It is idempotent on already-legal atoms, so a
caller that pre-sanitizes (the nl path via ``invoke_callables._legal_symbol``)
is unaffected by the second pass here.
"""

from __future__ import annotations

import re
from typing import Dict, Iterable, Tuple

# Reserved words of the modal grammar — must never be treated as atoms.
_KEYWORDS = frozenset(
    {
        "forall",
        "exists",
        "true",
        "false",
        "type",
        "prop",
        "and",
        "or",
        "not",
        "implies",
    }
)

# A modal atom token (mirrors ``invoke_callables._atom_re`` / #1260): any
# identifier-shaped run including underscores, so ``joke_teleprompter`` is
# captured as ONE token rather than split around the underscore.
_ATOM_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

# The MlParser declaration grammar (firsthand-confirmed via the ParserException
# message reproduced in #1326): first letter alphabetic, rest alphanumeric, NO
# underscores/separators.
_LEGAL_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9]*$")


class ModalIdentifierNormalizer:
    """Sound, memoized mapping of modal atoms to MlParser-legal identifiers.

    ``reserved`` pre-seeds the collision set (e.g. atoms already legal in the
    KB) so a generated symbol never shadows a real atom. Generated candidates
    are also added to the collision set, so two distinct source atoms that
    PascalCase to the same stem are disambiguated rather than collapsed — the
    soundness guard missing from the original inline #1260 closure.
    """

    def __init__(self, reserved: Iterable[str] = ()) -> None:
        self._reserved: set[str] = set(reserved)
        self._forward: Dict[str, str] = {}

    def legalize(self, atom: str) -> str:
        """Return an MlParser-legal identifier for ``atom`` (memoized)."""
        if atom in _KEYWORDS or _LEGAL_RE.match(atom):
            return atom
        cached = self._forward.get(atom)
        if cached is not None:
            return cached
        parts = [p for p in re.split(r"[^A-Za-z0-9]+", atom) if p]
        candidate = "".join(p[:1].upper() + p[1:] for p in parts) or "MpAtom"
        if not _LEGAL_RE.match(candidate) or candidate in self._reserved:
            # Rare: degenerate stem or collision — disambiguate, but keep the
            # readable stem as the base (not a bare MpAtomN).
            base = candidate if _LEGAL_RE.match(candidate) else "MpAtom"
            suffix = 1
            while f"{base}{suffix}" in self._reserved:
                suffix += 1
            candidate = f"{base}{suffix}"
        self._reserved.add(candidate)
        self._forward[atom] = candidate
        return candidate

    def normalize_belief_set(self, content: str) -> Tuple[str, Dict[str, str]]:
        """Normalize every atom in a modal belief-set string.

        Returns ``(normalized_content, reverse_map)`` where ``reverse_map`` is
        ``{normalized: original}`` for readability/traceability. Atoms already
        legal are absent from the map (they pass through verbatim).
        """
        normalized = _ATOM_RE.sub(lambda m: self.legalize(m.group(0)), content)
        reverse = {v: k for k, v in self._forward.items()}
        return normalized, reverse
