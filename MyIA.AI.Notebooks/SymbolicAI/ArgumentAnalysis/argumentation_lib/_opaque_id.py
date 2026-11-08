# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/evaluation/opaque_id.py
# Source SHA1 : 60933b0904a86a77eb9a5017069b43e4b6fac0bc (65L @ 2e2a1c3c)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_opaque_id.py
# Copy LICENSE : MIT (inherited from upstream)
# Issue de pilotage #23163 (serie Argument_Analysis complete) -- See EPIC #23163
#
# VERBATIM SANS MODIFICATION : le corps ci-dessous est byte-for-byte identique
# a l'amont aux fins de ligne pres. Seule cette entete de provenance est
# ajoutee -- convention des ports verbatim du dossier (cf `_atms_core.py`).
# Role porte : ID opaques deterministes (sha256(salt+name), 8 hex) -- sel secret obligatoire
# Fins de ligne : l'amont livre ce fichier en CRLF, le depot l'impose en LF
# (`.gitattributes` : `*.py text eol=lf`) ; le contenu est identique a l'amont
# aux fins de ligne pres (cf NOTICE-EPITA, section "Fins de ligne").
# =============================================================================
"""Deterministic opaque ID generation for privacy-safe references.

Produces stable identifiers from sensitive source names — stable means the
same (name, salt) always yields the same 8-char hex prefix of sha256. The
strength of the obfuscation depends entirely on the secrecy of the salt:

- A secret salt makes the ID unpredictable to anyone who does not hold it.
- A public salt makes the ID a deterministic function of ``source_name``:
  anyone who guesses a candidate name can recompute the ID in O(1) and
  confirm whether it matches a published opaque reference.

Property actually held by this module: an opaque ID is **not reversible**
(sha256 has no pre-image attack), and it is **collision-resistant for
distinct names under a fixed secret salt**. It is **not a one-way
function over the name** — a public salt turns the function into a
confirmation oracle, not an obfuscation.

For a secret to actually hide the mapping, callers MUST provide a salt
either as the ``salt=`` argument or via the ``OPAQUE_ID_SALT`` environment
variable. The function raises ``RuntimeError`` otherwise. The previous
default salt (``"epita-arg-analysis-2025"``) lived as a literal in this
file — a tracked, public string — and provided no privacy: any reader
of the repository could confirm a guessed name against a published ID.
This module no longer ships a fallback so that silent regression to a
public salt is impossible.

See #1973 for the audit and rationale.
"""

import hashlib
import os


def opaque_id(source_name: str, salt: str | None = None) -> str:
    """Return a deterministic 8-char opaque ID from a source name.

    Args:
        source_name: The sensitive identifier to obfuscate.
        salt: Salt to mix into the hash. If ``None``, the function reads
              ``OPAQUE_ID_SALT`` from the environment. If neither is
              available, the function raises ``RuntimeError`` rather
              than fall back to a default — a default would be either
              tracked (public) or rotated (breaking published IDs).
              Operators must set the env var explicitly.

    Returns:
        First 8 hex characters of ``sha256(salt + name)``.

    Raises:
        RuntimeError: when neither ``salt`` nor ``OPAQUE_ID_SALT`` is
            available. Callers that need to handle this should set
            ``OPAQUE_ID_SALT`` in their environment (``.env`` locally,
            secrets in CI).
    """
    effective_salt = (salt or os.getenv("OPAQUE_ID_SALT") or "").strip()
    if not effective_salt:
        raise RuntimeError(
            "OPAQUE_ID_SALT is required: no salt argument was passed "
            "and the OPAQUE_ID_SALT environment variable is unset. "
            "A public default would let any reader of the repo "
            "confirm a guessed name against a published opaque ID; "
            "set OPAQUE_ID_SALT in your .env / CI secrets instead."
        )
    digest = hashlib.sha256(f"{effective_salt}{source_name}".encode()).hexdigest()
    return digest[:8]
