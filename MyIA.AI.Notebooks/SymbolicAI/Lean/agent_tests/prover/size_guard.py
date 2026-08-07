"""Delta-based size guard + edit sandbox for the Lean prover harness.

Two complementary mechanisms to stop the autonomous prover from "improving"
sorry count by quietly shrinking the file instead of proving the sorry:

1. **Delta-based size guard** -- ``check_size_delta``.

   The pre-existing absolute cap (5000 lines, ``prover.tools._check_file_size_guard``)
   creates a perverse incentive: when the file crosses the threshold mid-run,
   the prover's only way to stay under it is to **delete** content -- which
   observed DEMO 63 (cycle-98) did to the tune of 622 lines on a 5385-line file,
   silently deleting guard theorems to fit the cap.

   ``check_size_delta`` complements the absolute cap with three DELTA checks:
   * **Net insertions** (``MAX_NET_INSERTIONS``): blocks a single edit that
     adds more than the cap. Catches "I'll just write the whole proof in one
     shot" attempts that bypass context-boundary checks.
   * **Net deletions** (``MAX_NET_DELETION_LINES`` absolute, plus a
     ``MAX_NET_DELETION_PCT`` percentage of original): blocks an edit that
     strips a suspicious chunk of lines. Catches the DEMO 63 pattern: 622
     deleted lines on a 5385-line file (11.5% but 622 > 500 absolute).
   * **Pre-existing oversized files** (``INSERT_ONLY_THRESHOLD``): when the
     original file is already above the absolute cap, allows only insert-mode
     edits (net lines must be ``>= 0``). Catches "delete-to-fit" attempts
     against files that grew beyond the cap through legitimate evolution.

   The absolute cap (5000 lines) is kept as a **post-edit safety net** in
   ``prover.tools._check_file_size_guard`` for the case where the file grows
   under successive small inserts; the delta check is the **primary gate**
   applied before the write.

2. **Edit sandbox** -- ``EditSandbox``.

   A file-level checkpoint taken **once**, on the first edit, so a runaway
   edit sequence (or a verifier crash, or an abort) cannot leave the file
   in an unsound state. The sandbox exposes:
   * ``snapshot()``: copies the file to a temp path. Idempotent (no-op on
     subsequent calls within the same sandbox).
   * ``restore()``: copies the snapshot back over the live file. Called by
     the verifier-failure / loop-error paths in ``prover/tools.py``.
   * ``drop()``: deletes the snapshot temp file. Called on the happy path
     where the edit is verified and accepted, to free disk.

   The sandbox is **pure stdlib** (uses ``tempfile`` + ``shutil``): no
   dependency on Lean, agent_framework, or any LLM stack, so it loads even
   when the rest of the harness cannot.

Why this module is a standalone file
------------------------------------
This module follows the same pattern as ``prover.forensic_guards``: it is
extracted to a stdlib-only file so unit tests can load it by file path
without dragging ``agent_framework`` into pytest collection time on bare
CI runners. ``prover.tools`` re-imports these names, so behaviour is
unchanged for the runtime harness.

See Epic #1453 (prover harness co-evolution), DEMO 63 forensic finding
(size_guard perverse incentive + non-sandboxed edit), and the dispatch
msg-20260806T180640-8evgl8 for the original sub-grain brief.
"""

from __future__ import annotations

import shutil
import tempfile
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Constants (tuned for the typical .lean tactic-prover workload)
# ---------------------------------------------------------------------------
# A single edit may add up to N net lines. Sized for "one proof block plus a
# helper lemma or two" — anything more is a structural rewrite and belongs in
# file_replace_lines with explicit allow_structural=True.
MAX_NET_INSERTIONS = 1000

# A single edit may delete up to N net lines. Sized above "one sorry block +
# a few lines of strategy comment" so legitimate cleanup passes, but well
# below "delete a whole guard theorem to fit the cap" (DEMO 63 was -622).
MAX_NET_DELETION_LINES = 500

# And the same deletion, expressed as a fraction of the original file. 10%
# of a 5000-line file = 500 lines, which matches MAX_NET_DELETION_LINES for
# files near the absolute cap. Smaller files get a tighter ceiling.
MAX_NET_DELETION_PCT = 0.10

# When the ORIGINAL file already exceeds this line count, only insert-mode
# edits are allowed (net lines >= 0). This is the "insert-only allowance"
# that prevents the perverse "delete-to-fit" incentive on files that grew
# above the absolute cap through legitimate evolution.
INSERT_ONLY_THRESHOLD = 5000


# ---------------------------------------------------------------------------
# Delta-based size guard
# ---------------------------------------------------------------------------

def _line_count(content: str) -> int:
    """Count lines in a string (matches ``str.count('\\n') + 1`` semantics used in tools.py)."""
    return content.count("\n") + 1


def check_size_delta(orig_content: str, new_content: str,
                     operation: str) -> Optional[str]:
    """Reject edits that grow or shrink the file by an implausible amount.

    Args:
        orig_content: File content BEFORE the edit.
        new_content: Hypothetical file content AFTER the edit.
        operation: Tool name (``file_replace_lines`` / ``file_insert_lines`` /
            ``file_replace_sorry``) for the error message.

    Returns:
        ``None`` if the edit is allowed, otherwise a human-readable error
        string explaining which delta rule was violated.
    """
    orig_lines = _line_count(orig_content)
    new_lines = _line_count(new_content)
    net = new_lines - orig_lines
    orig_above_cap = orig_lines > INSERT_ONLY_THRESHOLD

    # Rule 1: insert-only allowance for pre-existing oversized files.
    if orig_above_cap and net < 0:
        return (
            f"BLOCKED by size-delta guard ({operation}): file already has {orig_lines} lines "
            f"(>{INSERT_ONLY_THRESHOLD}); insert-only allowance is active. "
            f"This edit would delete {abs(net)} net lines, which is forbidden — "
            f"the absolute cap from a previous run must not be 'solved' by silent deletions. "
            f"Make a smaller, additive edit (file_insert_lines) or split into multiple edits."
        )

    # Rule 2: net insertions cap.
    if net > MAX_NET_INSERTIONS:
        return (
            f"BLOCKED by size-delta guard ({operation}): net insertion of {net} lines "
            f"exceeds cap of {MAX_NET_INSERTIONS}. "
            f"A single tactic-tool edit should not add more than {MAX_NET_INSERTIONS} lines. "
            f"Split into smaller inserts (file_insert_lines), or check that you are not "
            f"rewriting a whole section by accident."
        )

    # Rule 3: net deletions cap (absolute + percentage).
    if net < 0:
        abs_del = abs(net)
        pct_del = abs_del / max(1, orig_lines)
        if abs_del > MAX_NET_DELETION_LINES:
            return (
                f"BLOCKED by size-delta guard ({operation}): net deletion of {abs_del} lines "
                f"exceeds absolute cap of {MAX_NET_DELETION_LINES}. "
                f"Large deletions can silently remove guard theorems (DEMO 63 forensic: "
                f"622-line net deletion on a 5385-line file erased 3 c.91 guard theorems). "
                f"Use targeted file_replace_lines on a narrower range, or split into "
                f"multiple smaller edits."
            )
        if pct_del > MAX_NET_DELETION_PCT:
            return (
                f"BLOCKED by size-delta guard ({operation}): net deletion of {abs_del} lines "
                f"({pct_del:.1%} of original) exceeds percentage cap of "
                f"{MAX_NET_DELETION_PCT:.0%}. "
                f"Deletions of more than {MAX_NET_DELETION_PCT:.0%} of the file are "
                f"structural rewrites, not tactic edits — use file_replace_lines with "
                f"allow_structural=True or revise the strategy."
            )

    return None


# ---------------------------------------------------------------------------
# Edit sandbox
# ---------------------------------------------------------------------------

class EditSandbox:
    """One-shot checkpoint of a file, restored on demand.

    Lifecycle:
        sb = EditSandbox(Path("/abs/path/to/File.lean"))
        sb.snapshot()                   # copies the file to a temp path
        ... edits applied to the file ...
        sb.restore()                    # on verifier failure: revert to snapshot
        # OR
        sb.drop()                       # on happy path: free the snapshot

    The sandbox is **idempotent on ``snapshot()``**: a second call is a no-op,
    so callers don't need to track whether they have already snapshotted.

    Thread-safety: not thread-safe. The prover runs single-threaded per file.
    """

    def __init__(self, filepath: Path):
        self._filepath = filepath
        self._snapshot_path: Optional[Path] = None

    @property
    def has_snapshot(self) -> bool:
        return self._snapshot_path is not None

    def snapshot(self) -> Path:
        """Copy the current file to a temp path; return that path.

        No-op (returns the existing snapshot path) if already snapshotted.
        """
        if self._snapshot_path is not None:
            return self._snapshot_path
        # NamedTemporaryFile with delete=False + a stable suffix so a
        # crash investigator can correlate the temp file with its origin.
        fd, name = tempfile.mkstemp(
            prefix=f"{self._filepath.name}.",
            suffix=".sandbox",
            dir=str(self._filepath.parent),
        )
        try:
            # mkstemp opens the file descriptor; copy via shutil to honor
            # encoding-aware reads.
            import os
            os.close(fd)
            shutil.copy2(self._filepath, name)
        except Exception:
            # Best-effort cleanup of the empty temp file on copy failure.
            try:
                Path(name).unlink(missing_ok=True)
            except Exception:
                pass
            raise
        self._snapshot_path = Path(name)
        return self._snapshot_path

    def restore(self) -> bool:
        """Restore the snapshot over the live file. Returns True if restored."""
        if self._snapshot_path is None:
            return False
        if not self._snapshot_path.exists():
            # Snapshot lost (e.g. someone rm'd the temp file) — nothing to do.
            self._snapshot_path = None
            return False
        shutil.copy2(self._snapshot_path, self._filepath)
        return True

    def drop(self) -> None:
        """Discard the snapshot. Idempotent."""
        if self._snapshot_path is None:
            return
        try:
            self._snapshot_path.unlink(missing_ok=True)
        finally:
            self._snapshot_path = None