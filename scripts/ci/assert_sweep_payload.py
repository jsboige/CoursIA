#!/usr/bin/env python3
"""assert_sweep_payload.py -- positive control for the review-coverage organ.

## Why this exists

`review_coverage.py` is **advisory**: it always exits 0, by design (#11232 --
"il ne peut pas bloquer, c'est precisement l'absence qui est le defaut"). That
design has a cost the organ paid in full: for 60 consecutive scheduled runs it
exited 0 *without ever sweeping a single PR*, because `--threshold ""` killed
argparse before the sweep. The run was green; the organ was dead.

A `--help >/dev/null` control does not close that hole -- it proves argparse
parses, nothing more (Hermes' reserve on PR #13370). What distinguishes a live
sweep from a dead one is the **payload**: `review_coverage.py` prints its
result dict only *after* the sweep has run. So the control asserts on the
payload, not on an exit code.

The workflow step running this assertion is allowed to go red. That is the
point: the organ's own breakage becomes visible instead of reading green.

## Run

    python scripts/review_coverage.py --dry-run | tee sweep.json
    python scripts/ci/assert_sweep_payload.py sweep.json
"""
from __future__ import annotations

import json
import sys

REQUIRED_KEYS = frozenset(
    {"threshold", "dry_run", "flagged", "cleared",
     "skipped_draft", "skipped_base", "errors"}
)
LIST_KEYS = ("flagged", "cleared", "skipped_draft", "skipped_base")


def check(raw: str) -> tuple[bool, str]:
    """Return (ok, message) for a captured `review_coverage.py` stdout."""
    raw = (raw or "").strip()
    if not raw:
        return False, "stdout vide -- aucun balayage n'a eu lieu."
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        return False, f"stdout non-JSON ({exc}) -- pas un payload de balayage."
    if not isinstance(payload, dict):
        return False, f"payload de type {type(payload).__name__}, attendu un objet."
    missing = REQUIRED_KEYS - set(payload)
    if missing:
        return False, f"cles absentes du payload : {sorted(missing)}."
    for key in LIST_KEYS:
        if not isinstance(payload[key], list):
            return False, f"cle {key!r} de type {type(payload[key]).__name__}, attendu une liste."
    seen = sum(len(payload[key]) for key in LIST_KEYS)
    return True, (
        f"balayage effectif -- seuil={payload['threshold']} "
        f"PRs examinees={seen} flagged={len(payload['flagged'])} "
        f"cleared={len(payload['cleared'])} erreurs={len(payload['errors'])}"
    )


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print("usage: assert_sweep_payload.py <fichier-stdout>", file=sys.stderr)
        return 2
    try:
        with open(argv[0], encoding="utf-8") as handle:
            raw = handle.read()
    except OSError as exc:
        # NEVER fail open: an unreadable capture is indistinguishable from a
        # dead sweep, and treating it as a pass is the exact defect this
        # control exists to catch.
        print(f"CONTROLE POSITIF ECHOUE : capture illisible ({exc}).", file=sys.stderr)
        return 1
    ok, message = check(raw)
    if not ok:
        print(f"CONTROLE POSITIF ECHOUE : {message}", file=sys.stderr)
        return 1
    print(message)
    return 0


if __name__ == "__main__":
    sys.exit(main())
