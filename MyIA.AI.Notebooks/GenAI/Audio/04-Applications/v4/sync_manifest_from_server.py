"""Sync v4 fishaudio_references/manifest.json with FishAudio server state.

The server is the source of truth: a reference present in
``GET /v1/references/list`` is genuinely cloned, regardless of what the
manifest says.  This script reconciles ``clone_failed`` entries whose
reference_id IS on the server to ``cloned``.

Usage:
    python sync_manifest_from_server.py [--dry-run]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from fishaudio_client import list_references

MANIFEST = Path(__file__).resolve().parent / "outputs" / "fishaudio_references" / "manifest.json"


def main(dry_run: bool = False) -> int:
    if not MANIFEST.exists():
        print(f"FATAL: manifest not found: {MANIFEST}")
        return 1

    refs = json.loads(MANIFEST.read_text(encoding="utf-8"))
    server = list_references()
    server_ids = set(server.get("reference_ids", []))
    print(f"[SYNC] Server reports {len(server_ids)} references")
    print(f"[SYNC] Manifest has {len(refs)} references")

    promoted = 0
    missing = 0
    for ref in refs:
        rid = ref["reference_id"]
        on_server = rid in server_ids
        manifest_status = ref.get("status")
        if on_server and manifest_status != "cloned":
            print(f"  [PROMOTE] {rid}: '{manifest_status}' -> 'cloned' (on server)")
            ref["status"] = "cloned"
            promoted += 1
        elif not on_server and manifest_status == "cloned":
            print(f"  [WARN] {rid}: manifest='cloned' but missing from server")
            missing += 1

    print(f"\n[SYNC] Promoted: {promoted}")
    print(f"[SYNC] Missing-on-server (manifest=cloned): {missing}")
    cloned_total = sum(1 for r in refs if r.get("status") == "cloned")
    print(f"[SYNC] Total cloned after sync: {cloned_total}/{len(refs)}")

    if dry_run:
        print("[SYNC] --dry-run: manifest NOT written")
        return 0

    if promoted > 0:
        MANIFEST.write_text(
            json.dumps(refs, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"[SYNC] Manifest updated: {MANIFEST}")
    else:
        print("[SYNC] No changes")
    return 0


if __name__ == "__main__":
    sys.exit(main(dry_run="--dry-run" in sys.argv))
