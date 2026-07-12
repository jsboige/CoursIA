"""Retry voice clones for entries in manifest.json with status=clone_failed.

Instrumented upload that captures HTTP status + response body on failure to
diagnose the 9/13 clone_failed entries documented in P1 manifest.

Usage:
    python retry_failed_clones.py [--dry-run]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import requests
from dotenv import load_dotenv

load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")

FISHAUDIO_URL = "http://localhost:8197"
MANIFEST = Path(__file__).resolve().parent / "outputs" / "fishaudio_references" / "manifest.json"


def upload_reference_instrumented(reference_id: str, audio_path: str, text: str) -> dict:
    """Upload reference with full error capture.

    Returns dict with keys:
      ok (bool), status_code (int|None), body (str), exc (str|None)
    """
    try:
        with open(audio_path, "rb") as audio_file:
            resp = requests.post(
                f"{FISHAUDIO_URL}/v1/references/add",
                data={"id": reference_id, "text": text},
                files={"audio": (Path(audio_path).name, audio_file, "audio/mpeg")},
                timeout=60,
            )
        body = resp.text[:1000] if resp.text else "<empty>"
        return {
            "ok": resp.ok,
            "status_code": resp.status_code,
            "body": body,
            "exc": None,
        }
    except requests.RequestException as exc:
        body = "<no response>"
        status = None
        if hasattr(exc, "response") and exc.response is not None:
            body = exc.response.text[:1000]
            status = exc.response.status_code
        return {
            "ok": False,
            "status_code": status,
            "body": body,
            "exc": str(exc),
        }


def main(dry_run: bool = False) -> int:
    if not MANIFEST.exists():
        print(f"FATAL: manifest not found: {MANIFEST}")
        return 1

    refs = json.loads(MANIFEST.read_text(encoding="utf-8"))
    failed = [r for r in refs if r.get("status") == "clone_failed"]
    print(f"[RETRY] Found {len(failed)}/{len(refs)} clone_failed entries")
    if not failed:
        print("[RETRY] Nothing to do.")
        return 0

    if dry_run:
        for r in failed:
            print(f"  DRY: {r['reference_id']} ({Path(r['sample_mp3_path']).name})")
        return 0

    results = []
    succeeded = 0
    for ref in failed:
        rid = ref["reference_id"]
        path = ref["sample_mp3_path"]
        text = ref["sample_text"]
        if not Path(path).exists():
            print(f"  [SKIP] {rid}: MP3 missing at {path}")
            results.append({"id": rid, "ok": False, "reason": "mp3_missing"})
            continue

        print(f"  [TRY] {rid} ({Path(path).name}, {len(text)} chars)")
        out = upload_reference_instrumented(rid, path, text)
        print(f"    -> ok={out['ok']} status={out['status_code']}")
        if not out["ok"]:
            print(f"    body={out['body'][:200]}")
            if out["exc"]:
                print(f"    exc={out['exc']}")
        results.append({"id": rid, **out})

        if out["ok"]:
            ref["status"] = "cloned"
            succeeded += 1

    print()
    print(f"[RETRY] Succeeded: {succeeded}/{len(failed)}")
    print(f"[RETRY] Still failed: {len(failed) - succeeded}/{len(failed)}")
    total_cloned = sum(1 for r in refs if r.get("status") == "cloned")
    print(f"[RETRY] Total cloned in manifest: {total_cloned}/{len(refs)}")

    if succeeded > 0:
        MANIFEST.write_text(
            json.dumps(refs, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"[RETRY] Manifest updated: {MANIFEST}")

    # Write diagnostic log
    log_path = Path(__file__).resolve().parent / "outputs" / "fishaudio_references" / "retry_log.json"
    log_path.write_text(json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"[RETRY] Log: {log_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(dry_run="--dry-run" in sys.argv))
