"""Warm up the local TTS engines before a bench run.

These services lazy-load their model into VRAM on the first inference request,
and the cold-load can exceed the client/gateway timeout (-> RemoteDisconnected
on the first real call). Firing one tiny render per engine here makes the model
resident so the bench's first measured call is already warm. Prints a readiness
verdict per engine; exits 0 if at least fish + qwen are ready (the priority pair).
"""
import sys
import time
from pathlib import Path

_LAB_DIR = Path(__file__).resolve().parent
_V4_DIR = _LAB_DIR.parent
for _p in (_LAB_DIR, _V4_DIR):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from fishaudio_client import fishaudio_tts  # noqa: E402
from qwen_tts_client import qwen_tts_voicedesign_chunked  # noqa: E402

try:
    from ab_engine_test import call_kokoro  # noqa: E402
except Exception:  # pragma: no cover
    call_kokoro = None

FLAT_REF_ID = "v4_narrator_male_neutral"
QWEN_INSTR = ("Un narrateur francais de livre audio, voix masculine grave et "
              "chaleureuse, intonation expressive.")
TINY = "Bonjour, ceci est un test."


def _try(name, fn):
    t0 = time.time()
    try:
        out = fn()
        dt = time.time() - t0
        ok = bool(out) and (not isinstance(out, (bytes, bytearray)) or len(out) > 1000)
        n = len(out) if isinstance(out, (bytes, bytearray)) else "?"
        print(f"  [{name}] {'READY' if ok else 'EMPTY'} ({dt:.1f}s, {n} bytes)")
        return ok
    except Exception as e:  # noqa: BLE001
        dt = time.time() - t0
        print(f"  [{name}] FAIL ({dt:.1f}s): {type(e).__name__}: {str(e)[:120]}")
        return False


def main():
    print("=== warming TTS engines (cold-load into VRAM) ===")
    fish_ok = _try("fish", lambda: fishaudio_tts(
        TINY, reference_id=FLAT_REF_ID, temperature=0.7, seed=42,
        format="mp3", timeout=600))
    qwen_ok = _try("qwen", lambda: qwen_tts_voicedesign_chunked(
        TINY, instructions=QWEN_INSTR, max_chars=160))
    kok_ok = False
    if call_kokoro is not None:
        kok_ok = _try("kokoro", lambda: call_kokoro(TINY))
    print(f"=== summary: fish={fish_ok} qwen={qwen_ok} kokoro={kok_ok} ===")
    sys.exit(0 if (fish_ok and qwen_ok) else 1)


if __name__ == "__main__":
    main()
