#!/bin/bash
# Patch funasr library and Fun-ASR model code at runtime
# These patches fix issues with Fun-ASR-Nano-2512 that aren't in upstream releases
set -e

AUTO_MODEL="/usr/local/lib/python3.11/dist-packages/funasr/auto/auto_model.py"
FUNASR_MODEL="/app/fun-asr-code/model.py"

# Patch 1: Remove batch_size guard in FunASRNano inference_prepare
# FunASRNano doesn't implement batch decoding, but the guard triggers incorrectly
# because batch_size is in milliseconds (from batch_size_s conversion), not a count
if grep -q "raise NotImplementedError.*batch decoding" "$FUNASR_MODEL" 2>/dev/null; then
    echo "Patching model.py: removing batch_size guard..."
    sed -i '/bs = kwargs\.get("batch_size"/,/raise NotImplementedError.*batch decoding/c\        # batch_size guard removed - FunASRNano processes one segment at a time via VAD' "$FUNASR_MODEL"
    echo "  Done"
else
    echo "model.py: batch_size guard already patched or absent"
fi

# Patch 2: Handle dict-format timestamps in auto_model.py results combining
# FunASR Nano returns timestamps as dicts {"start": ..., "end": ...} instead of lists
if ! grep -q "isinstance(t, dict)" "$AUTO_MODEL" 2>/dev/null; then
    echo "Patching auto_model.py: adding dict-format timestamp handling..."
    sed -i 's/for t in restored_data\[j\]\[k\]:/for t in restored_data[j][k]:\n                            if isinstance(t, dict):\n                                offset = vadsegments[j][0]\n                                t["start"] = t.get("start", 0) + offset\n                                t["end"] = t.get("end", 0) + offset\n                                continue/' "$AUTO_MODEL"
    echo "  Done"
else
    echo "auto_model.py: dict-format timestamp handling already patched"
fi

echo "Patches applied successfully"
