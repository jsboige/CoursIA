#!/usr/bin/env python3
"""Test P4 re-run with 29 official tags only — no free-form, no tts_context_prefix.

Runs on segments 0-20 (Act 1 exposition) to compare against existing annotated_v4.json.
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dotenv import load_dotenv
load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")

from v4.p4_annotation import load_inputs, annotate_batch, OUTPUTS
from v4.p5_tts import _compose_tts_text
from v4.schemas import ALL_PROSODY_TAGS

TEST_RANGE = range(0, 21)
OUTPUT_FILE = OUTPUTS / "annotated_v4_tags_only_test.json"


def main():
    segments, contexts = load_inputs()
    test_segs = [s for s in segments if s.seg_index in TEST_RANGE]
    print(f"Test sample: {len(test_segs)} segments (indices {TEST_RANGE.start}-{TEST_RANGE.stop - 1})")

    all_annotated = []
    prev_tags = None
    batch_idx = 1
    for i in range(0, len(test_segs), 10):
        batch = test_segs[i:i + 10]
        result = annotate_batch(batch, contexts, batch_idx, prev_tags)
        all_annotated.extend(result)
        if result:
            prev_tags = result[-1].prosody_tags
        batch_idx += 1

    out = {
        "methodology": "P4 re-run: 29 official tags only, no free-form, no tts_context_prefix",
        "test_range": list(TEST_RANGE),
        "segments": [a.model_dump() for a in all_annotated],
    }
    with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)

    official_tag_count = sum(len(s.prosody_tags) for s in all_annotated)
    free_form_tags = []
    official_tags_seen = []
    for s in all_annotated:
        tags = re.findall(r"\[([^\]]+)\]", s.annotated_text)
        for t in tags:
            if t.lower() in ALL_PROSODY_TAGS:
                official_tags_seen.append(t.lower())
            else:
                free_form_tags.append(t)

    print(f"\nResults: {len(all_annotated)} segments")
    print(f"  Official prosody_tags field: {official_tag_count}")
    print(f"  Official tags in annotated_text: {len(official_tags_seen)}")
    print(f"  Free-form tags (SHOULD BE 0): {len(free_form_tags)}")
    if free_form_tags:
        print(f"  Free-form examples: {free_form_tags[:5]}")

    for a in all_annotated[:5]:
        tts_text = _compose_tts_text(a)
        print(f"\n  seg {a.seg_index}:")
        print(f"    prosody_tags: {a.prosody_tags}")
        print(f"    annotated:    {a.annotated_text[:80]}...")
        print(f"    tts_text:     {tts_text[:80]}...")

    print(f"\nSaved: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
