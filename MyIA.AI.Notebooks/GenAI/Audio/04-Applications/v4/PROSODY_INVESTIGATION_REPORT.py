"""FishAudio S2-Pro Prosody Investigation Report.

Branch: feature/1273-prosody-tags-only
Date: 2026-05-26
Context: Epic #1273 audiobook pipeline, ai-01 dispatched 5-step protocol

Findings
========

1. FishAudio S2-Pro CAN vary F0 mean (pitch average).
   Unit tests showed 95.9 Hz F0 range across 12 test conditions:
   - [angry]: +50 Hz F0
   - temperature=0.3: -46 Hz F0
   - [whispering]: RMS -60%
   - [sad]: duration +37%

2. FishAudio S2-Pro CANNOT vary the melodic contour (prosody shape).
   Melody similarity analysis (z-score normalized DTW on F0 trajectories):
   - OLD pipeline diversity: 1.343 (cross-pair distance)
   - NEW (angry/sad tags + temp variation) diversity: 1.224
   - Ratio: 0.91x — NO improvement, slightly LESS diverse
   The cloned voice has a fixed intrinsic prosody that tags/temperature
   do not override at the melodic level.

3. Root cause of monotone audiobook output:
   - _NON_OFFICIAL_TAG_MAP routes emotion tags to pacing tags:
     firmly->emphasis, mockingly->emphasis, cold->low_voice
   - These pacing tags produce no melodic change
   - Temperature hardcoded at 0.7 for all segments
   - Even with emotion tags (angry, sad, excited) + variable temperature,
     the melodic contour remains identical

4. Qwen3-TTS is NOT viable as fallback:
   - 1.7B params, fits RTX 3090, French supported
   - BUT voice cloning + prosody control simultaneously is BROKEN
   - GitHub Discussion #218 confirms the issue

Test Scripts
============
- test_prosody_fix_v3.py: Final test with melody contour analysis (6 pairs)
- wer_validate_post_fix.py: WER validation tool (used for #1486)
- _legacy/: 7 archived intermediate test scripts

Recommendations
===============
1. Re-clone the narrator voice with more expressive samples (varied prosody)
2. Use multiple cloned voices (one per emotional register)
3. Explore TTS models with explicit melodic control (Piper, VITS+SSML)
4. Accept current prosody and focus on other quality improvements
"""
