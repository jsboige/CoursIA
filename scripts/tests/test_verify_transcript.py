"""Tests for scripts/tts_verification/verify_transcript.py — stage-1 WER/CER gate.

Locks the text normalization and the WER/CER math, which are pure logic (no audio,
no Whisper call) and therefore CI-testable. The network-facing function
``transcribe_audio`` is intentionally NOT exercised: it needs the local whisper-api
service, covered by the manual run on the #1028 review material.

Regression under test (hand-verified on audiobook #1028):
* Long dashes (``--``, ``—``, ``–``) and hyphen-joined compounds must split into
  separate tokens, not fuse. Previously ``-`` was kept in the allowed-character set,
  so ``Défaite--les Citoyens`` became one token ``défaite--les`` while Whisper
  transcribes ``défaite les`` -> the segment was counted as 17.24% WER despite a
  32/32 word match (false failure on French dialog text).
"""

import sys
from pathlib import Path

# Same sibling convention as test_verify_prosody.py: insert the tool dir and import
# the module directly.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tts_verification"))

from verify_transcript import (  # noqa: E402
    _normalize_text,
    compute_cer,
    compute_wer,
)


# --- _normalize_text: dash separation ----------------------------------------


def test_normalize_keeps_french_diacritics():
    assert _normalize_text("Héroïque garçon Noël") == "héroïque garçon noël"


def test_normalize_double_hyphen_splits_tokens():
    # The #1028 regression: "--" must separate, not fuse.
    assert _normalize_text("Défaite--les Citoyens") == "défaite les citoyens"


def test_normalize_em_dash_splits_tokens():
    assert _normalize_text("Mort»—passaient") == "mort passaient"


def test_normalize_en_dash_splits_tokens():
    assert _normalize_text("Mort – passaient") == "mort passaient"


def test_normalize_hyphen_compound_splits_tokens():
    # Whisper transcribes "francs-tireurs" as "francs tireurs"; the reference must
    # split the same way or the compound is counted as a substitution.
    assert _normalize_text("francs-tireurs") == "francs tireurs"


def test_normalize_strips_punctuation():
    assert _normalize_text("«Vengeurs!»...") == "vengeurs"


def test_normalize_collapses_whitespace():
    assert _normalize_text("a   b\t\nc") == "a b c"


# --- WER / CER math ----------------------------------------------------------


def test_wer_identical_is_zero():
    assert compute_wer("le chat dort", "le chat dort") == 0.0


def test_wer_real_substitution_is_nonzero():
    assert compute_wer("le chat dort", "le chien dort") > 0.0


def test_cer_identical_is_zero():
    assert compute_cer("le chat dort", "le chat dort") == 0.0


def test_wer_empty_reference_no_hypothesis_is_zero():
    assert compute_wer("", "") == 0.0


def test_wer_empty_reference_with_hypothesis_is_one():
    assert compute_wer("", "abc") == 1.0


def test_regression_audiobook_narrateur_dash_dialog_zero_wer():
    """#1028 narrateur segment: reference has long-dash dialog markup, Whisper drops
    the dashes. After the normalize fix this must be 0% WER, not ~17%."""
    reference = (
        "Des légions de francs-tireurs aux appellations héroïques: «les Vengeurs "
        "de la Défaite--les Citoyens de la Tombe--les Partageurs de la "
        "Mort»--passaient à leur tour, avec des airs de bandits."
    )
    hypothesis = (
        "des légions de francs-tireurs aux appellations héroïques les vengeurs de "
        "la défaite les citoyens de la tombe les partageurs de la mort passaient à "
        "leur tour avec des airs de bandits"
    )
    assert compute_wer(reference, hypothesis) == 0.0
