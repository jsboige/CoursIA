"""Omission control of p7, phase 1 (#19692) — offline tests.

Covers _missing_word_spans: the trigram alignment that counts >=3-word
passages missing from an ASR hypothesis. Method measured on the A0C bench
(#17586 c.6035598289): the unchunked CosyVoice3 render dropped whole
sentences that the mean WER (~0.12) could not see.

Run from the v4 directory:
    python -m pytest tests/test_p7_omission_control.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _spans(source: str, hyp: str) -> list[dict]:
    from v4.p7_verify import _missing_word_spans

    return _missing_word_spans(source, hyp)


def test_no_span_when_hypothesis_matches():
    """A faithful hypothesis yields zero spans — the control must not cry
    wolf on a clean render."""
    from v4.p7_verify import _missing_word_spans

    source = "Les voyageurs se regardaient avec une certaine honte."
    assert _missing_word_spans(source, source) == []
    assert _missing_word_spans(source, source.upper()) == []
    assert _missing_word_spans(source, source.replace("!", ".") + "!") == []


def test_detects_dropped_sentence():
    """The founding case: a whole sentence absent from the hypothesis must
    be reported as one span covering its words."""
    from v4.p7_verify import _missing_word_spans

    source = (
        "Des artilleurs sombres alignés avec des fantassins divers. "
        "Tous semblaient accablés et éreintés."
    )
    hyp = "Tous semblaient accablés et éreintés."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 1
    assert "artilleurs" in spans[0]["words"]
    assert spans[0]["end"] - spans[0]["start"] >= 6  # the 7-word sentence


def test_single_word_substitution_produces_halo_span():
    """Known primitive behavior: a substituted word breaks every trigram it
    touches, so ONE bad word yields a ~5-word halo span. This is why p7
    votes across three ASRs (_voted_missing_spans) instead of trusting one
    hypothesis — the test pins the halo so the vote's job stays visible."""
    from v4.p7_verify import _missing_word_spans

    source = "Il marchait doucement vers la grande maison blanche."
    hyp = "Il marchait vite vers la grande maison blanche."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 1
    assert "doucement" in spans[0]["words"]


def test_vote_filters_single_asr_noise():
    """A halo present under ONE model only is not an omission: the passage
    is spoken, one ASR misheard it. The 2-of-3 vote drops it (the measured
    behavior of the A0C bench, #17586)."""
    from v4.p7_verify import _voted_missing_spans

    source = "Il marchait doucement vers la grande maison blanche du notaire."
    spoken = source  # the render spoke it all
    misheard = "Il marchait vite vers la grande maison blanche du notaire."
    spans_by_model = {
        "tiny": _spans(source, misheard),
        "large-v3": _spans(source, spoken),
        "large-v3-turbo": _spans(source, spoken),
    }
    assert _voted_missing_spans(spans_by_model) == []


def test_vote_keeps_real_omission():
    """A passage missing under two models is a real omission, with its
    supporting models recorded."""
    from v4.p7_verify import _voted_missing_spans

    source = (
        "Des artilleurs sombres alignés avec des fantassins divers. "
        "Tous semblaient accablés et éreintés."
    )
    full = source
    dropped = "Tous semblaient accablés et éreintés."
    spans_by_model = {
        "tiny": _spans(source, dropped),
        "large-v3": _spans(source, dropped),
        "large-v3-turbo": _spans(source, full),
    }
    voted = _voted_missing_spans(spans_by_model)
    assert len(voted) == 1
    assert "artilleurs" in voted[0]["words"]
    assert voted[0]["absent_sous"] == ["large-v3", "tiny"]


def test_vote_clusters_shifted_halos():
    """Halos shift by a word or two between models: spans overlapping by
    >=3 words support the same omission even with different boundaries."""
    from v4.p7_verify import _voted_missing_spans

    spans_by_model = {
        "tiny": [{"start": 10, "end": 17, "words": "a b c d e f g"}],
        "large-v3": [{"start": 11, "end": 18, "words": "b c d e f g h"}],
    }
    voted = _voted_missing_spans(spans_by_model)
    assert len(voted) == 1
    assert voted[0]["absent_sous"] == ["large-v3", "tiny"]


def test_normalization_ignores_case_and_punctuation():
    """The alignment normalizes case/punctuation: cosmetic ASR differences
    are not omissions."""
    from v4.p7_verify import _missing_word_spans

    source = "Elle répondit: « Non, jamais. »"
    hyp = "elle répondit non jamais"
    assert _missing_word_spans(source, hyp) == []


def test_inflection_drift_is_known_false_positive():
    """Documented limitation: an inflection drift ('Tout semblait accablé'
    vs 'Tous semblaient accablés') breaks every trigram it touches and can
    flag a spoken passage. The test pins the behavior so a future change to
    the method (stemming?) is a deliberate one."""
    from v4.p7_verify import _missing_word_spans

    source = "Tous semblaient accablés, éreintés, incapables."
    hyp = "Tout semblait accablé, éreinté, incapable."
    spans = _missing_word_spans(source, hyp)
    # Flagged today (inflection breaks the trigrams) — known false positive.
    assert spans, "inflection drift is flagged by the current method"


def test_empty_or_tiny_reference():
    """References under min_words cannot produce a >=3-word span."""
    from v4.p7_verify import _missing_word_spans

    assert _missing_word_spans("Deux mots", "autre chose") == []
    assert _missing_word_spans("", "hypothèse") == []


def test_multiple_spans_reported_separately():
    """Two disjoint dropped passages yield two spans, not one merged."""
    from v4.p7_verify import _missing_word_spans

    source = (
        "Première phrase complète à garder. Deuxième phrase qui disparaît "
        "entièrement du rendu. Troisième phrase conservée aussi. Quatrième "
        "passage perdu dans l'audio final."
    )
    hyp = "Première phrase complète à garder. Troisième phrase conservée aussi."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 2
    # Words are normalized (lowercase) — the halo pulls 2 words before each
    # dropped passage, so assert on containment, not boundaries.
    assert "deuxième" in spans[0]["words"]
    assert "quatrième" in spans[1]["words"]
