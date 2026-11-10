"""Omission control of p7 (#19692) — offline tests.

Covers _missing_word_spans (word alignment via difflib) and
_voted_missing_spans (2-of-3 ASR vote with merge of overlapping voted
spans). The primitive replaced the phase-1 trigram shingles, which
over-flagged: one substituted word broke every trigram it touched and
produced a ~5-word halo (Zonos chunked measured 11 spans by trigrams vs 0
by alignment, #19695 c.6115711862).

Run from the v4 directory:
    python -m pytest tests/test_p7_omission_control.py -v
"""
from __future__ import annotations

import json
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
    be reported as one span covering its words, with exact boundaries."""
    from v4.p7_verify import _missing_word_spans

    source = (
        "Des artilleurs sombres alignés avec des fantassins divers. "
        "Tous semblaient accablés et éreintés."
    )
    hyp = "Tous semblaient accablés et éreintés."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 1
    assert "artilleurs" in spans[0]["words"]
    # Exact boundaries: the 8 dropped words, no halo.
    assert spans[0]["start"] == 0
    assert spans[0]["end"] - spans[0]["start"] == 8


def test_single_word_substitution_produces_no_span():
    """The gain of the alignment over the phase-1 trigram primitive: a
    substituted word is a `replace` run of equal length — no reference
    excess, no span. The trigram method flagged a ~5-word halo here; the
    alignment does not (#19695 c.6115711862)."""
    from v4.p7_verify import _missing_word_spans

    source = "Il marchait doucement vers la grande maison blanche."
    hyp = "Il marchait vite vers la grande maison blanche."
    assert _missing_word_spans(source, hyp) == []


def test_vote_filters_single_asr_noise():
    """A passage dropped under ONE model only is not an omission: the render
    spoke it, one ASR lost it. The 2-of-3 vote drops it (the measured
    behavior of the A0C bench, #17586)."""
    from v4.p7_verify import _voted_missing_spans

    source = (
        "Il marchait doucement vers la grande maison blanche du notaire. "
        "Le jardin était entretenu avec un soin meticuleux."
    )
    spoken = source  # the render spoke it all
    lost_by_one = "Il marchait doucement vers la grande maison blanche du notaire."
    spans_by_model = {
        "tiny": _spans(source, lost_by_one),  # drops the 5-word last sentence
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


def test_vote_clusters_shifted_boundaries():
    """Alignment boundaries shift by a word or two between models: spans
    overlapping by >=3 words support the same omission even with different
    boundaries."""
    from v4.p7_verify import _voted_missing_spans

    spans_by_model = {
        "tiny": [{"start": 10, "end": 17, "words": "a b c d e f g"}],
        "large-v3": [{"start": 11, "end": 18, "words": "b c d e f g h"}],
    }
    voted = _voted_missing_spans(spans_by_model)
    assert len(voted) == 1
    assert voted[0]["absent_sous"] == ["large-v3", "tiny"]


def test_vote_merges_overlapping_voted_spans():
    """One long drop can align differently under each ASR and land in
    neighbouring clusters: overlapping VOTED spans are one omission, merged
    into the wider of the two with the union of supporting models (the
    reference method of #19695 c.6115711862 — Zonos truncated counts 5,
    not 7). Here "a" and "c" vote one cluster, "b" and "c" a neighbouring
    one; the members overlap by <3 words (distinct clusters) but the voted
    spans overlap by 2."""
    from v4.p7_verify import _voted_missing_spans

    spans_by_model = {
        "a": [{"start": 10, "end": 30, "words": "w" * 20}],
        "b": [{"start": 28, "end": 50, "words": "w" * 22}],
        "c": [
            {"start": 10, "end": 30, "words": "w" * 20},
            {"start": 28, "end": 50, "words": "w" * 22},
        ],
    }
    voted = _voted_missing_spans(spans_by_model)
    assert len(voted) == 1
    # The wider of the two overlapping voted spans is kept...
    assert (voted[0]["start"], voted[0]["end"]) == (28, 50)
    # ...with the union of the supporting models.
    assert voted[0]["absent_sous"] == ["a", "b", "c"]


def test_normalization_ignores_case_and_punctuation():
    """The alignment normalizes case/punctuation: cosmetic ASR differences
    are not omissions."""
    from v4.p7_verify import _missing_word_spans

    source = "Elle répondit: « Non, jamais. »"
    hyp = "elle répondit non jamais"
    assert _missing_word_spans(source, hyp) == []


def test_inflection_drift_is_not_flagged():
    """An inflection drift ('Tout semblait accablé' vs 'Tous semblaient
    accablés') is a word-for-word replace run — no reference excess, no
    span. The phase-1 trigram primitive flagged this as a known false
    positive; the alignment closed it (#19692)."""
    from v4.p7_verify import _missing_word_spans

    source = "Tous semblaient accablés, éreintés, incapables."
    hyp = "Tout semblait accablé, éreinté, incapable."
    assert _missing_word_spans(source, hyp) == []


def test_replace_with_reference_excess_counts_once():
    """A passage spoken with words dropped AND substituted is a replace run:
    it counts only when the reference side exceeds the hypothesis side by
    >=3 words (5 vs 1 here)."""
    from v4.p7_verify import _missing_word_spans

    source = "Des artilleurs sombres alignés avec des fantassins divers."
    hyp = "Des fantassins divers."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 1
    assert spans[0]["end"] - spans[0]["start"] >= 3


def test_empty_or_tiny_reference():
    """References under min_words cannot produce a >=3-word span."""
    from v4.p7_verify import _missing_word_spans

    assert _missing_word_spans("Deux mots", "autre chose") == []
    assert _missing_word_spans("", "hypothèse") == []


def test_multiple_spans_reported_separately():
    """Two disjoint dropped passages yield two spans, not one merged — with
    exact boundaries (no halo)."""
    from v4.p7_verify import _missing_word_spans

    source = (
        "Première phrase complète à garder. Deuxième phrase qui disparaît "
        "entièrement du rendu. Troisième phrase conservée aussi. Quatrième "
        "passage perdu dans l'audio final."
    )
    hyp = "Première phrase complète à garder. Troisième phrase conservée aussi."
    spans = _missing_word_spans(source, hyp)
    assert len(spans) == 2
    assert "deuxième" in spans[0]["words"]
    assert "quatrième" in spans[1]["words"]
    # Exact boundaries: no halo words pulled from the spoken sentences.
    assert "première" not in spans[0]["words"]
    assert "troisième" not in spans[0]["words"]
    assert "troisième" not in spans[1]["words"]


def test_a0c_reference_controls_reproduced_exactly():
    """The hermetic A0C ground truth (#19695 c.6115711862): the four
    positive controls the primitive + vote must reproduce exactly. The
    trigram primitive failed the third (11 spans on Zonos chunked, expected
    0) — this test pins the alignment to the measured counts.

    Text: Boule de Suif (Maupassant, 1880) — public domain; hypotheses are
    the three ASR transcripts of the bench (tiny / large-v3 / large-v3-turbo).
    """
    from v4.p7_verify import _voted_missing_spans

    fixture = json.loads(
        (
            Path(__file__).resolve().parent / "fixtures" / "a0c_controls.json"
        ).read_text(encoding="utf-8")
    )
    reference = fixture["reference"]
    expected_counts = {
        "A0C-cosyvoice3": 2,
        "A0C-zonos": 5,
        "A0C-zonos-chunked": 0,
        "A0C-cosyvoice3-chunked": 2,
    }
    for name, expected in expected_counts.items():
        spans_by_model = {
            model: _spans(reference, hyp)
            for model, hyp in fixture["renders"][name].items()
        }
        voted = _voted_missing_spans(spans_by_model)
        assert len(voted) == expected, (
            f"{name}: {len(voted)} voted spans, expected {expected}"
        )

    # Zonos truncated: the 5 voted spans cover 248 reference words — the
    # sentence drops the mean WER (~0.13) could not see.
    spans_by_model = {
        model: _spans(reference, hyp)
        for model, hyp in fixture["renders"]["A0C-zonos"].items()
    }
    voted = _voted_missing_spans(spans_by_model)
    n_words = sum(s["end"] - s["start"] for s in voted)
    assert n_words == 248

    # CV3 unchunked: both omissions are 3/3-ASR confirmed.
    spans_by_model = {
        model: _spans(reference, hyp)
        for model, hyp in fixture["renders"]["A0C-cosyvoice3"].items()
    }
    voted = _voted_missing_spans(spans_by_model)
    assert all(len(s["absent_sous"]) == 3 for s in voted)
