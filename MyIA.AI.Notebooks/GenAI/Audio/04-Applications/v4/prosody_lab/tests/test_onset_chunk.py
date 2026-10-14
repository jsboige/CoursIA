"""test_onset_chunk.py -- couverture de corpus_damage_chunk.

Issue #19739 phase 2 : classifier onset/mid/end/spread des spans d'omission
sur les artefacts phase 1 (PR #19699 MERGEDe, organe p7).

Tests :
1. test_normalize_for_length : compte mots normalises (meme conv. p7).
2. test_classify_span_onset : span demarrant au mot 0 -> onset_drop.
3. test_classify_span_end : span finissant au dernier mot -> end_drop.
4. test_classify_span_mid : span entre les deux -> mid_omission.
5. test_classify_span_spread : span couvrant >= 80% du segment -> spread.
6. test_classify_span_too_short : span < 3 mots -> none.
7. test_classify_seg_too_short : seg < 3 mots -> none (invariant p7).
8. test_classify_records_majority : verdict par record = majorite.
9. test_classify_records_mixed_spread_dominates : spread > onset > end > mid.
10. test_classify_records_unclassified : seg_index absent -> unclassified.
11. test_classify_records_onset_segment_listed : onset_segments rempli.
12. test_build_seg_word_count_map_missing_file : fichier absent -> {}.
13. test_build_seg_word_count_map_parses_annotated : parsing JSON standard.
14. test_main_no_omission_report : exit 2 si omission-report absent.
15. test_smoke_run_end_to_end : run avec fixtures + sortie JSON structuree.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

# Permet l'import quand pytest est lance depuis la racine du worktree.
THIS_DIR = Path(__file__).resolve().parent
PROSODY_LAB = THIS_DIR.parent
sys.path.insert(0, str(PROSODY_LAB))

from corpus_damage_chunk import (  # noqa: E402
    ONSET_DROP,
    MID_OMISSION,
    END_DROP,
    SPREAD,
    NONE,
    classify_span_position,
    classify_records,
    build_seg_word_count_map,
    _normalize_for_length,
)


# ---------- 1. normalize_for_length ----------

def test_normalize_for_length() -> None:
    """Compte de mots normalises -- meme convention que p7."""
    # Normalise : NFC, lowercase, non-alnum -> espace, collapse whitespace.
    assert _normalize_for_length("Bonjour, monde !") == 2
    assert _normalize_for_length("L'été était accablé") == 4
    assert _normalize_for_length("  espaces   en trop  ") == 3
    assert _normalize_for_length("") == 0
    # Les chiffres comptent comme alnum, donc comme mots.
    assert _normalize_for_length("il etait 3 fois") == 4


# ---------- 2-7. classify_span_position ----------

def test_classify_span_onset() -> None:
    """Span demarrant au mot 0 -> onset_drop."""
    # "Quand la diligence" (4 mots), premiere triplette omise.
    assert classify_span_position(0, 3, seg_word_count=10) == ONSET_DROP


def test_classify_span_end() -> None:
    """Span finissant au dernier mot -> end_drop."""
    assert classify_span_position(7, 10, seg_word_count=10) == END_DROP


def test_classify_span_mid() -> None:
    """Span entre les deux -> mid_omission."""
    assert classify_span_position(3, 6, seg_word_count=10) == MID_OMISSION


def test_classify_span_spread() -> None:
    """Span couvrant >= 80% du segment -> spread (catastrophe).

    Convention de hierarchie : SPREAD (>=80%) prime sur ONSET_DROP (start=0)
    et END_DROP (end=seg_len). Un span (0, 7) sur 10 mots est onset_drop
    (70% < 80% mais start=0) -- c'est l'ordre des priorites qui tranche.
    """
    # 8 mots sur 10 = 80 % pile -> spread (categorie la plus haute).
    assert classify_span_position(0, 8, seg_word_count=10) == SPREAD
    # 9 mots sur 10 = 90 % -> spread.
    assert classify_span_position(0, 9, seg_word_count=10) == SPREAD
    # 7 mots sur 10 = 70 % -> onset_drop (start=0 et 70 < 80).
    assert classify_span_position(0, 7, seg_word_count=10) == ONSET_DROP


def test_classify_span_too_short() -> None:
    """Span < 3 mots -> none (invariant p7 min_words=3)."""
    # (2, 5) = 3 mots : OK -> mid_omission.
    assert classify_span_position(2, 5, seg_word_count=10) == MID_OMISSION
    # (2, 4) = 2 mots : trop court -> none.
    assert classify_span_position(2, 4, seg_word_count=10) == NONE
    # (2, 3) = 1 mot : trop court -> none.
    assert classify_span_position(2, 3, seg_word_count=10) == NONE
    # (0, 2) = 2 mots au debut : trop court -> none (pas onset_drop).
    assert classify_span_position(0, 2, seg_word_count=10) == NONE


def test_classify_seg_too_short() -> None:
    """Segment < 3 mots -> none (invariant p7 min_words=3)."""
    assert classify_span_position(0, 3, seg_word_count=2) == NONE
    assert classify_span_position(0, 5, seg_word_count=1) == NONE


def test_classify_span_empty_range() -> None:
    """Span vide (end <= start) -> none."""
    assert classify_span_position(5, 5, seg_word_count=10) == NONE
    assert classify_span_position(7, 3, seg_word_count=10) == NONE


# ---------- 8-11. classify_records ----------

def test_classify_records_majority() -> None:
    """Le verdict par record suit la hierarchie spread > onset > end > mid."""
    records = [
        {
            "seg_index": 10,
            "speaker": "narrator",
            "spans": [
                {"start": 0, "end": 3, "words": "premier triplette omise"},
            ],
        },
    ]
    seg_len_map = {"10": 10}
    report = classify_records(records, seg_len_map)
    assert report["counts"][ONSET_DROP] == 1
    assert report["counts"][MID_OMISSION] == 0
    assert len(report["onset_segments"]) == 1
    assert report["onset_segments"][0]["verdict"] == ONSET_DROP


def test_classify_records_mixed_spread_dominates() -> None:
    """Un spread parmi les spans impose le verdict spread du record."""
    records = [
        {
            "seg_index": 50,
            "speaker": "narrator",
            # Spread 0..8 (8 mots sur 10 = 80 %) + un mid 4..7 (3 mots).
            "spans": [
                {"start": 0, "end": 8, "words": "le segment presque entier"},
                {"start": 4, "end": 7, "words": "milieu"},
            ],
        },
    ]
    seg_len_map = {"50": 10}
    report = classify_records(records, seg_len_map)
    assert report["counts"][SPREAD] == 1
    assert report["counts"][MID_OMISSION] == 1
    assert len(report["spread_segments"]) == 1
    assert len(report["onset_segments"]) == 0


def test_classify_records_unclassified() -> None:
    """seg_index absent ou seg_len inconnu -> unclassified."""
    records = [
        {
            "seg_index": 999,  # pas dans seg_len_map
            "speaker": "narrator",
            "spans": [{"start": 0, "end": 3, "words": "test"}],
        },
        {
            # seg_index absent
            "speaker": "narrator",
            "spans": [{"start": 0, "end": 3, "words": "test"}],
        },
        {
            "seg_index": 1,
            "speaker": "narrator",
            # spans vide
            "spans": [],
        },
    ]
    seg_len_map = {"1": 10}  # 999 absent
    report = classify_records(records, seg_len_map)
    assert report["n_records"] == 3
    # 999 absent de seg_len_map -> unclassified, donc n_classified == 0.
    # Le 1er record (seg_index absent) et le 3eme (spans vide) sont
    # aussi unclassified par construction.
    assert report["n_classified"] == 0
    assert len(report["unclassified"]) == 3


def test_classify_records_onset_segment_listed() -> None:
    """onset_segments rempli avec first_span_words pour lecture humaine."""
    records = [
        {
            "seg_index": 57,  # exemple documente dans PR #19699
            "speaker": "narrator",
            "spans": [
                {"start": 0, "end": 3, "words": "chacun guettait l'arrivee"},
            ],
        },
    ]
    seg_len_map = {"57": 12}
    report = classify_records(records, seg_len_map)
    assert len(report["onset_segments"]) == 1
    seg = report["onset_segments"][0]
    assert seg["seg_index"] == 57
    assert seg["speaker"] == "narrator"
    assert seg["first_span_words"] == "chacun guettait l'arrivee"
    assert seg["verdict"] == ONSET_DROP


# ---------- 12-13. build_seg_word_count_map ----------

def test_build_seg_word_count_map_missing_file(tmp_path: Path) -> None:
    """Fichier absent -> dict vide, classification degradee."""
    missing = tmp_path / "nope.json"
    assert build_seg_word_count_map(missing) == {}


def test_build_seg_word_count_map_parses_annotated(tmp_path: Path) -> None:
    """Parsing standard d'un annotated_v4.json minimaliste.

    Convention : non-alnum -> espace, donc "Bouledesuif" reste un seul
    mot normalise (les separateurs typographiques sont le seul separateur).
    """
    annotated = tmp_path / "annotated.json"
    annotated.write_text(
        json.dumps(
            {
                "segments": [
                    {"seg_index": 0, "text": "Quand la diligence parut"},
                    {"seg_index": 1, "text": "Boule de suif rougit"},
                    {"seg_index": 5, "text": ""},  # vide -> 0 mots
                ]
            }
        ),
        encoding="utf-8",
    )
    m = build_seg_word_count_map(annotated)
    assert m["0"] == 4
    assert m["1"] == 4
    assert m["5"] == 0


# ---------- 14. main() exit codes ----------

def test_main_no_omission_report(tmp_path: Path, capsys) -> None:
    """omission-report absent -> exit 2."""
    # Importer seulement quand pytest est actif (lazy import de main).
    import corpus_damage_chunk as cdc

    rc = cdc.main.__wrapped__() if hasattr(cdc.main, "__wrapped__") else None
    # Pas de wrapper ; on invoque via argparse direct.
    import argparse

    parser = cdc.main.__globals__["p"] if False else None
    # Le plus simple : invoquer main() avec sys.argv, capturer SystemExit.
    import sys

    old_argv = sys.argv
    sys.argv = [
        "corpus_damage_chunk.py",
        "--omission-report",
        str(tmp_path / "missing.json"),
        "--annotated",
        str(tmp_path / "missing.json"),
    ]
    try:
        rc = cdc.main()
    except SystemExit as e:
        rc = e.code
    finally:
        sys.argv = old_argv
    assert rc == 2


# ---------- 15. smoke run end-to-end ----------

def test_smoke_run_end_to_end(tmp_path: Path, capsys) -> None:
    """Run complet avec artefacts en fichiers, sortie structuree."""
    annotated = tmp_path / "annotated.json"
    annotated.write_text(
        json.dumps(
            {
                "segments": [
                    {"seg_index": 10, "text": "Quand la diligence parut au loin"},
                    {"seg_index": 11, "text": "Le segment entier est reste muet"},
                    {"seg_index": 12, "text": "Phrase complete sans omission"},
                ],
            }
        ),
        encoding="utf-8",
    )
    omission = tmp_path / "omission.json"
    omission.write_text(
        json.dumps(
            {
                "records": [
                    {
                        "seg_index": 10,
                        "speaker": "narrator",
                        "spans": [
                            {"start": 0, "end": 3, "words": "quand la diligence"}
                        ],
                    },
                    {
                        "seg_index": 11,
                        "speaker": "narrator",
                        "spans": [
                            {"start": 0, "end": 6, "words": "le segment entier"}
                        ],
                    },
                ]
            }
        ),
        encoding="utf-8",
    )
    out = tmp_path / "out.json"

    import corpus_damage_chunk as cdc
    import sys

    old_argv = sys.argv
    sys.argv = [
        "corpus_damage_chunk.py",
        "--omission-report",
        str(omission),
        "--annotated",
        str(annotated),
        "--out",
        str(out),
    ]
    try:
        rc = cdc.main()
    except SystemExit as e:
        rc = e.code
    finally:
        sys.argv = old_argv

    assert rc == 0
    assert out.exists()
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["n_records"] == 2
    assert payload["n_classified"] == 2
    assert payload["counts"][ONSET_DROP] == 1  # seg 10
    assert payload["counts"][SPREAD] == 1  # seg 11 (6/7 = 86%)
    assert len(payload["onset_segments"]) == 1
    assert payload["onset_segments"][0]["seg_index"] == 10
    assert len(payload["spread_segments"]) == 1
    assert payload["spread_segments"][0]["seg_index"] == 11