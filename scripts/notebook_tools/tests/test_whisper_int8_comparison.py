"""Tests for scripts/whisper_int8_comparison.py — Whisper comparison helpers."""

import importlib.util
import os
from pathlib import Path

import pytest

# Set required env vars BEFORE importing the module (it raises EnvironmentError at import)
os.environ.setdefault("TTS_API_KEY", "test-key-for-unit-tests")
os.environ.setdefault("WHISPER_API_KEY", "test-key-for-unit-tests")

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent
    / "scripts"
    / "whisper_int8_comparison.py"
)
_spec = importlib.util.spec_from_file_location("whisper_int8_comparison", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

normalize = _mod.normalize
word_accuracy = _mod.word_accuracy
print_summary = _mod.print_summary


# --- normalize ---


class TestNormalize:
    def test_basic(self):
        assert normalize("Hello, World!") == "hello world"

    def test_french_punctuation(self):
        # Hyphens NOT stripped; space before ? preserved after .replace("?","")
        assert normalize("Bonjour, comment allez-vous ?") == "bonjour comment allez-vous "

    def test_strips_comma(self):
        assert normalize("a, b, c") == "a b c"

    def test_strips_question_mark(self):
        assert normalize("really?") == "really"

    def test_strips_period(self):
        assert normalize("fin.") == "fin"

    def test_strips_exclamation(self):
        assert normalize("wow!") == "wow"

    def test_lowercases(self):
        assert normalize("UPPERCASE") == "uppercase"

    def test_strips_leading_trailing(self):
        assert normalize("  hello  ") == "hello"

    def test_empty_string(self):
        assert normalize("") == ""

    def test_only_punctuation(self):
        assert normalize(",,??..!!") == ""


# --- word_accuracy ---


class TestWordAccuracy:
    def test_perfect_match(self):
        assert word_accuracy("hello world", "hello world") == 1.0

    def test_partial_match(self):
        # "hello" is in hypothesis, "world" is not
        acc = word_accuracy("hello world", "hello there")
        assert acc == 0.5

    def test_no_match(self):
        assert word_accuracy("alpha beta", "gamma delta") == 0.0

    def test_empty_reference_returns_one(self):
        """Edge case: empty reference = 100% accuracy."""
        assert word_accuracy("", "anything") == 1.0

    def test_empty_hypothesis(self):
        assert word_accuracy("hello world", "") == 0.0

    def test_both_empty(self):
        assert word_accuracy("", "") == 1.0

    def test_case_insensitive(self):
        assert word_accuracy("Hello World", "hello world") == 1.0

    def test_punctuation_ignored(self):
        assert word_accuracy("Hello, world!", "hello world") == 1.0

    def test_subset_match(self):
        """All reference words present in hypothesis = 1.0."""
        assert word_accuracy("bonjour", "bonjour comment allez-vous") == 1.0

    def test_repeated_words(self):
        """Each reference word counted once if present."""
        acc = word_accuracy("the the the", "the cat sat")
        assert acc == 1.0  # "the" is present in hypothesis


# --- print_summary ---


class TestPrintSummary:
    def test_empty_results(self, capsys):
        avg = print_summary("Test", [])
        assert avg == 0.0

    def test_all_perfect(self, capsys):
        results = [{"accuracy": 1.0}, {"accuracy": 1.0}]
        avg = print_summary("Test", results)
        assert avg == 1.0
        captured = capsys.readouterr()
        assert "avg accuracy=100.0%" in captured.out

    def test_mixed_accuracy(self, capsys):
        results = [{"accuracy": 0.8}, {"accuracy": 0.6}]
        avg = print_summary("Test", results)
        assert avg == pytest.approx(0.7)

    def test_ok_count(self, capsys):
        results = [{"accuracy": 0.9}, {"accuracy": 0.7}, {"accuracy": 0.5}]
        print_summary("Test", results)
        captured = capsys.readouterr()
        # 0.8 threshold: 0.9 >= 0.8 (OK), 0.7 < 0.8, 0.5 < 0.8 → 1/3 OK
        assert "1/3 phrases OK" in captured.out

    def test_missing_accuracy_treated_as_zero(self):
        results = [{"no_accuracy": True}]
        avg = print_summary("Test", results)
        assert avg == 0.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
