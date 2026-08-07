#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/strip_machine_paths.py.

strip_machine_paths.py is the canonical organ of rule-6 (secrets-hygiene.md
category-A, kernel-injected username leaks): it strips machine-username path
leaks from notebook outputs after a .NET / Python re-execution. It is run
fleet-wide on every re-exec (L532 probeAddresses strip), yet had **no test
suite** — a regression in its detection or redaction logic would silently
re-leak usernames into committed outputs across the whole cluster.

These tests pin the two contracts that must not regress:

1. **Detection (`_has_leak`)** — every one of the 8 runtime categories
   (nuget/pip/ipykernel/conda/hf/python/miniconda/windowsapps/other) is
   detected when it carries a username marker, and correctly **rejected**
   when it does not (tilde HOME placeholder, bare token, bare username).
2. **Redaction (`_redact_line`)** — the leaked prefix is replaced by
   ``<USER_PATH>`` while the trailing relative path (library / source-file /
   symbol — the pedagogical content) is preserved verbatim. Multi-occurrence
   lines, drive-letter prefixes, and double-backslash JSON-escaped paths are
   all handled.

Plus notebook-level integration (``count_leak_lines`` / ``find_leak_outputs``)
on a synthetic notebook and the ``--scan`` CLI.

Executable two ways::

    py scripts/tests/test_strip_machine_paths.py
    npx pytest scripts/tests/test_strip_machine_paths.py
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Import the module under test as a namespace object (NOT ``from ... import
# ACTIVE_CATEGORIES``): ACTIVE_CATEGORIES is a module global that tests must
# mutate in place to test the --category filter, and ``from`` rebinds the
# local namespace leaving the module global untouched (documented pitfall in
# the source, line ~196). All access goes through ``smp.<name>``.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
import strip_machine_paths as smp  # noqa: E402

SCRIPT = Path(smp.__file__).resolve()


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def _mk_notebook(tmp_path: Path, name: str, outputs_by_cell):
    """Build a minimal notebook with the given code-cell outputs.

    ``outputs_by_cell`` is a list; each entry is the ``outputs`` list of one
    code cell. Returns the path to the written .ipynb.
    """
    cells = []
    for outs in outputs_by_cell:
        cells.append({
            "cell_type": "code",
            "source": ["print('x')\n"],
            "metadata": {},
            "execution_count": 1,
            "outputs": outs,
        })
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _stream_out(text: str):
    """A stream (stderr/stdout) output whose ``text`` is a single string."""
    return {"output_type": "stream", "name": "stderr", "text": text}


def _display_out(plain: str):
    """A display_data output whose ``data['text/plain']`` is a list (nbformat
    convention: text/plain is a list of line-strings)."""
    return {
        "output_type": "display_data",
        "data": {"text/plain": [plain]},
        "metadata": {},
    }


# A real username as a kernel would inject it. Use a distinctive sentinel so
# a test failure pinpoints which assertion leaked it through.
USER = "boblebricoleur"

# One concrete leak sample per runtime category: (label, full_leaking_line).
# Each line carries BOTH the runtime cache token AND a ``Users\<USER>`` marker
# — the two conditions `_has_leak` requires. The trailing relative path after
# the cache token is the pedagogical content `_redact_line` must PRESERVE.
SAMPLES = [
    ("nuget",
     rf"Loading extensions from C:\Users\{USER}\.nuget\packages\microsoft.dotnet.interactive\1.0.0"),
    ("pip",
     rf"C:\Users\{USER}\AppData\Roaming\Python\Python313\site-packages\torch\__init__.py:410"),
    ("ipykernel",
     rf"C:\Users\{USER}\AppData\Local\Temp\ipykernel_12345\3456789.py:12: UserWarning"),
    ("conda",
     rf"C:\Users\{USER}\.conda\envs\mcp-jupyter-py310\lib\python3.10\site-packages\torch\nn\utils\weight_norm.py"),
    ("hf",
     rf"C:\Users\{USER}\.cache\huggingface\modules\transformers_modules\bert\modeling_bert.py"),
    ("python",
     rf"C:\Users\{USER}\AppData\Local\Programs\Python\Python313\python.exe -c pass"),
    ("miniconda",
     rf"C:\Users\{USER}\miniconda3\envs\ml\lib\python3.11\site-packages\numpy\__init__.py"),
    ("windowsapps",
     rf"C:\Users\{USER}\AppData\Local\Microsoft\WindowsApps\PythonSoftwareFoundation.Python.3.13_q\python.exe"),
    ("other",
     rf"Audio cree: C:\Users\{USER}\AppData\Local\Temp\test_audio.mp3"),
]


# ==========================================================================
# _normalize_bs
# ==========================================================================

class TestNormalizeBs:
    def test_collapses_doubled_backslashes(self):
        assert smp._normalize_bs(r"C:\\Users\\bob") == r"C:\Users\bob"

    def test_single_backslash_unchanged(self):
        assert smp._normalize_bs(r"C:\Users\bob") == r"C:\Users\bob"

    def test_no_backslash_unchanged(self):
        assert smp._normalize_bs("plain text") == "plain text"

    def test_non_str_passthrough(self):
        assert smp._normalize_bs(None) is None
        assert smp._normalize_bs(42) == 42


# ==========================================================================
# _has_leak — detection per category
# ==========================================================================

class TestHasLeakPositive:
    """Each runtime category, with a username marker, IS a leak."""

    @pytest.mark.parametrize("label,line", SAMPLES,
                             ids=[s[0] for s in SAMPLES])
    def test_detected(self, label, line):
        assert smp._has_leak(line) is True, f"category {label} not detected"

    # NOTE: Unix-style forward-slash paths (/Users/<u>/, /home/<u>/) are NOT
    # detected, although USERNAME_MARKERS lists them and the source comments
    # claim the HF token "is detected by the same token pair ... not
    # slash-strict". Firsthand (these tests): MACHINE_PATH_TOKENS are
    # backslash-only (".cache\\huggingface", ".conda\\envs"), so a forward-
    # slash Unix path carries no matching runtime token and `_has_leak`
    # returns False. This is benign on this Windows-only cluster (kernel-
    # injected paths are backslash), but the source comment is misleading.
    # Surfaced as a separate finding in the PR body — out of scope for this
    # test suite (which pins current behaviour, not aspirational claims).


class TestHasLeakNegative:
    """A line without a username marker is NOT a leak, even with a token."""

    def test_tilde_home_placeholder_not_leak(self):
        # The dotnet-interactive tilde variant (~\.nuget) is the HOME
        # placeholder — no username, so NOT a leak (must stay untouched).
        assert smp._has_leak(r"~\.nuget\packages\dotnet.interactive\1.0.0") is False

    def test_token_without_username_not_leak(self):
        # A bare cache token (no Users\<u>) is not a leak.
        assert smp._has_leak(r"Loading from .nuget\packages\foo") is False

    def test_username_without_token_not_leak(self):
        # A Users\ path with NO runtime cache token is not a category-A leak.
        assert smp._has_leak(r"C:\Users\bob\Desktop\notes.txt") is False

    def test_plain_text_not_leak(self):
        assert smp._has_leak("just some output with no paths") is False

    def test_empty_string_not_leak(self):
        assert smp._has_leak("") is False

    def test_non_str_not_leak(self):
        assert smp._has_leak(None) is False
        assert smp._has_leak(123) is False

    def test_idempotent_after_redaction(self):
        # A redacted line must be re-detected as NOT a leak — this is what
        # makes --apply-all idempotent (REDACTED_PATH carries no marker).
        for _label, line in SAMPLES:
            redacted = smp._redact_line(line)
            assert smp._has_leak(redacted) is False, (
                f"redacted line still detected as leak: {redacted!r}")


# ==========================================================================
# _redact_line — redaction contract
# ==========================================================================

class TestRedactLine:
    def test_replaces_username_prefix(self):
        line = rf"C:\Users\{USER}\.nuget\packages\foo\1.0.0\bar.dll"
        out = smp._redact_line(line)
        assert USER not in out
        assert smp.REDACTED_PATH in out

    def test_preserves_trailing_relative_path(self):
        # The pedagogical content (library path after the cache token) is kept.
        line = rf"C:\Users\{USER}\.nuget\packages\microsoft.dotnet.interactive\1.0.0\dllexport.dll"
        out = smp._redact_line(line)
        # The trailing relative path (from the cache token onward) survives.
        assert r"packages\microsoft.dotnet.interactive\1.0.0" in out or \
               r"microsoft.dotnet.interactive\1.0.0" in out, (
                   f"trailing pedagogical path lost in: {out!r}")
        assert USER not in out

    def test_preserves_filename_only_leaf(self):
        # Category "other": Audio cree: ...\Temp\test_audio.mp3 — the filename
        # is the leaf and must be preserved.
        line = rf"Audio cree: C:\Users\{USER}\AppData\Local\Temp\test_audio.mp3"
        out = smp._redact_line(line)
        assert "test_audio.mp3" in out
        assert USER not in out

    def test_drive_letter_prefix_consumed(self):
        # X:\Users\<u>\... → <USER_PATH>\... (drive letter dropped).
        line = rf"C:\Users\{USER}\.nuget\packages\foo"
        out = smp._redact_line(line)
        assert USER not in out
        # No orphaned drive letter before the placeholder.
        assert "C:\\" + smp.REDACTED_PATH not in out

    def test_multi_occurrence_scrubbed(self):
        # A single line carrying TWO username leaks (pip AppData + HF cache,
        # as in real HuggingFace UserWarnings) must scrub BOTH.
        line = (rf"C:\Users\{USER}\AppData\Roaming\Python\site-packages\peft "
                rf"loading C:\Users\{USER}\.cache\huggingface\modules\bert")
        out = smp._redact_line(line)
        assert out.count(USER) == 0, f"username remains: {out!r}"

    def test_double_backslash_normalized_then_redacted(self):
        # C538-L1: JSON re-serialization doubles backslashes. The doubled form
        # must still be detected AND redacted.
        line = rf"C:\\Users\\{USER}\\.nuget\\packages\\foo\\1.0.0\\bar.dll"
        out = smp._redact_line(line)
        assert USER not in out
        assert smp.REDACTED_PATH in out

    def test_non_str_passthrough(self):
        assert smp._redact_line(None) is None
        assert smp._redact_line(42) == 42


# ==========================================================================
# _first_matching_label — category attribution + priority order
# ==========================================================================

class TestFirstMatchingLabel:
    @pytest.mark.parametrize("label,line", SAMPLES,
                             ids=[s[0] for s in SAMPLES])
    def test_correct_label_per_category(self, label, line):
        assert smp._first_matching_label(line) == label

    def test_ipykernel_takes_priority_over_other(self):
        # An ipykernel temp path is ALSO a Temp path; ipykernel is more
        # specific and must be reported first (priority order in
        # MACHINE_PATH_TOKENS).
        line = rf"C:\Users\{USER}\AppData\Local\Temp\ipykernel_42\hash.py"
        assert smp._first_matching_label(line) == "ipykernel"

    def test_no_token_returns_empty(self):
        assert smp._first_matching_label("plain text no paths") == ""

    def test_double_bs_reports_correct_category(self):
        line = rf"C:\\Users\\{USER}\\.conda\\envs\\ml\\lib\\torch"
        assert smp._first_matching_label(line) == "conda"


# ==========================================================================
# _output_has_leak / _field_value — output-field wrappers
# ==========================================================================

class TestOutputHelpers:
    def test_output_has_leak_str(self):
        assert smp._output_has_leak(rf"C:\Users\{USER}\.nuget\packages\foo") is True

    def test_output_has_leak_list(self):
        text_list = ["first clean line\n", rf"C:\Users\{USER}\.nuget\packages\foo\n"]
        assert smp._output_has_leak(text_list) is True

    def test_output_has_leak_clean_list(self):
        assert smp._output_has_leak(["clean\n", "also clean\n"]) is False

    def test_output_has_leak_none(self):
        assert smp._output_has_leak(None) is False

    def test_field_value_data_key(self):
        out = {"data": {"text/plain": ["hello"]}}
        assert smp._field_value(out, "text/plain") == ["hello"]

    def test_field_value_stream_key(self):
        out = {"text": "stream text"}
        assert smp._field_value(out, "text") == "stream text"

    def test_field_value_data_key_missing(self):
        assert smp._field_value({"data": {}}, "text/plain") is None

    def test_field_value_unknown_key(self):
        assert smp._field_value({"data": {}}, "bogus") is None


# ==========================================================================
# Notebook-level: count_leak_lines / find_leak_outputs
# ==========================================================================

class TestNotebookLevel:
    def test_count_zero_on_clean_notebook(self, tmp_path):
        nb = _mk_notebook(tmp_path, "clean.ipynb", [
            [_stream_out("all good\n"), _display_out("result = 42")],
        ])
        assert smp.count_leak_lines(nb) == 0

    def test_count_one_leak_stream(self, tmp_path):
        nb = _mk_notebook(tmp_path, "leak.ipynb", [
            [_stream_out(rf"C:\Users\{USER}\.nuget\packages\foo\1.0.0\bar.dll\n")],
        ])
        assert smp.count_leak_lines(nb) == 1

    def test_count_multiple_distinct_leaks(self, tmp_path):
        nb = _mk_notebook(tmp_path, "multi.ipynb", [
            [_stream_out(rf"C:\Users\{USER}\.nuget\packages\foo\n"),
             _stream_out(rf"C:\Users\{USER}\AppData\Roaming\Python\site-packages\torch\n")],
        ])
        assert smp.count_leak_lines(nb) == 2

    def test_count_skips_markdown_cells(self, tmp_path):
        # count_leak_lines only scans code-cell outputs.
        nb_path = tmp_path / "md.ipynb"
        nb = {
            "cells": [
                {"cell_type": "markdown",
                 "source": [rf"some text C:\Users\{USER}\.nuget\packages\foo"]},
                {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
                 "execution_count": 1, "outputs": []},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        assert smp.count_leak_lines(nb_path) == 0

    def test_find_leak_outputs_locates_cell_output_field(self, tmp_path):
        nb = _mk_notebook(tmp_path, "locate.ipynb", [
            [_stream_out("clean\n")],                                  # cell 0
            [_display_out(rf"C:\Users\{USER}\.nuget\packages\foo")],    # cell 1, out 0
        ])
        hits = smp.find_leak_outputs(nb)
        assert hits == [(1, 0, "text/plain")]

    def test_count_returns_zero_on_missing_file(self, tmp_path):
        assert smp.count_leak_lines(tmp_path / "does_not_exist.ipynb") == 0

    def test_find_returns_empty_on_missing_file(self, tmp_path):
        assert smp.find_leak_outputs(tmp_path / "does_not_exist.ipynb") == []

    def test_count_returns_zero_on_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{not valid json", encoding="utf-8")
        assert smp.count_leak_lines(bad) == 0


# ==========================================================================
# ACTIVE_CATEGORIES filter (mutate module global, per source-doc instruction)
# ==========================================================================

class TestCategoryFilter:
    def test_filter_to_nuget_only(self):
        # Default: all categories detected.
        nuget_line = rf"C:\Users\{USER}\.nuget\packages\foo"
        pip_line = rf"C:\Users\{USER}\AppData\Roaming\Python\site-packages\torch"
        assert smp._has_leak(nuget_line) is True
        assert smp._has_leak(pip_line) is True
        try:
            smp.ACTIVE_CATEGORIES = {"nuget"}
            assert smp._has_leak(nuget_line) is True   # still detected
            assert smp._has_leak(pip_line) is False    # now filtered out
        finally:
            smp.ACTIVE_CATEGORIES = None               # restore default

    def test_active_tokens_respects_filter(self):
        try:
            smp.ACTIVE_CATEGORIES = {"conda", "hf"}
            labels = {label for label, _ in smp._active_tokens()}
            assert labels == {"conda", "hf"}
        finally:
            smp.ACTIVE_CATEGORIES = None

    def test_default_returns_all_tokens(self):
        smp.ACTIVE_CATEGORIES = None
        labels = {label for label, _ in smp._active_tokens()}
        assert labels == {lbl for lbl, _ in smp.MACHINE_PATH_TOKENS}


# ==========================================================================
# CLI --scan integration
# ==========================================================================

class TestCliScan:
    """CLI contract (verified against main() in strip_machine_paths.py):

    - ``--scan <path>`` is a **dry-run**: it prints ``[DEFECT]`` lines for
      leaky notebooks and a summary, and exits **0** (it is a reporter, not a
      gate). The gate signal (exit 1) only fires under ``--scan-all --check``.
    - A missing path raises ``parser.error`` (exit code 2 + message on stderr).
    """

    def _run(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            capture_output=True, text=True, timeout=60,
        )

    def test_scan_clean_notebook_reports_no_defect(self, tmp_path):
        nb = _mk_notebook(tmp_path, "clean.ipynb", [
            [_stream_out("all good\n")],
        ])
        r = self._run("--scan", str(nb))
        assert r.returncode == 0, r.stderr
        assert "[DEFECT]" not in r.stdout
        assert "0 notebook(s) carrying 0 leak" in r.stdout

    def test_scan_leaky_notebook_reports_defect(self, tmp_path):
        nb = _mk_notebook(tmp_path, "leak.ipynb", [
            [_stream_out(rf"C:\Users\{USER}\.nuget\packages\foo\1.0.0\bar.dll\n")],
        ])
        r = self._run("--scan", str(nb))
        # --scan is a dry-run reporter: exits 0, but flags the defect inline.
        assert r.returncode == 0, r.stderr
        assert "[DEFECT]" in r.stdout
        assert "leak.ipynb" in r.stdout
        assert "1 notebook(s) carrying 1 leak" in r.stdout

    def test_scan_missing_path_exits_two(self, tmp_path):
        # argparse parser.error() exits with code 2 and writes to stderr.
        r = self._run("--scan", str(tmp_path / "nope.ipynb"))
        assert r.returncode == 2, (
            f"expected exit 2 (argparse error), got {r.returncode}. "
            f"stderr={r.stderr!r}")
        assert "Traceback" not in r.stderr
        assert "path not found" in r.stderr.lower()


# --------------------------------------------------------------------------
# Direct-run harness (executable as ``py scripts/tests/test_strip_machine_paths.py``)
# --------------------------------------------------------------------------

if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
