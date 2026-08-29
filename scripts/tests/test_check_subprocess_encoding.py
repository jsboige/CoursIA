"""Tests for check_subprocess_encoding (ratchet gate, #13140).

Unit tests target the pure scan_source() parser (balanced-paren call spans,
the text/universal_newlines/encoding discrimination, multiline kwargs); the
integration tests drive main(argv) directly (per the cli-surface lesson:
running _run_check or scan_source through a bypassed argv hides CLI bugs).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_subprocess_encoding as cse  # noqa: E402


def test_clean_text_with_encoding():
    src = 'out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")\n'
    assert cse.scan_source(src) == []


def test_violation_text_without_encoding():
    src = "out = subprocess.run(cmd, capture_output=True, text=True)\n"
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 1


def test_violation_universal_newlines():
    src = "out = subprocess.check_output(cmd, universal_newlines=True)\n"
    assert len(cse.scan_source(src)) == 1


def test_multiline_encoding_on_separate_line_is_clean():
    # #13140 methodology: the false-negative class -- encoding= on its own
    # line of a multiline call must count as fixed.
    src = (
        "proc = subprocess.run(\n"
        "    ['gh', 'pr', 'view', str(n), '--json', 'body'],\n"
        "    capture_output=True,\n"
        "    text=True,\n"
        '    encoding="utf-8", errors="replace",\n'
        ")\n"
    )
    assert cse.scan_source(src) == []


def test_multiline_violation_reports_call_line():
    src = (
        "proc = subprocess.run(\n"
        "    ['git', 'log'],\n"
        "    capture_output=True,\n"
        "    text=True,\n"
        ")\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 1  # the line of the call, not of text=True


def test_bytes_mode_without_text_is_clean():
    src = "out = subprocess.run(cmd, capture_output=True)\n"
    assert cse.scan_source(src) == []


def test_text_false_is_clean():
    src = "out = subprocess.run(cmd, capture_output=True, text=False)\n"
    assert cse.scan_source(src) == []


def test_fstring_single_quote_variant_is_clean():
    src = (
        "print(f\"v: {subprocess.run(['git','config','x'], capture_output=True, "
        "text=True, encoding='utf-8', errors='replace').stdout.strip()}\")\n"
    )
    assert cse.scan_source(src) == []


def test_docstring_prose_mentioning_pattern_is_not_flagged():
    # The guard's own docstring (and any prose) mentions the defect pattern;
    # tokenize suppression keeps prose out of the findings (self-scan green).
    src = (
        '"""Gate doc: subprocess.run(cmd, text=True) without encoding= is bad.\n'
        'Also universal_newlines=True.\n'
        '"""\n'
        "import subprocess\n"
        "subprocess.run(['x'], text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 5


def test_comment_prose_mentioning_pattern_is_not_flagged():
    src = (
        "# legacy: subprocess.run(cmd, text=True) -- fixed in #12813\n"
        "import subprocess\n"
        "subprocess.run(['x'], text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 3


def test_fstring_defect_site_is_detected():
    # setup_hooks.py L225 class (#13140 tranche 2): the defect lived INSIDE an
    # f-string expression. f-strings are exempt from prose suppression.
    src = (
        'print(f"cfg: {subprocess.run([\'git\',\'config\',\'x\'], '
        "capture_output=True, text=True).stdout.strip()}\" )\n"
    )
    assert len(cse.scan_source(src)) == 1


def test_nested_parentheses_span_is_balanced():
    # The call contains a nested parenthesized expression (a lambda default);
    # the span must close on the CALL's closing paren, not the inner one.
    src = (
        "p = subprocess.run(cmd, capture_output=True, text=True,\n"
        "                   check=lambda r: (r or 0))\n"
        "q = subprocess.run(cmd2, text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 2  # BOTH calls violate: balanced parse works
    assert findings[1][0] == 3


def test_line_numbers_count_from_file_start():
    src = "x = 1\ny = 2\nz = subprocess.run(cmd, text=True)\n"
    findings = cse.scan_source(src)
    assert findings[0][0] == 3


def test_excluded_markers():
    assert cse.excluded("_peters/foo/bar.py")
    assert cse.excluded("MyIA.AI.Notebooks/x/.lake/packages/Foo.lean.py")
    assert not cse.excluded("scripts/pr_gate.py")


def test_main_files_mode_exit_codes(tmp_path, capsys):
    bad = tmp_path / "bad.py"
    bad.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                   encoding="utf-8")
    good = tmp_path / "good.py"
    good.write_text('import subprocess\nsubprocess.run(["x"], text=True, encoding="utf-8")\n',
                    encoding="utf-8")
    assert cse.main([str(good)]) == 0
    assert cse.main([str(bad)]) == 1
    out = capsys.readouterr().out
    assert "text=True without encoding=" in out


def test_main_files_mode_skips_vendored_and_non_py(tmp_path):
    vendored = tmp_path / "_peters" / "lib.py"
    vendored.parent.mkdir()
    vendored.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                        encoding="utf-8")
    assert cse.main([str(vendored)]) == 0


def test_main_base_mode(monkeypatch, capsys):
    monkeypatch.setattr(cse, "git_out", lambda *a: {
        ("merge-base", "origin/main", "HEAD"): "abc123\n",
        ("diff", "--name-only", "--diff-filter=AM", "abc123", "HEAD"):
            "scripts/a.py\n_peters/b.py\nnotebook.ipynb\n",
    }[a])
    # No files on disk with those names -> 0 violations, exit 0, paths filtered.
    assert cse.main(["--base", "origin/main"]) == 0
    out = capsys.readouterr().out
    assert "1 changed .py file(s)" in out
