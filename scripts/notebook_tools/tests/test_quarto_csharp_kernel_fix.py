"""Tests for quarto_csharp_kernel_fix — apply/restore byte-clean roundtrip + --path single-file mode.

Issue #11335 acceptance: ``apply``/``restore`` byte-clean (0 diff résiduel sur ``*.ipynb``)
+ Search-15 spot-check. The script was hardened in #11511 (DRIFT detection, --strict CI
guard). This suite pins the new --path single-file override against regressions: a future
refactor must keep the spot-check usable on one notebook without scanning the full tree.

Byte-clean meaning: the only bytes that differ between original and post-restore file
are the 4-byte stretch ``"C#"`` -> ``"csharp"`` at the kernelspec.language position.
Roundtrip (``apply`` then ``restore``) returns the file to its original bytes.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Make the script importable both as module (for in-process tests) and as CLI (for subprocess tests)
SCRIPT_DIR = Path(__file__).resolve().parents[2]  # scripts/
sys.path.insert(0, str(SCRIPT_DIR))


def _make_dotnet_notebook(tmp_path: Path, *, language: str = "C#",
                          kernel_name: str = ".net-csharp") -> Path:
    """Write a minimal .ipynb whose metadata.kernelspec matches the dotnet pattern."""
    nb = {
        "cells": [],
        "metadata": {
            "kernelspec": {
                "display_name": ".NET (C#)",
                "language": language,
                "name": kernel_name,
            },
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(nb, indent=2), encoding="utf-8")
    return p


def test_patched_spans_yields_c_sharp_token(tmp_path):
    from quarto_csharp_kernel_fix import patched_spans, LANG_CSHARP_TOKEN_RE, LANG_FIX_TOKEN_RE
    nb = _make_dotnet_notebook(tmp_path)
    data = nb.read_bytes()
    spans = list(patched_spans(data, LANG_CSHARP_TOKEN_RE))
    assert len(spans) == 1, f"expected 1 C# span, got {len(spans)}"
    assert data[spans[0][0]:spans[0][1]] == b'"C#"'

    fixed_spans = list(patched_spans(data, LANG_FIX_TOKEN_RE))
    assert fixed_spans == [], "no csharp span before apply"


def test_patched_spans_ignores_non_dotnet_kernel(tmp_path):
    from quarto_csharp_kernel_fix import patched_spans, LANG_CSHARP_TOKEN_RE
    nb = _make_dotnet_notebook(tmp_path, kernel_name="python3")
    data = nb.read_bytes()
    assert list(patched_spans(data, LANG_CSHARP_TOKEN_RE)) == []


def test_apply_single_file_roundtrip_byte_clean(tmp_path):
    """Issue #11335 acceptance: apply+restore on a single file returns the exact bytes."""
    from quarto_csharp_kernel_fix import cmd_apply, cmd_restore

    nb = _make_dotnet_notebook(tmp_path)
    original = nb.read_bytes()
    manifest = tmp_path / "manifest.json"

    # apply on this single file (root == tmp_path, path == nb)
    rc = cmd_apply(tmp_path, manifest, nb)
    assert rc == 0
    patched = nb.read_bytes()
    # exactly one byte position changed; the difference is +4 bytes
    # ("C#" -> "csharp" = 3 bytes -> 7 bytes, +4 bytes, in the right position)
    assert len(patched) == len(original) + 4, (
        f"expected +4 bytes (C# -> csharp), got {len(patched) - len(original)}"
    )
    # the offset recorded in the manifest must point at the original "C#" position
    m = json.loads(manifest.read_text(encoding="utf-8"))
    assert len(m) == 1
    rel, offsets = next(iter(m.items()))
    assert rel == nb.name
    assert len(offsets) == 1
    # the file at that offset now holds the 7-char token "csharp" (including quotes)
    assert patched[offsets[0]:offsets[0] + 8] == b'"csharp"', (
        f"expected '\"csharp\"' at offset {offsets[0]}, got "
        f"{patched[offsets[0]:offsets[0] + 8]!r}"
    )
    # and the original byte at that same offset was the 4-char token "C#" (including quotes)
    assert original[offsets[0]:offsets[0] + 4] == b'"C#"'

    # restore on this single file
    rc = cmd_restore(manifest, tmp_path, nb)
    assert rc == 0
    final = nb.read_bytes()
    assert final == original, (
        f"roundtrip not byte-clean: {len(final) - len(original)} bytes drift "
        f"(first diff at {next((i for i,(a,b) in enumerate(zip(original,final)) if a!=b), 'none')})"
    )
    assert not manifest.exists(), "manifest should be removed after successful restore"


def test_apply_refuses_double_apply_without_restore(tmp_path):
    """If the manifest from a previous apply is still around, a new apply refuses."""
    from quarto_csharp_kernel_fix import cmd_apply

    nb = _make_dotnet_notebook(tmp_path)
    manifest = tmp_path / "manifest.json"
    assert cmd_apply(tmp_path, manifest, nb) == 0
    # second apply must refuse (exit 1) and not modify anything
    rc = cmd_apply(tmp_path, manifest, nb)
    assert rc == 1


def test_check_reports_unpatched_then_patched(tmp_path):
    """check --strict exits 1 when unpatched; returns 0 after apply on the file."""
    from quarto_csharp_kernel_fix import cmd_apply, cmd_check, cmd_restore

    nb = _make_dotnet_notebook(tmp_path)
    manifest = tmp_path / "manifest.json"

    rc = cmd_check(tmp_path, strict=True)
    assert rc == 1

    assert cmd_apply(tmp_path, manifest, nb) == 0
    rc = cmd_check(tmp_path, strict=True)
    assert rc == 0
    # cleanup
    assert cmd_restore(manifest, tmp_path, nb) == 0


def test_cli_path_single_file_roundtrip(tmp_path):
    """End-to-end through the CLI (subprocess) — same guarantee as the in-process path."""
    nb = _make_dotnet_notebook(tmp_path)
    original = nb.read_bytes()
    manifest = tmp_path / "manifest.json"
    script = SCRIPT_DIR / "quarto_csharp_kernel_fix.py"

    # apply --path
    rc = subprocess.run(
        [sys.executable, str(script), "apply",
         "--root", str(tmp_path),
         "--path", str(nb),
         "--manifest", str(manifest)],
        check=False, capture_output=True, text=True,
    )
    assert rc.returncode == 0, rc.stderr
    patched = nb.read_bytes()
    assert len(patched) == len(original) + 4

    # restore --path
    rc = subprocess.run(
        [sys.executable, str(script), "restore",
         "--root", str(tmp_path),
         "--path", str(nb),
         "--manifest", str(manifest)],
        check=False, capture_output=True, text=True,
    )
    assert rc.returncode == 0, rc.stderr
    final = nb.read_bytes()
    assert final == original
    assert not manifest.exists()


def test_path_outside_root_rejected(tmp_path):
    """--path must be inside --root; otherwise ValueError."""
    import quarto_csharp_kernel_fix as qf
    outside = tmp_path / "outside.ipynb"
    outside.write_text("{}", encoding="utf-8")
    root = tmp_path / "root"
    root.mkdir()
    with pytest.raises(ValueError, match="outside --root"):
        list(qf.iter_targets(root, outside))