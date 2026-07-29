"""Tests for ``detect_manifest_field.py``.

The detector enforces that a changed ``assets/readme/MANIFEST.md`` declares
the ``Description visuelle`` field per figure entry (EPIC #5654, doctrine
#5780). It is wired into the pre-merge CI gate
``manifest-description-visuelle-gate.yml`` but had **no test suite** — these
tests lock its contract so a regression in the regex / block-scoping / exit
codes is caught before it ships to the gate.

Coverage:

- ``check_manifest`` — canonical ``##`` header, legacy ``###`` header,
  missing field (rc=1, names the offender), multiple figures partial vs all,
  no figure section (rc=0 degenerate), missing file (rc=2), tolerant field
  variant (no leading ``-``), case-insensitive field, encoding robustness
  (``errors="replace"``), and block-scoping (a field in a sibling figure's
  block does NOT satisfy the wrong figure).
- ``main`` — ``--check`` exit 0 conforming / exit 1 defective, no-``--check``
  always exit 0, missing path exit 2, and the ``/assets/readme/MANIFEST.md``
  scope filter (a MANIFEST elsewhere in the tree is ignored).

Run::

    python scripts/notebook_tools/tests/test_detect_manifest_field.py
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent.parent))

import detect_manifest_field as dmf  # noqa: E402


# --- fixtures / helpers --------------------------------------------------


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


def _manifest_one_canonical() -> str:
    """One canonical figure section that declares the field → conforming."""
    return (
        "# MANIFEST\n\n"
        "##  fig1.png\n\n"
        "- **Source** : notebook `nb.ipynb`\n"
        "- **Description visuelle** : heat map des poids\n"
        "- **Alt-text (FR)** : carte de chaleur\n"
        "- **Poids** : 12 KB\n"
    )


def _manifest_missing() -> str:
    """One figure section WITHOUT the field → defective."""
    return (
        "# MANIFEST\n\n"
        "##  fig1.png\n\n"
        "- **Source** : notebook `nb.ipynb`\n"
        "- **Alt-text (FR)** : carte de chaleur\n"
    )


# --- check_manifest ------------------------------------------------------


class TestCheckManifest:
    def test_canonical_conforming(self, tmp_path, capsys):
        p = _write(tmp_path, "MANIFEST.md", _manifest_one_canonical())
        assert dmf.check_manifest(p) == 0

    def test_missing_field_returns_1(self, tmp_path, capsys):
        p = _write(tmp_path, "MANIFEST.md", _manifest_missing())
        assert dmf.check_manifest(p) == 1
        err = capsys.readouterr().out
        assert "fig1.png" in err

    def test_legacy_triple_hash_header_conforming(self, tmp_path):
        """``### filename.png`` is the legacy v1/v2 form and is accepted."""
        content = (
            "###  fig1.png\n\n"
            "- **Description visuelle** : legacy desc\n"
        )
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 0

    def test_multiple_figures_all_conforming(self, tmp_path):
        content = (
            "##  a.png\n\n- **Description visuelle** : desc a\n\n"
            "##  b.png\n\n- **Description visuelle** : desc b\n\n"
        )
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 0

    def test_multiple_figures_partial_names_only_missing(self, tmp_path, capsys):
        content = (
            "##  a.png\n\n- **Description visuelle** : desc a\n\n"
            "##  b.png\n\n- **Alt-text (FR)** : no desc here\n\n"
            "##  c.png\n\n- **Description visuelle** : desc c\n\n"
        )
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 1
        out = capsys.readouterr().out
        assert "b.png" in out and "a.png" not in out

    def test_no_figure_section_returns_0(self, tmp_path):
        """A MANIFEST with no ``## x.png`` / ``### x.png`` is degenerate (rc=0)."""
        p = _write(tmp_path, "MANIFEST.md", "# MANIFEST\n\nJust prose, no figures.\n")
        assert dmf.check_manifest(p) == 0

    def test_missing_file_returns_2(self, tmp_path):
        assert dmf.check_manifest(tmp_path / "does_not_exist.md") == 2

    def test_tolerant_field_variant_without_leading_dash(self, tmp_path):
        """``**Description visuelle** :`` (no leading ``-``) is accepted."""
        content = "##  fig1.png\n\n**Description visuelle** : desc\n"
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 0

    def test_case_insensitive_field(self, tmp_path):
        """Field matching is ``IGNORECASE`` (``description visuelle`` matches)."""
        content = "##  fig1.png\n\n- **description visuelle** : desc\n"
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 0

    def test_encoding_robustness_does_not_crash(self, tmp_path):
        """``errors="replace"`` : a file with invalid UTF-8 bytes must not raise."""
        p = tmp_path / "MANIFEST.md"
        # ``## fig1.png`` header followed by a non-UTF-8 byte sequence.
        p.write_bytes(b"##  fig1.png\n\n\xff\xfe garbage\n")
        # Must return an int (1 — header present, field absent) without raising.
        assert dmf.check_manifest(p) == 1

    def test_field_in_sibling_block_does_not_satisfy_wrong_figure(self, tmp_path):
        """Block-scoping: a ``Description visuelle`` placed under figure B
        must NOT clear the requirement for figure A. A's block ends where
        B's header begins."""
        content = (
            "##  figA.png\n\n"   # no field in A's block
            "##  figB.png\n\n"
            "- **Description visuelle** : only for B\n"
        )
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 1  # figA missing

    def test_header_with_trailing_caption_not_a_section(self, tmp_path):
        """``## fig.png (caption)`` does NOT match the canonical header
        (``\\s*$`` anchor) → treated as no figure section → rc=0."""
        content = "##  fig1.png (some caption)\n\n- **Description visuelle** : x\n"
        p = _write(tmp_path, "MANIFEST.md", content)
        assert dmf.check_manifest(p) == 0

    def test_only_png_figures_are_checked_documents_scope(self, tmp_path):
        """``FIGURE_HEADER_RE`` matches ``.png`` only. A non-png figure header
        (e.g. ``## anim.gif``, observed in real MGS-submodule MANIFESTs) is
        NOT recognised as a figure section, so its ``Description visuelle``
        field is NOT enforced.

        This locks the current ``.png``-only scope as an explicit contract:
        extending the detector to ``.gif``/``.jpg``/``.svg`` is a deliberate
        scope change requiring doctrine #5654/#5780 sign-off, not an
        accidental regex tweak. If a non-png figure without a description
        must be caught, widen the regex AND update this test deliberately.
        """
        content = (
            "##  anim.gif\n\n"   # non-png header: NOT a checked section
            "- **Alt-text (FR)** : no description here\n"
        )
        p = _write(tmp_path, "MANIFEST.md", content)
        # rc=0 because the detector sees ZERO figure sections — the .gif is
        # invisible to it. This documents the limitation, not a green light.
        assert dmf.check_manifest(p) == 0


# --- main / CLI ----------------------------------------------------------


class TestMain:
    def test_check_flag_conforming_exit_0(self, tmp_path):
        p = _write(tmp_path, "MANIFEST.md", _manifest_one_canonical())
        # ``main`` only checks paths matching ``/assets/readme/MANIFEST.md``;
        # place it there so the scope filter admits it.
        scoped = tmp_path / "assets" / "readme" / "MANIFEST.md"
        scoped.parent.mkdir(parents=True)
        scoped.write_text(_manifest_one_canonical(), encoding="utf-8")
        assert dmf.main(["--check", str(scoped)]) == 0

    def test_check_flag_defective_exit_1(self, tmp_path):
        scoped = tmp_path / "assets" / "readme" / "MANIFEST.md"
        scoped.parent.mkdir(parents=True)
        scoped.write_text(_manifest_missing(), encoding="utf-8")
        assert dmf.main(["--check", str(scoped)]) == 1

    def test_no_check_flag_always_exit_0_even_defective(self, tmp_path):
        scoped = tmp_path / "assets" / "readme" / "MANIFEST.md"
        scoped.parent.mkdir(parents=True)
        scoped.write_text(_manifest_missing(), encoding="utf-8")
        assert dmf.main([str(scoped)]) == 0

    def test_missing_path_exit_2(self, tmp_path):
        assert dmf.main([str(tmp_path / "nope.md")]) == 2

    def test_scope_filter_ignores_manifest_outside_assets_readme(self, tmp_path):
        """A defective MANIFEST NOT under ``assets/readme/`` is out of scope
        and must NOT contribute to the defect count."""
        out_of_scope = tmp_path / "other" / "MANIFEST.md"
        out_of_scope.parent.mkdir(parents=True)
        out_of_scope.write_text(_manifest_missing(), encoding="utf-8")
        # Scan the tmp dir: the only MANIFEST is out-of-scope → 0 checked, rc 0.
        assert dmf.main(["--check", str(tmp_path)]) == 0

    def test_directory_scan_checks_in_scope_manifest(self, tmp_path):
        """A directory scan finds and checks an in-scope MANIFEST."""
        scoped = tmp_path / "assets" / "readme" / "MANIFEST.md"
        scoped.parent.mkdir(parents=True)
        scoped.write_text(_manifest_missing(), encoding="utf-8")
        assert dmf.main(["--check", str(tmp_path)]) == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
