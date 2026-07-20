"""Tests for ``scripts/i18n/sync.py`` and ``scripts/i18n/render.py`` (EPIC #4957).

These tests cover the i18n CSV-by-series pipeline. The design doc
``docs/i18n/CSV-by-series-design.md`` is the authoritative source for the
file format and key conventions.

Test grid (≥11 gates) :
1. Sync extracts h1 cell with the correct key.
2. Sync extracts h2 cells with section-specific keys (no collision across h2).
3. Sync extracts paragraph cells with sequential numbering per section.
4. Sync extracts table headers + rows with the ``table.<section>.<kind>.<N>`` schema.
5. Sync extracts list items with sequential numbering per section.
6. Sync extracts blockquote cells.
7. Sync preserves existing EN translations when FR is unchanged.
8. Sync preserves existing EN translations when FR is updated.
9. Sync warns (does not delete) keys absent from FR but present in CSV.
10. Render round-trip : sync + render on an unchanged FR reproduces a markdown
    document with the same cell count (byte-identical when EN is empty).
11. Render fallback : when EN is empty, render falls back to FR text.
12. Render warning on orphan keys (CSV keys not in FR).

Unit tests (primitive contracts, independent of the markdown layer) :
- ``_slug`` : lowercase + whitespace collapse + non-word strip, accented-Latin
  and CJK preservation, empty fallback, 40-char cap.
- ``write_csv`` : RFC-4180 format (QUOTE_ALL, LF terminator), header schema,
  ``keys_ordered`` row order, missing-lang empty cell, parent-dir creation,
  and round-trip through ``read_csv``.
- ``_extract_text`` : leaf precedence (text > raw), ``text``/``link``/``image``
  /``emphasis``/``strong`` re-emission as markdown, mixed string+dict children.

Run with : ``python -m pytest scripts/i18n/tests/test_sync_render.py -v``
"""
from __future__ import annotations

import sys
import os
import tempfile
from pathlib import Path

import pytest

# Allow imports from the scripts/i18n directory when running from the repo root.
_HERE = Path(__file__).resolve().parent
_SCRIPTS_I18N = _HERE.parent
_REPO_ROOT = _SCRIPTS_I18N.parent.parent
for p in (_SCRIPTS_I18N, _REPO_ROOT):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from scripts.i18n.sync import (  # noqa: E402
    _extract_text,
    _slug,
    parse_markdown,
    read_csv,
    sync,
    write_csv,
)
from scripts.i18n.render import render  # noqa: E402


_FR_FIXTURE = """# Titre Principal

Premier paragraphe d'introduction.

## Première Section

Contenu de la première section.

- item 1
- item 2

## Deuxième Section

Contenu de la deuxième section.

| Col A | Col B |
| --- | --- |
| val1 | val2 |
| val3 | val4 |

> Une citation importante.
"""


@pytest.fixture
def fr_text():
    return _FR_FIXTURE


@pytest.fixture
def tmp_paths(tmp_path):
    fr = tmp_path / "README.md"
    fr.write_text(_FR_FIXTURE, encoding="utf-8")
    csv = tmp_path / "README.csv"
    out = tmp_path / "README.en.md"
    return {"fr": fr, "csv": csv, "out": out, "tmp": tmp_path}


# --- Gate 1-6 : sync extraction ---------------------------------------- #
def test_sync_extracts_h1(fr_text):
    """The h1 cell has key ``# <h1>:<slug>`` and contains the title text."""
    doc = parse_markdown(fr_text)
    h1_cells = [c for c in doc.cells if c.kind == "h1"]
    assert len(h1_cells) == 1
    assert h1_cells[0].text == "Titre Principal"
    assert h1_cells[0].key.startswith("# <h1>:")


def test_sync_extracts_h2_with_section_keys(fr_text):
    """Each h2 gets a unique key ``## <h2>:<slug>`` with no collision."""
    doc = parse_markdown(fr_text)
    h2_cells = [c for c in doc.cells if c.kind == "h2"]
    assert len(h2_cells) == 2
    keys = [c.key for c in h2_cells]
    assert all(k.startswith("## <h2>:") for k in keys)
    assert keys[0] != keys[1], "h2 cells must have unique keys"


def test_sync_extracts_paragraphs_with_sequential_numbering(fr_text):
    """Paragraphs are numbered sequentially per section, scoped to current section slug."""
    doc = parse_markdown(fr_text)
    p_cells = [c for c in doc.cells if c.kind == "p"]
    keys = [c.key for c in p_cells]
    # The first paragraph (before any h2) is namespaced to the h1 slug ("titre_principal").
    # Subsequent paragraphs are namespaced to their h2 slug.
    assert any("titre_principal.para1" in k for k in keys), (
        f"intro paragraph must scope to h1 slug, got {keys}"
    )
    # _slug preserves accented Latin characters (première, deuxième).
    assert any("première_section.para1" in k for k in keys), (
        f"section 1 must namespace paragraphs to h2 slug, got {keys}"
    )
    assert any("deuxième_section.para1" in k for k in keys), (
        f"section 2 must namespace paragraphs to h2 slug, got {keys}"
    )
    # All paragraphs end in .para<N>
    assert all(".para" in k for k in keys)


def test_sync_extracts_table_with_correct_schema(fr_text):
    """Tables use ``table.<section>.header.<N>`` and ``table.<section>.row.<R>.col.<C>`` keys."""
    doc = parse_markdown(fr_text)
    th_cells = [c for c in doc.cells if c.kind == "th"]
    td_cells = [c for c in doc.cells if c.kind == "td"]
    assert len(th_cells) == 2
    assert len(td_cells) == 4
    assert all(c.key.startswith("table.deuxième_section.header.")
               for c in th_cells)
    assert all(c.key.startswith("table.deuxième_section.row.")
               for c in td_cells)


def test_sync_extracts_list_items_with_sequential_numbering(fr_text):
    """List items use ``<section>.list.item<N>`` keys."""
    doc = parse_markdown(fr_text)
    li_cells = [c for c in doc.cells if c.kind == "li"]
    assert len(li_cells) == 2
    assert li_cells[0].text == "item 1"
    assert li_cells[1].text == "item 2"
    assert all(".list.item" in c.key for c in li_cells)


def test_sync_extracts_blockquote(fr_text):
    """Blockquote cells have ``<section>.quote`` key."""
    doc = parse_markdown(fr_text)
    quote_cells = [c for c in doc.cells if c.kind == "quote"]
    assert len(quote_cells) == 1
    assert "citation importante" in quote_cells[0].text


# --- Gate 7-9 : sync CSV diff ---------------------------------------- #
def test_sync_preserves_existing_en_when_fr_unchanged(tmp_paths):
    """Modifying FR to itself preserves the EN column unchanged."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    sync(fr, csv_path)
    # Pre-fill EN for one cell to simulate a translation.
    langs, data = read_csv(csv_path)
    target_key = next(k for k in data if "titre_principal.para1" in k)
    data[target_key]["en"] = "Existing English translation"
    # Write back.
    import csv as csvmod
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        w = csvmod.writer(fh, quoting=csvmod.QUOTE_ALL, lineterminator="\n")
        w.writerow(["key"] + langs)
        for k, row in data.items():
            w.writerow([k] + [row.get(l, "") for l in langs])
    # Re-sync with same FR.
    stats = sync(fr, csv_path)
    assert stats["updated"] == 0
    assert stats["preserved"] >= 1
    _, data2 = read_csv(csv_path)
    assert data2[target_key]["en"] == "Existing English translation"


def test_sync_preserves_existing_en_when_fr_updates(tmp_paths):
    """Modifying the FR text updates the FR column but preserves EN."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    sync(fr, csv_path)
    langs, data = read_csv(csv_path)
    target_key = next(k for k in data if "titre_principal.para1" in k)
    data[target_key]["en"] = "Existing English translation"
    import csv as csvmod
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        w = csvmod.writer(fh, quoting=csvmod.QUOTE_ALL, lineterminator="\n")
        w.writerow(["key"] + langs)
        for k, row in data.items():
            w.writerow([k] + [row.get(l, "") for l in langs])
    # Modify the FR text and re-sync.
    fr.write_text(fr.read_text(encoding="utf-8").replace(
        "Premier paragraphe d'introduction.", "Premier paragraphe modifié."
    ), encoding="utf-8")
    stats = sync(fr, csv_path)
    assert stats["updated"] >= 1
    _, data2 = read_csv(csv_path)
    assert data2[target_key]["en"] == "Existing English translation"
    assert "modifié" in data2[target_key]["fr"]


def test_sync_preserves_orphan_keys(tmp_paths, capsys):
    """Keys in CSV but absent from FR are preserved (not auto-deleted)."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    sync(fr, csv_path)
    langs, data = read_csv(csv_path)
    data["FAKE_KEY.para1"] = {"fr": "clé inventée", "en": "fake key"}
    import csv as csvmod
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        w = csvmod.writer(fh, quoting=csvmod.QUOTE_ALL, lineterminator="\n")
        w.writerow(["key"] + langs)
        for k, row in data.items():
            w.writerow([k] + [row.get(l, "") for l in langs])
    sync(fr, csv_path, verbose=True)
    _, data2 = read_csv(csv_path)
    assert "FAKE_KEY.para1" in data2, "orphan key must be preserved"


# --- Gate 10-12 : render --------------------------------------------- #
def test_render_round_trip_count(tmp_paths):
    """Render produces the same number of cells as parse."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    out = tmp_paths["out"]
    sync(fr, csv_path)
    results = render(csv_path, fr, [("en", out)])
    assert len(results) == 1
    doc = parse_markdown(fr.read_text(encoding="utf-8"))
    assert results[0].n_cells == len(doc.cells)


def test_render_fallback_to_fr_when_en_empty(tmp_paths):
    """When EN cell is empty, render falls back to FR text."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    out = tmp_paths["out"]
    sync(fr, csv_path)
    results = render(csv_path, fr, [("en", out)])
    res = results[0]
    # All EN cells empty in fresh CSV → all fallback to FR.
    assert res.n_fallback == res.n_cells
    # Output text contains FR text.
    output = out.read_text(encoding="utf-8")
    assert "Premier paragraphe" in output
    assert "Titre Principal" in output


def test_render_warns_on_orphan_keys(tmp_paths, capsys):
    """Render warns (doesn't crash) when CSV has keys not in FR."""
    fr = tmp_paths["fr"]
    csv_path = tmp_paths["csv"]
    out = tmp_paths["out"]
    sync(fr, csv_path)
    langs, data = read_csv(csv_path)
    data["ORPHAN_KEY.para1"] = {"fr": "x", "en": "y"}
    import csv as csvmod
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        w = csvmod.writer(fh, quoting=csvmod.QUOTE_ALL, lineterminator="\n")
        w.writerow(["key"] + langs)
        for k, row in data.items():
            w.writerow([k] + [row.get(l, "") for l in langs])
    results = render(csv_path, fr, [("en", out)])
    assert "ORPHAN_KEY.para1" in results[0].orphan_keys


# --- Unit tests : _slug -------------------------------------------------- #
# ``_slug`` is the key-derivation primitive of the whole CSV pipeline : two
# distinct FR cells must map to two distinct keys, or translations silently
# overwrite each other. ``parse_markdown`` exercises it indirectly via every
# key, but a focused unit test pins the contract (CJK preserved, accents
# preserved, empty fallback, length cap) independently of the markdown layer.
def test_slug_lowercases_collapses_whitespace_strips_punct():
    """Lowercase, ``\\s+`` -> single underscore, non-word chars stripped."""
    assert _slug("Hello World!") == "hello_world"
    assert _slug("Multi  spaces\ttabs") == "multi_spaces_tabs"


def test_slug_preserves_accented_latin():
    """Python3 ``\\w`` is Unicode-aware : accented Latin (première) is kept.

    This matters for FR source content where section slugs namespace every
    downstream key (e.g. ``première_section.para1``). Stripping accents here
    would collide ``premiere`` and ``première`` sections.
    """
    assert _slug("Première Section") == "première_section"


def test_slug_preserves_cjk():
    """CJK ideographs (``一-鿿`` range kept by the explicit allow-list) survive.

    Required for zh/ja source cells — a stripped CJK slug would collapse every
    Chinese heading to the ``cell`` fallback and lose all translation keys.
    """
    s = _slug("测试中文标题")
    assert "测" in s and s != "cell", f"CJK must be preserved, got {s!r}"


def test_slug_empty_or_blank_falls_back_to_cell():
    """Empty / whitespace-only slug falls back to ``cell`` (never empty key)."""
    assert _slug("") == "cell"
    assert _slug("   ") == "cell"


def test_slug_truncates_to_40_chars():
    """Slug is capped at 40 chars to bound CSV key length."""
    assert _slug("a" * 50) == "a" * 40
    assert len(_slug("x" * 200)) == 40


# --- Unit tests : write_csv --------------------------------------------- #
# ``write_csv`` emits the RFC-4180 CSV consumed by the Argumentum .NET
# ``DatasetUpdater`` engine. ``sync()`` covers it indirectly through a full
# extract+diff round-trip, but the format contract (QUOTE_ALL, LF terminator,
# header schema, key ordering, parent-dir creation) is pinned here in isolation
# so a regression in the writer is caught without re-running the whole pipeline.
def test_write_csv_round_trips_through_read_csv(tmp_path):
    """write_csv then read_csv recovers the same data + language list."""
    csv_path = tmp_path / "sub" / "out.csv"
    langs = ["fr", "en", "es"]
    data = {
        "k1": {"fr": "a", "en": "A", "es": "α"},
        "k2": {"fr": "b", "en": "B", "es": "β"},
    }
    write_csv(csv_path, langs, data, keys_ordered=["k1", "k2"])
    rlangs, rdata = read_csv(csv_path)
    assert rlangs == langs
    assert rdata == data


def test_write_csv_header_is_key_plus_langs(tmp_path):
    """First row is the literal header ``key,<lang1>,<lang2>,...``."""
    csv_path = tmp_path / "out.csv"
    write_csv(csv_path, ["fr", "en"], {"k": {"fr": "x", "en": "y"}}, ["k"])
    first_line = csv_path.read_text(encoding="utf-8").splitlines()[0]
    assert first_line == '"key","fr","en"'


def test_write_csv_quotes_all_cells_and_uses_lf(tmp_path):
    """QUOTE_ALL -> every cell quoted ; lineterminator = LF (not CRLF).

    CRLF would break the Argumentum .NET reader line-splitting on the
    committed (autocrlf) repo. LF is the canonical RFC-4180 terminator here.
    """
    csv_path = tmp_path / "out.csv"
    write_csv(csv_path, ["fr"], {"k": {"fr": "v"}}, ["k"])
    raw = csv_path.read_bytes()
    assert b"\r\n" not in raw, "write_csv must not emit CRLF"
    text = raw.decode("utf-8")
    # Every non-empty line is fully quoted (QUOTE_ALL).
    for line in text.splitlines():
        assert line.startswith('"') and line.endswith('"'), (
            f"QUOTE_ALL expects every cell quoted, got {line!r}"
        )


def test_write_csv_respects_keys_ordered(tmp_path):
    """``keys_ordered`` controls row order, independent of dict insertion."""
    csv_path = tmp_path / "out.csv"
    data = {"zebra": {"fr": "z"}, "alpha": {"fr": "a"}, "mike": {"fr": "m"}}
    write_csv(csv_path, ["fr"], data, keys_ordered=["alpha", "mike", "zebra"])
    rows = csv_path.read_text(encoding="utf-8").splitlines()
    keys_in_file_order = [r.split('","')[0].lstrip('"') for r in rows[1:]]
    assert keys_in_file_order == ["alpha", "mike", "zebra"]


def test_write_csv_missing_lang_yields_empty_cell(tmp_path):
    """A key lacking one language writes an empty cell (not an error)."""
    csv_path = tmp_path / "out.csv"
    data = {"k1": {"fr": "a"}}  # no "en"
    write_csv(csv_path, ["fr", "en"], data, ["k1"])
    _, rdata = read_csv(csv_path)
    assert rdata["k1"]["fr"] == "a"
    assert rdata["k1"]["en"] == ""


def test_write_csv_creates_parent_dir(tmp_path):
    """``write_csv`` mkdirs the parent so a fresh series path works."""
    csv_path = tmp_path / "deep" / "nested" / "series.csv"
    assert not csv_path.parent.exists()
    write_csv(csv_path, ["fr"], {"k": {"fr": "v"}}, ["k"])
    assert csv_path.exists()


# --- Unit tests : _extract_text ----------------------------------------- #
# ``_extract_text`` flattens a mistune AST node into visible text while
# re-emitting link/image/emphasis as markdown so the translator keeps the URL.
# It is called ~12x per cell by ``parse_markdown`` ; a recursion or syntax bug
# would silently strip URLs / alt-text from every translated cell.
def test_extract_text_leaf_prefers_text_then_raw():
    """Leaf token (no children): ``text`` wins, else ``raw``."""
    assert _extract_text({"text": "hi", "raw": "hello"}) == "hi"
    assert _extract_text({"raw": "hello"}) == "hello"
    assert _extract_text({}) == ""


def test_extract_text_text_child():
    """Child of type ``text`` contributes its ``raw`` value."""
    tok = {"children": [{"type": "text", "raw": "hello"}]}
    assert _extract_text(tok) == "hello"


def test_extract_text_re_emits_link_as_markdown():
    """``link`` child is re-emitted ``[text](url)`` to preserve the URL."""
    tok = {"children": [
        {"type": "link", "attrs": {"url": "http://x"},
         "children": [{"type": "text", "raw": "click"}]},
    ]}
    assert _extract_text(tok) == "[click](http://x)"


def test_extract_text_re_emits_image_as_markdown():
    """``image`` child is re-emitted ``![alt](url)``."""
    tok = {"children": [
        {"type": "image", "attrs": {"url": "img.png", "alt": "pic"}},
    ]}
    assert _extract_text(tok) == "![pic](img.png)"


def test_extract_text_emphasis_and_strong():
    """``emphasis`` -> ``*x*`` ; ``strong`` -> ``**x**`` (recursion preserved)."""
    emph = {"children": [
        {"type": "emphasis", "children": [{"type": "text", "raw": "x"}]},
    ]}
    assert _extract_text(emph) == "*x*"
    strong = {"children": [
        {"type": "strong", "children": [{"type": "text", "raw": "x"}]},
    ]}
    assert _extract_text(strong) == "**x**"


def test_extract_text_mixed_string_and_dict_children():
    """``children`` may contain raw strings (mistune inline literals)."""
    tok = {"children": ["literal string", {"type": "text", "raw": " ok"}]}
    assert _extract_text(tok) == "literal string ok"
