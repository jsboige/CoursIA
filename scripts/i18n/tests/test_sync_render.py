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
from scripts.i18n.render import (  # noqa: E402
    _render_tokens_to_markdown,
    _tok_text,
    _walk_translate,
    render,
)
import mistune  # noqa: E402


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


# --- Unit tests : _walk_translate + _render_tokens_to_markdown ------------- #
# The three ``render`` integration tests above (gates 10-12) exercise the
# pipeline end-to-end through the top-level ``render()`` entry point, but they
# only assert on aggregate counts and the fallback/orphan behaviour — they do
# NOT isolate the per-token branch logic of the two largest pure helpers:
#   - ``_walk_translate``  : the 5-node-type section/counter/fallback state
#                            machine that mutates tokens in place.
#   - ``_render_tokens_to_markdown`` : the 8-token-type markdown emitter.
# These focused tests build real mistune ASTs and call the helpers directly,
# pinning the key-generation contract, the FR-fallback policy, the in-place
# mutation, and the markdown re-emission — so a regression in one branch is
# caught without re-running the whole sync+render round-trip.
_MD_PARSER = mistune.create_markdown(renderer=None, plugins=["table"])


def _walk_tokens(fr_md, csv_data=None, lang="en"):
    """Mirror ``render()``'s internal walk: parse FR, walk every token in place.

    Returns ``(tokens, stats, section)`` so tests can assert on the mutated
    tokens, the counter dict, and the carried-over section slug.
    """
    tokens = _MD_PARSER(fr_md)
    stats = {"n_cells": 0, "n_fallback": 0, "n_missing": 0}
    section = [""]
    p_count = [0]
    list_count = [0]
    h1_seen = [False]
    for tok in tokens:
        _walk_translate(tok, csv_data or {}, lang, section, stats,
                        p_count, list_count, h1_seen)
    return tokens, stats, section[0]


def _translated(tok):
    """Visible text of a token AFTER walk mutation (via the walk's own reader)."""
    return _tok_text(tok)


# --- _walk_translate : section / counter state machine ------------------- #
def test_walk_h1_sets_section_slug():
    """An h1 token sets the carried-over section slug (used by every downstream key)."""
    _, stats, section = _walk_tokens("# My Title\n\nFirst.\n", {})
    assert section == "my_title"
    # h1 itself is counted as a cell.
    assert stats["n_cells"] >= 1


def test_walk_h1_resets_paragraph_counter():
    """Each h1 restarts the per-section paragraph numbering (para1, then para1 again)."""
    fr = "# Sec One\n\nA para.\n\n# Sec Two\n\nAnother para.\n"
    # Provide a translation for the second h1's para1 only.
    csvd = {"sec_one.para1": {"fr": "A para.", "en": "EN_A"},
            "sec_two.para1": {"fr": "Another para.", "en": "EN_B"}}
    _, stats, _ = _walk_tokens(fr, csvd)
    # Both para1 keys resolve because the counter reset on the 2nd h1.
    assert stats.get("n_translated", 0) == 2


def test_walk_paragraph_before_any_h1_uses_intro_section():
    """A paragraph appearing before the first h1 keys under the ``intro`` fallback."""
    fr = "Preamble with no heading yet.\n"
    csvd = {"intro.para1": {"fr": "Preamble with no heading yet.", "en": "EN_PRE"}}
    tokens, stats, _ = _walk_tokens(fr, csvd)
    para = next(t for t in tokens if t.get("type") == "paragraph")
    assert _translated(para) == "EN_PRE"
    assert stats.get("n_translated", 0) == 1


def test_walk_empty_paragraph_is_skipped_not_counted():
    """A whitespace-only paragraph returns early — it is neither counted nor keyed."""
    fr = "# T\n\n   \n\nreal paragraph.\n"
    _, stats, _ = _walk_tokens(fr, {})
    # Only h1 (1) + the real paragraph (1) = 2 cells; the blank para is skipped.
    assert stats["n_cells"] == 2


# --- _walk_translate : CSV hit / FR fallback ----------------------------- #
def test_walk_csv_hit_translates_and_counts_translated():
    """A cell whose ``<key>.<lang>`` is non-empty gets translated (not fallback)."""
    fr = "# My Title\n\nFirst para.\n"
    csvd = {"my_title.para1": {"fr": "First para.", "en": "EN_FIRST"}}
    tokens, stats, _ = _walk_tokens(fr, csvd)
    para = next(t for t in tokens if t.get("type") == "paragraph")
    assert _translated(para) == "EN_FIRST"
    assert stats.get("n_translated", 0) == 1
    assert stats["n_fallback"] >= 1  # the h1 (no heading key in CSV) falls back


def test_walk_csv_miss_falls_back_to_fr_text():
    """A cell whose target-lang entry is empty keeps the original FR text."""
    fr = "# My Title\n\nFirst para.\n"
    csvd = {"my_title.para1": {"fr": "First para.", "en": ""}}
    tokens, stats, _ = _walk_tokens(fr, csvd)
    para = next(t for t in tokens if t.get("type") == "paragraph")
    assert _translated(para) == "First para."  # FR retained
    assert stats["n_fallback"] >= 1


def test_walk_unknown_token_type_is_a_noop():
    """A token type outside the 5 handled kinds (e.g. block_code) is left untouched."""
    fr = "# S\n\n```\ncode\n```\n"
    tokens, stats, _ = _walk_tokens(fr, {})
    code = next(t for t in tokens if t.get("type") == "block_code")
    # block_code is not a translatable kind -> only the h1 was counted.
    assert stats["n_cells"] == 1
    assert (code.get("raw") or "").strip() == "code"


# --- _walk_translate : block_quote / list / table keys ------------------- #
def test_walk_blockquote_key_replaces_child_paragraph():
    """Blockquote uses ``<section>.quote`` and rewrites its inner paragraph text."""
    fr = "# S\n\n> A quote here.\n"
    csvd = {"s.quote": {"fr": "A quote here.", "en": "EN_QUOTE"}}
    tokens, stats, _ = _walk_tokens(fr, csvd)
    assert stats.get("n_translated", 0) == 1
    # Emission reflects the translated quote.
    out = _render_tokens_to_markdown(tokens, csvd, "en", ["s"])
    assert "> EN_QUOTE" in out


def test_walk_list_items_numbered_sequentially():
    """List items use ``<section>.list.item<N>`` (1-based) and translate each."""
    fr = "# S\n\n- one\n- two\n"
    csvd = {"s.list.item1": {"fr": "one", "en": "EN1"},
            "s.list.item2": {"fr": "two", "en": "EN2"}}
    _, stats, _ = _walk_tokens(fr, csvd)
    assert stats.get("n_translated", 0) == 2


def test_walk_table_header_and_row_col_keys():
    """Tables use ``table.<section>.header.<N>`` and ``table.<section>.row.<R>.col.<C>``."""
    fr = "# S\n\n| A | B |\n| --- | --- |\n| 1 | 2 |\n"
    csvd = {
        "table.s.header.1": {"fr": "A", "en": "ENA"},
        "table.s.header.2": {"fr": "B", "en": "ENB"},
        "table.s.row.1.col.1": {"fr": "1", "en": "EN1"},
        "table.s.row.1.col.2": {"fr": "2", "en": "EN2"},
    }
    tokens, stats, _ = _walk_tokens(fr, csvd)
    assert stats.get("n_translated", 0) == 4
    out = _render_tokens_to_markdown(tokens, csvd, "en", ["s"])
    assert "| ENA | ENB |" in out
    assert "| EN1 | EN2 |" in out


def test_walk_render_h2_does_not_reset_section_observed_asymmetry():
    """OBSERVED ASYMMETRY (flagged for review, not fixed here).

    ``sync.parse_markdown`` scopes a paragraph to its **h2** section (the key
    for "Under sub." is ``sub.para1``), but ``render._walk_translate`` only
    updates ``section`` on an **h1** — so the same paragraph is looked up as
    ``main.para2`` on the render side. Consequently an h2-scoped translation
    stored in the CSV under ``sub.para1`` is NOT found by render, which falls
    back to FR. The existing round-trip test (gate 10, cell-count only) and
    the fallback test (gate 11, all-empty EN) both pass regardless and do not
    surface this. This assertion pins the CURRENT behaviour; it would flip if
    the asymmetry is reconciled (a separate fix, not this PR's subject).
    """
    fr = "# Main\n\nIntro.\n\n## Sub\n\nUnder sub.\n"
    # sync-side key for "Under sub." :
    sync_keys = [c.key for c in parse_markdown(fr).cells if c.kind == "p"]
    assert "sub.para1" in sync_keys, "sync must produce an h2-scoped key"
    # render-side : section stays the h1 slug, and the sub.para1 translation is
    # never consumed (render looks up main.<N>, finds nothing, falls back to FR).
    tokens, stats, section = _walk_tokens(
        fr, {"sub.para1": {"fr": "Under sub.", "en": "SHOULD_APPLY"}})
    assert section == "main", "h2 must NOT have updated the carried-over section"
    out = _render_tokens_to_markdown(tokens, {}, "en", [section])
    assert "SHOULD_APPLY" not in "\n".join(out), (
        "the h2-scoped EN translation leaked through — asymmetry may have been fixed")


# --- _render_tokens_to_markdown : 8 token-type emission ------------------ #
def test_render_emits_heading_with_level_hashes():
    """A heading token emits ``#`` * level, with blank lines around it."""
    fr = "# H1\n\nText.\n\n## H2\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert "# H1" in out
    assert "## H2" in out
    assert out[0] == "# H1"  # heading first, no leading blank


def test_render_emits_blockquote_with_gt_prefix():
    """A blockquote emits a ``> ``-prefixed line.

    NOTE (observed limitation, flagged): ``_extract_text`` flattens the quote's
    inline children WITHOUT preserving inter-line newlines, so a multi-line
    blockquote (``> line one\\n> line two``) collapses to a single concatenated
    string (``line oneline two``) and renders as ONE ``> `` line rather than
    two. This pins the current behaviour; the multiline structure is lost in
    extraction. (Distinct from the h2-section asymmetry surfaced above.)
    """
    fr = "# S\n\n> line one\n> line two\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", ["s"])
    quote_lines = [ln for ln in out if ln.startswith("> ")]
    assert quote_lines == ["> line oneline two"]


def test_render_emits_unordered_list_with_dash():
    """Unordered list items get a ``-`` prefix."""
    fr = "- a\n- b\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert "- a" in out and "- b" in out


def test_render_emits_ordered_list_with_number_dot():
    """Ordered list items get a ``N.`` prefix (1-based)."""
    fr = "1. first\n2. second\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert "1. first" in out and "2. second" in out


def test_render_list_item_emits_single_dash_prefix():
    """A single-line list item emits one ``- <text>`` line.

    NOTE: the emitter's multiline-continuation branch (``for j, line in
    enumerate(text.splitlines())``) is effectively unreachable through the real
    pipeline because ``_extract_text`` flattens list-item children to a single
    newline-free string. A list item therefore always renders as one line here.
    """
    fr = "- only line\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert "- only line" in out
    # Exactly one item line, no spurious continuation.
    assert sum(1 for ln in out if ln.startswith("- ")) == 1


def test_render_emits_table_with_separator_row():
    """A table emits header, a ``| --- | --- |`` separator, then body rows."""
    fr = "# S\n\n| A | B |\n| --- | --- |\n| 1 | 2 |\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", ["s"])
    assert "| A | B |" in out
    assert "| --- | --- |" in out
    assert "| 1 | 2 |" in out


def test_render_emits_block_code_fence():
    """A fenced code block emits opening fence + raw + closing fence.

    NOTE (observed limitation, flagged): mistune 3.x stores the fence language
    under ``attrs.info`` (e.g. ``{'info': 'python'}``), but the emitter reads
    ``tok.get("info", "")`` — the top-level field, which is ``None`` — so the
    language hint is DROPPED in the rendered output (```` ```python ```` becomes
    a bare ```` ``` ````). This pins the current behaviour; surfacing for review.
    """
    fr = "```python\nprint(1)\n```\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    joined = "\n".join(out)
    assert "```" in out  # opening + closing fences present
    assert "print(1)" in joined
    # Pin the limitation: the language is NOT preserved on output.
    assert "```python" not in joined


def test_render_emits_thematic_break():
    """A thematic break emits ``---``."""
    fr = "# S\n\n---\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", ["s"])
    assert "---" in out


def test_render_inserts_blank_line_between_blocks():
    """Two consecutive paragraphs are separated by a blank line (CommonMark spacing)."""
    fr = "# H\n\nPara one.\n\nPara two.\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert "Para one." in out and "Para two." in out
    # A blank line separates them.
    i1 = out.index("Para one.")
    assert out[i1 + 1] == "", "blank line must follow the first paragraph"


def test_render_strips_trailing_blank_lines():
    """The emitter strips trailing empty lines for clean output."""
    fr = "# H\n\nText.\n"
    tokens, _, _ = _walk_tokens(fr, {})
    out = _render_tokens_to_markdown(tokens, {}, "en", [""])
    assert out[-1] != "", "no trailing blank line"
    assert out[-1] == "Text."
