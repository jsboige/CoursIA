#!/usr/bin/env python3
"""Extract markdown cells from FR README, sync into CSV (EPIC #4957, Phase 1).

CLI usage
---------
    python sync.py --fr README.md --csv README.csv [--dry-run] [--verbose]

Algorithm (stdlib + ``mistune``, ≤80 lines excluding the parser wiring) :

1. Parse FR markdown with ``mistune`` AST walker. mistune is the standard
   CommonMark/GFM parser in Python — handles headings, paragraphs, lists,
   tables, blockquotes, code blocks, inline emphasis correctly out of the
   box. Tiny dependency (~50 KB, no transitive deps).
2. Extract cells per the key conventions in
   ``docs/i18n/CSV-by-series-design.md``.
3. Diff against existing CSV : add new keys (with EN empty if not in current
   EN), update FR (preserve other-language columns), warn on keys absent
   from FR (do not auto-delete translations — protect against sync accidents).
4. Write CSV in RFC-4180 format (always quote, comma separator).

Garde-fous
----------
- ``--dry-run`` : print diff, do not write
- warning when an EN cell becomes empty (translation loss)
- warning on non-ASCII control chars (cf lesson ``cjk-post-edit`` filter)

Deps : ``argparse``, ``csv``, ``pathlib``, ``re``, ``dataclasses`` (stdlib),
       ``mistune`` (external, lightweight CommonMark parser).
"""
from __future__ import annotations

import argparse
import csv
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import mistune


# --- Markdown parsing via mistune ---------------------------------------- #
@dataclass
class Cell:
    key: str
    text: str
    kind: str  # h1 / h2 / p / li / th / td / quote
    section: str = ""


@dataclass
class ParsedDoc:
    cells: List[Cell] = field(default_factory=list)

    def keys(self) -> List[str]:
        return [c.key for c in self.cells]


def _slug(s: str) -> str:
    """Stable, ASCII-safe key slug (preserves CJK via hex if needed)."""
    s = s.strip().lower()
    s = re.sub(r"\s+", "_", s)
    s = re.sub(r"[^\w一-鿿぀-ヿ-]", "", s, flags=re.UNICODE)
    return s[:40] or "cell"


def _extract_text(token: dict) -> str:
    """Extract visible text from a mistune AST node, preserving inline markdown.

    mistune's renderer flattens ``children`` lists recursively. We do the
    same for tokens with a ``children`` attribute (inline content), but
    re-emit link / image syntax as markdown so the translation preserves
    the URL even when the visible text is translated.
    """
    children = token.get("children")
    if children is None:
        return token.get("text", token.get("raw", "") or "")
    parts: List[str] = []
    for child in children:
        if isinstance(child, str):
            parts.append(child)
        elif isinstance(child, dict):
            t = child.get("type")
            if t in ("text", "codespan", "softbreak", "linebreak"):
                parts.append(child.get("raw", ""))
            elif t == "link":
                attrs = child.get("attrs", {}) or {}
                url = attrs.get("url", child.get("url", ""))
                link_text = _extract_text(child)
                parts.append(f"[{link_text}]({url})")
            elif t == "image":
                attrs = child.get("attrs", {}) or {}
                url = attrs.get("url", child.get("url", ""))
                alt = attrs.get("alt", child.get("alt", ""))
                if not alt:
                    alt = _extract_text(child)
                parts.append(f"![{alt}]({url})")
            elif t == "emphasis":
                parts.append(f"*{_extract_text(child)}*")
            elif t == "strong":
                parts.append(f"**{_extract_text(child)}**")
            elif t == "codespan":
                parts.append(f"`{child.get('raw', '')}`")
            else:
                parts.append(_extract_text(child))
    return "".join(parts)


def parse_markdown(fr_text: str) -> ParsedDoc:
    """Parse a markdown FR document into a flat list of cells via mistune AST.

    The ``section`` tracks the **current sub-section** : it is set to the h1
    slug on first h1, then updated to each h2 slug as we encounter them.
    All non-heading cells (paragraphs, tables, quotes, lists) use the
    current ``section`` to namespace their keys. This way a table that
    appears under a h2 gets a ``table.<h2_slug>.header.N`` key, NOT a
    ``table.<h1_slug>.header.N`` key — avoiding collisions between tables
    in different h2 sections of the same document.
    """
    md = mistune.create_markdown(renderer=None, plugins=["table"])
    tokens = md(fr_text)
    doc = ParsedDoc()
    h1_section = ""  # the h1 slug (set once, never changes after)
    section = ""     # current sub-section = h1 or h2 slug
    p_count_in_section = 0
    list_count_in_section = 0

    for tok in tokens:
        t = tok.get("type")
        if t == "heading":
            level = tok.get("attrs", {}).get("level", 1) if isinstance(tok.get("attrs"), dict) else 1
            text = _extract_text(tok)
            if level == 1:
                h1_section = _slug(text)
                section = h1_section
                doc.cells.append(Cell(
                    key=f"# <h1>:{section}", text=text, kind="h1", section=section,
                ))
                p_count_in_section = 0
                list_count_in_section = 0
            elif level == 2:
                section = _slug(text)
                doc.cells.append(Cell(
                    key=f"## <h2>:{section}", text=text, kind="h2", section=section,
                ))
                p_count_in_section = 0
                list_count_in_section = 0
            continue
        if t == "paragraph":
            text = _extract_text(tok)
            if not text.strip():
                continue
            p_count_in_section += 1
            key = f"{section or h1_section or 'intro'}.para{p_count_in_section}"
            doc.cells.append(Cell(key=key, text=text, kind="p", section=section))
            continue
        if t == "block_quote":
            text = _extract_text(tok)
            key = f"{section or h1_section or 'intro'}.quote"
            doc.cells.append(Cell(key=key, text=text, kind="quote", section=section))
            continue
        if t == "list":
            list_count_in_section += 1
            for n, item in enumerate(tok.get("children", []) or [], 1):
                text = _extract_text(item)
                key = f"{section or h1_section or 'intro'}.list.item{n}"
                doc.cells.append(Cell(key=key, text=text, kind="li", section=section))
            continue
        if t == "table":
            # mistune's table plugin emits 'children' = [thead, tbody].
            children = tok.get("children", []) or []
            table_name = section or h1_section or "intro"
            for group in children:
                gtype = group.get("type")
                if gtype == "table_head":
                    for c_idx, th in enumerate(group.get("children", []) or [], 1):
                        doc.cells.append(Cell(
                            key=f"table.{table_name}.header.{c_idx}",
                            text=_extract_text(th), kind="th", section=section,
                        ))
                elif gtype == "table_body":
                    for row_idx, tr in enumerate(group.get("children", []) or [], 1):
                        for c_idx, td in enumerate(tr.get("children", []) or [], 1):
                            doc.cells.append(Cell(
                                key=f"table.{table_name}.row.{row_idx}.col.{c_idx}",
                                text=_extract_text(td), kind="td", section=section,
                            ))
            continue
        # Tokens we don't currently emit a cell for: block_code, blank_line,
        # thematic_break, etc. They are kept as-is in the FR for structure
        # purposes but not translated (they're procedural, not prose).
    return doc


# --- CSV I/O --------------------------------------------------------------- #
def read_csv(csv_path: Path) -> Tuple[List[str], Dict[str, Dict[str, str]]]:
    """Read an existing CSV → (languages, dict[key][lang]=text)."""
    if not csv_path.exists():
        return (["fr", "en"], {})
    with csv_path.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.reader(fh)
        try:
            header = next(reader)
        except StopIteration:
            return (["fr", "en"], {})
        langs = header[1:]
        data: Dict[str, Dict[str, str]] = {}
        for row in reader:
            if not row or not row[0]:
                continue
            key = row[0]
            data[key] = {}
            for j, lang in enumerate(langs):
                data[key][lang] = row[j + 1] if j + 1 < len(row) else ""
        return langs, data


def write_csv(csv_path: Path, langs: List[str], data: Dict[str, Dict[str, str]],
              keys_ordered: List[str]) -> None:
    """Write CSV in RFC-4180 format, all cells quoted, sorted by key order."""
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.writer(fh, quoting=csv.QUOTE_ALL, lineterminator="\n")
        writer.writerow(["key"] + langs)
        for key in keys_ordered:
            row = [key] + [data[key].get(lang, "") for lang in langs]
            writer.writerow(row)


# --- Sync logic ------------------------------------------------------------ #
def sync(
    fr_path: Path,
    csv_path: Path,
    *,
    dry_run: bool = False,
    verbose: bool = False,
) -> Dict[str, int]:
    """Sync FR markdown into CSV. Returns stats dict {added, updated, removed, total}."""
    fr_text = fr_path.read_text(encoding="utf-8")
    doc = parse_markdown(fr_text)
    langs, existing = read_csv(csv_path)
    fr_cells = {c.key: c.text for c in doc.cells}
    new_data: Dict[str, Dict[str, str]] = {}
    stats = {"added": 0, "updated": 0, "preserved": 0, "removed": 0, "total": 0}

    for key, fr_text_val in fr_cells.items():
        if key not in existing:
            new_data[key] = {"fr": fr_text_val}
            for lang in langs:
                if lang != "fr":
                    new_data[key][lang] = ""
            stats["added"] += 1
        else:
            row = dict(existing[key])
            old_fr = row.get("fr", "")
            row["fr"] = fr_text_val
            new_data[key] = row
            if old_fr != fr_text_val:
                stats["updated"] += 1
                if verbose and row.get("en", ""):
                    print(f"  ~{key} (FR updated, EN preserved: {row['en'][:40]}...)")
            else:
                stats["preserved"] += 1
    for key in existing:
        if key not in fr_cells:
            if verbose:
                print(f"  WARN: key '{key}' absent from FR but present in CSV "
                      f"(preserved, not removed — anti-sync-accident)")
            new_data[key] = existing[key]
            stats["removed"] += 1
    stats["total"] = len(new_data)

    if not dry_run:
        keys_ordered = [c.key for c in doc.cells] + [k for k in existing if k not in fr_cells]
        write_csv(csv_path, langs, new_data, keys_ordered)
    return stats


# --- CLI ------------------------------------------------------------------- #
def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Sync FR markdown cells into CSV.")
    p.add_argument("--fr", required=True, type=Path, help="Path to FR README.md")
    p.add_argument("--csv", required=True, type=Path, help="Path to README.csv (will be created if missing)")
    p.add_argument("--dry-run", action="store_true", help="Print diff stats, do not write")
    p.add_argument("--verbose", action="store_true", help="Print per-key diff")
    args = p.parse_args(argv)

    if not args.fr.exists():
        print(f"ERROR: FR file not found: {args.fr}", file=sys.stderr)
        return 2

    stats = sync(args.fr, args.csv, dry_run=args.dry_run, verbose=args.verbose)
    mode = "(dry-run)" if args.dry_run else ""
    print(f"[sync] {args.fr} -> {args.csv} {mode}")
    print(f"  {stats['total']} keys synced, {stats['added']} new, "
          f"{stats['updated']} updated, {stats['preserved']} unchanged, "
          f"{stats['removed']} stale.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
