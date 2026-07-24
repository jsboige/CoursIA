#!/usr/bin/env python3
"""Detect markdown-rendering defects in Jupyter notebooks.

Motivation
----------
Agents reviewing or creating notebooks cannot render markdown in their heads, so a
whole class of *rendering* regressions slips through review unseen. Two concrete
families have repeatedly shipped to `main`:

1. **YAML frontmatter dumped into a rendered markdown cell** (the "cost frontmatter"
   / `cell-header` pattern, epic #8056). A markdown cell whose source is::

       ---
       title: "..."
       cost:
         api_usd_est: 0.00   # ...
       ---

   renders *badly*: markdown-it (VSCode / JupyterLab / nbviewer) treats the leading
   `---` as an `<hr>`, joins every `key: value` line into one run-on paragraph, and —
   because the **closing `---` directly follows a text line with no blank line** — parses
   `<paragraph>\n---` as a **setext H2 heading**, promoting the entire YAML block to one
   oversized title-sized text block. Ugly on first open.

2. **Oversized hints / asides**: exercise hints ("Indice", "Astuce", "Hint") that
   should be among the *smallest* text in a notebook, written as an H1/H2/H3 header
   (`# Indice`) so they render larger than the notebook title.

This script combs every notebook deterministically so the whole 800+ corpus is checked
at once instead of one notebook at a time.

Rules
-----
- ``frontmatter_supersize``  (ERROR): markdown cell = YAML frontmatter block whose closing
  ``---``/``===`` is a setext underline (no blank line before it) -> oversized H2 block.
- ``frontmatter_rawyaml``    (ERROR): markdown cell = YAML frontmatter block that does not
  supersize but still dumps raw ``key: value`` metadata as body text (unformatted).
- ``setext_oversized``       (ERROR): NON-frontmatter markdown cell where a long paragraph
  (>60 chars or multi-line, containing prose punctuation) is underlined by ``---``/``===``,
  accidentally promoted to an oversized heading.
- ``oversized_hint``         (WARN):  a hint/indice/astuce/note line written as an
  ``#``/``##``/``###`` header (renders larger than surrounding text).

The correct fix for frontmatter cells is to move the metadata into the notebook
``metadata`` (invisible, machine-readable) OR render it inside a fenced ```yaml block
OR as a small formatted markdown table. This script does NOT auto-fix — the target
formatting is a per-family editorial choice.

Baseline
--------
The corpus already carries ~520 pre-existing frontmatter violations. To introduce the
guard without blocking every unrelated PR, ``--check`` compares against a committed
baseline (``--baseline``) and fails only on **new** violations (keyed by a content hash
that is stable across cell reordering). Run ``--update-baseline`` after a remediation
batch to burn down the baseline.

Usage
-----
    python scripts/notebook_tools/detect_markdown_rendering.py --report
    python scripts/notebook_tools/detect_markdown_rendering.py --json
    python scripts/notebook_tools/detect_markdown_rendering.py --check --baseline scripts/notebook_tools/markdown_rendering_baseline.json
    python scripts/notebook_tools/detect_markdown_rendering.py --update-baseline --baseline scripts/notebook_tools/markdown_rendering_baseline.json
    python scripts/notebook_tools/detect_markdown_rendering.py --check path/to/one.ipynb   # ad-hoc, no baseline
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

# ------------------------------------------------------------------ severities
ERROR = "error"
WARN = "warn"

RULE_SEVERITY = {
    "frontmatter_supersize": ERROR,
    "frontmatter_rawyaml": ERROR,
    "setext_oversized": ERROR,
    "oversized_hint": WARN,
}

# a line that is *only* dashes/equals of length >= 3 (setext underline / thematic break)
_SETEXT_RE = re.compile(r"^\s{0,3}(-{3,}|={3,})\s*$")
_YAML_KV_RE = re.compile(r"^\s*[A-Za-z_][\w .\-]*:\s?(\S.*)?$")
# exercise-hint keywords, word-boundary. Deliberately NOT "note"/"remarque"
# (those are legitimate section headings, not the oversized-hint defect).
_HINT_RE = re.compile(r"\b(indice|indices|astuce|astuces|hint|hints)\b", re.IGNORECASE)
_HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+(.*)$")


def _as_text(source) -> str:
    if isinstance(source, list):
        return "".join(source)
    return source or ""


def _nonblank(lines):
    return [ln for ln in lines if ln.strip() != ""]


def _cell_hash(rule: str, text: str) -> str:
    """Content-stable key: (rule, normalized-source) so it survives cell reordering."""
    norm = "\n".join(ln.rstrip() for ln in text.strip().splitlines())
    return hashlib.sha1(f"{rule}\0{norm}".encode("utf-8")).hexdigest()[:16]


def _is_frontmatter_block(lines) -> bool:
    """True if the cell is a `---\\n ... \\n---` YAML frontmatter block.

    Requires (a) the leading non-blank line is ``---``, (b) a later non-blank line
    is also ``---``, and (c) the line *immediately* after the opening fence is
    non-blank. Condition (c) distinguishes real YAML frontmatter (content starts
    right after ``---``) from a thematic-break section divider (``---\\n\\n### H``),
    which is legitimate markdown and must NOT be flagged. Without (c), any prose
    section sandwiched between two ``---`` hr lines with two colon-bearing phrases
    (e.g. FR prose ``affiche :``) was misclassified as ``frontmatter_rawyaml``.
    """
    nz = _nonblank(lines)
    if not nz:
        return False
    if nz[0].strip() != "---":
        return False
    if not any(ln.strip() == "---" for ln in nz[1:]):
        return False
    # Locate the opening fence in the raw lines; the very next raw line must carry
    # content (YAML frontmatter never has a blank line right after the opening ---).
    for i, ln in enumerate(lines):
        if ln.strip() == "---":
            if i + 1 >= len(lines) or lines[i + 1].strip() == "":
                return False
            break
    return True


def _frontmatter_supersizes(lines) -> bool:
    """A setext underline whose IMMEDIATELY-preceding line is text -> oversized H2.

    CommonMark: a setext heading underline must be on the line directly after the
    paragraph. A blank line before ``---`` makes it a thematic break (``<hr>``), which
    renders fine — so we require ``lines[j-1]`` to be non-blank, no blank-skipping.
    """
    for j in range(1, len(lines)):
        if _SETEXT_RE.match(lines[j]):
            prev = lines[j - 1].strip()
            if prev and prev != "---" and not prev.startswith("#") and not _SETEXT_RE.match(lines[j - 1]):
                return True
    return False


def _looks_like_prose(text: str) -> bool:
    """Heuristic: multi-line, or long, or sentence-punctuated — not a legit short title."""
    t = text.strip()
    if "\n" in t:
        return True
    if len(t) > 60:
        return True
    # a real title rarely ends with a period / contains multiple sentences
    return t.count(".") >= 1 and len(t.split()) >= 8


def scan_cell(cell) -> list[dict]:
    """Return a list of findings (dicts without file/index) for one markdown cell."""
    if cell.get("cell_type") != "markdown":
        return []
    text = _as_text(cell.get("source"))
    if not text.strip():
        return []
    lines = text.split("\n")
    findings: list[dict] = []

    # ---- frontmatter-in-markdown ------------------------------------------------
    if _is_frontmatter_block(lines):
        nz = _nonblank(lines)
        yamlish = sum(1 for ln in nz[1:] if ln.strip() != "---" and _YAML_KV_RE.match(ln))
        if yamlish >= 2:
            if _frontmatter_supersizes(lines):
                rule = "frontmatter_supersize"
                msg = "YAML frontmatter in a markdown cell renders as one oversized H2 block (setext)"
            else:
                rule = "frontmatter_rawyaml"
                msg = "YAML frontmatter dumped as raw text in a markdown cell (unformatted)"
            findings.append({
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": msg,
                "evidence": nz[1].strip()[:100] if len(nz) > 1 else "---",
                "hash": _cell_hash(rule, text),
            })
            return findings  # a frontmatter cell is fully described; don't double-report setext

    # ---- accidental setext oversize (non-frontmatter prose underlined by ---) ----
    # A setext heading forms ONLY when the text line is IMMEDIATELY before the '---'
    # (no blank line between). `paragraph.\n\n---` is a thematic break and renders fine.
    for j in range(1, len(lines)):
        if _SETEXT_RE.match(lines[j]):
            k = j - 1
            if k < 0:
                continue
            prev = lines[k].strip()
            if not prev or prev.startswith("#") or _SETEXT_RE.match(lines[k]):
                continue
            # gather the paragraph promoted to heading (contiguous text lines above)
            p = k
            while p - 1 >= 0 and lines[p - 1].strip() != "" and not _SETEXT_RE.match(lines[p - 1]):
                p -= 1
            para = "\n".join(l.strip() for l in lines[p:k + 1])
            if _looks_like_prose(para):
                rule = "setext_oversized"
                findings.append({
                    "rule": rule,
                    "severity": RULE_SEVERITY[rule],
                    "message": "prose paragraph underlined by '---'/'===' renders as an oversized heading",
                    "evidence": para.replace("\n", " ")[:100],
                    "hash": _cell_hash(rule, text),
                })
                break  # one per cell is enough

    # ---- oversized hint (hint keyword as a heading) ------------------------------
    for ln in lines:
        m = _HEADING_RE.match(ln)
        if not m:
            continue
        level = len(m.group(1))
        head_text = m.group(2)
        if level <= 3 and _HINT_RE.search(head_text):
            rule = "oversized_hint"
            findings.append({
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": f"hint/aside written as an H{level} heading (renders larger than body text)",
                "evidence": ln.strip()[:100],
                "hash": _cell_hash(rule, text),
            })
            break

    return findings


def scan_notebook(path: Path) -> list[dict]:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 - report unreadable, don't crash the sweep
        return [{
            "file": str(path), "cell": -1, "rule": "unreadable",
            "severity": WARN, "message": f"cannot parse notebook: {exc}",
            "evidence": "", "hash": "",
        }]
    out: list[dict] = []
    for i, cell in enumerate(nb.get("cells", [])):
        for f in scan_cell(cell):
            f = dict(f)
            f["file"] = str(path).replace("\\", "/")
            f["cell"] = i
            out.append(f)
    return out


def gather(root: Path) -> list[dict]:
    if root.is_file() and root.suffix == ".ipynb":
        return scan_notebook(root)
    findings: list[dict] = []
    for p in sorted(root.rglob("*.ipynb")):
        if ".ipynb_checkpoints" in p.parts:
            continue
        findings.extend(scan_notebook(p))
    return findings


def load_baseline(path: Path) -> set[str]:
    if not path.exists():
        return set()
    data = json.loads(path.read_text(encoding="utf-8"))
    return set(data.get("hashes", []))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("root", nargs="?", default="MyIA.AI.Notebooks",
                    help="notebook file or directory to scan (default: MyIA.AI.Notebooks)")
    ap.add_argument("--check", action="store_true", help="exit 1 if any (new) ERROR is found")
    ap.add_argument("--report", action="store_true", help="human-readable listing")
    ap.add_argument("--json", action="store_true", help="machine-readable JSON output")
    ap.add_argument("--baseline", type=Path, default=None,
                    help="baseline JSON of known violations; --check fails only on NEW ones")
    ap.add_argument("--update-baseline", action="store_true",
                    help="write the current violation set to --baseline and exit")
    ap.add_argument("--severity", choices=[ERROR, WARN], default=None,
                    help="restrict output to this severity")
    args = ap.parse_args(argv)

    root = Path(args.root)
    if not root.exists():
        print(f"error: path not found: {root}", file=sys.stderr)
        return 2

    findings = gather(root)
    if args.severity:
        findings = [f for f in findings if f["severity"] == args.severity]

    # ---- update baseline --------------------------------------------------------
    if args.update_baseline:
        if not args.baseline:
            print("error: --update-baseline requires --baseline PATH", file=sys.stderr)
            return 2
        hashes = sorted({f["hash"] for f in findings if f["hash"]})
        payload = {
            "_comment": "Baseline of known markdown-rendering violations. Burn down, do not grow. "
                        "Regenerate with: python scripts/notebook_tools/detect_markdown_rendering.py "
                        "--update-baseline --baseline <this file>",
            "count": len(hashes),
            "hashes": hashes,
        }
        args.baseline.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"baseline written: {len(hashes)} violations -> {args.baseline}")
        return 0

    baseline = load_baseline(args.baseline) if args.baseline else set()
    new_findings = [f for f in findings if f["hash"] not in baseline] if baseline else findings

    # ---- output -----------------------------------------------------------------
    if args.json:
        print(json.dumps({
            "total": len(findings),
            "new": len(new_findings),
            "baseline_size": len(baseline),
            "findings": findings,
        }, indent=2))
    elif args.report or not args.check:
        by_rule: dict[str, int] = {}
        for f in findings:
            by_rule[f["rule"]] = by_rule.get(f["rule"], 0) + 1
        print(f"scanned: {root}")
        print(f"violations: {len(findings)} total"
              + (f" ({len(new_findings)} new vs baseline of {len(baseline)})" if baseline else ""))
        for rule in sorted(by_rule):
            print(f"  {RULE_SEVERITY.get(rule, '?'):>5} {rule}: {by_rule[rule]}")
        shown = new_findings if baseline else findings
        print()
        for f in shown[:200]:
            flag = "NEW " if (baseline and f["hash"] not in baseline) else ""
            print(f"  {flag}{f['severity'].upper():>5} {f['file']} cell#{f['cell']} [{f['rule']}]")
            print(f"        {f['evidence']}")
        if len(shown) > 200:
            print(f"  ... {len(shown) - 200} more")

    # ---- exit code --------------------------------------------------------------
    if args.check:
        blocking = [f for f in new_findings if f["severity"] == ERROR]
        if blocking:
            print(f"\nFAIL: {len(blocking)} new ERROR-level markdown-rendering violation(s).",
                  file=sys.stderr)
            for f in blocking[:50]:
                print(f"  {f['file']} cell#{f['cell']} [{f['rule']}] {f['evidence']}", file=sys.stderr)
            return 1
        print("OK: no new ERROR-level markdown-rendering violations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
