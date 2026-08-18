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
- ``source_list_missing_newlines`` (ERROR): markdown cell whose ``source`` lost the
  ``\n`` that its structure implies. Two manifestations of the same newline-stripping
  artifact, both caught here BEFORE ``_as_text`` joins the list verbatim (which would
  collapse the cell to one giant line and leave every downstream line-based rule with no
  structure to inspect -> silent 0-violation pass on a cell that renders as a single
  malformed block):
  - **multi-element** (N>=2 elements, fewer ``\n`` than the element count implies — e.g.
    N elements, 0 ``\n``). The original #10397 case (#10423).
  - **single-element** (``len(src) == 1`` string of >= 80 chars with 0 ``\n`` that starts
    with an ATX heading ``#{1,6}\\s+``). All line breaks were lost into one string, so
    the heading + body + list items are glued (``"## RésuméCe notebook"``,
    ``"profondeur**Objectif**"``) and the cell renders as one giant heading. A real ATX
    heading is a short single line, so 80+ chars / no ``\n`` / heading-start = heading
    with body glued. Exemplar: PR #10399 Argumentum_Cards cells 12/15/18 (876/1161/1085
    chars). Scoped to heading-start on purpose: legit single-line ``> blockquote`` /
    ``**bold**`` paragraphs are common and must NOT be flagged. A corpus sweep found ~43
    pre-existing single-element instances (Tweety-10, CSP-9, Planners, Lean-8) in addition
    to the multi-element ones — all baselined for burn-down.

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

# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650).
from notebook_walk import iter_notebooks  # noqa: E402

# ------------------------------------------------------------------ severities
ERROR = "error"
WARN = "warn"

RULE_SEVERITY = {
    "frontmatter_supersize": ERROR,
    "frontmatter_rawyaml": ERROR,
    "setext_oversized": ERROR,
    "oversized_hint": WARN,
    "source_list_missing_newlines": ERROR,
    "leading_dash_yaml_block": ERROR,
}

# a line that is *only* dashes/equals of length >= 3 (setext underline / thematic break)
_SETEXT_RE = re.compile(r"^\s{0,3}(-{3,}|={3,})\s*$")
# a line that is *only* dashes (>= 3): Pandoc reads a leading `---` as a
# yaml_metadata_block opener, so a markdown cell whose FIRST non-blank line is
# `---` dumps everything until the NEXT `---` (often in a later cell) as YAML.
# Non-YAML content (e.g. `**Papier** : ...`) crashes the Quarto render with
# `YAMLException`. `===` never opens a YAML block, so dashes only (#11630).
_LEADING_DASH_RE = re.compile(r"^\s{0,3}-{3,}\s*$")
# a fenced-code marker: >=3 backticks OR tildes, optionally indented up to 3 spaces.
# A ``` / ~~~ block renders its content VERBATIM, so a `---`/`===` line inside it is
# literal text (ASCII art, a cryptarithme divider, a box-drawing rule) — NOT a setext
# underline. Without fence-awareness the setext rules flagged ~11 such cells as
# `setext_oversized` false positives (CSP cryptarithmes, Sudoku grids, Mermaid-ish
# boxes). See PR follow-up to #8392 (same precision vein, different FP family).
_FENCE_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")
_YAML_KV_RE = re.compile(r"^\s*[A-Za-z_][\w .\-]*:\s?(\S.*)?$")
# exercise-hint keywords, word-boundary. Deliberately NOT "note"/"remarque"
# (those are legitimate section headings, not the oversized-hint defect).
_HINT_RE = re.compile(r"\b(indice|indices|astuce|astuces|hint|hints)\b", re.IGNORECASE)
_HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+(.*)$")

# single-element newline-stripping artifact: a markdown cell whose `source` is a
# one-element list whose string has 0 '\n', starts with an ATX heading, and is long.
# A real ATX heading is a short single line; 80+ chars / no '\n' / heading-start =
# heading + body content glued (all newlines lost into one string). See #10397
# single-element case, exemplar PR #10399.
_COLLAPSED_HEADING_START_RE = re.compile(r"^\s{0,3}#{1,6}\s+\S")
_COLLAPSED_SINGLE_MIN_LEN = 80


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


def _leading_dash_yaml_block(lines) -> bool:
    """True if the FIRST non-blank line is ``---`` (>= 3 dashes) followed by content.

    Pandoc opens a ``yaml_metadata_block`` only when the opening ``---`` is IMMEDIATELY
    followed by a non-blank line; ``---`` alone or followed by a blank line is a
    thematic break and renders fine. A head-dash + content cell starts a YAML block
    that closes only at the NEXT ``---`` in the document — typically the head-dash of a
    LATER cell — so non-YAML content between the dashes crashes the Quarto render
    (``YAMLException: unidentified alias ...``). Matches the #11629 defect shape
    (head-dash + non-blank successor), measured across the render closure (#11630).
    """
    for i, ln in enumerate(lines):
        if ln.strip() == "":
            continue
        if not _LEADING_DASH_RE.match(ln):
            return False
        return i + 1 < len(lines) and lines[i + 1].strip() != ""
    return False


def _inside_fence_lines(lines) -> set[int]:
    """Indices of lines that fall INSIDE a fenced-code block (verbatim, non-rendered).

    CommonMark fenced code: a marker line of >=3 backticks or tildes (indent <=3)
    opens a block; a later marker line of the SAME fence char with length >= the
    opening closes it. Lines strictly between the two markers (exclusive of both) are
    "inside" and render verbatim — so any ``---``/``===`` there is literal text, never a
    setext underline. Backtick and tilde fences are independent: a tilde line never
    closes a backtick block (and vice-versa). An unclosed fence leaves every subsequent
    line inside (defensive: prefer a false-negative on setext over a false-positive).
    """
    inside: set[int] = set()
    in_fence = False
    fence_char = None
    fence_len = 0
    for i, ln in enumerate(lines):
        m = _FENCE_RE.match(ln)
        if m:
            marker = m.group(1)
            ch, ln_len = marker[0], len(marker)
            if not in_fence:
                in_fence, fence_char, fence_len = True, ch, ln_len
                continue  # opening marker line itself is NOT inside
            elif ch == fence_char and ln_len >= fence_len:
                in_fence, fence_char, fence_len = False, None, 0
                continue  # closing marker line is NOT inside
            # a fence marker of the *other* char inside an open block is literal text
        if in_fence:
            inside.add(i)
    return inside


def _frontmatter_supersizes(lines, fenced: set[int] | None = None) -> bool:
    """A setext underline whose IMMEDIATELY-preceding line is text -> oversized H2.

    CommonMark: a setext heading underline must be on the line directly after the
    paragraph. A blank line before ``---`` makes it a thematic break (``<hr>``), which
    renders fine — so we require ``lines[j-1]`` to be non-blank, no blank-skipping.
    ``fenced`` carries the code-fence line indices (see ``_inside_fence_lines``): a
    ``---``/``===`` line inside a verbatim code block is literal text, not a setext
    underline, so it is skipped.
    """
    fenced = fenced or set()
    for j in range(1, len(lines)):
        if j in fenced:
            continue
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
    # ---- list-source without newlines (#10397) -----------------------------------
    # A markdown cell whose `source` is a list of N>=2 elements but carries fewer
    # '\n' than the element count implies collapses to one giant line when joined:
    # all structure (headings, paragraphs, frontmatter) is lost, the cell renders
    # as a single malformed block, and every downstream line-based rule sees one
    # line -> silent 0-violation pass. Catch the structural loss BEFORE the
    # line-based rules reason on the collapsed text.
    src = cell.get("source")
    if isinstance(src, list) and len(src) >= 2:
        nonblank_elems = [s for s in src if s.strip()]
        expected_breaks = max(0, len(nonblank_elems) - 1)
        actual_breaks = text.count("\n")
        if actual_breaks < expected_breaks and len(text.strip()) >= 40:
            rule = "source_list_missing_newlines"
            return [{
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": (f"markdown cell source is a list of {len(src)} elements with "
                            f"{actual_breaks} '\\n' (renders as {actual_breaks + 1} line(s) "
                            f"instead of ~{expected_breaks + 1}); line structure lost on join"),
                "evidence": text.strip()[:100],
                "hash": _cell_hash(rule, text),
            }]
    elif isinstance(src, list) and len(src) == 1:
        # single-element newline-stripping artifact: the whole cell is one string whose
        # '\n' were all lost. A legit single-line ATX heading is short; >=80 chars with
        # 0 '\n' and a heading-start = heading + body glued -> renders as one giant
        # heading. Heading-start scoping avoids FP on legit single-line `>`/`**` cells.
        single = src[0]
        if ("\n" not in single and len(single.strip()) >= _COLLAPSED_SINGLE_MIN_LEN
                and _COLLAPSED_HEADING_START_RE.match(single)):
            rule = "source_list_missing_newlines"
            return [{
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": (f"markdown cell source is a single-element list of {len(single)} "
                            f"chars with no '\\n' (heading + body collapsed into one string, "
                            f"renders as a giant heading); line structure lost"),
                "evidence": single.strip()[:100],
                "hash": _cell_hash(rule, text),
            }]
    lines = text.split("\n")
    # Lines inside a fenced-code block render verbatim: a `---`/`===` there is literal
    # text, not a setext underline. Computed once, reused by both setext rules.
    fenced = _inside_fence_lines(lines)
    findings: list[dict] = []

    # ---- frontmatter-in-markdown ------------------------------------------------
    if _is_frontmatter_block(lines):
        nz = _nonblank(lines)
        yamlish = sum(1 for ln in nz[1:] if ln.strip() != "---" and _YAML_KV_RE.match(ln))
        if yamlish >= 2:
            if _frontmatter_supersizes(lines, fenced):
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

    # ---- leading '---' opens a Pandoc yaml_metadata_block (#11630) --------------
    # A markdown cell whose FIRST non-blank line is `---` starts a yaml_metadata_block;
    # Pandoc keeps parsing YAML until the next `---` (cross-cell in practice). Non-YAML
    # content between the dashes -> YAMLException -> quarto render crash. The #11629 fix
    # replaced those head-dashes with `***` (a thematic break renders identically and can
    # never open a YAML block). Closure-scoped by --closure-quarto in main(): inert
    # outside the Quarto render closure (a `---` divider in Jupyter alone is harmless).
    if _leading_dash_yaml_block(lines):
        # A SELF-CONTAINED yaml_metadata_block (closing '---' in the same cell) whose
        # body is YAML-ish parses fine as document metadata -> the frontmatter branch
        # owns it. Only flag blocks whose body cannot be YAML, or that have NO closing
        # dash in the cell (cross-cell block = the #11629 render crash).
        skip = False
        if _is_frontmatter_block(lines):
            nz = _nonblank(lines)
            yamlish = sum(1 for ln in nz[1:] if ln.strip() != "---" and _YAML_KV_RE.match(ln))
            skip = yamlish >= 1
        if not skip:
            rule = "leading_dash_yaml_block"
            nz = _nonblank(lines)
            findings.append({
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": ("cell opens with '---' (Pandoc yaml_metadata_block): content until the "
                            "next '---' is parsed as YAML -> YAMLException if not valid YAML; "
                            "replace with '***'"),
                "evidence": nz[0][:100] if nz else "---",
                "hash": _cell_hash(rule, text),
            })

    # ---- accidental setext oversize (non-frontmatter prose underlined by ---) ----
    # A setext heading forms ONLY when the text line is IMMEDIATELY before the '---'
    # (no blank line between). `paragraph.\n\n---` is a thematic break and renders fine.
    for j in range(1, len(lines)):
        if j in fenced:
            continue  # `---`/`===` inside a verbatim code block is literal text
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
    # Fence-aware (parity with setext_oversized above): a hint keyword inside a
    # verbatim code block (e.g. a `# Indice :` Python comment in an exercise
    # scaffold) renders as literal code, NOT as an oversized heading -- skip it.
    for idx, ln in enumerate(lines):
        if idx in fenced:
            continue
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
    # Delegue au marcheur canonique ``notebook_walk.iter_notebooks`` (#8650) :
    # SKIP_DIRS canonique + filtre git tracked_only + filtre sur le chemin
    # RELATIF a la racine. Immunise contre la classe #8858 (l'ancien filtre
    # ``".ipynb_checkpoints" in p.parts`` sur les composants ABSOLUS faisait
    # matcher le parent du depot sous un dossier nomme ``_archive/`` /
    # ``archive/`` et reduisait le scan au silence). Single-file pass-through
    # preserved above.
    for p in iter_notebooks(root):
        findings.extend(scan_notebook(p))
    return findings


# ------------------------------------------------- Quarto render closure (#11630)
# Quarto reads a notebook either directly (it is in the _quarto.yml render-list) or
# because a RENDERED md/qmd file links to it (Quarto rewrites the link by reading the
# target notebook's metadata). Only notebooks in this closure expose their markdown
# cells to Pandoc, so leading_dash_yaml_block is scoped to it — a `---` divider in a
# notebook Jupyter renders (but Quarto never reads) is harmless.
_QUARTO_RENDER_ENTRY_RE = re.compile(r'^\s+- "([^"]+)"')
_IPYNB_LINK_RE = re.compile(r"\]\(([^)#]+\.ipynb)(?:#[^)]*)?\)")


def _quarto_render_entries(quarto_yml: Path) -> list[str]:
    """The ``project.render`` list entries of a ``_quarto.yml`` (comments skipped)."""
    entries: list[str] = []
    try:
        lines = quarto_yml.read_text(encoding="utf-8").splitlines()
    except OSError:
        return entries
    in_render = False
    for ln in lines:
        s = ln.rstrip()
        if not in_render:
            if s.strip() == "render:":
                in_render = True
            continue
        if s.strip() == "" or s.strip().startswith("#"):
            continue
        m = _QUARTO_RENDER_ENTRY_RE.match(s)
        if m:
            entries.append(m.group(1))
        else:
            break  # end of the flat render list (next YAML key)
    return entries


def _resolve_render_entry(repo_root: Path, entry: str) -> list[Path]:
    """Resolve a render-list entry (plain path or glob) to concrete files."""
    if "*" in entry:
        return [p for p in repo_root.glob(entry) if p.is_file()]
    p = repo_root / entry
    return [p] if p.is_file() else []


def compute_quarto_closure(quarto_yml: Path, repo_root: Path) -> set[str]:
    """Absolute posix paths of the notebooks Quarto reads (render-list + linked)."""
    root_res = repo_root.resolve()
    closure: set[str] = set()
    md_files: list[Path] = []
    for entry in _quarto_render_entries(quarto_yml):
        for p in _resolve_render_entry(root_res, entry):
            if p.suffix == ".ipynb":
                closure.add(p.as_posix())
            else:
                md_files.append(p)
    for md in md_files:
        try:
            text = md.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in _IPYNB_LINK_RE.finditer(text):
            target = (md.parent / m.group(1)).resolve()
            if target.is_file():
                closure.add(target.as_posix())
    return closure


def _closure_scope_findings(findings: list[dict], closure: set[str]) -> list[dict]:
    """Scope leading_dash_yaml_block to the closure; every other rule is untouched."""
    if not closure:
        return findings
    return [
        f for f in findings
        if f["rule"] != "leading_dash_yaml_block"
        or str(Path(f["file"]).resolve()).replace("\\", "/") in closure
    ]


def _selfcheck(quarto_yml: Path | None) -> int:
    """Positive control: replay the pre-#11629 state, fail if the guard misses it."""
    fails: list[str] = []
    # Exact markdown cell 3 of 02_fallacy_datasets_landscape.ipynb as of blob
    # 9b3543a27 (pre-#11629): head-dash + content, no closing dash in the cell.
    pre_fix = ("---\n### Dataset 1 — Logic / LogicClimate (Jin et al. 2022)\n\n"
               "**Papier** : Jin et al., *Logical Fallacy Detection*, Findings of EMNLP 2022 — "
               "[arXiv:2202.13758](https://arxiv.org/abs/2202.13758). Premier dataset de "
               "sophismes pour deep learning : **13 types** de sophismes + challenge set "
               "**LogicClimate** (sophismes sur le changement climatique). Repo GitHub : "
               "`causalNLP/logical-fallacy`.")
    cell = {"cell_type": "markdown", "source": pre_fix}
    if not any(f["rule"] == "leading_dash_yaml_block" for f in scan_cell(cell)):
        fails.append("positive control: pre-#11629 cell (leading '---') produced no "
                     "leading_dash_yaml_block finding")
    safe = {"cell_type": "markdown",
            "source": "### Dataset 1 — Logic / LogicClimate (Jin et al. 2022)\n\n---\n\ntexte"}
    if any(f["rule"] == "leading_dash_yaml_block" for f in scan_cell(safe)):
        fails.append("negative control: '---' NOT at cell head produced a false positive")
    divider = {"cell_type": "markdown", "source": "---"}
    if any(f["rule"] == "leading_dash_yaml_block" for f in scan_cell(divider)):
        fails.append("negative control: bare '---' divider (no content after) false-positived")
    if quarto_yml is not None and quarto_yml.exists():
        closure = compute_quarto_closure(quarto_yml, Path.cwd())
        if not closure:
            fails.append(f"closure control: {quarto_yml} produced an empty closure")
        target = (Path.cwd() / "MyIA.AI.Notebooks/FallacyDetection/02_fallacy_datasets_landscape.ipynb")
        if target.exists() and target.resolve().as_posix() not in closure:
            fails.append("closure control: FallacyDetection/02_ notebook not in Quarto closure")
    for msg in fails:
        print(f"SELFCHECK FAIL: {msg}", file=sys.stderr)
    if not fails:
        print("selfcheck OK: leading_dash_yaml_block fires on the pre-#11629 state")
    return 1 if fails else 0


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
    ap.add_argument("--closure-quarto", type=Path, default=None, metavar="QUARTO_YML",
                    help="scope the leading_dash_yaml_block rule to the Quarto render "
                         "closure (render-list notebooks + notebooks linked from rendered "
                         "md/qmd). Inert without this flag. Pass --closure-quarto _quarto.yml "
                         "on --update-baseline too, so the baseline absorbs the closure.")
    ap.add_argument("--selfcheck", action="store_true",
                    help="positive control: replay the pre-#11629 cell state and exit 1 if "
                         "the leading_dash_yaml_block rule misses it")
    args = ap.parse_args(argv)

    if args.selfcheck:
        return _selfcheck(args.closure_quarto)

    root = Path(args.root)
    if not root.exists():
        print(f"error: path not found: {root}", file=sys.stderr)
        return 2

    findings = gather(root)
    if args.closure_quarto is not None:
        closure = compute_quarto_closure(args.closure_quarto, Path.cwd())
        findings = _closure_scope_findings(findings, closure)
    else:
        # leading_dash_yaml_block is meaningful ONLY inside the Quarto render closure
        # (a `---` divider in a notebook Jupyter renders but Quarto never reads is
        # harmless) -- a repo-wide scan without --closure-quarto must not see it,
        # otherwise it cries on ~164 harmless cells and the gate gets ignored.
        findings = [f for f in findings if f["rule"] != "leading_dash_yaml_block"]
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
                        "--update-baseline --closure-quarto _quarto.yml --baseline <this file> "
                        "(--closure-quarto REQUIRED: it scopes leading_dash_yaml_block to the "
                        "Quarto render closure; without it those hashes are dropped and the next "
                        "--check --closure-quarto in CI reports them as NEW)",
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
