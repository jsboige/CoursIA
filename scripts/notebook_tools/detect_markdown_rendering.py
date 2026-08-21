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
    python scripts/notebook_tools/detect_markdown_rendering.py --selfcheck  # embedded controls, both #11630 forms
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
    "yaml_block_open_no_close": ERROR,
    "setext_oversized": ERROR,
    # Reste WARN : la regle matche aussi des titres de section LEGITIMES.
    # `### Indices` dans QC-Py-02-Platform-Fundamentals est une vraie section
    # (Principe / Objectif / Indices), pas un commentaire fuite -- la promouvoir
    # rougirait du contenu sain. Mesure du 2026-08-21 : 3 des 9 hits hors
    # baseline sont de cette forme.
    "oversized_hint": WARN,
    # #12109 : ERROR (bloquant). Un titre ATX imbrique dans une puce ou une
    # citation (`- # Indice : ...`) n'a aucun usage legitime -- il rend un <h1>
    # A L'INTERIEUR d'une puce. Mesure du 2026-08-21 sur le rendu GitHub de
    # QC-Py-26 (getComputedStyle, iframe notebooks.githubusercontent.com) :
    # 6 titres a `29.0304px`, la plus grosse police de la page, pour des
    # commentaires Python d'exercice -- alors que le meme notebook ecrit
    # ailleurs la forme saine `- \`# Indice\` : ...`.
    #
    # Cout de la promotion, mesure avant de la faire : 298 hits corpus dont
    # 289 deja baselines ; 6 vivants sur 2 notebooks, reparees dans la meme PR.
    # Le cliquet est delta (ligne ~1009 : `new_findings`), donc la dette
    # historique reste grandfathered.
    #
    # La promotion etait deja identifiee comme necessaire dans l'en-tete de
    # `.github/workflows/markdown-rendering-guard.yml` ("tracked follow-up on
    # #3966") -- et #3966 a ete FERMEE sans que le suivi soit fait. C'est ce
    # trou qui a laisse passer #12009.
    "heading_in_list": ERROR,
    "source_list_missing_newlines": ERROR,
    # #12064: ERROR (bloquant) -- the corpus measure is 1 hit / 20,576 markdown
    # cells (the true positive (A) PT_11 cell 5), reproduced by this lane. That
    # precision is what buys blocking status; a wider pattern set would need
    # its own FP re-measure first ([[handrolled-pattern-set-undercounts-silently]]
    # cuts both ways: widening silently under- AND over-counts).
    "code_stmt_in_markdown": ERROR,
}

# Reparation outillee, PAR REGLE (#12089). Le garde rougissait sans jamais nommer
# la commande qui repare : `grep -rn fix_hr_separator .github/workflows/` rendait
# zero, et chaque auteur qui tombait dessus devait la redecouvrir. Mesure du
# 2026-08-21 : 14 PRs sur 5 lanes le matin, puis 11 PRs sur 3 lanes l'apres-midi,
# toutes sur `yaml_block_open_no_close`, toutes reparees par la meme commande.
#
# La table est volontairement PARTIELLE : `fix_hr_separator.py` ne traite QUE le
# separateur `---` en tete de cellule. Les six autres regles n'ont pas de fixer
# outille, et leur absence ici EST le message — annoncer une reparation
# automatique pour une regle qui n'en a pas couterait plus cher que le silence.
RULE_REPAIR = {
    "yaml_block_open_no_close": (
        "python scripts/notebook_tools/fix_hr_separator.py --apply <notebook>"
    ),
    # #12109 : promue ERROR dans la meme PR que son fixer -- une regle bloquante
    # sans commande de reparation nommee fait redecouvrir le remede a chaque
    # auteur qui tombe dessus (c'est le constat qui a fonde cette table).
    "heading_in_list": (
        "python scripts/notebook_tools/fix_hint_headings.py --apply <notebook>"
    ),
}

# Le gating par hash de baseline rend ce rappel necessaire : le garde ne rougit
# que sur les violations NOUVELLES, mais editer une cellule deja en violation
# change son hash et la fait resurgir comme neuve. Reparer la seule tranche
# touchee laisse donc le garde rouge.
_REPAIR_SCOPE_NOTE = (
    "Lancer la reparation sur le notebook ENTIER, pas sur les seules cellules "
    "modifiees : le gating par baseline fait resurgir toute cellule en "
    "violation dont le hash a change."
)

# a line that is *only* dashes/equals of length >= 3 (setext underline / thematic break)
_SETEXT_RE = re.compile(r"^\s{0,3}(-{3,}|={3,})\s*$")
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
# Heading nested in a list item / blockquote (`- # Indice : ...`, `> # Note`,
# `1. # Astuce`, up to 3 container markers, each optionally indented). Same
# in-list blind spot as scan_md_hierarchy.py's `^`-anchored HEADING_RE: CommonMark
# renders these as real H1-H6 (giant font) while the anchored regex never sees
# them -- 1325 pre-existing hits corpus-wide, incl. the 6 unflagged ones of PR
# #11823. WARN (parity with oversized_hint): the class pre-dates the rule, the
# drift gate on new hits is #11829 sous-issue #2. See #11829.
_CONTAINER_HEADING_RE = re.compile(
    r"^(?:[ \t]*(?:[-*+]|\d+[.)]|>)[ \t]+){1,3}(#{1,6})\s+(.*\S)\s*$")

# #12064 -- a bare code-statement line in a markdown cell. A stub MOVED from a
# code cell into markdown renders as prose (not code), is invisible to
# count_exercises.py (it counts code cells), and to the H.3 pre-commit (a
# markdown cell has neither execution_count nor outputs to fail on) -- the
# move doesn't satisfy H.3, it makes H.3 inapplicable. Observed on PR #11952
# cells 15/17/19 (Console.WriteLine exercise stubs) and on main as PT_11
# cell 5 (a Papermill `parameters` anchor that never executes, contradicting
# the executed cell 4). The leading `(?: {0,3})` is load-bearing: a block
# indented 4+ spaces is a legitimate markdown indented-code block and must
# NOT match (measured: excluding it drops corpus noise by ~3x -- 3 hits
# become 1). Pattern set deliberately narrow (8 forms, the observed class);
# widening requires re-measuring FPs with new positive controls.
_STMT_LINE_RE = re.compile(
    r"^(?: {0,3})("
    r"Console\.WriteLine\(|print\(|return\s+\S|import\s+\w|"
    r"using\s+\w+;|def\s+\w+\(|var\s+\w+\s*=|#r\s+\"nuget)"
)

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


def _is_yaml_block_open_no_close(lines, fenced: set[int]) -> bool:
    """True if the cell opens a YAML frontmatter block but never closes it.

    A markdown cell whose first non-blank line is exactly ``---`` (and there is
    NO later ``---`` to close the block) opens a YAML metadata block in Pandoc
    -- regardless of whether the line AFTER the opener is blank. The block then
    extends until end-of-document or until the next ``---`` line *anywhere in
    the rendered output*, turning the page into a YAML error or a single
    oversized setext heading. Reproduced 2026-08-18 on
    ``MyIA.AI.Notebooks/FallacyDetection/02_fallacy_datasets_landscape.ipynb``
    pre-#11629 (8 cells ``---\\n### Dataset N -- ...``) AND on
    ``SymbolicAI/SymbolicLearning/SL-8-KnowledgeGraphs-ILP.ipynb`` (15 cells
    ``---\\n\\n## Titre`` -- the SECOND outage, 20:27Z, after #11629).

    The earlier claim that a blank line after the opening ``---`` made it a
    "thematic break, not a YAML opener" was empirically refuted: Pandoc opens
    the ``yaml_metadata_block`` either way (oracle js-yaml on the SL-8 form:
    ``scanned=1 bad=1``, *bad indentation of a mapping entry*). The ONLY safe
    head-``---`` is a BARE divider -- a cell containing nothing but the
    ``---`` line -- which renders as ``<hr>`` (Pandoc needs a following line
    to start a YAML block). The fenced set lets us ignore ``---`` lines that
    live inside verbatim code blocks (those are literal text, not YAML markers).

    Returns True when the cell opens a YAML block with no closing ``---``
    anywhere in the rest of the cell.
    """
    # First non-blank line must be exactly ``---``.
    nz = _nonblank(lines)
    if not nz:
        return False
    if nz[0].strip() != "---":
        return False
    # A cell that is ONLY the ``---`` line is a thematic break (``<hr>``), not
    # an opener: Pandoc needs a following non-blank line to start YAML parsing.
    if len(nz) == 1:
        return False
    # Locate the opening fence in the raw lines.
    for i, ln in enumerate(lines):
        if ln.strip() == "---":
            break
    # Now: NO later ``---`` anywhere in the rest of the cell closes the block.
    # Skip fence-internal lines so a verbatim ``---`` ASCII divider doesn't
    # count as a closer.
    for j in range(i + 1, len(lines)):
        if j in fenced:
            continue
        if lines[j].strip() == "---":
            return False  # has a closer -> handled by _is_frontmatter_block
    return True  # opener with no closer in this cell


def _selfcheck() -> int:
    """Embedded positive/negative controls for ``yaml_block_open_no_close``.

    #11630 postmortem (ai-01 arbitration, 2026-08-18): BOTH implementations
    calibrated their positive control on the FIRST outage form
    (``---\\n### Dataset N``, FallacyDetection/02 pre-#11629) and let the
    SECOND form pass -- ``---\\n\\n## Titre`` (SL-8, the notebook that took
    the site down at 20:27Z AFTER #11629). The exemption claiming a blank
    line after ``---`` made it a "thematic break" was the blind spot; the
    oracle js-yaml and the outage both refute it. A detection pattern
    validates on its false negatives, not its hits (anti-regression), so the
    embedded control game carries BOTH observed forms plus the negatives
    (bare divider, complete frontmatter, plain prose). Exit 1 on any miss --
    a rule that silently stops seeing a defect form must fail loudly.

    Wired as ``--selfcheck``; the guard workflow runs it so a future
    refactor of this rule that loses a form breaks CI instead of rendering
    a cleaner-looking violation count.
    """
    fixtures: list[tuple[str, str, bool]] = [
        # (name, cell source, expected: rule fires?)
        ("FallacyDetection/02 pre-#11629 (--- + immediate content)",
         "---\n### Dataset N -- biased language in news\n\nIntroduction text.",
         True),
        ("SL-8 (--- + blank line + title)",
         "---\n\n## Knowledge graphs and ILP\n\nBody text of the section.",
         True),
        ("bare --- divider (nothing after)",
         "---\n",
         False),
        ("complete frontmatter (has closer)",
         "---\ntitle: Foo\n---\n",
         False),
        ("plain prose cell (no --- head)",
         "# Heading\n\nPlain paragraph, no dashes.\n",
         False),
    ]
    failed: list[str] = []
    for name, src, expected in fixtures:
        lines = src.split("\n")
        fenced = _inside_fence_lines(lines)
        got = _is_yaml_block_open_no_close(lines, fenced)
        if got != expected:
            failed.append(f"{name}: rule fired={got}, expected={expected}")
    if failed:
        print("selfcheck FAIL:", file=sys.stderr)
        for f in failed:
            print(f"  !! {f}", file=sys.stderr)
        return 1
    print("selfcheck OK: yaml_block_open_no_close fires on both observed forms "
          "(FallacyDetection/02 + SL-8), silent on bare divider / complete "
          "frontmatter / prose")

    # ---- code_stmt_in_markdown (#12064) ----------------------------------------
    # Positive control = the cell-15 fixture of PR #11952 verbatim; negatives =
    # the two LEGITIMATE renderings of the same code (indented-4 block, fenced
    # block) plus plain prose. Validates through scan_cell (the real entry
    # point), not just the regex.
    stmt_fixtures: list[tuple[str, str, bool]] = [
        ("PR #11952 cell 15 (Console.WriteLine stub, bare)",
         'Exercice 5 -- affichez la valeur.\nConsole.WriteLine("Exercice 5 a completer");\n',
         True),
        ("PT_11 cell 5 (parameters anchor, print())",
         '# Set True for real training on GPU.\n'
         'LOAD_MODEL_AND_TRAIN = False\n'
         'print(f"LOAD_MODEL_AND_TRAIN = {LOAD_MODEL_AND_TRAIN}")\n',
         True),
        ("same stub, indented 4 spaces (legit code block)",
         "Exercice 5 -- affichez la valeur.\n\n    Console.WriteLine(\"Exercice 5 a completer\");\n",
         False),
        ("same stub, inside a fence (legit code block)",
         "Exercice 5 -- affichez la valeur.\n\n```csharp\nConsole.WriteLine(\"Exercice 5 a completer\");\n```\n",
         False),
        ("plain prose (no statement line)",
         "# Titre\n\nUn paragraphe qui explique l'exercice, sans code nu.\n",
         False),
    ]
    for name, src, expected in stmt_fixtures:
        fired = any(f["rule"] == "code_stmt_in_markdown"
                    for f in scan_cell({"cell_type": "markdown", "source": src}))
        if fired != expected:
            failed.append(f"{name}: code_stmt_in_markdown fired={fired}, expected={expected}")
    if failed:
        print("selfcheck FAIL:", file=sys.stderr)
        for f in failed:
            print(f"  !! {f}", file=sys.stderr)
        return 1
    print("selfcheck OK: code_stmt_in_markdown fires on both observed forms "
          "(#11952 stub + PT_11 parameters anchor), silent on indented block / "
          "fence / prose")
    return 0


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

    # ---- yaml-block-open-no-close (#11630) --------------------------------------
    # Catches the angle left by `_is_frontmatter_block`: a cell whose first non-blank
    # line is exactly `---` but with NO closing `---` in the same cell still opens a
    # YAML metadata block in Pandoc -- the block extends until end-of-document or
    # until the next `---` line anywhere in the rendered output, corrupting the page.
    # Must run BEFORE `_is_frontmatter_block` (the latter early-returns on a complete
    # frontmatter cell, so a `---` opener without closer would never be checked for
    # the no-close shape). The 8 cells in 02_fallacy_datasets_landscape.ipynb pre-#11629
    # were exactly this shape: `---<NL>### Dataset N -- ...`, no closer.
    if _is_yaml_block_open_no_close(lines, fenced):
        findings.append({
            "rule": "yaml_block_open_no_close",
            "severity": RULE_SEVERITY["yaml_block_open_no_close"],
            "message": ("cell opens a YAML frontmatter block with `---` as the first line "
                        "but no closing `---` in the same cell; Pandoc extends the block "
                        "until end-of-document or the next `---` in the rendered output, "
                        "corrupting the page. Fix: replace the leading `---` with `***` "
                        "(CommonMark thematic break, identical render, no YAML opener)"),
            "evidence": lines[0].strip(),
            "hash": _cell_hash("yaml_block_open_no_close", text),
        })
        return findings  # the YAML-opener shape fully describes this cell

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

    # ---- heading nested in a list item / blockquote (#11829) ---------------------
    # Fence-aware (parity with oversized_hint above): a `# comment` inside a code
    # block is literal code, not a heading. One finding per cell (the hash is
    # per-cell anyway); the evidence names the first offending line.
    for idx, ln in enumerate(lines):
        if idx in fenced:
            continue
        m = _CONTAINER_HEADING_RE.match(ln)
        if not m:
            continue
        rule = "heading_in_list"
        level = len(m.group(1))
        findings.append({
            "rule": rule,
            "severity": RULE_SEVERITY[rule],
            "message": f"heading nested in a list/blockquote (renders as giant H{level})",
            "evidence": ln.strip()[:100],
            "hash": _cell_hash(rule, text),
        })
        break

    # ---- bare code statement in markdown (#12064) --------------------------------
    # Fence-aware AND indent-aware: a statement inside a ``` fence renders as
    # code (legit), and a block indented 4+ spaces is an indented-code block
    # (legit). The `_STMT_LINE_RE` leading `(?: {0,3})` carries the indent
    # exclusion; the `idx in fenced` skip carries the fence exclusion.
    for idx, ln in enumerate(lines):
        if idx in fenced:
            continue
        if _STMT_LINE_RE.match(ln):
            rule = "code_stmt_in_markdown"
            findings.append({
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": ("bare code statement in a markdown cell renders as prose, is "
                            "invisible to count_exercises.py, and escapes the H.3 pre-commit "
                            "(a markdown cell has no execution_count to be null). Either "
                            "restore it as a code cell or wrap it in a ``` fence"),
                "evidence": ln.strip()[:100],
                "hash": _cell_hash(rule, text),
            })
            break  # one per cell is enough

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


def _quarto_render_list(quarto_yml: Path) -> list[Path]:
    """Files Quarto renders explicitly listed under ``project.render``.

    Returns relative paths (as they appear in the YAML). Empty list on a
    missing file, invalid YAML or missing key -- the caller falls back to the
    full repo scan. A missing PyYAML dependency is NOT an empty-list case:
    it raises RuntimeError naming the dependency, so a dead closure scan can
    never masquerade as "nothing to render" (#11850 -- pre-fix, a runner
    without pyyaml silently scanned 0 of 792 render-list entries while the
    error accused _quarto.yml of being empty/invalid).
    """
    if not quarto_yml.exists():
        return []
    try:
        import yaml  # local import: the script otherwise stays yaml-free
    except ImportError as exc:
        raise RuntimeError(
            "pyyaml is not installed -- the Quarto render-list cannot be read. "
            "This is a missing dependency (fix: pip install pyyaml), NOT an "
            "empty or invalid quarto-yml."
        ) from exc
    try:
        data = yaml.safe_load(quarto_yml.read_text(encoding="utf-8"))
    except yaml.YAMLError:
        return []
    render = (((data or {}).get("project") or {}).get("render") or [])
    out: list[Path] = []
    for entry in render:
        if not isinstance(entry, str):
            continue
        # Skip globs -- the scanner needs concrete paths. Globs like
        # ``*.qmd`` / ``README.md`` don't expand under safe_load anyway, but
        # leave them as-is to let the caller decide what to do.
        if any(c in entry for c in "*?["):
            continue
        out.append(Path(entry))
    return out


_NOTEBOOK_LINK_RE_CACHE: dict[str, re.Pattern[str]] = {}


def _notebook_link_pattern() -> re.Pattern[str]:
    """Regex that catches a relative link to a ``.ipynb`` file from markdown text.

    Three flavors covered by alternation: (a) markdown ](URL) · (b) href="URL" ·
    (c) bare URL preceded by space/quote. The match captures the WHOLE branch
    (prefix + URL); callers pass the result through ``_strip_branch_prefix``
    to extract just the URL. Char class ``[A-Za-z0-9_./-]`` covers relative
    paths + ``../``.

    Why not "one shared capture group" ? Python's regex engine numbers groups
    by POSITION across alternation branches -- three ``(url)`` groups means
    3 capture groups, NOT one. So the pattern uses a single outer named
    group ``url`` wrapping the alternation, and we strip the branch prefix
    post-match.

    The trailing lookahead ``(?=[\\s'"<>)]|[.,;:!?]|$)`` accepts EITHER a
    closing delimiter (``'``, ``"``, ``<``, ``>``, ``(``, ``)``, whitespace,
    end-of-text) OR a single terminal-punctuation character (``.``, ``,``,
    ``;``, ``:``, ``!``, ``?``). Without the punctuation
    class, a sentence-final bare link like ``voir foo.ipynb.`` would NOT
    match: the ``.`` is not in the original character class, so the regex
    stops short and the link falls out of the closure entirely. The
    post-match ``rstrip`` only fires AFTER the regex captures, so a missing
    capture is invisible to it -- exactly the silent-FN class that #11643
    reserves (cf. ``[[handrolled-pattern-set-undercounts-silently]]``).

    Note: the parenthesis-and-quote branches in the alternation (``](``
    and ``href="'") are markdown delimiters, not part of the URL;
    these already terminate at the closing ``)`` or ``"`` and need no
    punctuation extension. The punctuation class is for the bare-URL
    branch (``(?:^|[\\s\"'])+URL``) where a link ends in mid-prose.
    """
    if "main" not in _NOTEBOOK_LINK_RE_CACHE:
        url_nc = r"[A-Za-z0-9_./-]+\.ipynb"  # char class only, NO capture
        _NOTEBOOK_LINK_RE_CACHE["main"] = re.compile(
            r"(?P<url>" +
            r"\]\(" + url_nc +
            r"|href=['\"]" + url_nc +
            r"|(?:^|[\s\"'])" + url_nc +
            r")" +
            # Trailing context: closing delimiter (whitespace, quote, bracket,
            # end-of-text) OR a single terminal punctuation character (``.``,
            # ``,``, ``;``, ``:``, ``!``, ``?``). The punctuation class is
            # necessary for bare sentence-final links like ``... voir foo.ipynb.``
            # to match at all -- without it, the regex stops on ``.`` and the
            # post-match ``rstrip`` never sees the URL (#11643 FN reserve).
            r"(?=[\s'\"\)<>]|[.,;:!?]|$)",
            re.IGNORECASE,
        )
    return _NOTEBOOK_LINK_RE_CACHE["main"]


# Pre-built post-processor -- after a regex match, extract the trailing
# ``.ipynb`` URL from the branch prefix. Used by ``_notebook_targets_from_render_list``.
_NOTEBOOK_URL_TAIL = re.compile(r".*?([A-Za-z0-9_./-]+\.ipynb)\s*$")


def _strip_branch_prefix(matched: str) -> str:
    """Return the trailing ``.ipynb`` URL from a regex branch match.

    The regex captures one of ``](foo.ipynb)``, ``href="foo.ipynb"`` or
    ``[space]foo.ipynb``. We keep only the URL (``foo.ipynb``) by anchoring
    the suffix char class via ``_NOTEBOOK_URL_TAIL``.
    """
    m = _NOTEBOOK_URL_TAIL.match(matched)
    return m.group(1) if m else matched


def _notebook_targets_from_render_list(repo_root: Path, render_paths: list[Path]) -> set[Path]:
    """Compute the *closure* : notebooks reachable from a rendered page.

    Starts from the explicit render-list (ipynb/md/qmd files) and follows
    ``.ipynb`` links one hop out of the rendered .md/.qmd/.ipynb files. The
    result is the set of notebooks that Quarto will *transitively* render --
    which is precisely the set whose frontmatter defects corrupt the page
    (cf. #11630 : the PR that broke main didn't touch the broken notebook, it
    only added a link to it from a rendered README). Single-hop by design:
    Quarto's link rewriting is one-step (rendered file -> linked file -> its
    own .html), and the empirical incident on 2026-08-17 was one-hop.
    """
    targets: set[Path] = set()
    # Seed: explicit render-list entries that ARE notebooks.
    for p in render_paths:
        if p.suffix == ".ipynb":
            targets.add(p)
    # Follow links from rendered pages (.md / .qmd / .ipynb) to .ipynb targets.
    pattern = _notebook_link_pattern()
    for p in render_paths:
        if p.suffix not in (".md", ".qmd", ".ipynb"):
            continue
        abs_p = repo_root / p
        if not abs_p.exists():
            continue
        try:
            text = abs_p.read_text(encoding="utf-8")
        except Exception:
            continue
        # For notebooks, links live in markdown cell sources -- extract them
        # by scanning the raw JSON. Simpler: scan the whole file as text, the
        # regex tolerates either context (markdown link syntax or HTML href).
        for m in pattern.finditer(text):
            link = m.group("url") if "url" in m.groupdict() else m.group(0)
            link = _strip_branch_prefix(link)
            if not link:
                continue
            link = link.strip().rstrip(".,;:!?)")
            # Drop fragment / query.
            link = link.split("#", 1)[0].split("?", 1)[0]
            if not link:
                continue
            # Resolve relative to the rendered file's directory.
            try:
                target = (abs_p.parent / link).resolve()
            except Exception:
                continue
            try:
                rel = target.relative_to(repo_root.resolve())
            except ValueError:
                continue
            if rel.suffix == ".ipynb":
                targets.add(Path(rel))
    return targets


def gather_closure(repo_root: Path, quarto_yml: Path) -> list[dict]:
    """Scan only the Quarto closure (render-list + linked notebooks).

    See ``_notebook_targets_from_render_list`` for the definition. Returns the
    same finding shape as ``gather``. Empty list on YAML parse failure (the
    caller decides whether to fail or fall back -- the CLI exits 2 with a
    clear message). Raises RuntimeError when pyyaml is missing -- never
    report an empty closure for an unreadable dependency (#11850).
    """
    render_paths = _quarto_render_list(quarto_yml)
    if not render_paths:
        return []
    targets = _notebook_targets_from_render_list(repo_root, render_paths)
    findings: list[dict] = []
    for rel in sorted(targets):
        abs_p = repo_root / rel
        if not abs_p.exists():
            continue
        findings.extend(scan_notebook(abs_p))
    return findings


def load_baseline(path: Path) -> set[str]:
    if not path.exists():
        return set()
    data = json.loads(path.read_text(encoding="utf-8"))
    return set(data.get("hashes", []))



def _print_repair_hints(blocking: list) -> None:
    """Nomme la commande de reparation des regles qui en ont une (#12089).

    Ne dit RIEN pour les regles absentes de `RULE_REPAIR` : un garde qui
    suggererait une commande inoperante ferait perdre plus de temps qu'il n'en
    fait gagner. Les regles sans fixer sont listees a part, explicitement, pour
    que l'auteur sache que le silence est mesure et non un oubli.
    """
    rules = {f["rule"] for f in blocking}
    fixable = sorted(r for r in rules if r in RULE_REPAIR)
    manual = sorted(r for r in rules if r not in RULE_REPAIR)
    if fixable:
        print("\nReparation outillee :", file=sys.stderr)
        for rule in fixable:
            print(f"  [{rule}] {RULE_REPAIR[rule]}", file=sys.stderr)
        print(f"  {_REPAIR_SCOPE_NOTE}", file=sys.stderr)
    if manual:
        print("\nSans reparation outillee (edition manuelle de la cellule) : "
              + ", ".join(manual), file=sys.stderr)


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
    ap.add_argument("--closure", action="store_true",
                    help="restrict scan to the Quarto closure: render-list + "
                         "notebooks reachable by .ipynb links from rendered "
                         "pages. The pre-#11630 main-line breakage happened "
                         "because the offending notebook was NOT in the "
                         "render-list -- it was only referenced as a link from "
                         "a rendered README. Repository-wide scan flags 351 "
                         "false-positive cells; the closure scan flags only "
                         "the ones that actually break a rendered page. See "
                         "#11630 for the rationale.")
    ap.add_argument("--quarto-yml", type=Path, default=Path("_quarto.yml"),
                    help="path to the Quarto project YAML (default: ./_quarto.yml)")
    ap.add_argument("--selfcheck", action="store_true",
                    help="run the embedded positive/negative controls of the "
                         "yaml_block_open_no_close rule (BOTH observed forms: "
                         "FallacyDetection/02 `---` + content AND SL-8 "
                         "`---` + blank + title) and exit 1 on any miss "
                         "(#11630). No scan root required.")
    args = ap.parse_args(argv)

    if args.selfcheck:
        return _selfcheck()

    root = Path(args.root)
    if not root.exists():
        print(f"error: path not found: {root}", file=sys.stderr)
        return 2

    if args.closure:
        # Closure scan: Quarto render-list + notebooks reachable by .ipynb links
        # from any rendered page. See #11630. Repo-root = the directory holding
        # _quarto.yml (we resolve relative to the cwd, same as the YAML path).
        repo_root = args.quarto_yml.resolve().parent
        try:
            render_paths = _quarto_render_list(args.quarto_yml)
        except RuntimeError as exc:
            # Missing pyyaml -- name the dependency, never the YAML file
            # (#11850: this used to exit as "empty/invalid _quarto.yml").
            print(f"error: {exc}", file=sys.stderr)
            return 2
        if not render_paths:
            print(f"error: --closure requires a parseable {args.quarto_yml} "
                  f"with a project.render list; got empty/invalid", file=sys.stderr)
            return 2
        targets = _notebook_targets_from_render_list(repo_root, render_paths)
        print(f"--closure: render-list={len(render_paths)} closure-targets={len(targets)}", file=sys.stderr)
        findings = []
        for rel in sorted(targets):
            abs_p = repo_root / rel
            if abs_p.exists():
                findings.extend(scan_notebook(abs_p))
    else:
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
            _print_repair_hints(blocking)
            return 1
        print("OK: no new ERROR-level markdown-rendering violations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
