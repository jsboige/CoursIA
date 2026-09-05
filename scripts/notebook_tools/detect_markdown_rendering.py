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
- ``unclosed_bold``          (WARN):  a paragraph with an ODD number of ``**``
  delimiters. CommonMark cannot close emphasis across a blank line, so an odd
  count guarantees at least one ``**`` that renders literally or overflows into
  bold (stray closer, mid-word ``**``, opener whose closer fell in another
  paragraph). Count excludes code spans (paired backticks) and thematic-break
  lines (``***``/``---`` alone on a line are block boundaries); list items and
  ATX headings start their own paragraph so a stray cannot be balanced by the
  next item. WARN-first discipline (parity with ``oversized_hint``): the class
  is measured at 16 cells corpus-wide (issue #12112), to be burned down.
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
- ``source_list_broken_words`` (ERROR): markdown cell whose ``source`` list splits a
  word mid-word — the INVERSE of ``source_list_missing_newlines`` (#12363). A repair
  that re-splits a list can cut a word in half across two segments; the GitHub render
  re-joins them so the defect is INVISIBLE on render, but every segment-by-segment
  consumer (diff, translation, twin-parity content-SHA, pedagogical grep) sees the
  word broken. Detected when a segment does not end with ``\n``, ends with a letter,
  and the next segment starts with a letter (the boundary glues two word-halves with
  nothing between). Runs AFTER the missing-newlines early-returns: the ratchet targets
  the post-repair shape ('\n' adequate everywhere, ONE mid-word boundary), where the
  missing-newlines rule is silent and only this rule sees the split. Corpus measure
  2026-08-25: 0 hits repo-wide — a pure cliquet, ERROR is safe because ``--check``
  only blocks NEW violations.

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
import os
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
    # #12112: WARN-first -- the class is measured at 16 cells corpus-wide; the
    # drift gate on new hits is the issue's acceptance. A stray '**' is a
    # cosmetic rendering defect, not a page-breaking one (unlike the ERRORs).
    "unclosed_bold": WARN,
    "source_list_missing_newlines": ERROR,
    # #12363: ERROR (bloquant) -- the corpus measure is 0 hits repo-wide on
    # 2026-08-25 (903 total findings across the other 4 rules, none of them
    # broken-words). A pure ratchet: the rule is the INVERSE of
    # source_list_missing_newlines (a repair that re-splits a list may cut a
    # word mid-word, invisible on render but breaking segment-by-segment
    # consumers). Count 0 + delta-vs-baseline --check = only NEW violations
    # block, which is exactly the cliquet the issue asks for ("la prochaine
    # tranche ne puisse pas l'introduire sans rougir").
    "source_list_broken_words": ERROR,
    # #12064: ERROR (bloquant) -- the corpus measure is 1 hit / 20,576 markdown
    # cells (the true positive (A) PT_11 cell 5), reproduced by this lane. That
    # precision is what buys blocking status; a wider pattern set would need
    # its own FP re-measure first ([[handrolled-pattern-set-undercounts-silently]]
    # cuts both ways: widening silently under- AND over-counts).
    "code_stmt_in_markdown": ERROR,
    # #12110: WARN-first -- 14 occurrences mesurées sur 7 notebooks avant la
    # vague de réparation (4 PRs mergées par po-2023/po-2024/po-2025), 3 cas (B)
    # légitimement marqués (terme technique "蒸馏" / nom produit "海螺3"). Le
    # WARN d'abord suit la discipline #12107 (heading_in_list) et #12112
    # (unclosed_bold): promouvoir ERROR seulement après mesure du taux de FP
    # sur le corpus, jamais a priori.
    "cjk_in_prose": WARN,
}

# #12110 -- allowlist (fichier, cellule) des cas CJK LEGITIMES (classe B du
# corps de l'issue). 3 entrées mesurées sur main 2026-08-22 :
#   - PT_11b cell 5 et 19 : "蒸馏" (distillation) -- terme technique assumé
#     cité à côté de "DeepSeek-R1", à confirmer avec l'auteur
#   - Video/02-6-MiniMax-H3 cell 1 : "海螺3" (Hailuo 3.0) -- nom chinois réel
#     du produit
# Clé = path POSIX (slashes forward, comme émis par scan_notebook). Si une
# nouvelle entrée s'ajoute, elle DOIT figurer dans le selfcheck pour valider
# que la règle ne tire pas dessus. Inversement, si la liste grossit sans
# selfcheck, c'est le pattern d'une règle qui sous-compte en silence.
_CJK_ALLOWLIST: set[tuple[str, int]] = {
    ("MyIA.AI.Notebooks/GenAI/PostTraining/PT_11d_multiseed_qwen35_4x100.ipynb", 5),
    ("MyIA.AI.Notebooks/GenAI/PostTraining/PT_11d_multiseed_qwen35_4x100.ipynb", 19),
    ("MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb", 1),
}

# #12110 -- fichiers dont le scope est multilingue assumé (pas de la prose FR).
# L'exclusion au PATHNAME est plus sûre qu'au contenu : on ne lit pas la
# cellule pour décider de la scanner, on s'appuie sur la convention de nommage
# déjà portée par le pipeline translation-sync. Pas de risque de faux négatif
# par false positive sur la convention : un notebook FR nommé foo.ipynb qui
# contiendrait "你好" sera détecté (le défaut); un notebook "multilingue"
# nommé foo_zh.ipynb ne le sera pas (l'intention).
_CJK_LANG_SUFFIXES = ("_zh", "_ja", "_ko")

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
# a thematic-break line (*, -, _) -- a BLOCK boundary in CommonMark, so it is
# never part of a paragraph and its stars must not count toward emphasis.
# Used by the unclosed_bold rule (#12112); the spaced forms (- - -, * * *)
# fall through to _LIST_ITEM_RE, which is also a block boundary.
_THEMATIC_BREAK_RE = re.compile(r"^\s{0,3}(?:\*{3,}|-{3,}|_{3,})\s*$")
# a list-item start (CommonMark: 1-9 digits + . or ) + space, or a bullet).
# Each item is its own paragraph, so a stray '**' cannot be balanced away by
# the next item's stars (#12112).
_LIST_ITEM_RE = re.compile(r"^\s{0,3}(?:[-*+]|\d{1,9}[.)])\s+")
# a fenced-code marker: >=3 backticks OR tildes, optionally indented up to 3 spaces.
# A ``` / ~~~ block renders its content VERBATIM, so a `---`/`===` line inside it is
# literal text (ASCII art, a cryptarithme divider, a box-drawing rule) — NOT a setext
# underline. Without fence-awareness the setext rules flagged ~11 such cells as
# `setext_oversized` false positives (CSP cryptarithmes, Sudoku grids, Mermaid-ish
# boxes). See PR follow-up to #8392 (same precision vein, different FP family).
_FENCE_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")
# blockquote prefix (up to 3 nestings, optional space after '>'): a fence can
# live INSIDE a blockquote (`> ```bash` ... `> ````) and its content still
# renders verbatim -- CommonMark keeps the fenced block within the quote.
# _FENCE_RE alone is blind to the prefix, so `_inside_fence_lines` strips it
# before matching (Search-10-SymbolicAutomata c23: `> # Windows` bash comments
# inside a blockquoted fence were flagged heading_in_list, a scanner FP).
_BQ_PREFIX_RE = re.compile(r"^\s{0,3}(?:>\s?){1,3}")
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

# #12110 -- a CJK (Chinese-Japanese-Korean) character in a markdown cell whose
# source is otherwise French prose. The defect pattern: a model-generated cell
# wrote a word in CJK in the middle of a French sentence, e.g.
# ``plus均匀isée`` (= "plus uniforme") or ``est刻意ée`` (= "est construite").
# These are prose defects, not data: the CJK word is meant to be French but the
# model slipped, leaving a token that no francophone reader can decode.
#
# Pattern covers the four CJK blocks observed in the inventory of #12110:
# hiragana (U+3040-309F), katakana (U+30A0-30FF), CJK Unified Ideographs
# (U+4E00-9FFF), Hangul Syllables (U+AC00-D7A3). CJK Compatibility Ideographs
# (U+F900-FAFF), Extension A (U+3400-4DBF), and the kana supplement
# (U+1B00-1BFF / U+1F200-1F2FF) are deliberately OMITTED -- the corpus has not
# produced a defect in those blocks, and a pattern set that grows past its
# observed forms is the second-order FN risk
# ([[handrolled-pattern-set-undercounts-silently]] cuts both ways).
_CJK_RE = re.compile(r"[぀-ゟ゠-ヿ㐀-䶿一-鿿가-힯]")

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


def _broken_words_in_list(src: list[str]) -> str | None:
    """First consecutive pair whose join splits a word mid-word (#12363).

    The INVERSE of the missing-newlines artifact: a repair that re-splits a
    markdown list may cut a word in half, leaving the two halves on adjacent
    segments. GitHub re-joins them on render (so it looks correct) but any
    segment-by-segment consumer (diff, translation, twin-parity content-SHA,
    pedagogical grep) sees the word broken. Detected when a segment does NOT
    end with '\\n', ends with a letter, and the next segment starts with a
    letter -- the boundary recreates the word with nothing between.

    Returns a quote of the offending pair, or None. A segment ending with '\\n'
    is a normal line break and is never flagged; a segment ending with space
    followed by a letter is a legit join (space preserved) and is not flagged.
    """
    for a, b in zip(src, src[1:]):
        if not a or not b:
            continue
        if a.endswith("\n"):
            continue
        if a[-1].isalpha() and b[0].isalpha():
            return f"{a!r} + {b!r}"
    return None


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
    ``MyIA.AI.Notebooks/GenAI/FallacyDetection/02_fallacy_datasets_landscape.ipynb`` (descended into GenAI/ via tranche 1 of #13581; was ``MyIA.AI.Notebooks/FallacyDetection/`` pre-2026-08-30)
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
    (``---\\n### Dataset N``, GenAI/FallacyDetection/02 pre-#11629, formerly under ``MyIA.AI.Notebooks/FallacyDetection/``) and let the
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
    # fence fixtures (#11947 residual): validates the fence oracle itself on its
    # false negatives. A detection pattern validates on what it must NOT flag:
    # here, bash comments (`> # Windows`) inside a BLOCKQUOTED fenced block were
    # the last heading_in_list corpus FP (Search-10-SymbolicAutomata c23) -- the
    # prefix-blind _FENCE_RE let them reach the prose rules.
    fence_fixtures: list[tuple[str, list[str], set[int]]] = [
        # (name, lines, expected inside-set)
        ("blockquote fence: bash comments are verbatim",
         ["> ```bash", "> # Windows", "> choco install graphviz", "> ```"],
         {1, 2}),
        ("plain fence: content verbatim",
         ["```bash", "# Windows", "choco install graphviz", "```"],
         {1, 2}),
        ("blockquote prose OUTSIDE any fence stays scannable",
         ["> # Windows", "text"],
         set()),
        ("tilde fence inside blockquote",
         ["> ~~~", "> # note", "> ~~~"],
         {1}),
    ]
    for name, flines, expected in fence_fixtures:
        got = _inside_fence_lines(flines)
        if got != expected:
            failed.append(f"{name}: inside={sorted(got)}, expected={sorted(expected)}")
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

    # ---- unclosed_bold (#12112) ------------------------------------------------
    # The six controls that validated the corpus scan: fires on the two
    # CONFIRMED defect shapes of #12112 (mid-word stray balancing an earlier
    # opener, bold opener with no closer); silent on the four legit renderings
    # (valid bold, SOFT line break = valid CommonMark, thematic break, code
    # span); fires again when a filet and a defect COEXIST in the same cell
    # (the filet exclusion must not silence a real defect next to it).
    bold_fixtures: list[tuple[str, str, bool]] = [
        ("unclosed bold, mid-word stray (rl_6b cell 19 shape)",
         "Le **bootstrap** est annule sur `terminated`. La valeur future reste "
         "une estim**ee valide.",
         True),
        ("unclosed bold opener, no closer (QC-Py-10 cell 31 shape)",
         "**Methode `CanEnterPosition()` : validation multi-niveaux.",
         True),
        ("valid bold",
         "Texte avec **gras valide** bien ferme.",
         False),
        ("soft line break (valid CommonMark)",
         "**gras sur\ndeux lignes** sans ligne vide.",
         False),
        ("thematic break line",
         "Paragraphe un.\n\n---\n\nParagraphe deux.",
         False),
        ("code span (literal stars)",
         "Texte avec `**pas du gras**` dedans.",
         False),
        ("filet + defect coexist in the same cell",
         "**gras valide** ici.\n\n---\n\nTexte avec **defaut",
         True),
    ]
    for name, src, expected in bold_fixtures:
        fired = any(f["rule"] == "unclosed_bold"
                    for f in scan_cell({"cell_type": "markdown", "source": src}))
        if fired != expected:
            failed.append(f"{name}: unclosed_bold fired={fired}, expected={expected}")
    if failed:
        print("selfcheck FAIL:", file=sys.stderr)
        for f in failed:
            print(f"  !! {f}", file=sys.stderr)
        return 1
    print("selfcheck OK: unclosed_bold fires on both confirmed #12112 shapes "
          "and on filet+defect coexistence; silent on valid bold / soft break / "
          "thematic break / code span")

    # ---- cjk_in_prose (#12110) --------------------------------------------------
    # Six controls that validate the corpus scan: fires on the THREE observed
    # defect shapes from #12110 (QC-Py-21 CJK glued to FR suffix, ICT-15e
    # morphological morpheme mid-word, Video-Operations-Basics arbitrary token),
    # silent on the THREE legitimate renderings (CJK inside a ``` fence = code
    # data, TTS cell with Japanese demo data, multilingual notebook stem).
    # Validates through scan_cell (the real entry point), not just the regex,
    # so a future refactor that drops the fence exclusion or the allowlist
    # break loudly on the corpus ground truth.
    #
    # The Audio/02-8 #12110 case (B) -- Japanese in a TTS test cell -- lives
    # in a CODE cell (cell#35), not markdown. scan_cell never sees it: the
    # markdown-only filter is itself the implicit exclusion. We test the
    # explicit fence + per-cell allowlist paths here; the code-cell exclusion
    # is the markdown filter that scan_cell already applies at line 638 (the
    # `if cell.get("cell_type") != "markdown": return []` early-return).
    cjk_fixtures: list[tuple[str, str, bool]] = [
        # ---- positives: defect shapes from #12110 inventory ----
        ("QC-Py-21 cell 9 (est刻意ée -- mid-FR-suffix CJK)",
         "La structure en **3 blocs** visible est刻意ée dans la simulation.",
         True),
        ("QC-Py-21 cell 51 (allocation plus均匀isée -- CJK glued to -isée)",
         "Présente une allocation beaucoup plus均匀isée que Mean-Variance.",
         True),
        ("Video-Operations-Basics cell 27 (chemin vidéo任意 -- mid-prose)",
         "Pour saisir un chemin vidéo任意, on appelle la fonction `pick()`.",
         True),
        # ---- negatives: legitimate CJK contexts (NOT prose defects) ----
        ("CJK inside ``` fence (legit code data)",
         "Voici la démo japonaise :\n\n```\nこんにちは、世界\n```\n",
         False),
        # Multilingual-stem exclusion is tested via scan_notebook (file
        # level), not scan_cell (cell level) -- the regex would otherwise fire
        # on the multilingual cell, by design (the file path is what excludes).
    ]
    for name, src, expected in cjk_fixtures:
        fired = any(f["rule"] == "cjk_in_prose"
                    for f in scan_cell({"cell_type": "markdown", "source": src}))
        if fired != expected:
            failed.append(f"{name}: cjk_in_prose fired={fired}, expected={expected}")
    if failed:
        print("selfcheck FAIL:", file=sys.stderr)
        for f in failed:
            print(f"  !! {f}", file=sys.stderr)
        return 1
    print("selfcheck OK: cjk_in_prose fires on the 3 #12110 defect shapes "
          "(QC-Py-21 mid-suffix, Video mid-prose) and is silent on fenced CJK; "
          "multilingual-stem exclusion tested via scan_notebook; code-cell "
          "exclusion is the markdown-only filter in scan_cell itself")

    # ---- source_list_broken_words (#12363) ------------------------------------
    # The ratchet for the INVERSE of the missing-newlines artifact: a repair
    # that re-splits a list may cut a word mid-word. Two positive controls:
    # (a) the realistic post-repair shape -- '\n' everywhere EXCEPT one
    # boundary that cuts a word, so missing-newlines is silent (breaks ==
    # expected) and ONLY this rule sees the split; (b) the verbatim issue
    # witness ["une phrase cou", "pee au milieu"], checked on the helper --
    # through scan_cell that shape also trips the co-occurring missing-
    # newlines collapse (0 breaks < expected), which claims the diagnosis
    # first; the organ detects the cell either way. Negatives: newline-
    # terminated segments, space-preserved join.
    broken_fixtures: list[tuple[str, list[str], bool]] = [
        ("post-repair shape: \\n adequate, ONE mid-word boundary",
         ["ligne un\n", "une phrase cou", "pee au milieu\n", "ligne trois\n"],
         True),
        ("newline-terminated segments (legit)",
         ["ligne complete\n", "suivante\n"],
         False),
        ("space-preserved join (legit)",
         ["foo ", "bar"],
         False),
    ]
    for name, src, expected in broken_fixtures:
        fired = any(f["rule"] == "source_list_broken_words"
                    for f in scan_cell({"cell_type": "markdown", "source": src}))
        if fired != expected:
            failed.append(f"{name}: source_list_broken_words fired={fired}, expected={expected}")
    if _broken_words_in_list(["une phrase cou", "pee au milieu"]) is None:
        failed.append("verbatim #12363 witness ['une phrase cou', 'pee au milieu'] "
                      "not seen by _broken_words_in_list")
    if failed:
        print("selfcheck FAIL:", file=sys.stderr)
        for f in failed:
            print(f"  !! {f}", file=sys.stderr)
        return 1
    print("selfcheck OK: source_list_broken_words fires on the post-repair "
          "mid-word boundary and the verbatim #12363 witness (helper level); "
          "silent on newline-terminated and space-preserved joins")
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
    Fence markers may carry a blockquote prefix (``> ```bash``): the prefix is
    stripped before matching, so blockquoted fences bound their verbatim content
    exactly like plain ones.
    """
    inside: set[int] = set()
    in_fence = False
    fence_char = None
    fence_len = 0
    for i, ln in enumerate(lines):
        m = _FENCE_RE.match(_BQ_PREFIX_RE.sub("", ln, count=1))
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


def _strip_inline_code(text: str) -> str:
    """Drop inline code spans (paired backtick runs) so their content is not counted.

    CommonMark: an inline code span is a run of N backticks, matching content, and a
    closing run of N backticks; an UNCLOSED run extends to the end of the paragraph.
    The toggle mirrors that: a backtick run flips in/out of code, and an odd number of
    runs leaves the tail in code (its '**' are literal, never emphasis delimiters).
    """
    out: list[str] = []
    in_code = False
    i, n = 0, len(text)
    while i < n:
        if text[i] == "`":
            j = i
            while j < n and text[j] == "`":
                j += 1
            in_code = not in_code
            i = j
        else:
            if not in_code:
                out.append(text[i])
            i += 1
    return "".join(out)


def _unclosed_bold_cell(lines, fenced: set[int]) -> str | None:
    """Return the first paragraph with an odd '**' count, else None (#12112).

    Paragraph = contiguous non-blank, non-fence, non-thematic-break lines; ATX
    headings and list-item starts begin their own paragraph (CommonMark). Odd
    '**' count per paragraph -> at least one '**' renders literally or overflows
    into bold (emphasis cannot cross a blank line, so an opener cannot close in
    the next paragraph). Code spans are stripped before counting. The return
    value is the offending paragraph (single-line, for evidence); the caller
    emits one finding per cell.
    """
    para: list[str] = []

    def flush() -> str | None:
        if not para:
            return None
        txt = _strip_inline_code("\n".join(para))
        if txt.count("**") % 2 == 1:
            return " ".join(ln.strip() for ln in para)
        return None

    for idx, ln in enumerate(lines):
        if idx in fenced:
            hit = flush()
            if hit:
                return hit
            para = []
            continue
        stripped = ln.strip()
        if not stripped or _THEMATIC_BREAK_RE.match(ln):
            hit = flush()
            if hit:
                return hit
            para = []
            continue
        if _HEADING_RE.match(ln) or _LIST_ITEM_RE.match(ln):
            hit = flush()
            if hit:
                return hit
            para = [ln]
            continue
        para.append(ln)
    return flush()


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
    # ---- source-list broken-words (#12363) -----------------------------------
    # INVERSE of the missing-newlines rule above: a repair that re-splits a
    # markdown list may cut a word mid-word. Placed AFTER the missing-newlines
    # early-returns because the ratchet targets a cell that HAS proper '\n'
    # (the fix was applied) but was re-split at a wrong spot -- so it does not
    # trigger the missing-newlines rule but DOES break a word. Runs before the
    # line-based rules (which reason on the JOINED text, hiding the split).
    if isinstance(src, list) and len(src) >= 2:
        broken = _broken_words_in_list(src)
        if broken:
            rule = "source_list_broken_words"
            return [{
                "rule": rule,
                "severity": RULE_SEVERITY[rule],
                "message": (f"markdown cell source list splits a word mid-word at "
                            f"boundary {broken}: segment does not end with '\\n' and "
                            f"both neighbors start/end with a letter, so the render "
                            f"join glues two word-halves (invisible on render, breaks "
                            f"segment-by-segment consumers)"),
                "evidence": text.strip()[:100],
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
        # #12338: no early return here. The YAML-opener finding describes the
        # cell's head, not its body: a `- # Indice` line further down is a
        # separate rendering defect (heading_in_list) that this return was
        # silencing -- on the 8 QC-Py notebooks of #12332, all 18 cells with
        # heading_in_list were yaml cells, and the detector reported 0. The
        # finding hashes are per-rule, so both can coexist in the baseline.

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

    # ---- unclosed bold (#12112) -------------------------------------------------
    # Count '**' per paragraph (CommonMark: emphasis cannot cross a blank line,
    # so an odd count = at least one literal or overflowing '**'). Code spans
    # are stripped (their '**' is literal); thematic-break lines are paragraph
    # boundaries; list items / headings start their own paragraph so a stray
    # '**' cannot be balanced by the next item's stars.
    hit = _unclosed_bold_cell(lines, fenced)
    if hit:
        rule = "unclosed_bold"
        findings.append({
            "rule": rule,
            "severity": RULE_SEVERITY[rule],
            "message": ("odd number of '**' delimiters in a paragraph (CommonMark "
                        "cannot close emphasis across a blank line): at least one "
                        "'**' renders literally or overflows into bold. Match every "
                        "opener with a closer inside the same paragraph, or remove "
                        "the stray '**'"),
            "evidence": hit[:100],
            "hash": _cell_hash(rule, text),
        })

    # ---- CJK in French prose (#12110) -------------------------------------------
    # A CJK token glued to a French suffix (e.g. ``plus均匀isée``) renders as
    # garbled prose for a francophone reader -- the model wrote the word in
    # CJK and kept going in French. Per-line scan, fence-aware: a CJK token
    # inside a ``` / ~~~ block is verbatim code, not prose (same exclusion
    # rationale as the other fence-aware rules). Hits are NOT filtered by the
    # allowlist here -- ``scan_notebook`` consults ``_CJK_ALLOWLIST`` to drop
    # the 3 corpus-measured legitimate cells (terme technique / nom produit).
    # Without that allowlist, this rule would systematically over-fire on
    # PT_11 (蒸馏) and Video/02-6 (海螺3). Why per-line: a single-line evidence
    # is more readable than the full text snippet in the report, and the regex
    # does not span lines in 100% of observed cases (#12110 inventory).
    for idx, ln in enumerate(lines):
        if idx in fenced:
            continue
        m = _CJK_RE.search(ln)
        if not m:
            continue
        rule = "cjk_in_prose"
        findings.append({
            "rule": rule,
            "severity": RULE_SEVERITY[rule],
            "message": ("CJK character in French prose -- likely a model that wrote "
                        "a word in CJK mid-sentence (e.g. ``plus均匀isée`` -> "
                        "``plus uniforme``). Either rewrite the cell in French, "
                        "or add the (file, cell) pair to ``_CJK_ALLOWLIST`` with "
                        "an explicit justification if the token is legitimate "
                        "(nom produit, terme technique assumé)"),
            "evidence": f"U+{ord(m.group(0)):04X} ({m.group(0)!r}) in: {ln.strip()[:80]}",
            "hash": _cell_hash(rule, text),
        })
        break  # one finding per cell is enough

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
    # #12110 -- multilingual notebooks (filename suffix _zh / _ja / _ko) are
    # ASSUMED to contain CJK legitimately. Skipping at the file level avoids
    # the per-cell allowlist having to enumerate every cell of every
    # translation target. Convention already enforced by translation-sync.yml.
    posix_path = str(path).replace("\\", "/")
    stem_lower = path.stem.lower()
    if any(stem_lower.endswith(suffix) for suffix in _CJK_LANG_SUFFIXES):
        return []
    out: list[dict] = []
    for i, cell in enumerate(nb.get("cells", [])):
        # #12110 -- per-(file, cell) allowlist for corpus-measured legitimate
        # cells (3 entries on main 2026-08-22: PT_11b 蒸馏 and 02-6-MiniMax 海螺3).
        # The allowlist is consulted AFTER scan_cell emits the finding (so the
        # cell is still scanned for OTHER rules like unclosed_bold), and only
        # filters out the cjk_in_prose finding, never the rest of the report.
        cell_findings = scan_cell(cell)
        cell_findings = [
            f for f in cell_findings
            if not (f["rule"] == "cjk_in_prose"
                    and (posix_path, i) in _CJK_ALLOWLIST)
        ]
        for f in cell_findings:
            f = dict(f)
            f["file"] = posix_path
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
    ap.add_argument("--max-findings", type=int, default=200, metavar="N",
                    help="cap the human-readable findings listing (default: 200)")
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
        max_findings = max(0, args.max_findings)
        print()
        for f in shown[:max_findings]:
            flag = "NEW " if (baseline and f["hash"] not in baseline) else ""
            print(f"  {flag}{f['severity'].upper():>5} {f['file']} cell#{f['cell']} [{f['rule']}]")
            print(f"        {f['evidence']}")
        if len(shown) > max_findings:
            print(f"  ... {len(shown) - max_findings} more")

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
    # SIGPIPE-safe exit (#14590): when the consumer (head, less, |) closes the
    # pipe mid-listing, that is not a scan error. Redirect stdout to devnull so
    # the interpreter's final flush does not re-raise BrokenPipeError
    # ("Exception ignored in: <_io.TextIOWrapper ...>"), then exit 141
    # (128 + SIGPIPE), the shell convention.
    try:
        rc = main()
    except BrokenPipeError:
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
        rc = 141
    raise SystemExit(rc)
