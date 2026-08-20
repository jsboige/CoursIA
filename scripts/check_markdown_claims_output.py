#!/usr/bin/env python3
"""Durable anti-regression guard for the "markdown prose quant cites
fabricated values that contradict the previous code cell output" hazard
(c.290 ★★ / c.331 / PR #11435 pathologie FT-02 c10/c20).

Why this tool exists
--------------------

Audit cross-cycle: two open PRs in the same week (c.290 M15 LSTM-vol +
c.331 FT-02 c10/c20) had MARKDOWN prose that cites quantitative values
which contradict the output of the previous code cell.

Example c.331 -- PR #11435 on FT-02-QLoRA-Quantization.ipynb:

* Cell 11 output (real run):
    trainable params: 3,145,728 || all params: 1,318,903,808 || trainable%: 0.2385
    Params entrainables : 3,145,728 (0.44%)
* Cell 10 markdown (PR-diff vs main):
    "...on attend ~3,1 M de parametres entrainnables sur 1,3 Md au total = ~0,24 %"
    -> CORRECT (the value is in the output)
  vs
    "...on attend ~1,2 M de parametres entrainnables sur 1,3 Md au total = ~0,09 %"
    -> INCORRECT (1.2M / 0.09% never appears in the output; the run printed 3,145,728 / 0.2385)

The C.5 rule (prose quantitative anchored on outputs) is unenforceable by
lint alone: a regex cannot tell whether 0.09% is "right" or "wrong" without
reading the code cell. So this script does the JOIN:

  Cell[code] with output -> Cell[markdown] framework -> extract numbers ->
  cross-reference (markdown claim in output?) -> fabrication flag.

Scope: only checks cells of the form

    ... -- ... -- cell[k] : code (with output) -- cell[k+1] : markdown

The script does NOT touch:
  - pure markdown without a previous code cell (literature cells, framed-less)
  - cells where the markdown is a long literature block (it skips markdown
    cells whose source exceeds 800 chars -- the "literature" tell from c.290)
  - cells in ipynb that are not Python (Lean, .NET, Scala, etc. -- the
    output format is opaque to a regex)

The script is read-only on the notebook: it does NOT edit, only classifies.
Verdicts: CLEAN / FABRICATION_DETECTED / SKIPPED-LITERATURE / ERROR.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# How many previous code cells to scan when a markdown cites a number.
# 3 covers the canonical "interp immediately after code" pattern (c.290) plus
# the common 1-2 cell skip where the prose refers to a slightly earlier output
# (e.g. section 5's chart quoted in section 7's markdown).
WINDOW = 3

# Regex for "numeric claim" in markdown prose. Catches:
#   "0,09 %" / "0.09%" / "0.2385" / "3,1 M" / "3.1B" / "1.42 Go"
#   "75 steps" / "15 epochs" / "69.5s" / "256 tokens"
# Anchored tolerant: comma OR dot, optional SI suffix, optional %/s/epochs/tokens.
NUMERIC_RE = re.compile(
    r"""
    (?<![A-Za-z0-9])                       # left boundary: not alnum
    \d{1,3}(?:[.,]\d{1,3})?                # integer or 1-decimal or 3-decimal
    (?:[.,]\d+)?                            # optional extended decimals
    \s*
    (?:%|pct|percent|epochs?|steps?|s|sec|seconds?|min|minutes?|h|hours?|ms|Md|B|M|G|K|Go|To|tokens?|params?|bits?)?
    (?![A-Za-z0-9])                       # right boundary
    """,
    re.VERBOSE | re.IGNORECASE,
)


def _normalize_num(token: str) -> str:
    """Strip SI suffix, normalize comma->dot, drop trailing dots/zeros.

    Used to expose a comparable form across markdown and output.
    """
    t = token.strip()
    # Strip trailing "% s Md Go etc"
    t = re.sub(r"\s*(?:%|pct|percent|epochs?|steps?|s|sec|seconds?|min|minutes?|h|hours?|ms|Md|B|M|G|K|Go|To|tokens?|params?|bits?)\s*$", "", t, flags=re.IGNORECASE)
    # Strip whitespace
    t = t.replace(" ", "").replace("\xa0", "")
    # Normalize commas. The "1,2 M" decimal-comma case (last group = 1-3 digits,
    # decimal) is the dominant francophone case; the "3,145,728" thousands case
    # is rarer. Test fixture pins: "3,145,728" -> "3145.728" (last comma = decimal,
    # not thousands -- ambiguous, but matches c.290 output text). Strategy:
    # join all but last segment with no separator, last segment prefixed with ".".
    if t.count(",") >= 1:
        comma_parts = t.split(",")
        # Drop thousand separators in middle (3-digit groups), then treat the
        # LAST comma as decimal point (francophone convention):
        # "3,145,728" -> "3" + ".145" + ".728" -> we keep "3.145.728" as
        # an artifact of our flattening. But the test pins "3145.728" --
        # meaning the FIRST comma is thousands, the LAST is decimal.
        # Resolve by: if there are >1 commas and middle groups are 3 digits,
        # drop those middle commas; keep last as decimal.
        if len(comma_parts) >= 3 and all(len(p) == 3 and p.isdigit() for p in comma_parts[1:-1]):
            # Drop middle thousand-separator commas; last becomes decimal.
            # "3,145,728" -> "3" + "145" + ".728" = "3145.728".
            head = "".join(comma_parts[:-1])
            tail = "." + comma_parts[-1]
            t = head + tail
        else:
            # Decimal comma (single or last is decimal)
            t = ".".join(comma_parts)
    return t


def _substantive(norm: str) -> bool:
    """A 'substantive' numeric claim is one whose magnitude is not ambiguous
    with section markers, footnotes, or list indices. Empirical floor:
    - len >= 4 (so '7' / '01' / '5' are skipped: section markers, FT-01 identifier)
    - OR len == 3 with a non-trivial decimal form (e.g. '3.1', '0.9', '1.3')
      -- these are real magnitudes: 'OPT-1.3B', 'LoRA r=3.1', etc.
    - not just '0' / '0.0' / '0.00' (zero is rarely a substantive claim)
    """
    if norm in {"0", "0.0", "0.00", "0.000", "0.0000"}:
        return False
    if len(norm) >= 4:
        return True
    if len(norm) == 3 and "." in norm:
        # Short decimal like '3.1' / '0.9' / '1.3' are real magnitudes.
        return True
    return False


def _output_text(outputs: list) -> str:
    """Flatten an `outputs` array (cell.output) into a single searchable string."""
    if not outputs:
        return ""
    chunks: list[str] = []
    for out in outputs:
        if not isinstance(out, dict):
            continue
        ot = out.get("output_type") or out.get("type")
        if ot == "stream":
            chunks.append(str(out.get("text", "")))
        elif ot in ("execute_result", "display_data"):
            data = out.get("data", {}) or {}
            for k in ("text/plain", "text/html", "application/vnd.jupyter.widget-view+json"):
                v = data.get(k)
                if isinstance(v, list):
                    chunks.append("".join(str(x) for x in v))
                elif v is not None:
                    chunks.append(str(v))
    return "\n".join(chunks)


def _lit_skip(source: str) -> bool:
    """Tell: a markdown cell is a literature block (long prose) vs a quantitative
    interpolation cell. We DON'T skip on length alone: c.290 pathologie sat in
    cells of length ~3000 chars (the cell with '## ~0,09 %'). Instead, we
    skip on EXPLICIT literature headers -- the convention is a heading, not
    a length."""
    s = source.lower()
    for marker in ("## bibliographie", "## references", "## pour aller plus loin",
                   "## further reading", "## sources", "## liens",
                   "## webographie", "## ressources complementaires"):
        if marker in s:
            return True
    return False


def _is_md_heading_line(line: str) -> bool:
    """A markdown heading line starts with #. Numbering like '## 7. Comparaison'
    is structural, not a quantitative claim."""
    return line.lstrip().startswith("#")


def _strip_md_structure(src: str) -> str:
    """Drop heading lines + code fences + table-headers so we only scan prose
    sentences. Code fences are STATEFUL (a ``` line opens and closes a block)."""
    kept: list[str] = []
    in_fence = False
    for line in src.splitlines():
        if line.strip().startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if _is_md_heading_line(line):
            continue
        if line.lstrip().startswith("|"):
            continue
        kept.append(line)
    return "\n".join(kept)


# Tokens that, when appearing immediately before a number, mark the
# number as a version reference (not a quantitative claim). Case
# insensitive, word-boundary anchored. The list is OPEN: c.366 FP
# manifest opened on SMT-LIB 2.6, Python 3.10, .NET 9.0, PEP 8,
# Mathlib 4, CUDA 12.x, pandas 2.x, Version=10.0.0, v2.5, Lean 4.
_VERSION_PREFIX_RE = re.compile(
    r"(?i)\b(?:"
    r"smt[-\s]?lib|sm[-\s]?lib|smlib|pep\b|python\b|\.?net\b|mathlib\b|"
    r"cuda\b|pandas\b|pytorch\b|numpy\b|scipy\b|transformers\b|peft\b|"
    r"bitsandbytes\b|huggingface\b|onnx\b|tensorflow\b|opencv\b|rust\b|"
    r"cargo\b|java\b|scala\b|kotlin\b|haskell\b|fsharp\b|f#|lean\b|"
    r"pypy\b|node\.?js?|golang\b|swift\b|angular\b|react\b|next\.?js?|"
    r"nuxt\b|svelte\b|spark\b|jupyter\b|latex\b|tex\b|miktex\b|"
    r"matlab\b|simulink\b|qt\b|kde\b|gnome\b|wayland\b|x11\b|"
    r"sqlite\b|mysql\b|postgres\b|redis\b|kafka\b|nginx\b|apache\b|"
    r"tomcat\b|maven\b|gradle\b|eslint\b|prettier\b|webpack\b|vite\b|"
    r"rollup\b|v\b|version\b|ver\b|release\b|rel\b|"
    r"r\b"
    r")\s*[=:=]?\s*$"
)


def _is_version_token(prose: str, match_pos: int) -> bool:
    """Return True if the numeric match at `match_pos` follows a version
    prefix token (SMT-LIB, Python, .NET, v, Version=).

    Looks at the 30 chars BEFORE the match, looking for the deepest
    version-prefix token that ends right before the match. Used to skip
    false positives where the markdown prose names a software version,
    not a measurement. c.366 / #11694."""
    prefix_start = max(0, match_pos - 30)
    prefix = prose[prefix_start:match_pos]
    # rstrip only trailing whitespace -- the regex anchors on 'end of
    # stripped prefix' so the literal token must be the LAST thing in
    # the prefix.
    stripped = prefix.rstrip()
    if not stripped:
        return False
    return bool(_VERSION_PREFIX_RE.search(stripped))


# Hints that mark an inline-code span as QUOTED text (exception message,
# version string, file path) rather than a measurement. The detector MUST
# skip these: the notebook reports a literal text, not a number it
# measured. c.366 / #11694.
_EXCEPTION_HINT_RE = re.compile(
    r"(?:" r"Exception|Error|Version=|FileNotFound|PermissionError|"
    r"ModuleNotFound|ImportError|OSError|RuntimeError|TypeError|"
    r"ValueError|KeyError|ServerError|ClientError|CudaError|"
    r"NaN|Inf|\.dll|\.so|\.jar|\.exe|\.pdb|\.lib|"
    r":[\\\\/]|\\\\Users\\\\|/Users/|:\\\\|/home/|Traceback|"
    r"assembly|Framework|version|FATAL"
    r")",
    re.IGNORECASE,
)

# Tightened hint set used ONLY for the LINE-scoped fallback. We restrict
# it to strongly-quoted-text signals so a line that happens to say
# "kernel" or "error" doesn't suppress unrelated legitimate numerics on
# the same line.
_EXCEPTION_LINE_HINT_RE = re.compile(
    r"(?:Exception|Version=|FileNotFound|Traceback|assembly)\b",
    re.IGNORECASE,
)


def _in_exception_code_span(prose: str, match_pos: int, match_end: int) -> bool:
    """Return True if the numeric match sits inside an inline code span
    (between two backticks) whose text carries an exception/version/path
    hint. The span is then QUOTED text, not a measurement.

    NOTE: the first argument MUST be `prose` (the markdown source with
    structural lines stripped by `_strip_md_structure`), not the raw
    cell source. The match positions `match_pos` / `match_end` are
    computed against `prose` (see c.415-L1 ★★). Passing the raw cell
    source under the misleading name `src` was a c.366 latent bug --
    offsets in the prose-stripped text don't match the raw source when
    headings / table headers / fences were removed, and the line
    fallback (`line_start = src.rfind("\\n", 0, match_pos) + 1`) would
    point to the wrong line. The productive call site (l. below) has
    always passed `prose` correctly; this rename pins the contract.

    Detection: trace the inline code span containing `match_pos` by
    counting backticks from the START of the cell (markdown inline
    spans are toggled by pairs of backticks; unescaped single backticks
    delimit span boundaries). If the matched span text carries a hint,
    the number is quoted. c.366 / #11694.

    Fallback: if the SPAN check misses (e.g. quoted assembly string
    "FSharp.Core.dll 10.x, assembly 10.0.0.0" outside any backtick pair),
    look at the surrounding LINE -- if the same line carries a hint,
    the line is reporting a literal text it saw, not measuring. We bound
    the hint-fallback to a single line so legitimate prose numbers on
    unrelated lines stay detected.
    """
    span_text = _nearest_inline_code_span(prose, match_pos)
    if span_text is not None and _EXCEPTION_HINT_RE.search(span_text):
        return True
    # Line-scoped fallback: same-line carries a strongly-quoted-text
    # signal (Exception / Version= / FileNotFound / Traceback / "assembly
    # 10.0.0.0" pattern). Distinguishes "talking about a 4.5 in prose"
    # from "quoting a file that says Version=10.0.0".
    line_start = prose.rfind("\n", 0, match_pos) + 1
    line_end = prose.find("\n", match_end)
    if line_end < 0:
        line_end = len(prose)
    line = prose[line_start:line_end]
    return bool(_EXCEPTION_LINE_HINT_RE.search(line))


def _nearest_inline_code_span(prose: str, pos: int) -> str | None:
    """Walk backticks inside a 200-char window around `pos` to find the
    enclosing inline code span (single-backtick convention); return its
    text or None if the position is not inside a span.

    Algorithm: collect backtick positions in [pos-200, pos+200). Find
    a PAIR (open, close) such that open < pos < close and no other
    opening between open and pos. Return prose[open+1:close].
    """
    WIN = 200
    lo = max(0, pos - WIN)
    hi = min(len(prose), pos + WIN)
    window = prose[lo:hi]
    # Find all backtick positions within the window (offset back to
    # absolute by adding lo).
    ticks = [lo + i for i, c in enumerate(window) if c == "`"]
    # Locate pos within the global list
    pos_idx = -1
    for i, t in enumerate(ticks):
        if t <= pos:
            pos_idx = i
        else:
            break
    if pos_idx < 0:
        return None
    # pos sits AFTER ticks[pos_idx]. If that tick is the OPENING of a
    # span, find the NEXT tick in ticks (the closing one). The span
    # contains pos iff ticks[pos_idx] < pos < ticks[pos_idx + 1].
    if pos_idx + 1 >= len(ticks):
        return None
    open_pos = ticks[pos_idx]
    close_pos = ticks[pos_idx + 1]
    if open_pos >= pos or close_pos <= pos:
        return None
    # If there is a tick between open_pos and pos with no matching
    # closing on the same side, the span structure is ambiguous;
    # still take the immediately enclosing pair -- it's what
    # markdown renderers do for adjacent spans.
    return prose[open_pos + 1:close_pos]


def check_notebook(path: Path) -> dict:
    """Scan a single notebook. Returns a structured dict compatible with
    JSON serialization (so the script can be consumed by CI gates)."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return {
            "path": str(path),
            "verdict": "ERROR",
            "errors": [f"json.loads failed: {e}"],
            "findings": [],
        }

    cells = nb.get("cells", []) or []
    findings: list[dict] = []
    skipped_lit = 0
    skipped_no_prev = 0
    skipped_no_output = 0

    for idx, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        src = "".join(cell.get("source", []) if isinstance(cell.get("source"), list) else [str(cell.get("source", ""))])
        if not src or _lit_skip(src):
            skipped_lit += 1
            continue
        # Drop heading lines + table-headers + code fences from the prose
        # we scan (structurals are not quantitative claims).
        prose = _strip_md_structure(src)
        # Find the previous code cells (within window) with output
        prev_code_idxs: list[int] = []
        for j in range(idx - 1, -1, -1):
            if cells[j].get("cell_type") == "code":
                prev_code_idxs.append(j)
                if len(prev_code_idxs) >= WINDOW:
                    break
        if not prev_code_idxs:
            skipped_no_prev += 1
            continue
        # Concat outputs of the previous code cells (within window)
        out_chunks: list[str] = []
        any_output = False
        for j in prev_code_idxs:
            outs = cells[j].get("outputs") or []
            if outs:
                any_output = True
            out_chunks.append(_output_text(outs))
        if not any_output:
            skipped_no_output += 1
            continue
        out_text = "\n".join(out_chunks)
        # Extract numeric claims from the markdown prose. We iterate via
        # finditer so we get (span_start, span_end, raw) for each match
        # -- this is needed for the version-token and inline-code-span
        # filters added in c.366 / #11694.
        for m in NUMERIC_RE.finditer(prose):
            raw = m.group(0)
            match_pos = m.start()
            match_end = m.end()
            norm = _normalize_num(raw)
            if not _substantive(norm):
                continue
            # FP filters (c.366): skip version-number citations and
            # numbers inside quoted exception/version/path spans.
            if _is_version_token(prose, match_pos):
                continue
            if _in_exception_code_span(prose, match_pos, match_end):
                continue
            # Search the normalized form in the output text (plus adjacent
            # variants: e.g. "0.24" present in "0.2385")
            if norm not in out_text and not _fuzzy_present(norm, out_text):
                findings.append({
                    "markdown_cell": idx,
                    "code_cell": prev_code_idxs[0],
                    "window": prev_code_idxs,
                    "raw": raw,
                    "normalized": norm,
                    "context": _excerpt(src, raw),
                })

    n_findings = len(findings)
    verdict = "CLEAN" if n_findings == 0 else "FABRICATION_DETECTED"
    return {
        "path": str(path),
        "verdict": verdict,
        "findings": findings,
        "stats": {
            "skipped_literature": skipped_lit,
            "skipped_no_prev_code": skipped_no_prev,
            "skipped_no_output": skipped_no_output,
        },
    }


def _fuzzy_present(norm: str, out_text: str) -> bool:
    """A numeric claim may match output via several patterns:
      (a) prefix-of-output: '1.3' matches '1.3B' for magnitude (followed by
          non-digit) -- '1.3' does NOT match '1.32 Go' (followed by digit
          AND not at start of output).
      (b) rounded-head: '0.24' matches '0.2385' (output's start IS a
          TRUNCATION of the norm with a digit continuation).
      (c) magnitude-prefix against comma-stripped output: '3.1' matches
          '3,145,728' (output has 3,145,728 = 3.1M, claim is the magnitude
          prefix when thousand separators are stripped).
    The minimum norm length is 3 chars (so '7' / '5' are skipped).
    """
    if len(norm) < 3:
        return False
    # Clause (a): prefix is present in the output, followed by non-digit.
    for cut in range(len(norm), 2, -1):
        prefix = norm[:cut]
        pos = 0
        while True:
            i = out_text.find(prefix, pos)
            if i < 0:
                break
            after = out_text[i + len(prefix):i + len(prefix) + 1]
            if not after or not after.isdigit():
                return True
            pos = i + 1
    # Clause (b): output's start IS a TRUNCATION of the norm with digit
    # continuation (norm rounded up to a finer-precision output).
    if len(norm) >= 4:
        truncated = norm[:-1]
        if out_text.startswith(truncated):
            after = out_text[len(truncated):len(truncated) + 1]
            if after and after.isdigit():
                return True
    # Clause (c): norm is a magnitude prefix when output's thousand
    # separators are stripped (output "3,145,728" -> "3145728", norm
    # "3.1" -- treat the dot in the norm as a marker; we re-anchor the
    # norm against the output by matching the leading digits before the
    # dot). Gated by len(norm) >= 4 OR the output containing a comma
    # (large-number signal: 3.1M magnitude against 3,145,728). The
    # comma-gate distinguishes '3.1' vs '3,145,728' (magnitude) from
    # '1.3' vs '1.32' (precision -- no comma, no magnitude match).
    if "." in norm and len(norm) >= 3 and ("," in out_text or len(norm) >= 4):
        head, tail = norm.split(".", 1)
        digit_run = re.sub(r"[^0-9]", "", out_text)
        combined = head + tail  # e.g. "3.1" -> "31"
        if combined and combined in digit_run:
            pos = digit_run.find(combined)
            tail_len = len(digit_run) - (pos + len(combined))
            # Tolerance: a 7-digit "3,145,728" has 5 trailing digits
            # after the magnitude "31". Cap at 12 digits total in the
            # digit_run (8+ trailing) so the magnitude is bounded.
            if tail_len <= 12:
                return True
    return False


def _excerpt(src: str, raw: str) -> str:
    """Return a 70-char excerpt around the raw claim, for diagnostics."""
    pos = src.find(raw)
    if pos < 0:
        return raw[:70]
    start = max(0, pos - 30)
    end = min(len(src), pos + len(raw) + 40)
    return src[start:end].replace("\n", " ")[:120]


def render(result: dict) -> str:
    lines: list[str] = []
    p = result["path"]
    v = result["verdict"]
    head = f"NOTEBOOK {p} -- verdict: {v}"
    lines.append(head)
    lines.append("=" * len(head))
    if result.get("errors"):
        for e in result["errors"]:
            lines.append(f"  ! {e}")
    s = result.get("stats", {})
    if s:
        lines.append(
            f"  scanned: lit-skip={s.get('skipped_literature', 0)}, "
            f"no-prev={s.get('skipped_no_prev_code', 0)}, "
            f"no-output={s.get('skipped_no_output', 0)}"
        )
    if result["findings"]:
        lines.append(f"  findings: {len(result['findings'])} potential fabrication(s)")
        for f in result["findings"]:
            lines.append(
                f"    md[{f['markdown_cell']}] (after code[{f['code_cell']}]) "
                f"raw={f['raw']!r} normalized={f['normalized']!r}"
            )
            lines.append(f"      context: ...{f['context']}...")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Detect markdown cells that cite numeric values absent from the "
            "previous code cell's output (c.290 pathologie, C.5 violation)."
        ),
        epilog=(
            "Exit: 0 CLEAN, 1 FABRICATION_DETECTED, 2 ERROR. "
            "Use --json for CI gate consumption."
        ),
    )
    ap.add_argument("notebooks", nargs="+", help="paths to .ipynb files")
    ap.add_argument("--window", type=int, default=WINDOW,
                    help=f"number of previous code cells to scan (default {WINDOW})")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="JSON output (one result per notebook)")
    args = ap.parse_args()

    results: list[dict] = []
    for nb_path in args.notebooks:
        p = Path(nb_path)
        if not p.exists():
            results.append({
                "path": str(p),
                "verdict": "ERROR",
                "errors": [f"file not found: {p}"],
                "findings": [],
            })
            continue
        results.append(check_notebook(p))

    if args.as_json:
        print(json.dumps(results, ensure_ascii=False, indent=2))
    else:
        for r in results:
            print(render(r))
            print()

    fabricated = sum(1 for r in results if r["verdict"] == "FABRICATION_DETECTED")
    errored = sum(1 for r in results if r["verdict"] == "ERROR")
    if errored:
        return 2
    return 1 if fabricated else 0


if __name__ == "__main__":
    sys.exit(main())
