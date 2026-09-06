#!/usr/bin/env python3
"""Scan notebooks for the systemic defects of the "enrich" density wave.

Productionises the validator extension asked for on CoursIA #13410 (comments
2026-09-01 19:36Z and 20:19Z, NanoClaw aggregate) and roo-extensions #3374:
the enrich generator ships recurring defect classes that the cell-ORDERING
scanner (scan_cell_ordering.py, Epic #3240) cannot see, because they are
CONTENT defects, not position defects. Every check below was calibrated
against the real wave PRs (#14161, #14164, #14166): each reproduces the
corresponding reviewer finding, and legitimate patterns stay silent.

Defect classes and their mechanical checks:

  Class (a) cited facts must be grounded in real outputs
    LOW   UNGROUNDED_NUMBER    a specific decimal (>= 4 digits) cited in an
                               anchored markdown cell appears nowhere in the
                               notebook's code sources or text outputs
  Class (b) "extended cells" must not become rewrites
    HIGH  MD_REWRITE           < 25% of the base's substantive markdown lines
                               survive verbatim in head (vs --base only)
    MED   MD_SURVIVAL_LOW      < 50% survive -- the rewrite-more-than-extend
                               signature of the wave (#14161 measured 30%,
                               #14166 20%, #14164 31%)
  Class (c) accents must survive enrichment
    HIGH  DIACRITICS_LOSS      a markdown line survives enrichment only as
                               its de-accented skeleton (#14166 measured
                               99 -> 1 chars, i.e. -99%); content REMOVED by
                               the PR is exempt (#14795: splitting 15
                               accented cells out of GT-04 collapsed the
                               file total while every surviving line kept
                               its accents)
  Class (d) inline arithmetic must be true
    HIGH  ARITH_WRONG          "A x B = C" stated in markdown is false
  Class (e) hrefs must resolve at head
    HIGH  HREF_MISSING         a relative href resolves to no file in the
                               repo tree (#14127: 2 rewritten hrefs -> 404)
  Class (f) `code[N]` anchors must resolve at HEAD, not at MAIN
    HIGH  ANCHOR_OOR           N >= number of code cells: the pointer is out
                               of range in code-index space (#14166: 4/13
                               anchors; #14164: 6/12)
    MED   ANCHOR_ABS_MD        absolute cell N is markdown at head: the
                               generator wrote the anchor against MAIN's
                               absolute layout and the inserted markdown
                               shifted it onto a markdown cell (#14161:
                               5/8 unique pointers landed on markdown)
    MED   ANCHOR_ADJACENCY     under the code-index convention the pointer
                               resolves to neither the nearest preceding nor
                               the nearest following code cell of the
                               markdown that carries it
  Class (g) entities taught must exist
    HIGH  PHANTOM_IN_FENCE     an identifier shown inside fenced code blocks
                               (>= 2 fences) exists nowhere in the notebook's
                               code or text outputs (#14166: `Race` shown 6x
                               while the code defines `Switch`)
  Class (h) no complete solution in front of a TODO exercise
    HIGH  SOLUTION_LEAK        the markdown cell directly before a TODO
                               exercise cell carries a fenced block that
                               looks like a worked solution (#14161: full
                               proof protocols before `-- TODO etudiant`)

Precision-first, like scan_cell_ordering.py: the scanner is READ-ONLY, every
finding cites its evidence, MED/LOW findings are signals for the reviewer,
and the CI wrapper (enrich_quality_ci.py) gates on NEW HIGH findings only.

Anchor convention imposed by this scanner (the fix for class (f)):
`code[N]` = the N-th CODE cell, 0-based, counted in the HEAD layout, i.e.
after every markdown insertion. Generators that index against MAIN (or mix
absolute and code-index spaces) trip ANCHOR_OOR / ANCHOR_ABS_MD /
ANCHOR_ADJACENCY.

Usage:
    python scan_enrich_quality.py <notebook.ipynb>
    python scan_enrich_quality.py <notebook.ipynb> --base <base.ipynb>
    python scan_enrich_quality.py --family Search/Part2-CSP
    python scan_enrich_quality.py --all --severity MED --json

Exit codes:
    0 - no findings at or above --fail-on (default HIGH)
    1 - findings at or above --fail-on
    2 - usage / IO error
"""

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIRS = {
    ".ipynb_checkpoints", ".git", "__pycache__", "obj", "bin",
    "_output", "research", "archive", "partner-course", "examples",
    ".venv", "node_modules",
}

SEVERITY_ORDER = {"LOW": 0, "MED": 1, "HIGH": 2}

# --- anchors (class f) ------------------------------------------------------

_ANCHOR_RE = re.compile(r"\bcode\[(\d+)\]")

# --- TODO / exercise markers (class h) --------------------------------------

_TODO_RE = re.compile(r"(TODO[_ ]etudiant|TODO[_ ]student|à compléter|a completer|\bsorry\b)", re.I)

# A fenced block line that reads like implementation, not like a skeleton.
# Skeletons end on `;` / `{` / `...` and carry no body; solutions have
# `exact ...`, `return ...`, `:= ...`, `x = ...` bodies.
_BODYISH_RE = re.compile(r"\b(exact|return|yield|printfn|println|Console\.WriteLine)\b|:=|=>|[^=!<>+\-*/]=[^=]")
# A fenced block must also contain at least one LOGIC line to count as a
# worked solution: exercise scaffolding legitimately shows given-data
# assignments (`jobs_data = [...]`) and API call lines (`using var h = ...`)
# in front of TODO cells -- those are not leaks.
_LOGIC_RE = re.compile(r"\b(foreach|for|while|if|exact|return|theorem|proof|match|switch)\b|:=\s*by")

# --- arithmetic (class d) ---------------------------------------------------

_ARITH_RE = re.compile(
    r"(\d+(?:[.,]\d+)?)\s*[×x\*]\s*(\d+(?:[.,]\d+)?)\s*=\s*(\d[\d\s ]*(?:[.,]\d+)?)")

# --- hrefs (class e) --------------------------------------------------------

_MD_LINK_RE = re.compile(r"\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
_HTML_HREF_RE = re.compile(r"<a\s[^>]*href=\"([^\"]+)\"", re.I)
_SKIP_TARGET_PREFIXES = ("http://", "https://", "mailto:", "#", "data:", "/")

# --- accents (class c) ------------------------------------------------------

_ACCENT_RE = re.compile(r"[À-ÖØ-öø-ÿĀ-žŒœ]")

# --- numbers (class a) ------------------------------------------------------

_DECIMAL_RE = re.compile(r"\b\d+\.\d+\b")
# significant digits >= 4 -- precise enough that a fabricated value is a
# signal, generic enough that bounds (0.05) and constants (0.99) stay silent

# --- phantoms (class g) -----------------------------------------------------

_FENCE_RE = re.compile(r"^\s*(```+|~~~+)\s*(\w*)")
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]{2,}")
# A line that reads as CODE, not as prose or simulated output: prose like
# "Planning realisable avec B : duree = 4.5h" has none of these constructs.
_CODEISH_LINE_RE = re.compile(r"[([{};]|:=|=>|\"")
# Trailing comments (Lean `--`, C# `//`, Python `#`) carry French prose words
# that are not entities ("chaque poids vaut 1/2") -> stripped before tokens.
_TRAILING_COMMENT_RE = re.compile(r"\s(--|//|#)\s.*$")
# fences whose info string marks runnable code; shell/console/json fences
# legitimately name external commands and are not phantom territory
_CODE_FENCE_LANGS = {
    "", "python", "py", "lean", "csharp", "cs", "cpp", "c", "java", "kotlin",
    "ts", "typescript", "js", "javascript", "fsharp", "fs", "rust", "rs",
}
_KEYWORDS = {
    "for", "while", "def", "class", "return", "import", "from", "print",
    "self", "this", "void", "public", "static", "private", "let", "mut",
    "fun", "var", "const", "new", "if", "else", "elif", "not", "and", "or",
    "None", "True", "False", "true", "false", "nil", "in", "is", "lambda",
    "with", "try", "except", "raise", "yield", "using", "namespace", "string",
    "int", "float", "bool", "list", "dict", "set", "tuple", "len", "range",
    "theorem", "example", "lemma", "proof", "sorry", "admit", "exact",
    "have", "show", "fun", "match", "case", "switch", "break", "continue",
    "defn", "main", "args", "console", "system", "math", "task", "async",
    "await", "throw", "catch", "finally", "struct", "enum", "interface",
    "extends", "implements", "override", "virtual", "abstract", "sealed",
    "internal", "protected", "readonly", "write", "read", "open", "close",
}


def _src(cell: dict) -> str:
    src = cell.get("source", [])
    return src if isinstance(src, str) else "".join(src)


def _output_text(cell: dict) -> str:
    """Text of a code cell's outputs, EXCLUDING base64 image payloads.

    A bare `Race` match inside an image/png base64 blob (#14166) is pure
    alphabet coincidence -- only text lanes are evidence of existence.
    """
    parts = []
    for out in cell.get("outputs", []) or []:
        if not isinstance(out, dict):
            continue
        if out.get("output_type") == "stream":
            t = out.get("text", [])
            parts.append(t if isinstance(t, str) else "".join(t))
            continue
        data = out.get("data") or {}
        for key in ("text/plain", "text/html", "text/markdown"):
            t = data.get(key)
            if isinstance(t, str):
                parts.append(t)
            elif isinstance(t, list):
                parts.append("".join(t))
    return "\n".join(parts)


def _md_cells(cells: list[dict]):
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "markdown":
            yield i, cell


def _fenced_blocks(text: str) -> list[tuple[str, str]]:
    """(info_string, block_text) for each fenced block; fences toggling only."""
    blocks, cur, info, in_fence = [], [], "", False
    for ln in text.splitlines():
        m = _FENCE_RE.match(ln)
        if m:
            if in_fence:
                blocks.append((info, "\n".join(cur)))
                cur, in_fence = [], False
            else:
                info, cur, in_fence = m.group(2).lower(), [], True
            continue
        if in_fence:
            cur.append(ln)
    return blocks


def scan_anchors(cells: list[dict]) -> list[dict]:
    """Class (f): code[N] must resolve to a code cell in the HEAD layout."""
    findings = []
    n = len(cells)
    code_abs = [i for i, c in enumerate(cells) if c.get("cell_type") == "code"]
    n_code = len(code_abs)
    for i, cell in _md_cells(cells):
        text = _src(cell)
        seen: set[int] = set()
        for m in _ANCHOR_RE.finditer(text):
            idx = int(m.group(1))
            if idx in seen:
                continue
            seen.add(idx)
            if idx >= n_code:
                abs_state = "markdown" if idx < n and cells[idx].get("cell_type") == "markdown" else "out of notebook"
                findings.append({
                    "cell_index": i, "category": "ANCHOR_OOR", "severity": "HIGH",
                    "evidence": m.group(0),
                    "message": f"code[{idx}] exceeds the {n_code} code cell(s) of the head layout "
                               f"(absolute cell {idx} is {abs_state}); anchors must index the "
                               f"head's code cells, not MAIN's layout",
                })
                continue
            target = code_abs[idx]
            before = [a for a in code_abs if a < i]
            after = [a for a in code_abs if a > i]
            nearest = {before[-1]} if before else set()
            if after:
                nearest.add(after[0])
            adjacency_ok = not nearest or target in nearest
            # The absolute-md reading only matters when the code-index reading
            # is ALSO wrong (non-adjacent): a correctly code-indexed anchor in
            # a notebook whose absolute cell N happens to be prose is healthy.
            if not adjacency_ok and idx < n and cells[idx].get("cell_type") == "markdown":
                findings.append({
                    "cell_index": i, "category": "ANCHOR_ABS_MD", "severity": "MED",
                    "evidence": m.group(0),
                    "message": f"code[{idx}] points at a markdown cell in absolute indexing AND "
                               f"misses the nearest code cells; if the anchor was written against "
                               f"MAIN's absolute layout, inserted markdown shifted it onto prose -- "
                               f"rebase to the head layout",
                })
            if not adjacency_ok:
                findings.append({
                    "cell_index": i, "category": "ANCHOR_ADJACENCY", "severity": "MED",
                    "evidence": m.group(0),
                    "message": f"code[{idx}] resolves to code cell {target}, not the nearest code "
                               f"cell(s) around this markdown ({sorted(nearest)})",
                })
    return findings


def _deaccent(text: str) -> str:
    return "".join(ch for ch in unicodedata.normalize("NFD", text.lower())
                   if not unicodedata.combining(ch))


def scan_diacritics(head_cells: list[dict], base_cells: list[dict] | None) -> list[dict]:
    """Class (c): surviving markdown lines must keep their accents.

    A line REMOVED by the PR is content removal, not de-accentation (#14795:
    splitting 15 accented cells out of GT-04 collapsed the total 375 -> 96
    while every surviving line kept its accents). The loss signature is a
    line that survives -- same de-accented skeleton -- with all its accents
    gone, the #14166 enrich-wave defect.
    """
    if base_cells is None:
        return []
    skeleton_accents: dict[str, list[int]] = {}
    for _, c in _md_cells(head_cells):
        for ln in _src(c).splitlines():
            s = _deaccent(ln.strip())
            if len(s) >= 15:
                skeleton_accents.setdefault(s, []).append(
                    len(_ACCENT_RE.findall(ln)))
    lost_lines = 0
    lost_chars = 0
    for _, c in _md_cells(base_cells):
        for ln in _src(c).splitlines():
            accents = len(_ACCENT_RE.findall(ln))
            if accents < 3:  # too few for one line to speak of a loss
                continue
            s = _deaccent(ln.strip())
            if len(s) < 15:
                continue
            counts = skeleton_accents.get(s)
            if counts and max(counts) == 0:
                lost_lines += 1
                lost_chars += accents
    if not lost_lines:
        return []
    # HIGH from 10 lost chars (2-3 typical md lines) or 3 lines; the wave
    # incident #14166 measured 99 lost chars.
    severity = "HIGH" if (lost_lines >= 3 or lost_chars >= 10) else "MED"
    return [{
        "cell_index": 0, "category": "DIACRITICS_LOSS", "severity": severity,
        "evidence": f"{lost_lines} surviving line(s) lost {lost_chars} accented char(s)",
        "message": f"{lost_lines} markdown line(s) survive only as de-accented "
                   f"rewrites ({lost_chars} accented chars lost) -- content "
                   f"removed by the PR is exempt, only surviving lines count",
    }]


def scan_survival(head_cells: list[dict], base_cells: list[dict] | None) -> list[dict]:
    """Class (b): extended cells keep their substance; rewrites get flagged."""
    if base_cells is None:
        return []
    lines = []
    for _, c in _md_cells(base_cells):
        for ln in _src(c).splitlines():
            if len(ln.strip()) >= 15:
                lines.append(ln.strip())
    if not lines:
        return []
    head_text = "\n".join(_src(c) for _, c in _md_cells(head_cells))
    survived = sum(1 for ln in lines if ln in head_text)
    pct = survived / len(lines)
    if pct < 0.25:
        return [{
            "cell_index": 0, "category": "MD_REWRITE", "severity": "HIGH",
            "evidence": f"{survived}/{len(lines)} base lines survive",
            "message": f"only {survived}/{len(lines)} substantive markdown lines of the base "
                       f"survive verbatim ({pct:.0%}) -- announced extension is a rewrite",
        }]
    if pct < 0.5:
        return [{
            "cell_index": 0, "category": "MD_SURVIVAL_LOW", "severity": "MED",
            "evidence": f"{survived}/{len(lines)} base lines survive",
            "message": f"{survived}/{len(lines)} substantive markdown lines survive verbatim "
                       f"({pct:.0%}) -- rewrite-more-than-extend signature",
        }]
    return []


def scan_href(notebook: Path, cells: list[dict], repo_root: Path) -> list[dict]:
    """Class (e): relative hrefs must resolve against the real tree at head."""
    findings = []
    nb_dir = notebook.parent
    for i, cell in _md_cells(cells):
        targets = _MD_LINK_RE.findall(_src(cell)) + _HTML_HREF_RE.findall(_src(cell))
        seen = set()
        for t in targets:
            t = unquote(t).strip()
            frag = t.split("#", 1)[0].strip()
            if not frag or frag != frag.lstrip():
                continue
            if any(frag.startswith(p) for p in _SKIP_TARGET_PREFIXES):
                continue
            frag = frag.rstrip("/")
            if frag in seen:
                continue
            seen.add(frag)
            candidates = [
                repo_root / frag,
                nb_dir / frag,
                repo_root / (frag + ".ipynb"),
                nb_dir / (frag + ".ipynb"),
            ]
            if not any(p.exists() for p in candidates):
                findings.append({
                    "cell_index": i, "category": "HREF_MISSING", "severity": "HIGH",
                    "evidence": frag[:120],
                    "message": f"relative href '{frag}' resolves to no file under the repo tree "
                               f"(checked repo root and notebook dir)",
                })
    return findings


def scan_solution_leak(cells: list[dict]) -> list[dict]:
    """Class (h): no worked solution directly in front of a TODO exercise."""
    findings = []
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        src = _src(cell)
        if not _TODO_RE.search(src):
            continue
        if i == 0 or cells[i - 1].get("cell_type") != "markdown":
            continue
        code_tokens = set(_IDENT_RE.findall(src))
        for info, block in _fenced_blocks(_src(cells[i - 1])):
            if not block.strip() or _TODO_RE.search(block):
                continue  # a skeleton (with its own TODO/sorry) is scaffolding
            bodyish = [ln for ln in block.splitlines()
                       if ln.strip() and _BODYISH_RE.search(ln)]
            if not bodyish:
                continue
            if not _LOGIC_RE.search(block):
                continue  # given-data / API-call scaffolding, not a solution
            shared = sorted(t for t in set(_IDENT_RE.findall(block)) & code_tokens
                            if len(t) >= 5)[:4]
            if len(shared) < 2:
                continue
            findings.append({
                "cell_index": i - 1, "category": "SOLUTION_LEAK", "severity": "HIGH",
                "evidence": bodyish[0].strip()[:120],
                "message": f"worked-solution block directly before the TODO exercise "
                           f"(shares {', '.join(shared)}); move it to a solutions annex",
            })
    return findings


def scan_arithmetic(cells: list[dict]) -> list[dict]:
    """Class (d): stated inline multiplication must be arithmetically true."""
    findings = []
    for i, cell in _md_cells(cells):
        text = _src(cell)
        for m in _ARITH_RE.finditer(text):
            # Skip the tail of a longer sum: "2 x 7 x 3 = 42" and
            # "20x5 + 25x3 + ... = 375" match their tail "7 x 3 = 42" /
            # "40x2 = 375" unless the char before the first operand is
            # guarded.
            before = text[:m.start()].rstrip()
            if before and before[-1] in "0123456789.,×x*+-":
                continue
            a = float(m.group(1).replace(",", "."))
            b = float(m.group(2).replace(",", "."))
            raw = m.group(3).replace(" ", "").replace(" ", "").replace(",", ".")
            try:
                c = float(raw)
            except ValueError:
                continue
            if a == 0 or b == 0:
                continue
            expected = a * b
            if c != 0 and abs(expected - c) / max(abs(expected), abs(c)) > 0.02:
                findings.append({
                    "cell_index": i, "category": "ARITH_WRONG", "severity": "HIGH",
                    "evidence": m.group(0)[:120],
                    "message": f"stated '{m.group(0).strip()[:60]}' is false: "
                               f"{m.group(1)} x {m.group(2)} = {expected:g}",
                })
    return findings


def scan_phantom(cells: list[dict]) -> list[dict]:
    """Class (g): an identifier shown as code in >= 2 fences must exist."""
    findings = []
    fence_counts: dict[str, int] = {}
    for _, cell in _md_cells(cells):
        for info, block in _fenced_blocks(_src(cell)):
            if info not in _CODE_FENCE_LANGS:
                continue
            idents = set()
            for raw in block.splitlines():
                s = _TRAILING_COMMENT_RE.sub("", raw.strip())
                if not s or s.startswith(("#", "//", "--", "*")):
                    continue
                if not _CODEISH_LINE_RE.search(s):
                    continue
                for m in _IDENT_RE.finditer(s):
                    tok = m.group(0)
                    if tok in _KEYWORDS:
                        continue
                    after = s[m.end():m.end() + 2]
                    before = s[max(0, m.start() - 2):m.start()]
                    used_as_code = (
                        after[:1] in ("(", '"', ".")
                        or after[:2] in (" =", ":=", "<-", "::")
                        or before in (".", "::")
                    )
                    if used_as_code:
                        idents.add(tok)
            for tok in idents:
                fence_counts[tok] = fence_counts.get(tok, 0) + 1
    corpus = "\n".join(
        [_src(c) for c in cells if c.get("cell_type") == "code"]
        + [_output_text(c) for c in cells if c.get("cell_type") == "code"]
    )
    for tok, count in sorted(fence_counts.items()):
        if count < 2:
            continue
        if not re.search(rf"(?<![A-Za-z0-9_]){re.escape(tok)}(?![A-Za-z0-9_])", corpus):
            findings.append({
                "cell_index": 0, "category": "PHANTOM_IN_FENCE", "severity": "HIGH",
                "evidence": f"{tok} x{count} in fences",
                "message": f"entity '{tok}' is shown as code in {count} fenced block(s) but "
                           f"exists nowhere in the notebook's code or outputs "
                           f"(phantom rename of a real entity?)",
            })
    return findings


def scan_numbers(cells: list[dict]) -> list[dict]:
    """Class (a): specific decimals in anchored cells must be grounded."""
    findings = []
    corpus = "\n".join(
        [_src(c) for c in cells if c.get("cell_type") == "code"]
        + [_output_text(c) for c in cells if c.get("cell_type") == "code"]
    )
    for i, cell in _md_cells(cells):
        text = _src(cell)
        if not _ANCHOR_RE.search(text):
            continue
        missing = []
        for m in _DECIMAL_RE.finditer(text):
            val = m.group(0)
            if len(val.replace(".", "")) < 4:
                continue  # bounds and short constants are not evidence-grade
            pat = rf"(?<![\d.]){re.escape(val)}(?![\d.])"
            if not re.search(pat, corpus):
                missing.append(val)
        if missing:
            uniq = sorted(set(missing))[:3]
            findings.append({
                "cell_index": i, "category": "UNGROUNDED_NUMBER", "severity": "LOW",
                "evidence": ", ".join(uniq),
                "message": f"precise decimal(s) {', '.join(uniq)} cited in an anchored cell "
                           f"appear in no code source or output -- verify against the anchored run",
            })
    return findings


def scan_notebook(path: Path, base: Path | None = None, repo_root: Path | None = None) -> dict:
    repo_root = repo_root or REPO_ROOT
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as exc:
        return {"path": str(path), "error": str(exc), "findings": []}
    base_cells = None
    if base is not None:
        try:
            base_cells = json.loads(base.read_text(encoding="utf-8")).get("cells", [])
        except (json.JSONDecodeError, UnicodeDecodeError, OSError):
            base_cells = None
    cells = nb.get("cells", [])
    findings = (
        scan_anchors(cells)
        + scan_diacritics(cells, base_cells)
        + scan_survival(cells, base_cells)
        + scan_href(path, cells, repo_root)
        + scan_solution_leak(cells)
        + scan_arithmetic(cells)
        + scan_phantom(cells)
        + scan_numbers(cells)
    )
    findings.sort(key=lambda f: (f["cell_index"], -SEVERITY_ORDER[f["severity"]]))
    return {"path": str(path), "findings": findings}


def find_notebooks(family: str | None = None) -> list[Path]:
    root = NOTEBOOKS_DIR / family if family else NOTEBOOKS_DIR
    if not root.exists():
        return []
    out = []
    for p in root.rglob("*.ipynb"):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        out.append(p)
    return sorted(out)


def _rel(path: str) -> str:
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return path


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Scan notebooks for enrich-wave content defects (classes (a)-(h)).")
    ap.add_argument("notebook", nargs="?", help="single notebook path")
    ap.add_argument("--base", help="base revision of the notebook (enables classes (b) and (c))")
    ap.add_argument("--family", help="scan a family dir under MyIA.AI.Notebooks/")
    ap.add_argument("--all", action="store_true", help="scan all pedagogical notebooks")
    ap.add_argument("--repo-root", default=None, help="tree against which hrefs resolve (default: this repo)")
    ap.add_argument("--json", action="store_true", help="JSON output")
    ap.add_argument("--severity", choices=["LOW", "MED", "HIGH"], help="only show findings at/above this severity")
    ap.add_argument("--fail-on", choices=["LOW", "MED", "HIGH"], default="HIGH",
                    help="exit 1 if any finding at/above this severity (default HIGH)")
    args = ap.parse_args(argv)

    if args.notebook:
        targets = [Path(args.notebook)]
    elif args.family:
        targets = find_notebooks(args.family)
    elif args.all:
        targets = find_notebooks()
    else:
        ap.error("provide a notebook path, --family, or --all")
        return 2

    if not targets:
        print("No notebooks found.", file=sys.stderr)
        return 2

    repo_root = Path(args.repo_root).resolve() if args.repo_root else REPO_ROOT
    min_show = SEVERITY_ORDER[args.severity] if args.severity else -1
    fail_at = SEVERITY_ORDER[args.fail_on]

    reports = []
    worst = -1
    for path in targets:
        base = Path(args.base) if args.base and args.notebook else None
        rep = scan_notebook(path, base=base, repo_root=repo_root)
        rep["findings"] = [f for f in rep["findings"] if SEVERITY_ORDER[f["severity"]] >= min_show]
        if rep["findings"]:
            worst = max(worst, max(SEVERITY_ORDER[f["severity"]] for f in rep["findings"]))
        reports.append(rep)

    if args.json:
        print(json.dumps({"reports": [r for r in reports if r.get("findings") or r.get("error")]},
                         ensure_ascii=False, indent=2))
    else:
        total = 0
        for rep in reports:
            if rep.get("error"):
                print(f"  ERROR {_rel(rep['path'])}: {rep['error']}")
                continue
            if not rep["findings"]:
                continue
            print(f"\n{_rel(rep['path'])}")
            for f in rep["findings"]:
                total += 1
                print(f"  [{f['severity']:4}] cell#{f['cell_index']:<3} {f['category']:18} {f['message']}")
                print(f"         > {f['evidence']}")
        scanned = len(targets)
        clean = sum(1 for r in reports if not r.get("findings") and not r.get("error"))
        print(f"\nScanned {scanned} notebook(s): {clean} clean, {total} finding(s).")

    return 1 if worst >= fail_at else 0


if __name__ == "__main__":
    sys.exit(main())
