#!/usr/bin/env python3
"""Check that math syntax in notebook markdown cells actually renders.

Motivation (#17380, user review of IIT-06): "pas mal de syntaxe mathematique
n'est pas interpretee et formatee dans les paragraphes de markdown". The
notebook itself measured CLEAN (62/62 scopes render under KaTeX 0.18, zero
orphan dollars) -- the non-rendering the user saw was the VIEWER's (VS Code
does not render inline `$...$` in notebook markdown cells by default), not
the notebook's. But the corpus-wide question stands: which notebooks carry
math that NO mainstream viewer (Jupyter MathJax, GitHub, VS Code/KaTeX)
would render as written?

Four detectable classes, markdown cells only (in code cells LaTeX-looking
text is legitimate). Two discriminants learned from the first corpus
measurement (458 raw hits, most of them false positives): fenced code
blocks (```` ``` ````) are masked before everything -- Lean/pseudo-code and
shell `$var` inside fences are code, not prose -- and a `$` immediately
followed by a digit is currency ("costs $5"), not a math delimiter:

  1. LATEX-PURE-DELIMS -- `\\(...\\)` or `\\[...\\]` in markdown prose.
     Jupyter, GitHub and VS Code render `$...$` / `$$...$$`; the pure LaTeX
     delimiters are left as literal text. Detected outside code spans.
  2. ODD-DOLLARS -- a paragraph (blank-line-separated block) whose count of
     single `$` is odd after removing paired `$$`, code and currency: one
     unmatched dollar silently breaks MathJax pairing for the WHOLE
     paragraph, so valid formulas elsewhere in it stop rendering too.
  3. NUDE-LATEX -- a known LaTeX command (`\\Phi`, `\\mathbb`, `\\frac`, ...)
     outside any math scope and outside code: prose that was meant to be
     math but lost its delimiters renders as raw backslash soup.
  4. KATEX-UNRENDERABLE -- a `$...$` / `$$...$$` scope that KaTeX refuses
     (throwOnError). This is the empirical class: what the most common
     non-MathJax viewer (VS Code) actually fails on. Skipped, and SAID so,
     when node+katex are not resolvable -- a skipped leg is never a green
     one (#14849).

Exit codes:
    0 -- no occurrence found
    1 -- at least one occurrence (advisory organ: the workflow converts
         this to ::warning::, never a block)
    2 -- error (unreadable notebook, bad arguments)

Usage:
    python check_math_render.py                       # whole repo
    python check_math_render.py --path <file.ipynb>   # single notebook
    python check_math_render.py --pr-diff BASE HEAD   # notebooks in range
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
EXCLUDED_DIRS = ("/.lake/", "/_archive/", "/node_modules/", "/.venv/")
EXCLUDED_SUFFIX = "_output.ipynb"

BACKTICK_SPAN = re.compile(r"`[^`\n]*`")
FENCED_BLOCK = re.compile(r"```[\s\S]*?(?:```|$)")
LATEX_INLINE = re.compile(r"\\\(.*?\\\)")
LATEX_BLOCK = re.compile(r"\\\[.*?\\\]")
MATH_SCOPE = re.compile(r"\$\$([\s\S]+?)\$\$|\$([^$\n]+?)\$")
CURRENCY_DOLLAR = re.compile(r"\$\d")
KNOWN_COMMANDS = (
    "Phi", "mathbb", "mathcal", "mathbf", "mathrm", "mathsf", "lfloor",
    "rfloor", "frac", "dfrac", "tfrac", "sqrt", "log", "ln", "exp", "min",
    "max", "sum", "prod", "int", "to", "gets", "cdot", "times", "div",
    "pmod", "bmod", "quad", "qquad", "text", "textbf", "left", "right",
    "begin", "end", "aligned", "matrix", "pmatrix", "Rightarrow",
    "Leftarrow", "Leftrightarrow", "rightarrow", "leftrightarrow", "mapsto",
    "sim", "simeq", "approx", "equiv", "neq", "geq", "leq", "in", "notin",
    "subset", "subseteq", "cup", "cap", "forall", "exists", "neg", "land",
    "lor", "oplus", "otimes", "rangle", "langle", "rang",
)
NUDE_LATEX = re.compile(
    r"\\(?:" + "|".join(KNOWN_COMMANDS) + r")\b"
)

KATEX_PROBE = r"""
const katex = require("katex");
let input = "";
process.stdin.on("data", (d) => (input += d));
process.stdin.on("end", () => {
  const scopes = JSON.parse(input);
  const fails = [];
  for (const s of scopes) {
    try {
      katex.renderToString(s.formula, {
        displayMode: s.display,
        throwOnError: true,
        strict: false,
        trust: false,
      });
    } catch (e) {
      fails.push({ pos: s.pos, error: String(e.message).slice(0, 160) });
    }
  }
  process.stdout.write(JSON.stringify(fails));
});
"""


def cell_text(source) -> str:
    return source if isinstance(source, str) else "".join(source)


def katex_available() -> bool:
    if shutil.which("node") is None:
        return False
    probe = subprocess.run(
        ["node", "-e", "require.resolve('katex')"],
        capture_output=True, text=True,
    )
    return probe.returncode == 0


def katex_failures(scopes: list[dict]) -> list[dict]:
    payload = [{"formula": s["formula"], "display": s["display"], "pos": i}
               for i, s in enumerate(scopes)]
    proc = subprocess.run(
        ["node", "-e", KATEX_PROBE],
        input=json.dumps(payload),
        capture_output=True, text=True, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"katex probe failed: {proc.stderr[:200]}")
    return json.loads(proc.stdout or "[]")


def find_defects(source, with_katex: bool) -> tuple[list[dict], list[dict]]:
    """Returns (defects, math_scopes) for one markdown cell source."""
    text = cell_text(source)
    defects: list[dict] = []
    scopes: list[dict] = []

    masked = FENCED_BLOCK.sub("```", text)
    masked = BACKTICK_SPAN.sub("``", masked)

    for m in LATEX_INLINE.finditer(masked):
        defects.append({
            "kind": "LATEX-PURE-DELIMS", "detail": m.group(0)[:60],
            "pos": m.start(),
            "context": masked[max(0, m.start() - 30):m.end() + 30].replace("\n", "\\n"),
        })
    for m in LATEX_BLOCK.finditer(masked):
        defects.append({
            "kind": "LATEX-PURE-DELIMS", "detail": m.group(0)[:60],
            "pos": m.start(),
            "context": masked[max(0, m.start() - 30):m.end() + 30].replace("\n", "\\n"),
        })

    for para in re.split(r"\n\s*\n", masked):
        without_display = re.sub(r"\$\$[\s\S]*?\$\$", "", para)
        without_currency = CURRENCY_DOLLAR.sub("D", without_display)
        singles = without_currency.count("$")
        if singles % 2 == 1:
            defects.append({
                "kind": "ODD-DOLLARS", "detail": f"{singles} single '$' in paragraph",
                "pos": 0,
                "context": para.replace("\n", " ")[:100],
            })

    def _capture(m):
        formula = (m.group(1) if m.group(1) is not None else m.group(2) or "").strip()
        scopes.append({"formula": formula,
                       "display": m.group(1) is not None,
                       "pos": m.start()})
        return "$"

    stripped = MATH_SCOPE.sub(_capture, masked)
    stripped = LATEX_INLINE.sub("", LATEX_BLOCK.sub("", stripped))
    for m in NUDE_LATEX.finditer(stripped):
        defects.append({
            "kind": "NUDE-LATEX", "detail": m.group(0),
            "pos": m.start(),
            "context": stripped[max(0, m.start() - 30):m.end() + 30].replace("\n", "\\n"),
        })

    if with_katex and scopes:
        for f in katex_failures(scopes):
            defects.append({
                "kind": "KATEX-UNRENDERABLE",
                "detail": f"{f['error']} :: {scopes[f['pos']]['formula'][:60]}",
                "pos": f["pos"],
                "context": scopes[f["pos"]]["formula"][:100],
            })

    return defects, scopes


def scan_notebook(path: Path, with_katex: bool) -> list[dict]:
    nb = json.loads(path.read_text(encoding="utf-8"))
    out = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        defects, _ = find_defects(cell.get("source", []), with_katex)
        for d in defects:
            out.append({"cell_index": idx, "cell_id": cell.get("id", "?"), **d})
    return out


def iter_repo_notebooks():
    for p in sorted(REPO_ROOT.glob("MyIA.AI.Notebooks/**/*.ipynb")):
        s = str(p).replace("\\", "/")
        if any(x in s for x in EXCLUDED_DIRS) or s.endswith(EXCLUDED_SUFFIX):
            continue
        yield p


def pr_diff_files(base: str, head: str) -> list[Path]:
    proc = subprocess.run(
        ["git", "diff", "--name-only", base, head],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    )
    return [REPO_ROOT / f for f in proc.stdout.splitlines()
            if f.endswith(".ipynb") and (REPO_ROOT / f).exists()]


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    scope = p.add_mutually_exclusive_group()
    scope.add_argument("--path", metavar="FILE", help="single notebook")
    scope.add_argument("--pr-diff", nargs=2, metavar=("BASE", "HEAD"),
                       help="notebooks changed in BASE..HEAD")
    p.add_argument("--json", action="store_true", help="JSON output")
    p.add_argument("--no-katex", action="store_true",
                   help="skip the KaTeX leg (static classes only)")
    args = p.parse_args(argv)

    if args.path:
        targets = [Path(args.path)]
    elif args.pr_diff:
        targets = pr_diff_files(*args.pr_diff)
    else:
        targets = list(iter_repo_notebooks())

    with_katex = not args.no_katex and katex_available()
    if not args.no_katex and not with_katex:
        print("[KATEX] node+katex non resolubles -- jambe KaTeX SAUTEE "
              "(verdict partiel, pas vert)")

    results, errors = [], []
    for path in targets:
        try:
            defects = scan_notebook(path, with_katex)
        except Exception as e:
            errors.append({"notebook": str(path), "error": str(e)})
            continue
        if defects:
            results.append({"notebook": str(path), "defects": defects})

    if args.json:
        print(json.dumps({
            "occurrences": sum(len(r["defects"]) for r in results),
            "katex_leg": "on" if with_katex else "skipped",
            "notebooks": results, "errors": errors}, indent=1))
    else:
        for r in results:
            for d in r["defects"]:
                try:
                    rel = str(Path(r["notebook"]).relative_to(REPO_ROOT))
                except ValueError:
                    rel = r["notebook"]
                print(f"{d['kind']}  {rel} cell#{d['cell_index']} id={d['cell_id']}")
                print(f"    {d['detail']}")
                print(f"    ...{d['context']}...")
        for e in errors:
            print(f"UNREADABLE {e['notebook']} :: {e['error']}")
        total = sum(len(r["defects"]) for r in results)
        print(f"=== {total} occurrence(s) in {len(results)} notebook(s), "
              f"{len(errors)} unreadable, katex "
              f"{'on' if with_katex else 'skipped'} ===")

    return 2 if errors and not results else (1 if results else 0)


if __name__ == "__main__":
    sys.exit(main())
