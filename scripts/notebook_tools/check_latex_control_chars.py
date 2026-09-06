#!/usr/bin/env python3
"""Check for control characters that ate a LaTeX escape inside math scopes.

Issue #14859: LaTeX generated from a NON-raw Python string loses its
backslash to an escape sequence -- `\\theta` becomes TAB + "heta", `\\neg`
becomes LF + "eg", `\\frac` becomes FF + "rac". The JSON stays valid, the
notebook opens, every other guard passes, and the formula does not render.
Measured on main 2026-09-06: 47 occurrences across 3 notebooks (the issue's
own paste lost 16 of them -- cell d2756261 alone carries 14).

Three discriminants, without which the detector lies (two of them were
learned the hard way during the issue's own measurement):

  1. markdown cells ONLY -- in code, a newline before `else:` is legitimate;
  2. the occurrence sits INSIDE a math scope `$...$` / `$$...$$`. Inline
     `$...$` never crosses a raw newline: pairing two unrelated dollars
     (currency, `$FILE` in backticks) is how a first version over-counted
     by mixing prose newlines into fake scopes. Dollars inside backtick
     spans are code, not delimiters;
  3. the characters AFTER the control char are a known command queue --
     the escape ate the backslash AND the first letter, so `\\theta` leaves
     "heta", not "theta". Searching for "theta" returns zero, and that
     zero is indistinguishable from absence of the defect.

Additional exclusions:
  - a real newline preceded by a backslash (LaTeX row break `\\\\` before
    a wrapped line) is legitimate;
  - the character AFTER the queue must not continue a word -- TeX command
    names are maximal alpha runs, so `$	o$` matches (`\\to`) but a TAB
    before "optionnel" does not (`op` is not `\\top` there).

Exit codes:
    0 -- no occurrence found
    1 -- at least one occurrence (advisory organ: the workflow converts
         this to a label + ::warning::, never a block)
    2 -- error (unreadable notebook, bad arguments)

Usage:
    python check_latex_control_chars.py                       # whole repo
    python check_latex_control_chars.py --path <file.ipynb>   # single notebook
    python check_latex_control_chars.py --pr-diff BASE HEAD   # PR diff scope
    python check_latex_control_chars.py --json                # JSON output
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

CTRL = {
    "\t": ("TAB", "t"),
    "\n": ("LF", "n"),
    "\r": ("CR", "r"),
    "\f": ("FF", "f"),
    "\v": ("VT", "v"),
    "\x08": ("BS", "b"),
    "\x07": ("BEL", "a"),
}
# queues = command name minus its first letter (the escape ate both).
# Superset of the issue's table: `eq` (\neq) and `arnothing` (\varnothing)
# are measured defects the issue's own list omitted. The `a` row covers the
# seventh Python escape (#14900): a hand-copied table had omitted BEL and
# two measured `\approx` went undetected -- the coverage test compares
# against the seven escapes, never against this table.
QUEUES = {
    "t": {"heta", "imes", "ext", "op", "au", "ilde", "o"},
    "n": {"eg", "abla", "otin", "ewline", "eq", "e", "u"},
    "r": {"ightarrow", "angle", "ho", "floor", "ight"},
    "f": {"orall", "rac", "rown", "lat"},
    "v": {"ee", "dash", "arphi", "ec", "ert", "arnothing"},
    "b": {"eta", "egin", "igcup", "ot", "ar", "inom"},
    "a": {"pprox", "lpha", "ngle", "leph", "st", "top",
          "rccos", "rcsin", "rctan", "rray", "malg"},
}
MAXQ = 10
EXCLUDED_DIRS = ("/_archive/", "/.ipynb_checkpoints/", "/.lake/")
EXCLUDED_SUFFIX = "_output.ipynb"


def math_scopes(text: str):
    """Yield (start, end) of $...$ / $$...$$ scopes.

    Inline scopes stop at a raw newline (a pairing across lines joins two
    unrelated dollars). Display scopes may span lines. Backtick spans are
    code.
    """
    i, n = 0, len(text)
    in_backtick = False
    while i < n:
        ch = text[i]
        if ch == "`":
            in_backtick = not in_backtick
            i += 1
            continue
        if in_backtick:
            i += 1
            continue
        if ch == "\\" and i + 1 < n and text[i + 1] in "$`":
            i += 2
            continue
        if text.startswith("$$", i):
            j = text.find("$$", i + 2)
            if j == -1:
                break
            yield (i + 2, j)
            i = j + 2
        elif ch == "$":
            j = i + 1
            while j < n and text[j] != "$" and text[j] != "\n":
                if text[j] == "\\":
                    j += 1
                j += 1
            if j < n and text[j] == "$":
                yield (i + 1, j)
                i = j + 1
            else:
                i += 1
        else:
            i += 1


def _match_queue(after: str, first: str):
    """Longest queue match; the char after the queue must not continue a
    word (TeX command names are maximal alpha runs: `op` inside `optionnel`
    is not \\top)."""
    for ln in range(min(MAXQ, len(after)), 0, -1):
        cand = after[:ln]
        if cand in QUEUES[first]:
            nxt = after[ln] if ln < len(after) else ""
            if nxt.isalpha():
                return None
            return cand
    return None


def find_defects(source) -> list[dict]:
    """Defects in one markdown cell source (str or list of str)."""
    text = source if isinstance(source, str) else "".join(source)
    hits = []
    for start, end in math_scopes(text):
        seg = text[start:end]
        k = 0
        while k < len(seg):
            ch = seg[k]
            if ch not in CTRL:
                k += 1
                continue
            glob = start + k
            name, first = CTRL[ch]
            if ch == "\n":
                # a LF right after a backslash (LaTeX row break, wrapped
                # line) is legitimate; anything else inside a math scope
                # with a command queue is the eaten-`\n` defect
                prev = text[glob - 1] if glob >= 1 else ""
                if prev == "\\":
                    k += 1
                    continue
            queue = _match_queue(seg[k + 1 : k + 1 + MAXQ], first)
            if queue is None:
                k += 1
                continue
            ctx = text[max(0, glob - 30) : glob + 30].replace("\n", "\\n")
            hits.append({
                "ctrl": name, "command": "\\" + first + queue,
                "pos": glob, "context": ctx,
            })
            k += 1 + len(queue)
    return hits


def scan_notebook(path: Path) -> list[dict]:
    """Defects for one notebook: [{cell_index, cell_id, defect...}]."""
    nb = json.loads(path.read_text(encoding="utf-8"))
    out = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        for d in find_defects(cell.get("source", [])):
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
    return [REPO_ROOT / f for f in proc.stdout.splitlines() if f.endswith(".ipynb")]


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    scope = p.add_mutually_exclusive_group()
    scope.add_argument("--path", metavar="FILE", help="single notebook")
    scope.add_argument("--pr-diff", nargs=2, metavar=("BASE", "HEAD"),
                       help="notebooks changed in BASE..HEAD")
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args(argv)

    if args.path:
        targets = [Path(args.path)]
    elif args.pr_diff:
        targets = pr_diff_files(*args.pr_diff)
    else:
        targets = list(iter_repo_notebooks())

    results, errors = [], []
    for path in targets:
        try:
            defects = scan_notebook(path)
        except Exception as e:  # unreadable notebook: report, keep scanning
            errors.append({"notebook": str(path), "error": str(e)})
            continue
        if defects:
            results.append({"notebook": str(path), "defects": defects})

    if args.json:
        print(json.dumps({"occurrences": sum(len(r["defects"]) for r in results),
                          "notebooks": results, "errors": errors}, indent=1))
    else:
        for r in results:
            for d in r["defects"]:
                try:
                    rel = str(Path(r["notebook"]).relative_to(REPO_ROOT))
                except ValueError:  # target outside the repo (--path temp file)
                    rel = r["notebook"]
                print(f"{d['ctrl']} -> {d['command']}  {rel} cell#{d['cell_index']} id={d['cell_id']}")
                print(f"    ...{d['context']}...")
        for e in errors:
            print(f"UNREADABLE {e['notebook']} :: {e['error']}")
        total = sum(len(r["defects"]) for r in results)
        print(f"=== {total} occurrence(s) in {len(results)} notebook(s), "
              f"{len(errors)} unreadable ===")

    return 2 if errors and not results else (1 if results else 0)


if __name__ == "__main__":
    sys.exit(main())
