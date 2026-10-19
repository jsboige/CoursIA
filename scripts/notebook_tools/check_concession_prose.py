"""Detector: prose of concession ADDED to a notebook, commit by commit.

Epic #21424, tranche T5 (issue #21433).

The Epic's founding case (#21121, merged on Lean-11/11b) is a "correction"
that rewrote the notebook's prose to ADMIT the degraded state ("limites
honnexetes", "illustratif", "non disponible", "execution sautee", verdict
INTRINSIC) instead of repairing it. Two mechanisms are measured here: a
derivation of the environment (a later, unrelated commit re-executes the
notebook on a machine without the key / GPU / model) and a realignment onto a
degraded output (the prose becomes true, the notebook stays broken).

This detector counts the lines of prose ADDED by a commit that admit the
degraded state. It is a separate organ from check_output_collapse.py (T1,
#21426) and is NOT a gate.

Why "added lines" and not "the stock at head" (correction F1 of the
clusterManager-Myia review on #21425): the review measured, on the founding
commit 6eb23754b7, FIVE markdown lines matching CONCESSION_RE at head, ALL of
them already present at the parent 6eb23754b7^ -- the diff adds exactly ONE
("le cote honnete du verdict..."). The code delivered in #21425 scanned the
whole notebook at head, so its counts mixed inherited stock with added flow,
and its thresholds (n_concessions >= 5) were measured on that mixture. This
organ counts only the ADDED lines, per cell, via a line diff of the cell
source between sha^ and sha.

The motif list is the one delivered in #21425 (closed as a duplicate of T1),
reused verbatim: it is the union of the SIGNATURE motifs of the collapse
organ and the human-side vocabulary of "this notebook admits it did not really
run". Matching is accent-blind and case-blind (text is normalized first).

What this is NOT: a discriminant for the blocking mode of
check_output_collapse.py (T2, #21426). Measured on 5 242 history rows, the
`n_concessions >= 5` threshold alone fires on 44.2 % of the notebooks that
touch a notebook -- about 99 % false positives. Prose of admission does not
say whether the output collapsed. This organ serves to INVENTORY the
admissions to be verified, not to gate a PR.

Usage:
    python check_concession_prose.py --commit <sha> [--json]
    python check_concession_prose.py --history [--since <date>] [--out <file>]
    python check_concession_prose.py --self-test

Exit 1 iff the inspected scope carries at least one added concession line.
With ``--json`` the full row structure is emitted.
"""

import argparse
import difflib
import json
import re
import sys
import unicodedata
from datetime import datetime, timezone

# The motif list delivered in #21425 (closed as a duplicate of T1), reused
# verbatim. Accent-blind: "sautee" catches "sauté(e)".
CONCESSION_RE = re.compile(
    r"honnete|illustrati|non disponible|pas disponible|indisponible|non tenu"
    r"|sautee|simulee?s?\b|mode (simulation|degrade|simule)"
    r"|hors scope|limites"
    r"|n'a pas pu|non execute|cle api absente|api non configuree|placeholder"
)

# The founding commit of the Epic (#21121 / #20629), replayed by
# --self-test. It adds exactly ONE concession line ("le cote honnete du
# verdict...") while FIVE concession lines are already present at its parent:
# the pair is the positive control of the F1 correction.
SELF_TEST_COMMIT = "6eb23754b7"
SELF_TEST_PARENT = "6eb23754b7^"
SELF_TEST_NOTEBOOK = ("MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/"
                      "Argumentation-Obs-04-Recollement-Strate6-Python.ipynb")
SELF_TEST_MIN_ADDED = 1

# A commit that touches a notebook but adds no concession line: the control
# of the "ordinary prose does not fire" case.
SELF_TEST_ORDINARY = (
    "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/"
    "Argumentation-Obs-04-Recollement-Strate6-Python.ipynb")


def _normalize(text):
    """Lowercase, accents stripped: motif matching is accent-blind."""
    decomposed = unicodedata.normalize("NFD", text)
    stripped = "".join(c for c in decomposed
                       if unicodedata.category(c) != "Mn")
    return stripped.lower()


def _cell_source(cell):
    """The markdown source of a cell, as one string.

    nbformat stores `cell.source` either as a str or as a list of str whose
    concatenation is the source (each element already ends with "\n" except
    the last). Both shapes are flattened here.
    """
    source = cell.get("source")
    if isinstance(source, list):
        return "".join(str(x) for x in source)
    return str(source or "")


def _markdown_cells(nb):
    """{key: cell} for every markdown cell, keyed by cell id when present."""
    out = {}
    if not nb:
        return out
    for i, c in enumerate(nb.get("cells", []) or []):
        if c.get("cell_type") != "markdown":
            continue
        key = c.get("id") or ("pos-%d" % i)
        out[key] = c
    return out


def _added_lines(base_source, head_source):
    """Lines present in head_source but not in base_source.

    A line diff on the cell source: only the ADDED side is kept. The diff is
    computed per cell, so a concession line written in one cell is never
    attributed to another.
    """
    base_lines = (base_source or "").splitlines()
    head_lines = (head_source or "").splitlines()
    added = []
    for line in difflib.ndiff(base_lines, head_lines):
        if line.startswith("+ "):
            added.append(line[2:])
        elif line.startswith("+"):
            added.append(line[1:])
    return added


def analyze(base_nb, head_nb):
    """Concession lines ADDED between two parsed notebooks.

    Two kinds are kept apart, because the calibration must keep them apart:

    ``added``           the notebook existed at the parent, and the line is
                        proven added by the diff of the cell source. This
                        is the F1 count -- the lines a commit really wrote.
    ``notebook-added``  the whole notebook is new in this commit: there is
                        no baseline, so NO line can be proven added, and
                        the finding is reported under its own kind. The
                        notebook may be degraded from birth; that is the
                        second mechanism of the Epic.

    A cell added inside an EXISTING notebook is a normal ``added``: its
    baseline is the empty source, every line of it is proven added.
    """
    added_notebook = base_nb is None
    b_cells = _markdown_cells(base_nb)
    h_cells = _markdown_cells(head_nb)

    added_findings = []
    notebook_added_findings = []
    for key, h_cell in h_cells.items():
        b_cell = b_cells.get(key)
        if b_cell is None:
            # Cell added inside an existing notebook: the whole cell is the
            # addition (the common case of a prose rewrite, where a whole
            # paragraph is inserted).
            base_source = ""
        else:
            base_source = _cell_source(b_cell)
        head_source = _cell_source(h_cell)
        for line in _added_lines(base_source, head_source):
            if not CONCESSION_RE.search(_normalize(line)):
                continue
            finding = {"cell": key, "line": line.strip()[:200]}
            if added_notebook:
                notebook_added_findings.append(finding)
            else:
                added_findings.append(finding)
    return {
        "added_notebook": added_notebook,
        "concessions": added_findings,
        "notebook_added_concessions": notebook_added_findings,
        "n_concessions": len(added_findings),
        "n_notebook_added": len(notebook_added_findings),
    }


def _git(args, cwd=None):
    """Run a git command, return stdout as text (None on failure)."""
    import subprocess
    try:
        proc = subprocess.run(["git"] + list(args), cwd=cwd,
                              capture_output=True, text=True, encoding="utf-8",
                              errors="replace")
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout


def _read_notebook_at(ref, path, cwd=None):
    """Parse the notebook blob at `ref`, or None if absent/unparsable."""
    import json as _json
    raw = _git(["show", "%s:%s" % (ref, path)], cwd=cwd)
    if raw is None:
        return None
    try:
        return _json.loads(raw)
    except ValueError:
        return None


def _notebooks_of_commit(sha, cwd=None):
    """The notebook paths touched by a commit (name-status, A/M/R)."""
    out = _git(["show", "--name-status", "--format=", sha], cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        status = parts[0][:1]
        if status in ("A", "M", "R", "C", "T"):
            paths.append(parts[-1])
    return [p for p in paths if p.endswith(".ipynb")]


def analyze_commit(sha, cwd=None, parent=None):
    """Row for one commit: the concession lines it ADDED, per notebook."""
    if parent is None:
        parent = sha + "^"
    rows = []
    for path in _notebooks_of_commit(sha, cwd=cwd):
        base_nb = _read_notebook_at(parent, path, cwd=cwd)
        head_nb = _read_notebook_at(sha, path, cwd=cwd)
        if head_nb is None:
            continue
        row = analyze(base_nb, head_nb)
        row["notebook"] = path
        row["commit"] = sha
        rows.append(row)
    return rows


def history(since=None, cwd=None, out=None):
    """Replay the first-parent history, one JSON line per commit.

    Resumable: a commit already emitted (by short SHA) is skipped, so an
    interrupted run can be resumed on the same output file.
    """
    args = ["rev-list", "--first-parent"]
    if since:
        args += ["--since=%s" % since]
    args.append("HEAD")
    shas = (_git(args, cwd=cwd) or "").split()
    seen = set()
    if out:
        try:
            with open(out, "r", encoding="utf-8") as fh:
                for line in fh:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        seen.add(json.loads(line)["commit"][:12])
                    except (ValueError, KeyError, TypeError):
                        continue
        except OSError:
            seen = set()

    handle = open(out, "a", encoding="utf-8") if out else sys.stdout
    try:
        for sha in shas:
            if sha[:12] in seen:
                continue
            for row in analyze_commit(sha, cwd=cwd):
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
            handle.flush()
    finally:
        if out:
            handle.close()
    return 0


def self_test(cwd=None):
    """Positive and negative controls, then the founding-commit replay.

    A detector that cannot be shown to fire is indistinguishable from one
    that is unplugged -- the same contract that keeps the siblings honest.
    """
    failures = []

    # 1. the motif fires on the prose shapes of an admission
    positives = [
        "## Note honnete : la cellule 5 a ete executee partiellement",
        "**Mode simulation** -- la branche Anthropic n'est pas testee ici",
        "API non configuree, merci de renseigner OPENAI_API_KEY",
        "cle api absente sur la machine d'execution",
        "execution sautee (le modele n'est pas disponible)",
        "ce carnet a des limites : la jambe QC n'est pas executee",
        "placeholder pour les exemples reels",
    ]
    for line in positives:
        if not CONCESSION_RE.search(_normalize(line)):
            failures.append("CONCESSION_RE missed positive control: "
                            + line[:60])
    # 2. ordinary prose does not match
    if CONCESSION_RE.search(_normalize(
            "Cette cellule calcule la moyenne du tableau ci-dessus.")):
        failures.append("CONCESSION_RE over-fired on ordinary prose")

    # 3. a line ADDED to a cell is counted
    nb_base = {"cells": [{"cell_type": "markdown", "id": "a",
                           "source": ["## Introduction\n"]}]}
    nb_head = {"cells": [{"cell_type": "markdown", "id": "a",
                           "source": ["## Introduction\n",
                                      "Le cote honnete du verdict est nuance.\n"]}]}
    r = analyze(nb_base, nb_head)
    if r["n_concessions"] != 1:
        failures.append("added concession line not counted (got %d)"
                        % r["n_concessions"])
    # 4. a concession line ALREADY PRESENT at the parent is NOT counted
    r = analyze(nb_head, nb_head)
    if r["n_concessions"] != 0:
        failures.append("pre-existing concession line counted (got %d)"
                        % r["n_concessions"])
    # 5. ordinary added prose is not counted
    nb_ord = {"cells": [{"cell_type": "markdown", "id": "a",
                          "source": ["## Introduction\n",
                                     "Le tableau suivant resume les mesures.\n"]}]}
    r = analyze(nb_base, nb_ord)
    if r["n_concessions"] != 0:
        failures.append("ordinary added prose counted (got %d)"
                        % r["n_concessions"])
    # 6. a notebook ADDED by the commit has no baseline: no line is proven
    #    added, the finding is reported under its own kind
    r = analyze(None, nb_head)
    if r["n_concessions"] != 0:
        failures.append("added notebook produced an 'added' finding (got %d)"
                        % r["n_concessions"])
    if r["n_notebook_added"] != 1:
        failures.append("added notebook did not report its concession "
                        "under 'notebook-added' (got %d)"
                        % r["n_notebook_added"])
    # 7. a code cell carrying a concession string is not prose
    nb_code = {"cells": [{"cell_type": "code", "id": "c",
                           "source": ["print('execution sautee')\n"]}]}
    if analyze(nb_base, nb_code)["n_concessions"] != 0:
        failures.append("code cell counted as prose")

    # 8. replay the founding commit of the Epic: exactly ONE added line
    if (_git(["cat-file", "-e", SELF_TEST_COMMIT], cwd=cwd) is None
            or _git(["cat-file", "-e", SELF_TEST_PARENT], cwd=cwd) is None):
        print("SKIP replay: reference commits not in this clone")
    else:
        rows = analyze_commit(SELF_TEST_COMMIT, cwd=cwd)
        total = sum(row["n_concessions"] for row in rows)
        detail = [f["line"][:70] for row in rows for f in row["concessions"]]
        print("replay " + SELF_TEST_COMMIT[:12] + ": added concession lines "
              + str(total) + " " + str(detail))
        if total < SELF_TEST_MIN_ADDED:
            failures.append("replay added concession lines " + str(total)
                            + " < " + str(SELF_TEST_MIN_ADDED) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: added lines counted, pre-existing stock silent, "
          "ordinary prose silent, founding replay fires")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Detector: prose of concession ADDED to a notebook, "
                    "commit by commit (Epic #21424, T5 / issue #21433). "
                    "Advisory, not a gate.")
    ap.add_argument("--commit", help="Single commit to inspect")
    ap.add_argument("--history", action="store_true",
                    help="Replay the first-parent history")
    ap.add_argument("--since", help="Start date for --history (git syntax)")
    ap.add_argument("--out", help="Output file for --history (JSONL, "
                                  "resumable)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative controls, then replay the "
                         "founding commit of the Epic")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.history:
        return history(since=args.since, out=args.out)

    if not args.commit:
        ap.error("--commit, --history or --self-test required")

    rows = analyze_commit(args.commit)
    total = sum(r["n_concessions"] for r in rows)
    total_new = sum(r["n_notebook_added"] for r in rows)
    if args.as_json:
        print(json.dumps({"commit": args.commit, "rows": rows,
                          "n_concessions": total,
                          "n_notebook_added": total_new},
                         indent=2, ensure_ascii=False))
    else:
        print("commit " + args.commit[:12] + " | " + str(total)
              + " added concession line(s) | " + str(total_new)
              + " concession line(s) in a notebook added by this commit")
        for r in rows:
            for f in r["concessions"]:
                print("  ADDED " + r["notebook"] + " cell " + str(f["cell"])
                      + ": " + f["line"])
            for f in r["notebook_added_concessions"]:
                print("  NOTEBOOK-ADDED " + r["notebook"] + " cell "
                      + str(f["cell"]) + ": " + f["line"])
    return 1 if (total or total_new) else 0


if __name__ == "__main__":
    sys.exit(main())
