"""Ratchet gate: a re-execution must not ADD tool-failure text or machine paths
to committed notebook outputs.

Issue #11685. Commit 988155353765b07adcef4a43e3b0e01611cfa61a re-executed
Infer-3-Factor-Graphs and Infer-8-TrueSkill on a machine without Graphviz.
Six failure banners and twelve absolute machine paths entered the committed
outputs of two published pedagogical notebooks, and the three surfaces
consulted at merge time all returned CLEAN:

  1. ``output_type == "error"``: 0 before, 0 after. The .NET helper writes the
     Graphviz failure to ``stdout``; it never raises. No structural error
     counter can see it.
  2. Render volume by MIME family: +862 B / -1411 B. The SVG survived through
     a fallback path, so both deltas sat in the noise.
  3. ``_UNAVAILABLE_PATTERNS`` of check_render_volume_delta.py -- three
     hand-written patterns (``non disponible``, ``not available``,
     ``importerror``). The real message matches none of them.

Surface 3 is the failure mode this file exists to close: "found nothing" and
"did not look" returned the same value. A pattern set is validated by its
FALSE NEGATIVES -- write the forms it must catch, then check that it catches
them -- never by its hits. Hence ``--self-test``, which replays the founding
commit and REFUSES to pass if it comes back empty.

Two classes, both ratcheted 0 -> N against the merge base:

  TOOL_FAILURE   text in a stream / text-plain output saying an external tool
                 could not be started or was not found.
  MACHINE_PATH   an absolute filesystem path of the executing machine
                 (``D:\\dev\\...``, ``/home/<user>/``, ``/Users/<user>/``).

Only notebooks CHANGED between the merge base and HEAD are judged, and only
occurrences whose count GREW are reported. A notebook that already carried
such text keeps it: this is a ratchet, not a repo-wide scold. Pre-existing
debt is surfaced by ``--all`` (advisory sweep), never by the gate.

Usage:
    python check_output_failure_text.py <base-ref> [--json]
    python check_output_failure_text.py --all [--json]
    python check_output_failure_text.py --self-test

Base ref is resolved to merge-base(base-ref, HEAD): a branch behind its base
is judged on its own diff only. Comparing trees instead attributes to the PR
everything the base advanced meanwhile -- measured at 15 notebooks / 9
regressions vs 1 / 0 on #11528, and that false verdict is the dangerous kind
(it sends an author to "repair" notebooks they never opened).

Exit 1 iff at least one changed notebook grew either class.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Same exclusions as check_papermill_ratchet.py / check_exec_ratchet.py.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")

# Founding commit, replayed by --self-test. Expected floor measured firsthand
# against its parent (see #11685).
SELF_TEST_COMMIT = "988155353765b07adcef4a43e3b0e01611cfa61a"
SELF_TEST_MIN_TOOL = 6
SELF_TEST_MIN_PATH = 12

# Backslash built by codepoint: a literal one does not survive every transport
# intact (heredoc, quoting), and a pattern that arrives half-escaped matches
# nothing WITHOUT raising -- the silent-undercount failure this file exists to
# close would reappear inside the detector itself.
BS = chr(92)

# --- class 1: an external tool could not be started -------------------------
# Every pattern here has a witness in _PATTERN_WITNESSES below. Adding one
# without its witness is how a pattern set starts lying.
TOOL_FAILURE_PATTERNS = (
    re.compile(r"problem with converting", re.IGNORECASE),
    re.compile(r"an error occurred trying to start process", re.IGNORECASE),
    re.compile(r"is not installed,\s*install", re.IGNORECASE),
    re.compile(r"add a path to .{0,20} to the path", re.IGNORECASE),
    re.compile(r"executablenotfound", re.IGNORECASE),
    re.compile(r"modulenotfounderror", re.IGNORECASE),
    re.compile(r"filenotfound(error|exception)", re.IGNORECASE),
    re.compile(r"command not found", re.IGNORECASE),
    re.compile(r"is not recognized as an internal or external command",
               re.IGNORECASE),
    re.compile(r"n.est pas reconnu en tant que commande", re.IGNORECASE),
    re.compile(r"fichier .{0,12} est introuvable", re.IGNORECASE),
    re.compile(r"no such file or directory", re.IGNORECASE),
    # inherited from check_render_volume_delta._UNAVAILABLE_PATTERNS
    re.compile(r"non\s+disponible", re.IGNORECASE),
    re.compile(r"not\s+available", re.IGNORECASE),
    re.compile(r"importerror", re.IGNORECASE),
)

# Witnesses: real strings observed in committed outputs. The self-test asserts
# each is matched by at least one pattern -- the false-negative check the
# founding incident needed and did not have.
_PATTERN_WITNESSES = (
    "Problem with converting DOT to SVG",
    "An error occurred trying to start process 'dot' with working directory",
    'If "dot" program is not installed, install Graphviz',
    'and add a path to "dot" to the PATH',
    "Le fichier specifie est introuvable.",
    "ModuleNotFoundError: No module named 'simanneal'",
    "graphviz.backend.ExecutableNotFound",
    "bash: dot: command not found",
    "simanneal non disponible",
)

# --- class 2: absolute path of the executing machine ------------------------
MACHINE_PATH_PATTERNS = (
    # Windows drive-letter path with at least two segments: D:\dev\CoursIA
    # BS + BS is the regex source for "one literal backslash": a single BS
    # here would escape the following brace and require a literal "{1,2}"
    # in the text -- a pattern that matches nothing and raises nothing. The
    # witness below is what caught exactly that, before this shipped.
    re.compile("[A-Za-z]:" + BS + BS + "{1,2}"
               + "[^" + BS + BS + '"\\s]{1,60}'
               + BS + BS + "{1,2}"
               + "[^" + BS + BS + '"\\s]{1,60}'),
    re.compile(r"/home/[A-Za-z0-9_.-]{2,32}/"),
    re.compile(r"/Users/[A-Za-z0-9_.-]{2,32}/"),
    re.compile(r"/mnt/[a-z]/[A-Za-z0-9_.-]{2,32}/"),
)

_PATH_WITNESSES = (
    "D:" + BS + "dev" + BS + "CoursIA-2-c1301-231-fbpy" + BS + "MyIA.AI.Notebooks",
    "/home/agent/CoursIA/MyIA.AI.Notebooks",
    "/Users/jsboige/CoursIA/scripts",
)


def git(*args, cwd=None):
    """Run a git command, returning stdout (utf-8) or None on failure."""
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def resolve_base(base, cwd=None):
    """Resolve `base` to merge-base(base, HEAD). See module docstring."""
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


def changed_notebooks(base, head="HEAD", cwd=None):
    """Notebooks added/copied/modified/renamed between base and head."""
    out = git("diff", "--name-only", "--diff-filter=ACMR", base, head,
              "--", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace(BS, "/")
        if posix and not any(m in "/" + posix for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def all_notebooks(cwd=None):
    """Every tracked deliverable notebook (advisory sweep)."""
    out = git("ls-files", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace(BS, "/")
        if posix and not any(m in "/" + posix for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def read_notebook_at(ref, path, cwd=None):
    """Notebook JSON at a git ref (None = working tree), or None if absent."""
    if ref is None:
        try:
            return json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return None
    raw = git("show", ref + ":" + path, cwd=cwd)
    if raw is None:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


def output_texts(nb):
    """Yield (cell_index, text) for every textual output of every code cell.

    Covers stream (stdout AND stderr) plus the text/plain of execute_result
    and display_data, and error tracebacks. text/html is deliberately
    excluded: an inline SVG is rendered deliverable, and its markup routinely
    contains strings that read like paths.
    """
    for i, cell in enumerate(nb.get("cells", []) or []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []) or []:
            kind = out.get("output_type")
            if kind == "stream":
                text = out.get("text", "")
                yield i, ("".join(text) if isinstance(text, list)
                          else str(text))
            elif kind in ("execute_result", "display_data"):
                plain = (out.get("data", {}) or {}).get("text/plain")
                if plain is not None:
                    yield i, ("".join(plain) if isinstance(plain, list)
                              else str(plain))
            elif kind == "error":
                tb = out.get("traceback", []) or []
                yield i, "\n".join(str(x) for x in tb)


def scan(nb):
    """{class: [(cell_index, matched_text), ...]} for one notebook."""
    found = {"TOOL_FAILURE": [], "MACHINE_PATH": []}
    if not nb:
        return found
    for idx, text in output_texts(nb):
        if not text:
            continue
        for pat in TOOL_FAILURE_PATTERNS:
            m = pat.search(text)
            if m:
                found["TOOL_FAILURE"].append((idx, m.group(0)[:120]))
                break
        for pat in MACHINE_PATH_PATTERNS:
            for m in pat.finditer(text):
                found["MACHINE_PATH"].append((idx, m.group(0)[:120]))
    return found


def compare(base_ref, head_ref, paths, cwd=None):
    """Per-notebook growth of each class between base_ref and head_ref."""
    rows = []
    for path in paths:
        base_nb = read_notebook_at(base_ref, path, cwd=cwd)
        head_nb = read_notebook_at(head_ref, path, cwd=cwd)
        if head_nb is None:
            continue
        # A notebook ADDED by the branch has no base blob. Counting its whole
        # content as growth turns the ratchet into an absolute gate for that
        # one file -- the over-accusation shape measured on #11528 and #11668.
        # It is reported (advisory) and never gates.
        added = base_nb is None
        b = scan(base_nb)
        h = scan(head_nb)
        row = {"notebook": path, "added": added, "classes": {}}
        regressed = False
        for cls in ("TOOL_FAILURE", "MACHINE_PATH"):
            n_base, n_head = len(b[cls]), len(h[cls])
            entry = {"base": n_base, "head": n_head, "delta": n_head - n_base}
            if n_head > n_base:
                if not added:
                    regressed = True
                entry["samples"] = [{"cell": c, "match": t}
                                    for c, t in h[cls][:6]]
            row["classes"][cls] = entry
        row["regressed"] = regressed
        rows.append(row)
    return rows


def self_test(cwd=None):
    """Positive control. A detector that cannot be shown to fire is
    indistinguishable from one that is unplugged."""
    failures = []

    for witness in _PATTERN_WITNESSES:
        if not any(p.search(witness) for p in TOOL_FAILURE_PATTERNS):
            failures.append("TOOL_FAILURE witness unmatched: " + repr(witness))
    for witness in _PATH_WITNESSES:
        if not any(p.search(witness) for p in MACHINE_PATH_PATTERNS):
            failures.append("MACHINE_PATH witness unmatched: " + repr(witness))

    # Negative control: ordinary pedagogical output must stay silent.
    for benign in ("P(Auburn) = 0,700",
                   "Compiling model... done.",
                   "Solution trouvee en 11.39s (avec simanneal)",
                   "Energie finale: 0 | Solution valide: True",
                   "Backtracking: 49/201/295 appels"):
        hit = ([p.pattern for p in TOOL_FAILURE_PATTERNS if p.search(benign)]
               + [p.pattern for p in MACHINE_PATH_PATTERNS if p.search(benign)])
        if hit:
            failures.append("benign text matched " + str(hit) + ": "
                            + repr(benign))

    # Replay the founding commit against its parent.
    if git("cat-file", "-e", SELF_TEST_COMMIT, cwd=cwd) is None:
        print("SKIP replay: " + SELF_TEST_COMMIT[:12] + " not in this clone")
    else:
        parent = SELF_TEST_COMMIT + "^"
        paths = changed_notebooks(parent, SELF_TEST_COMMIT, cwd=cwd)
        rows = compare(parent, SELF_TEST_COMMIT, paths, cwd=cwd)
        tool = sum(r["classes"]["TOOL_FAILURE"]["delta"] for r in rows)
        n_path = sum(r["classes"]["MACHINE_PATH"]["delta"] for r in rows)
        print("replay " + SELF_TEST_COMMIT[:12] + ": " + str(len(paths))
              + " notebooks, TOOL_FAILURE +" + str(tool)
              + ", MACHINE_PATH +" + str(n_path))
        if tool < SELF_TEST_MIN_TOOL:
            failures.append("replay TOOL_FAILURE +" + str(tool) + " < "
                            + str(SELF_TEST_MIN_TOOL) + " expected")
        if n_path < SELF_TEST_MIN_PATH:
            failures.append("replay MACHINE_PATH +" + str(n_path) + " < "
                            + str(SELF_TEST_MIN_PATH) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses matched, benign text silent, replay fires")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Ratchet: no NEW tool-failure text or machine path in "
                    "committed notebook outputs.")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--all", action="store_true",
                    help="Advisory sweep of every tracked notebook (no gate)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative control, then replay #11685")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.all:
        rows = []
        for path in all_notebooks():
            found = scan(read_notebook_at(None, path))
            if found["TOOL_FAILURE"] or found["MACHINE_PATH"]:
                rows.append({
                    "notebook": path,
                    "TOOL_FAILURE": [{"cell": c, "match": t}
                                     for c, t in found["TOOL_FAILURE"]],
                    "MACHINE_PATH": [{"cell": c, "match": t}
                                     for c, t in found["MACHINE_PATH"]]})
        if args.as_json:
            print(json.dumps({"mode": "sweep", "notebooks": len(rows),
                              "rows": rows}, indent=2, ensure_ascii=False))
        else:
            print("ADVISORY sweep: " + str(len(rows)) + " notebooks carry "
                  "failure text or machine paths in committed outputs")
            for r in rows:
                print("  " + r["notebook"]
                      + "  tool=" + str(len(r["TOOL_FAILURE"]))
                      + " path=" + str(len(r["MACHINE_PATH"])))
        return 0

    if not args.base:
        ap.error("base ref required (or --all / --self-test)")

    base = resolve_base(args.base)
    paths = changed_notebooks(base)
    rows = compare(base, None, paths)
    bad = [r for r in rows if r["regressed"]]

    if args.as_json:
        print(json.dumps({"base_ref": args.base, "merge_base": base,
                          "changed": len(paths), "regressions": len(bad),
                          "rows": rows}, indent=2, ensure_ascii=False))
    else:
        print("base " + str(args.base) + " -> merge-base " + base[:12]
              + " | " + str(len(paths)) + " changed notebooks | "
              + str(len(bad)) + " regressed")
        for r in rows:
            if r.get("added") and any(e["head"] for e in r["classes"].values()):
                print("  ADVISORY (added by this branch, no baseline) "
                      + r["notebook"])
        for r in bad:
            print("\nFAIL " + r["notebook"])
            for cls, e in r["classes"].items():
                if e["delta"] > 0:
                    print("  " + cls + ": " + str(e["base"]) + " -> "
                          + str(e["head"]) + " (+" + str(e["delta"]) + ")")
                    for s in e.get("samples", []):
                        print("     cell[" + str(s["cell"]) + "] " + s["match"])
        if bad:
            print("\nCause is on the executing machine, not in the notebook: "
                  "install the missing tool and RE-EXECUTE. Never hand-edit a "
                  "committed output (Stop & Repair, secrets-hygiene rule 6).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
