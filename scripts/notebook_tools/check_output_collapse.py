"""Advisory ratchet: a re-execution must not silently collapse a notebook's
OUTPUT VOLUME -- the mirror image of check_output_flood.py.

Issue #15327 / user reserve on #15209 (2026-09-08: « Il n'est pas normal que
ni le CI ni la review l'ait detecte. Gros rouge et investigation necessaire ! »).
Measured firsthand on the reference case (Lean-7b-Examples.ipynb,
6b327a9bf -> 56d98429a): 11 -> 11 code cells, 0 error cells, real
execution_counts everywhere, and output_chars 10637 -> 2985 (-71.9 %). The
graceful-degradation guards (``if api_ok:``) did their job: three cells ran
"successfully" and printed ``Execution sautee (API non configuree)`` instead
of their real output (2195 -> 147, 2568 -> 38, 2074 -> 42 chars).

Every existing surface stayed green on that diff: H.1 (no ``error`` output),
H.3/pre-commit (cells executed with outputs), the failure-text ratchet (a
skip notice is not a failure banner), the output-flood ratchet (asymmetric:
it catches INFLATION, not contraction), markdown-content-loss (it measures
markdown, and the markdown GREW). The repo had a ratchet against output
inflation and none against output collapse. This file closes that hole.

Design constraint (ai-01 measurement on #15327, 2026-09-09): the AGGREGATE
notebook contraction ratio alone is a ~100 % false-positive signal -- over
14 days / 162 commits, every contraction > 50 % (3 of them) was a legitimate
PR (declared lightening, content split into a notebook created in the same
commit, compiler-warning purge), and the one real degradation (#15209) never
crossed a 50 % aggregate threshold that would have separated it from noise
anyway. A useful instrument therefore needs a CAUSE DISCRIMINANT, not a
finer aggregate threshold. Two signals, two mechanical exemptions:

  SIGNATURE  a cell whose base output is substantial and whose head output
             matches a graceful-degradation motif (``execution sautee``,
             ``non configure``, ``mode simulation``, ``skipped``,
             ``not available``) while contracting at all -- catches the
             whole "re-executed without the keys" class, not just #15209.
             Narrow by construction; not subject to the exemptions below
             (a split or a warning purge does not leave skip notices behind).
  MAGNITUDE  a cell whose output loses an ORDER OF MAGNITUDE (factor >= 10
             over a noise floor), subject to the two legitimate causes that
             are mechanically detectable:
               - MOVED CONTENT: a notebook CREATED by the same diff gains a
                 comparable output volume (>= MOVED_GAIN_FRACTION of the
                 loss) -- compare at diff scale, not file scale.
               - DIAGNOSTIC PURGE: the removed text is predominantly
                 diagnostic-shaped (CS#### / warning / DeprecationWarning
                 lines) -- classify the removed lines, not just count them.
             The third legitimate cause (declared lightening) is
             human-side: the PR body carries a
             ``## Output-collapse justification`` section naming the cell
             and the reason, same contract as the other ratchets.

Placement: the gate is BLOCKING in the fast lane since T2 of #21424
(``blocking=True`` dans ``scripts/ci/fast_lane_registry.py``). Un finding
``SIGNATURE`` ou ``MAGNITUDE`` est un echec dur, sauf si le body de la PR
porte une section ``## Output-collapse justification`` qui nomme la cellule
et le motif. L'advisory avait ete pose le temps de calibrer le seuil sur
l'historique -- ce calage est fait, le regime bloque est le regime courant.

Cells are matched BASE -> HEAD by nbformat cell ``id`` when both sides carry
one, falling back to positional index (same contract as the flood sibling).
A cell DELETED by the PR has no head counterpart and produces no finding (a
notebook that deletes code cells loses volume legitimately); a notebook
ADDED by the branch has no baseline and is never judged, though its output
volume counts toward the moved-content exemption of the same diff.

Usage:
    python check_output_collapse.py <base-ref> [--json]
    python check_output_collapse.py --self-test

Base ref is resolved to merge-base(base-ref, HEAD), same as the siblings.

Exit 1 iff at least one changed notebook carries a non-exempt finding. With
``--json`` the full row structure (including exempted findings and their
reasons) is emitted for calibration.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import unicodedata
from collections import Counter

# Reuse the siblings' git plumbing so all three ratchets share one
# implementation of "what changed between the merge base and HEAD".
from check_output_failure_text import (
    EXCLUDE_MARKERS,
    changed_notebooks,
    resolve_base,
    read_notebook_at,
)
from check_output_flood import _cell_key

# A base output below this many chars is noise (a shorter tqdm bar, a
# different seed): never judged. The reference case's guilty cells sit at
# 2074-2568 chars; ai-01's calibration puts the p99 per-cell output object
# count at 1, so 500 chars of text is already a substantial cell.
BASE_FLOOR = 500

# Order-of-magnitude contraction (reference case: factors 14.9 / 67.6 / 49.4).
MAGNITUDE_FACTOR = 10

# The signature signal needs SOME real contraction, not sub-noise jitter, but
# deliberately far below the magnitude factor: the motif itself is the
# discriminator, the ratio only rules out a coincidental substring.
SIGNATURE_FACTOR = 2

# Moved-content exemption: an added notebook's output volume counts against
# the magnitude losses of the same diff from this fraction up ("un volume
# comparable", ai-01 on #14795's split).
MOVED_GAIN_FRACTION = 0.5

# Diagnostic-purge exemption: this fraction of the REMOVED lines must be
# diagnostic-shaped for the cell to be exempt (Sudoku-06 #15144 purged 21
# CS8632 warnings -- the warnings WERE the output).
DIAGNOSTIC_LINE_FRACTION = 0.8

# Issue #21424 T2-corrige (2026-10-19, calibration coordinateur sur 23
# cellules main) : la signature devient << motif present en tete ET absent
# en base, meme cellule >>. Le plancher de 500 ignore les sorties reelles
# perdues entre 200 et 400 caracteres (Bonsai `recipe-cell` 274 chars,
# App-5-Timetabling 361 chars), et la contraction x2 ignore les replis qui
# remplacent une ligne par une ligne de meme longueur (Planners-0 538->593,
# MiniMax 218->239) ou qui font grossir la cellule en y ajoutant le motif
# (Kokoro `f82ed24e` 566->15602). Vocabulaire elargi d'apres les motifs
# observes sur les 10 derives confirmees a la lecture (cf. PR #21426
# CHANGES_REQUESTED et commentaire 6268481954).
DEGRADATION_RE = re.compile(
    r"execution sautee"
    r"|comparaison sautee"
    r"|non configure"
    r"|not configured"
    r"|mode simulation"
    r"|\bskipped\b"
    r"|not available"
    r"|non disponible"
    r"|indisponible"
    r"|unavailable"
    r"|non installe"
    r"|n[' ]?est pas installe"
    r"|not installed"
    r"|demonstration sautee"
    r"|generation sautee"
    r"|\bskip(ping|pee)?\b"
    r"|cles? (api )?(absente|manquante)"
    r"|api[_ ]key (absente|manquante|missing)"
    r"|mode (squelette|mock|degrade)"
    r"|simulee? :"
)

# Issue #21424 T2-corrige : la regle << motif nouveau >> attrape aussi 8
# faux positifs mesures (coordinateur, 2026-10-19, jeu des 23 cellules
# de calibration). On les exempte explicitement. La liste est STRICTEMENT
# specifique pour eviter d'innocenter les 4 controles positifs (Bonsai,
# Planners-0, Kokoro f82ed24e, SD-3.5) dont les sorties REELLES portent
# le motif en clair. Une exemption non listee ici laisse passer le
# finding vers le gate. Couverture mesuree sur les 13 FPs : 4/8 exempte
# (9 PT_11d_qwen, 14 11_Quantization, 18 MultiModel-Video, 19
# Video-Workflow). Les 4 FPs restants (4 AceStep, 15+16
# 04-Claude-CLI-Agents, 23 Planners-6-Domains) relevent de la
# justification explicite par le PR (cf. parse_collapse_justification).
#
# Portee de l'exemption : la LIGNE, pas la cellule (#21426 R3). Une
# cellule qui melange un avertissement de bibliotheque et une degradation
# reelle (co-occurrence) doit rester signalee ; seule la ligne exemptée
# est retiree, puis DEGRADATION_RE est cherche sur le reste
# (cf. _strip_exempt_lines).
EXEMPT_FP_PATTERNS = re.compile(
    r"\[transformers\]"  # library-specific bracket (transformers warning)
    r"|sdpa fallback"
    r"|allow_fallback"
    r"|flash[- ]?attn? .*(absent|fall|fallback)"
    r"|\.env non trouve"  # specific .env warning, not a real degradation
)

# Diagnostic-shaped lines (removed-text classification). CS#### is the C#
# compiler; the warning family covers Python (DeprecationWarning and
# friends) and both spellings of the French "warning : CS####".
DIAGNOSTIC_RE = re.compile(
    r"\bCS\d{4}\b"
    r"|warning"
    r"|deprecationwarning"
    r"|futurewarning"
    r"|userwarning"
    r"|runtimewarning"
    r"|pendingdeprecationwarning"
)

# Reference case (#15209), replayed by --self-test. 56d98429a is the
# measured PR head; its parent-side base is the main commit 6b327a9bf.
SELF_TEST_BASE = "6b327a9bf"
SELF_TEST_HEAD = "56d98429a"
SELF_TEST_NOTEBOOK = "MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-7b-Examples.ipynb"
SELF_TEST_MIN_FINDINGS = 3


def _normalize(text):
    """Lowercase, accents stripped: motif matching is accent-blind."""
    decomposed = unicodedata.normalize("NFD", text)
    stripped = "".join(c for c in decomposed
                       if unicodedata.category(c) != "Mn")
    return stripped.lower()


def _text_of(value):
    """nbformat stores output text as str or list[str]; flatten both."""
    if isinstance(value, list):
        return "".join(str(x) for x in value)
    return str(value or "")


def _cell_output_text(cell):
    """Concatenated `text` + `data["text/plain"]` of a cell's outputs.

    This is the exact quantity the issue defines as the output volume.
    """
    parts = []
    for o in cell.get("outputs", []) or []:
        parts.append(_text_of(o.get("text")))
        data = o.get("data") or {}
        parts.append(_text_of(data.get("text/plain")))
    return "".join(parts)


def _cell_chars(cell):
    return len(_cell_output_text(cell))


def _code_cells(nb):
    """{(id-or-positional-key): cell} for every code cell."""
    if not nb:
        return {}
    out = {}
    for i, c in enumerate(nb.get("cells", []) or []):
        if c.get("cell_type") != "code":
            continue
        out[_cell_key(c, i)] = c
    return out


def _strip_exempt_lines(text):
    """Drop the lines that carry a library-warning marker.

    The FP exemption is LINE-scoped, not cell-scoped. A cell whose output
    mixes a library warning with a real degradation -- co-occurrence, the
    positive control of #21426 R3 (``sdpa fallback engaged.`` on one line,
    ``ComfyUI non disponible : generation skippee.`` on the next) -- must
    still be flagged. Dropping only the offending lines, then searching
    the remainder, keeps the real degradation visible.

    Line granularity is not a nicety: the ``[transformers]`` warning line
    itself contains ``not available``, a DEGRADATION_RE motif. Removing
    the exempt *match* instead of the exempt *line* would leave that
    motif behind and re-flag a known false positive.
    """
    kept = []
    for line in text.splitlines():
        if EXEMPT_FP_PATTERNS.search(_normalize(line)):
            continue
        kept.append(line)
    return "\n".join(kept)


def _diagnostic_fraction(base_text, head_text):
    """Fraction (in chars) of the REMOVED text that is diagnostic-shaped.

    Removed lines are a multiset difference (duplicate warnings count), so a
    purge of 21 identical CS8632 lines is fully accounted. The fraction is
    weighted by CHARS, not lines: the ratchet guards output VOLUME, so a
    purge that also swallows a large real output line must not ride along a
    handful of short warnings.
    """
    removed = Counter(base_text.splitlines()) - Counter(head_text.splitlines())
    total = sum(len(line) * n for line, n in removed.items())
    if total == 0:
        return 0.0
    diag = sum(len(line) * n for line, n in removed.items()
               if DIAGNOSTIC_RE.search(_normalize(line)))
    return diag / total


def analyze(base_nb, head_nb):
    """Pure per-notebook collapse analysis on two parsed notebooks.

    ``base_nb`` is None for a notebook ADDED by the branch (never judged).
    Returns one row dict; the moved-content exemption is applied later, at
    diff scale, by ``compare`` (it needs the other rows of the same diff).

    Detection rules (Issue #21424 T2-corrige, calibration 2026-10-19) :

      - ``signature`` : motif DEGRADATION_RE present dans la sortie de
        tete ET absent dans la sortie de base, SANS plancher ni
        contraction (couvre les replis de meme longueur et les cellules
        qui grossissent en y ajoutant le motif). Les lignes porteuses
        d'un marqueur EXEMPT_FP_PATTERNS (avertissements de bibliotheque)
        sont retirees AVANT la recherche du motif -- exemption
        line-scoped, pas cell-scoped (#21426 R3).
      - ``magnitude`` : contraction d'un ordre de grandeur (factor >= 10)
        sans motif de degradation, exempte par purge de diagnostic ou
        contenu deplace au niveau du diff.
    """
    added = base_nb is None
    b_cells, h_cells = _code_cells(base_nb), _code_cells(head_nb)

    b_total = sum(_cell_chars(c) for c in b_cells.values())
    h_total = sum(_cell_chars(c) for c in h_cells.values())

    findings = []
    for key, h_cell in h_cells.items():
        b_cell = b_cells.get(key)
        if b_cell is None:
            continue  # cell added by the branch: no baseline, no judgement
        b_chars, h_chars = _cell_chars(b_cell), _cell_chars(h_cell)
        b_text = _cell_output_text(b_cell)
        h_text = _cell_output_text(h_cell)
        b_norm = _normalize(b_text)
        h_norm = _normalize(h_text)
        factor = b_chars / max(h_chars, 1)

        # Signature: motif nouveau, sans plancher ni contraction.
        # Bonsai 274 chars (sous ancien plancher), Planners-0 538->593
        # (longueur egale), Kokoro 566->15602 (grossit) sont tous
        # attrapes ici.
        m_h = DEGRADATION_RE.search(_normalize(_strip_exempt_lines(h_text)))
        m_b = DEGRADATION_RE.search(b_norm)
        if m_h is not None and m_b is None:
            findings.append({
                "cell": key, "kind": "signature",
                "base": b_chars, "head": h_chars,
                "factor": round(factor, 2),
                "motif": m_h.group(0),
            })
            continue

        # Magnitude: contraction d'un ordre de grandeur, exempte par
        # purge de diagnostic. ATTENTION : le plancher porte sur la BASE
        # (b_chars >= BASE_FLOOR = 500). Une cellule dont la base est
        # deja sous 500 chars n'est jugee par AUCUNE des deux regles --
        # signature exige un motif nouveau, magnitude exige une base
        # >= 500. QC @17 (428 -> 0) est ce point mort mesure, hors
        # perimetre de cet organe (cf. le blind spot dans le body).
        if b_chars >= BASE_FLOOR and factor >= MAGNITUDE_FACTOR:
            diag_frac = _diagnostic_fraction(b_text, h_text)
            if diag_frac >= DIAGNOSTIC_LINE_FRACTION:
                findings.append({
                    "cell": key, "kind": "exempt-diagnostic",
                    "base": b_chars, "head": h_chars,
                    "factor": round(factor, 1),
                    "diagnostic_fraction": round(diag_frac, 2),
                })
            else:
                findings.append({
                    "cell": key, "kind": "magnitude",
                    "base": b_chars, "head": h_chars,
                    "factor": round(factor, 1),
                })

    regressed = (not added) and any(
        f["kind"] in ("signature", "magnitude") for f in findings)
    return {
        "added": added,
        "base_total": b_total,
        "head_total": h_total,
        "cells": findings,
        "regressed": regressed,
    }


def _apply_moved_content(rows):
    """Diff-scale exemption: volume that reappears in an ADDED notebook of
    the same diff is content that moved, not content that vanished."""
    moved_gain = sum(r["head_total"] for r in rows if r["added"])
    magnitude_loss = sum(f["base"] - f["head"] for r in rows
                         for f in r["cells"] if f["kind"] == "magnitude")
    if magnitude_loss <= 0 or moved_gain < MOVED_GAIN_FRACTION * magnitude_loss:
        return rows
    for r in rows:
        for f in r["cells"]:
            if f["kind"] == "magnitude":
                f["kind"] = "exempt-moved"
                f["moved_gain"] = moved_gain
        r["regressed"] = any(f["kind"] == "signature" for f in r["cells"])
    return rows


def compare(base_ref, head_ref, paths, cwd=None):
    """Per-notebook collapse between two refs, then the diff-scale exemption.

    ``head_ref`` is None for the working tree (same contract as the siblings).
    """
    rows = []
    for path in paths:
        base_nb = read_notebook_at(base_ref, path, cwd=cwd)
        head_nb = read_notebook_at(head_ref, path, cwd=cwd)
        if head_nb is None:
            continue
        row = analyze(base_nb, head_nb)
        row["notebook"] = path
        rows.append(row)
    return _apply_moved_content(rows)


# ---------------------------------------------------------------------------
# Mode --history : replay compare() over the first-parent history of main.
# Issue #21424 T1 (H.6 audit-history organ, never built). One JSON line per
# finding (not per commit): the finding is the cell, the line is its
# restore point and the commit that emptied it. A single corrupt notebook
# never aborts the run (Issue #21424 T1 acceptance).
# ---------------------------------------------------------------------------
BS = "\\"  # path separator on Windows (matches sibling EXCLUDE_MARKERS)
MAX_RESTORE_BACK = 20


def _git(*args, cwd=None):
    """Thin wrapper around git for the history replay.

    Returns stdout (utf-8) or None on failure. Same contract as
    ``check_output_failure_text.git`` but kept local so the T1 work does not
    touch the siblings' public surface.
    """
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                              encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def _cell_chars_at(ref, path, cwd=None):
    """Map cell_key -> char count for the code cells of a notebook at a ref.

    Returns None if the notebook is absent at that ref (added later, deleted
    earlier). The history walk uses this to score a candidate restore point.
    """
    nb = read_notebook_at(ref, path, cwd=cwd)
    if nb is None:
        return None
    return {k: _cell_chars(c) for k, c in _code_cells(nb).items()}


def _find_restore_point(path, cell_key, culprit_sha, base_chars, cwd=None,
                        max_back=MAX_RESTORE_BACK):
    """Walk back from culprit_sha^ to find a parent where the cell is real.

    Bounded walk: a cell whose legitimate history is consistently small
    returns None and the calling line keeps a ``"restore_point": null``
    entry. The bound keeps the cost linear in the number of findings.
    """
    seen = set()
    cur = culprit_sha
    for _ in range(max_back):
        out = _git("log", cur, "--first-parent", "--format=%H", "-n", "2",
                   cwd=cwd)
        if not out:
            return None
        shas = [s for s in out.strip().splitlines() if s]
        if len(shas) < 2:
            return None
        parent = shas[1]
        if parent in seen:
            return None
        seen.add(parent)
        chars_map = _cell_chars_at(parent, path, cwd=cwd)
        if chars_map is None:
            # notebook absent at this commit (not yet added) -- still walk back
            cur = parent
            continue
        chars = chars_map.get(cell_key)
        # Issue #21424 T2-corrige : le plancher de restauration est abaisse
        # de 500 a 150, pour suivre le plancher de signature. Les cellules
        # perdues reelles font souvent 200-400 chars (Bonsai 274, App-5
        # 361, MiniMax 218, Planners-0 538), le seuil de 500 les ignore.
        if chars is not None and chars >= 150:
            meta = _git("log", parent, "--first-parent", "-n", "1",
                        "--format=%H %ad %s", "--date=short", cwd=cwd)
            if meta:
                parts = meta.strip().split(" ", 2)
                if len(parts) == 3:
                    return {"sha": parts[0], "date": parts[1],
                            "subject": parts[2][:160]}
                if len(parts) == 2:
                    return {"sha": parts[0], "date": parts[1],
                            "subject": ""}
            return None
        cur = parent
    return None


def history(since, until, notebook=None, cwd=None, limit=None):
    """Replay the ratchet on the first-parent history of main since SINCE.

    Yields one JSON-ready dict per finding (signature or magnitude, after
    the diff-scale exemptions). A finding is a cell whose output at commit
    C crosses one of the two thresholds; C is the culprit, the last parent
    where the cell was substantial is the restore point.

    Smoke testing: ``--limit 50`` over a recent window. Full history: expect
    a few minutes, dominated by ``read_notebook_at`` on each C^ (10-20
    parents per finding times the number of findings).
    """
    since = since or "2026-04-01"
    until = until or "2099-01-01"
    out_log = _git("log", "origin/main", "--first-parent",
                   "--since=" + since, "--until=" + until,
                   "--format=%H %ad %s", "--date=short", cwd=cwd)
    if not out_log:
        return
    commits = []
    for line in out_log.splitlines():
        parts = line.split(" ", 2)
        if len(parts) < 3:
            continue
        commits.append({"sha": parts[0], "date": parts[1],
                         "subject": parts[2]})
    if limit:
        commits = commits[:limit]

    for i, c in enumerate(commits):
        diff_out = _git("diff-tree", "--no-commit-id", "--name-only", "-r",
                        c["sha"], cwd=cwd)
        if not diff_out:
            continue
        paths = [p.replace(BS, "/") for p in diff_out.splitlines()
                 if p.endswith(".ipynb") and not p.endswith("_output.ipynb")
                 and (notebook is None or p == notebook)]
        if not paths:
            continue
        try:
            rows = compare(c["sha"] + "^", c["sha"], paths, cwd=cwd)
        except Exception:
            # one corrupt notebook must not stop the run (acceptance)
            continue
        for r in rows:
            if not r.get("regressed"):
                continue
            for f in r["cells"]:
                if f["kind"] not in ("signature", "magnitude"):
                    continue
                rp = _find_restore_point(r["notebook"], f["cell"],
                                          c["sha"], f["base"], cwd=cwd)
                yield {
                    "notebook": r["notebook"],
                    "cell": f["cell"],
                    "kind": f["kind"],
                    "culprit": {"sha": c["sha"], "date": c["date"],
                                 "subject": c["subject"][:160]},
                    "restore_point": rp,
                    "base": f["base"],
                    "head": f["head"],
                    "factor": f["factor"],
                }


def self_test(cwd=None):
    """Positive and negative control, then the reference-case replay.

    A detector that cannot be shown to fire is indistinguishable from one
    that is unplugged -- the same contract that keeps the siblings honest.
    """
    failures = []

    def _nb(cells):
        """Build a synthetic notebook from [(id, output_text)]."""
        return {"cells": [
            {"cell_type": "code", "id": k, "outputs": [
                {"output_type": "stream", "text": t}]}
            for k, t in cells]}

    def _analyze(base_cells, head_cells, added=False):
        return analyze(None if added else _nb(base_cells), _nb(head_cells))

    long_text = "x" * 1000
    skip_notice = ("[INFO] API non configuree - execution sautee\n"
                   "Configurez OPENAI_API_KEY pour executer les exemples\n")

    # 1. signature fires: substantial base, skip-notice head, real contraction
    r = _analyze([("a", long_text)], [("a", skip_notice)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("signature (1000 -> skip notice) not flagged")
    # 2. magnitude fires: order-of-magnitude contraction without a motif
    r = _analyze([("a", long_text)], [("a", "y" * 40)])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("magnitude (1000 -> 40) not flagged")
    # 3. benign variance stays silent (30 % churn is not a collapse)
    if _analyze([("a", long_text)], [("a", "x" * 700)])["cells"]:
        failures.append("benign contraction (1000 -> 700) flagged")
    # 4. small base stays silent (below the noise floor, even x1000)
    if _analyze([("a", "x" * 400)], [("a", "y")])["cells"]:
        failures.append("sub-floor base (400 -> 1) flagged")
    # 5. growth stays silent
    if _analyze([("a", long_text)], [("a", "x" * 5000)])["cells"]:
        failures.append("growth (1000 -> 5000) flagged")
    # 6. diagnostic purge is exempt: base is 30 warning lines, head is clean
    warnings = "".join(
        "warning CS8632: Une reference nullable est requise %d\n" % i
        for i in range(30))
    r = _analyze([("a", warnings)], [("a", "Build succeeded.\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "exempt-diagnostic"):
        failures.append("diagnostic purge not exempted")
    if r["regressed"]:
        failures.append("diagnostic purge exempted but still regressed")
    # 7. mixed cell is NOT exempt: the purge swallowed a large real output
    #    line together with the warnings (char-weighted fraction ~0.65)
    mixed = warnings + "real result: " + "z" * 900 + "\n"
    r = _analyze([("a", mixed)], [("a", "real result: " + "z" * 50 + "\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("purge swallowing real output exempted (should flag)")
    # 8. accent-blind motif: "configuré" with accent still matches
    r = _analyze([("a", long_text)],
                 [("a", "Execution sautée (API non configurée)\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("accented motif (sautée/configurée) not matched")
    # 9. added notebook is never judged
    if _analyze([], [("a", skip_notice)], added=True)["regressed"]:
        failures.append("added notebook judged instead of skipped")
    # 10. deleted cell loses volume legitimately: no head key, no finding
    if _analyze([("a", long_text), ("b", long_text)], [("a", long_text)])["cells"]:
        failures.append("deleted cell produced a finding")
    # 11. index-shift is not misattributed (same contract as the flood)
    if any(f["cell"] == "a" for f in
           _analyze([("a", long_text)],
                    [("zz", "y"), ("a", long_text)])["cells"]):
        failures.append("unchanged cell flagged after benign insert")

    # 12. moved-content exemption at diff scale: notebook A collapses a cell,
    #     notebook B is CREATED by the same diff with comparable volume.
    rows = [
        analyze(_nb([("a", long_text * 3)]), _nb([("a", "y" * 30)])),
        analyze(None, _nb([("b", "z" * 1500)])),
    ]
    _apply_moved_content(rows)
    if rows[0]["cells"] and rows[0]["cells"][0]["kind"] != "exempt-moved":
        failures.append("moved content not exempted at diff scale")
    if rows[0]["regressed"]:
        failures.append("moved content exempted but still regressed")
    # 13. ...but a moved gain BELOW the fraction does not exempt
    rows = [
        analyze(_nb([("a", long_text * 3)]), _nb([("a", "y" * 30)])),
        analyze(None, _nb([("b", "z" * 300)])),
    ]
    _apply_moved_content(rows)
    if not rows[0]["regressed"]:
        failures.append("insufficient moved gain exempted the collapse")

    # 14. Issue #21424 T2-corrige : quatre controles positifs pris sur les
    #     10 derives confirmees a la lecture par le coordinateur (PR
    #     #21426 CHANGES_REQUESTED). Chaque cas utilise le texte reel
    #     mesure au commit fautif et a son parent. Les cas sous plancher
    #     (Bonsai 274 chars), a longueur egale (Planners-0 538->593), ou
    #     avec croissance (Kokoro f82ed24e 566->15602) sont autant de
    #     cas que l'ancien organe ratait systematiquement.
    bonsai_b = ("Token charge depuis D:\\Dev\\CoursIA\\.secrets\\qwen-api-user.token\n"
                "ComfyUI connecte : http://127.0.0.1:8188\n"
                "  GPU : cuda:0 NVIDIA GeForce RTX 3090 : cudaMallocAsync (24.0 GB)\n"
                "Generation terminee en 2.0s\n"
                "  Image : bonsai_demo_00001_.png\n"
                "  Params : 1024x1024, 4 steps, seed=42\n")
    bonsai_h = ("ComfyUI non disponible : COMFYUI_API_URL manquant dans .env\n"
                "La generation sera skippee.\n\n"
                "Generation skipped (ComfyUI non disponible).\n")
    r = _analyze([("recipe-cell", bonsai_b)], [("recipe-cell", bonsai_h)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("calibration Bonsai (sous plancher 274 chars, motif"
                        " non disponible) not flagged")
    else:
        print("calibration Bonsai (sous plancher): flagged as signature,"
              " motif=" + r["cells"][0].get("motif", ""))

    pl0_b = ("============================================================\n"
             "RESUME DE L'ENVIRONNEMENT PLANIFICATION\n"
             "============================================================\n"
             "Plateforme:      Windows\n"
             "Python:          3.13.12\n"
             "------------------------------------------------------------\n"
             "unified-planning: OK\nOR-Tools:        OK\nDocker:          OK\n"
             "Fast Downward:   OK (Docker)\n"
             "============================================================\n\n"
             "Environnement pret pour les notebooks de planification.\n"
             "Fast Downward disponible pour la planification optimale.\n")
    pl0_h = ("============================================================\n"
             "RESUME DE L'ENVIRONNEMENT PLANIFICATION\n"
             "============================================================\n"
             "Plateforme:      Windows\n"
             "Python:          3.13.7\n"
             "------------------------------------------------------------\n"
             "unified-planning: OK\nOR-Tools:        OK\nDocker:          OK\n"
             "Fast Downward:   Non disponible\n"
             "============================================================\n\n"
             "Environnement pret pour les notebooks de planification.\n"
             "Note: Fast Downward non disponible via Docker.\n"
             "Vous pourrez utiliser d'autres solveurs avec unified-planning.\n")
    r = _analyze([("cell-17", pl0_b)], [("cell-17", pl0_h)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("calibration Planners-0 (longueur egale 538->593,"
                        " motif non disponible) not flagged")
    else:
        print("calibration Planners-0 (longueur egale): flagged as signature")

    # Kokoro f82ed24e : la cellule grossit (566 -> 15602 chars) parce que
    # le notebook telecharge HF ajoute des logs httpx en sortie, puis
    # degrade par un message d'absence. Le motif "n'est pas installe"
    # apparait uniquement en queue de la sortie.
    kokoro_h = ("INFLECT-NANO-V1 - TTS ULTRA-LEGER\n" + "x" * 15000 +
                "\nDependance manquante (No module named 'torchaudio').\n"
                "Inflect-Nano n'est pas installe - demonstration sautee"
                " (graceful).\n")
    kokoro_b = ("INFLECT-NANO-V1 - TTS ULTRA-LEGER\n" +
                "Recuperation du modele Inflect-Nano-v1...\n"
                "Backend : cuda\n"
                "Params : acoustic=3,465,125  vocoder=1,167,077  total=4,632,202\n"
                "Generation reussie\n  Duree audio : 4.49s\n"
                "  Temps CPU : 2.03s  (RTF = 0.453, < 1 = plus rapide que"
                " le temps reel)\n")
    r = _analyze([("f82ed24e", kokoro_b)], [("f82ed24e", kokoro_h)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("calibration Kokoro f82ed24e (cellule qui grossit"
                        " 566->15602, motif n'est pas installe) not flagged")
    else:
        print("calibration Kokoro f82ed24e (cellule qui grossit):"
              " flagged as signature")

    sd35_b = ("Toutes les dependances sont disponibles\n"
              ".env charge depuis: D:\\Dev\\CoursIA\\.env\n"
              "Stable Diffusion 3.5 - Generation de Pointe\n"
              "Date: 2026-08-15 15:06:14\n"
              "HuggingFace: Token configure\n")
    sd35_h = ("WARNING: diffusers non installe - pip install diffusers\n"
              "Dependances manquantes: ['diffusers']\n"
              ".env charge depuis: .env\n"
              "Stable Diffusion 3.5 - Generation de Pointe\n"
              "Date: 2026-08-18 06:32:31\n"
              "HuggingFace: Token configure\n")
    r = _analyze([("cell-1", sd35_b)], [("cell-1", sd35_h)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("calibration SD-3.5 (classique 598->346, motif"
                        " non installe) not flagged")
    else:
        print("calibration SD-3.5 (classique): flagged as signature")

    # 14b. Exemptions FP : un cas par marqueur de la liste, tous
    #     mesures. Hors ligne exemptee, le contenu est NEUTRE : ce qui
    #     fait taire la cellule, c'est l'exemption de la ligne -- pas
    #     une cellule entiere muette (#21426 R3).
    transformers_h = ("[transformers] the fast path is not available because"
                       " one of the required library is not installed.\n"
                       "Falling back to torch implementation.\n"
                       "loading weights: 0%|          | 0/320\n")
    sdpa_h = ("Loading checkpoint: sdpa fallback engaged due to flash"
              " attention absence.\n"
              "model output: tensor([0.1, 0.2, 0.3])\n")
    allow_h = ("torch.backends.cuda.allow_fallback = True\n"
               "model output: tensor([0.1, 0.2, 0.3])\n")
    flash_h = ("flash-attn fallback engaged, torch native attention used\n"
               "model output: tensor([0.1, 0.2, 0.3])\n")
    env_h = ("warning: .env non trouve, utilisation variables"
             " environnement\n"
             "verification gpu...\n"
             "model output: tensor([0.1, 0.2, 0.3])\n")
    for label, h in [("transformers", transformers_h),
                     ("sdpa fallback", sdpa_h),
                     ("allow_fallback", allow_h),
                     ("flash-attn", flash_h),
                     (".env non trouve", env_h)]:
        # Base neutre de 600 chars : au-dessus du plancher de magnitude
        # (500), mais assez court pour que le ratio base/tete reste
        # sous MAGNITUDE_FACTOR -- ce test mesure l'EXEMPTION de
        # signature, pas la regle de contraction.
        r = _analyze([("x", "x" * 600)], [("x", h)])
        if r["cells"]:
            failures.append("FP exemption " + label + " failed: still"
                            " flagged as " + r["cells"][0]["kind"])
        else:
            print("FP exemption " + label + ": silent (not flagged)")

    # 14c. Co-occurrence (#21426 R3) : CONTROLE POSITIF. La ligne
    #     exemptee est retiree, le reste est juge. Une cellule qui
    #     melange un avertissement de bibliotheque et une degradation
    #     REELLE doit rester signalee -- l'exemption ne porte pas sur
    #     la cellule entiere.
    cooc_h = ("Loading checkpoint: sdpa fallback engaged due to flash"
              " attention absence.\n"
              "ComfyUI non disponible : generation skippee.\n"
              "model output: tensor([0.1, 0.2, 0.3])\n")
    r = _analyze([("x", long_text)], [("x", cooc_h)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("co-occurrence R3 (ligne exemptee + degradation"
                        " reelle) not flagged")
    else:
        print("co-occurrence R3 (ligne exemptee + degradation reelle):"
              " flagged as signature")

    # 15. body-justification parser (Issue #21424 T2): the section is the
    #     marker. Cells inside the section are returned as (notebook, cell)
    #     pairs; the section header itself is the gate bypass.
    body_ok = ("## Output-collapse justification\n"
               "- Lean-7b-Examples.ipynb cell eb711ddb: faux positif, prose imprimee\n"
               "- Lean-7b-Examples.ipynb#4d4322dd allègement déclaré (probe)\n"
               "- Lean-7b-Examples.ipynb@32aa3fbb contenu déplacé dans la cellule 6\n"
               "## Other section\n")
    j = parse_collapse_justification(body_ok)
    if ("Lean-7b-Examples.ipynb", "eb711ddb") not in j:
        failures.append("body-justification: cell id not extracted (form 1)")
    if ("Lean-7b-Examples.ipynb", "4d4322dd") not in j:
        failures.append("body-justification: cell id not extracted (form 2)")
    if j.get(("Lean-7b-Examples.ipynb", "eb711ddb"), "") == "":
        failures.append("body-justification: reason not captured")
    if parse_collapse_justification(""):
        failures.append("body-justification: empty body returns non-empty")
    if parse_collapse_justification("## no marker here"):
        failures.append("body-justification: missing section returns non-empty")
    if parse_collapse_justification("## Output-collapse justification\nno cells"):
        failures.append("body-justification: section without cells is non-empty")

    # 15a. T2-corrige : la soupape restreinte a 3 motifs. Une raison qui
    #      nomme une absence d'environnement (cle, outil, mode degrade)
    #      est REFUSEE et compte comme non traitee.
    for refused_reason in [
        "API key not configured",
        "cle api absente",
        "mode degrade accepte",
        "GPU absent",
        "skipped",
        "demonstration sautee",
    ]:
        if classify_justification_reason(refused_reason) != "refused":
            failures.append("soupape: refused reason not classified as"
                            " refused: " + refused_reason)
    for accepted_reason in [
        "faux positif (avertissement transformers)",
        "allègement déclaré",
        "contenu déplacé",
        "deplace vers cellule 6",
        "moved content",
    ]:
        if classify_justification_reason(accepted_reason) != "accepted":
            failures.append("soupape: accepted reason not classified as"
                            " accepted: " + accepted_reason)
    if classify_justification_reason("") != "empty":
        failures.append("soupape: empty reason not classified as empty")
    if classify_justification_reason("just prose without a keyword") != "refused":
        failures.append("soupape: prose without keyword not refused")

    # 15b. Unaddressed : une justification refusee compte comme non
    #      traitee. C'est la restriction demandee par la revue
    #      CHANGES_REQUESTED sur #21426.
    rows_j = [
        {"notebook": "Lean-7b-Examples.ipynb",
         "cells": [{"cell": "eb711ddb", "kind": "signature",
                    "factor": 14.9, "base": 1000, "head": 67},
                   {"cell": "4d4322dd", "kind": "magnitude",
                    "factor": 49.4, "base": 1000, "head": 20},
                   {"cell": "32aa3fbb", "kind": "magnitude",
                    "factor": 49.4, "base": 1000, "head": 20}]},
    ]
    body_mixed = ("## Output-collapse justification\n"
                  "- Lean-7b-Examples.ipynb cell eb711ddb: faux positif\n"
                  "- Lean-7b-Examples.ipynb cell 4d4322dd: API key not configured\n"
                  "- Lean-7b-Examples.ipynb cell 32aa3fbb: allègement déclaré\n")
    j_mixed = parse_collapse_justification(body_mixed)
    un = _unaddressed(rows_j, j_mixed)
    # eb711ddb: accepted (faux positif) -> covered
    # 4d4322dd: refused (api key not configured) -> unaddressed
    # 32aa3fbb: accepted (allegement declare) -> covered
    if len(un) != 1 or un[0]["cell"] != "4d4322dd":
        failures.append("soupape: refused reason did not stay unaddressed:"
                        " got " + str([u["cell"] for u in un]))

    # 14. history mode: replay the ratchet on the first-parent history
    #     of main. The replay should NOT crash and should be deterministic
    #     over the same window. The reference case is replayed directly:
    #     we walk back from SELF_TEST_HEAD to find a parent where the cells
    #     were substantial (Issue #21424 T1 acceptance -- the founding
    #     collapse of #15209 had a real restore point).
    from check_output_failure_text import git
    if (git("cat-file", "-e", SELF_TEST_HEAD, cwd=cwd) is None
            or git("cat-file", "-e", SELF_TEST_BASE, cwd=cwd) is None):
        print("SKIP history: reference commits not in this clone")
    else:
        # The reference case collapsed 3 cells (signature kind). For each
        # one, _find_restore_point must return a non-null restore point
        # BEFORE the base of the collapse (cells that were substantial
        # before the squash that produced 56d98429a).
        rows = compare(SELF_TEST_BASE, SELF_TEST_HEAD,
                       [SELF_TEST_NOTEBOOK], cwd=cwd)
        r0 = rows[0] if rows else {}
        cells = [f for f in r0.get("cells", [])
                 if f["kind"] in ("signature", "magnitude")]
        if not cells:
            failures.append("history reference case: compare() found 0"
                            " signature/magnitude findings to walk back from")
        else:
            for f in cells[:3]:
                rp = _find_restore_point(SELF_TEST_NOTEBOOK, f["cell"],
                                          SELF_TEST_HEAD, f["base"], cwd=cwd)
                if rp is None:
                    failures.append("history reference case: cell "
                                    + str(f["cell"]) + " has no restore point")
                else:
                    # Restore point must be BEFORE the head (earlier SHA
                    # in first-parent terms; we accept any earlier commit).
                    if rp["sha"] == SELF_TEST_HEAD:
                        failures.append("history reference case: restore point"
                                        " is the culprit itself")
                    if "subject" not in rp or "date" not in rp:
                        failures.append("history reference case: restore"
                                        " point missing date/subject")
            # Also check the data shape that history() yields -- the keys
            # are part of the public contract (T1 acceptance). Build a
            # synthetic history() output from a known finding to verify
            # the yield shape without driving a full walk.
            f0 = cells[0]
            rp = _find_restore_point(SELF_TEST_NOTEBOOK, f0["cell"],
                                      SELF_TEST_HEAD, f0["base"], cwd=cwd)
            synthetic = {
                "notebook": SELF_TEST_NOTEBOOK,
                "cell": f0["cell"],
                "kind": f0["kind"],
                "culprit": {"sha": SELF_TEST_HEAD, "date": "2026-01-01",
                             "subject": "synthetic"},
                "restore_point": rp,
                "base": f0["base"],
                "head": f0["head"],
                "factor": f0["factor"],
            }
            for key in ("notebook", "cell", "kind", "culprit",
                        "restore_point", "base", "head", "factor"):
                if key not in synthetic:
                    failures.append("history contract: finding missing key "
                                    + key)
            if "sha" not in synthetic["culprit"]:
                failures.append("history contract: culprit missing sha")
            if cells[0]["kind"] == "signature":
                print("history reference case: " + str(len(cells))
                      + " finding(s), first cell " + str(cells[0]["cell"])
                      + " factor x" + str(cells[0]["factor"])
                      + " -> restore point found")

    # Replay the reference case (#15209).
    from check_output_failure_text import git
    if (git("cat-file", "-e", SELF_TEST_HEAD, cwd=cwd) is None
            or git("cat-file", "-e", SELF_TEST_BASE, cwd=cwd) is None):
        print("SKIP replay: reference commits not in this clone")
    else:
        rrows = compare(SELF_TEST_BASE, SELF_TEST_HEAD,
                        [SELF_TEST_NOTEBOOK], cwd=cwd)
        r0 = rrows[0] if rrows else {}
        n_sig = sum(1 for f in r0.get("cells", [])
                    if f["kind"] == "signature")
        print("replay " + SELF_TEST_HEAD[:12] + " on "
              + SELF_TEST_NOTEBOOK.split("/")[-1] + ": total "
              + str(r0.get("base_total")) + " -> " + str(r0.get("head_total"))
              + ", signature findings " + str(n_sig)
              + " " + str([f["cell"] + " x" + str(f["factor"])
                           for f in r0.get("cells", [])]))
        if n_sig < SELF_TEST_MIN_FINDINGS:
            failures.append("replay signature findings " + str(n_sig)
                            + " < " + str(SELF_TEST_MIN_FINDINGS) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses fired, benign churn silent, exemptions "
          "hold, reference replay fires")
    return 0


# ---------------------------------------------------------------------------
# Body-justification bypass (Issue #21424 T2 / NAMING c.2193 family).
# The PR may carry a `## Output-collapse justification` section listing the
# cells the author considers legitimate. The organ reports which flagged
# findings are NOT covered by the section; only those gate the merge.
# ---------------------------------------------------------------------------
JUSTIFICATION_HEADER = re.compile(
    r"^##\s*Output-collapse\s*justification\b[^\n]*\n(.*?)(?=^##\s|\Z)",
    re.IGNORECASE | re.MULTILINE | re.DOTALL,
)
# A cell line: `- notebook.ipynb cell abcd1234: reason` or
#              `- notebook.ipynb#abcd1234 reason` or
#              `- abcd1234 (notebook.ipynb): reason`.
# The cell id accepts the hyphen: the nbformat ids of this repo are the
# conventional `cell-<nom>` (`cell-setup`, `cell-melody`,
# `cell-text-to-music`), and a `[A-Za-z0-9_]+` capture stopped at the
# hyphen -- the bypass then named a cell that does not exist, and the
# finding stayed unaddressed on exactly the notebooks it targets
# (measured on `02-3-MusicGen-Generation.ipynb`, cell `cell-melody`).
JUSTIFICATION_CELL = re.compile(
    r"^\s*[-*]\s*"
    r"(?P<notebook>[^#\s:]+(?:\.ipynb))"
    r"(?:\s*cell\s+|\s*#)(?P<cell>[A-Za-z0-9_-]+)"
    r"\b",
    re.IGNORECASE,
)

# Issue #21424 T2-corrige (2026-10-19, revue coordinateur) : la soupape
# accepte seulement 3 motifs de justification. Toute raison qui nomme
# une absence d'environnement (cle, outil, GPU, service, mode degrade)
# est REFUSEE et compte comme non traitee (= HARD-fail). Les trois
# motifs acceptes : faux positif (avertissement bibliotheque, prose
# imprimee), allegement declare, contenu deplace.
ACCEPTED_JUSTIFICATION_RE = re.compile(
    r"\bfaux[ -]?positif\b"
    r"|\ballegement\b|\balleg[eé]\b"
    r"|\bcontenu deplace\b|\bdeplace\b|\bmoved\b",
    re.IGNORECASE,
)
# Refused keywords : any of these in the reason text means the
# justification is REJECTED. Conservative: default is to refuse if no
# accepted keyword is found.
REFUSED_JUSTIFICATION_RE = re.compile(
    r"\b(non disponible|indisponible|non installe|n[' ]?est pas installe"
    r"|not installed|not available)"
    r"|\b(non configure|not configured|cles? (api )?(absente|manquante)"
    r"|api[_ ]key (absente|manquante|missing))"
    r"|\b(mode (squelette|mock|degrade|simulation))"
    r"|\b(skipped|skip(ping|pee)|demonstration sautee|generation sautee)"
    r"|\b(gpu absent|out of scope|hors scope|env(ironment)? (absent|manquant))",
    re.IGNORECASE,
)


def _load_pr_body(path):
    """Return the PR body markdown, or '' if absent.

    ``--pr-body-file <path>`` names a file and is read as such. Otherwise
    the env var ``COLLAPSE_PR_BODY`` carries the body **in memory** -- the
    form the workflows use, since writing ``${{ github.event.pull_request.body }}``
    to a file trips the CodeQL ``actions/code-injection`` pattern (same
    channel as ``MD_CONTENT_LOSS_PR_BODY``, #13491).

    The env var is ALSO accepted as a path: a value that names an existing
    file is read, so a dispatch caller that materialises the body keeps
    working. Without that fallback the in-memory text was opened as a
    filename and every caller silently lost its justification (#21552).

    An empty value means 'no body available, do not bypass'.
    """
    if path is not None:
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                return f.read()
        except OSError:
            return ""
    value = os.environ.get("COLLAPSE_PR_BODY", "")
    if not value:
        return ""
    try:
        with open(value, "r", encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return value
    except ValueError:  # nom de fichier invalide sur ce systeme : c'est du texte
        return value


def parse_collapse_justification(body):
    """Extract the set of (notebook, cell) pairs the body justifies.

    Returns a dict ``{(notebook, cell): "reason text..."}`` so the caller
    can both count and surface the justifications. Returns an empty dict
    if the section is absent or no cell lines parse.
    """
    if not body:
        return {}
    m = JUSTIFICATION_HEADER.search(body)
    if not m:
        return {}
    section = m.group(1)
    justified = {}
    for line in section.splitlines():
        m2 = JUSTIFICATION_CELL.search(line)
        if not m2:
            continue
        notebook = m2.group("notebook")
        cell = m2.group("cell")
        # Reason = the part of the line after the cell token
        tail = line[m2.end():].strip(" :;-")
        justified[(notebook, cell)] = tail[:240]
    return justified


def classify_justification_reason(reason):
    """Return 'accepted', 'refused' or 'empty' for a justification reason.

    'accepted' : the reason names one of the 3 accepted motifs
                 (faux positif, allegement, contenu deplace).
    'refused'  : the reason names a refused motif (env absent, mode
                 degrade, cle absente, etc.) -- the Epic #21424 and
                 #21427 (CLAUDE.md section C.2) close this door.
    'empty'    : no reason text -- the cell is not justified.

    Matching is accent-blind (cf. ``_normalize``), so 'allègement' and
    'allegement' both count.
    """
    if not reason or not reason.strip():
        return "empty"
    norm = _normalize(reason)
    if REFUSED_JUSTIFICATION_RE.search(norm):
        return "refused"
    if ACCEPTED_JUSTIFICATION_RE.search(norm):
        return "accepted"
    # Default : refuse silently. A line that names neither an accepted
    # motif nor a refused one is treated as a soft refusal -- the
    # author has not justified anything, they have just left prose.
    return "refused"


def _unaddressed(bad_rows, justified):
    """Flatten flagged findings into a list of dicts not covered by the body.

    A cell listed in ``justified`` is only treated as covered when its
    reason classifies as 'accepted'. 'refused' reasons (env absent, mode
    degrade, etc.) keep the cell unaddressed -- this is the soupape
    restriction demanded in the PR #21426 CHANGES_REQUESTED review.
    """
    out = []
    for r in bad_rows:
        for f in r["cells"]:
            if f["kind"] not in ("signature", "magnitude"):
                continue
            key = (r["notebook"], f["cell"])
            if key in justified:
                klass = classify_justification_reason(justified[key])
                if klass == "accepted":
                    continue
            out.append({"notebook": r["notebook"], "cell": f["cell"],
                        "kind": f["kind"], "factor": f["factor"],
                        "base": f["base"], "head": f["head"]})
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Advisory ratchet: no silent per-cell collapse of output"
                    " volume between the merge base and HEAD (mirror of"
                    " check_output_flood.py).")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative control, then replay the"
                         " reference case (#15209)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--history", action="store_true",
                    help="Replay the ratchet on the first-parent history of"
                         " main (Issue #21424 T1 / H.6 audit-history organ)."
                         " Yields one JSON line per finding, each with its"
                         " culprit commit and the last parent where the cell"
                         " was substantial (restore point).")
    ap.add_argument("--since", default="2026-04-01",
                    help="Lower bound for --history (default: 2026-04-01)")
    ap.add_argument("--until", default="2099-01-01",
                    help="Upper bound for --history (default: 2099-01-01)")
    ap.add_argument("--notebook", default=None,
                    help="Restrict --history to one notebook path (POSIX)")
    ap.add_argument("--limit", type=int, default=None,
                    help="Cap the number of commits scanned (smoke testing)")
    ap.add_argument("--pr-body-file", default=None,
                    help="Path to the PR body markdown (used for the"
                         " '## Output-collapse justification' bypass)"
                         " or empty string '' to skip. Falls back to env"
                         " COLLAPSE_PR_BODY if unset.")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.history:
        findings = list(history(args.since, args.until,
                                notebook=args.notebook, limit=args.limit))
        for f in findings:
            print(json.dumps(f, ensure_ascii=False))
        print("# findings: " + str(len(findings)), file=sys.stderr)
        return 0

    if not args.base:
        ap.error("base ref required (or --self-test / --history)")

    base = resolve_base(args.base)
    paths = changed_notebooks(base)
    rows = compare(base, None, paths)
    bad = [r for r in rows if r["regressed"]]

    # T2 (Issue #21424): the body-justification bypass. A PR may justify
    # one or more flagged cells in a `## Output-collapse justification`
    # section. Justified cells are removed from the gate verdict; the
    # remaining unaddressed cells are still reported. The marker is
    # case-insensitive and tolerates trailing whitespace or a colon.
    pr_body = _load_pr_body(args.pr_body_file)
    justified = parse_collapse_justification(pr_body) if pr_body else {}

    if args.as_json:
        print(json.dumps({"base_ref": args.base, "merge_base": base,
                          "changed": len(paths), "flagged": len(bad),
                          "justified": len(justified),
                          "unaddressed": _unaddressed(bad, justified),
                          "rows": rows}, indent=2, ensure_ascii=False))
    else:
        unaddressed = _unaddressed(bad, justified)
        print("base " + str(args.base) + " -> merge-base " + base[:12]
              + " | " + str(len(paths)) + " changed notebooks | "
              + str(len(bad)) + " flagged | " + str(len(justified))
              + " justified in body (" + ("no body read" if not pr_body
                                          else str(len(pr_body)) + " chars read")
              + ") | " + str(len(unaddressed))
              + " unaddressed")
        for r in rows:
            for f in r["cells"]:
                if f["kind"].startswith("exempt-"):
                    print("  EXEMPT (" + f["kind"][7:] + ") "
                          + r["notebook"] + " cell " + str(f["cell"]) + " "
                          + str(f["base"]) + " -> " + str(f["head"])
                          + " (x" + str(f["factor"]) + ")")
        for r in bad:
            print("\nFLAGGED " + r["notebook"] + "  total "
                  + str(r["base_total"]) + " -> " + str(r["head_total"]))
            for f in r["cells"]:
                if f["kind"] in ("signature", "magnitude"):
                    key = (r["notebook"], f["cell"])
                    tag = "JUSTIFIED" if key in justified else "OPEN"
                    print("  " + tag + " " + f["kind"].upper() + ": cell "
                          + str(f["cell"]) + " " + str(f["base"]) + " -> "
                          + str(f["head"]) + " (x" + str(f["factor"]) + ")"
                          + ((" -- " + justified[key]) if key in justified
                             and justified[key] else ""))
        if unaddressed:
            print("\nUNADDRESSED (" + str(len(unaddressed)) + " cell(s) ):"
                  " the PR body must carry a '## Output-collapse"
                  " justification' section listing each cell, OR the"
                  " contraction must be fixed and the cell RE-EXECUTED"
                  " (Stop & Repair, NAMING c.595 + c.598). The signature"
                  " signal usually means a re-execution without API keys"
                  " -- re-execute with the keys configured.")
            if not pr_body:
                print("La section ne peut pas couvrir ces cellules :"
                      " AUCUN body de PR n'a ete recu (ni --pr-body-file,"
                      " ni COLLAPSE_PR_BODY). Verifier le cablage du"
                      " workflow, ce n'est pas un defaut de la PR.")
            print("Forme attendue de chaque ligne : le chemin COMPLET du"
                  " carnet, repo-relative -- pas le basename. Exemple :"
                  " `- MyIA.AI.Notebooks/Search/Search-11-Metaheuristics.ipynb"
                  " cellule <id> -- <motif>` ; les lignes FLAGGED ci-dessus"
                  " donnent deja le chemin et l'id a recopier.")
        elif bad:
            print("\nAll flagged cells are covered by the '## Output-collapse"
                  " justification' section in the body. Gate passes.")
    return 1 if _unaddressed(bad, justified) else 0


if __name__ == "__main__":
    sys.exit(main())
