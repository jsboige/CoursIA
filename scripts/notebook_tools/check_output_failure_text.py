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

A third, ADVISORY class (#18916, Lean-10 demo mode):

  DECLARED_FALLBACK  one of the two DEGRADED_HINT soft motifs whose banner is
                 printed BY THE CELL'S OWN SOURCE -- a demo-mode stub that
                 says, in its own code, what it will print when the tool is
                 absent (``print('[SKIP] LeanDojo non disponible')``, or an
                 f-string stub under a literal ``[SKIP]`` marker). Reported,
                 never gated: a documented fallback is not an unnoticed
                 failure. Hard patterns stay unexemptible in every case.

                 The exemption is additionally CONDITIONED ON THE BASE: a
                 declared banner is not a fallback when the same cell (by
                 ``id``) carried a substantial output at the merge base. A
                 render replaced by a banner is a LOSS OF CAPABILITY -- the
                 damage #3473 / #11685 measured -- so that hit stays a
                 TOOL_FAILURE and keeps gating. Only a cell that is new, or
                 that was already in fallback at base, is a DECLARED_FALLBACK.

Only notebooks CHANGED between the merge base and HEAD are judged, and only
occurrences whose count GREW are reported. A notebook that already carried
such text keeps it: this is a ratchet, not a repo-wide scold. Pre-existing
debt is surfaced by ``--all`` (advisory sweep), never by the gate.

MACHINE_PATH is also matched on document and cell METADATA string values
(``metadata.path``, or any metadata key whose value is a string), not only on
cell outputs (#14513): a re-execution can leak an absolute path into
``metadata.path`` without touching a single output, which the output-only gate
read as ``0 regressed`` while the branch carried the path. The extension is
kept to MACHINE_PATH -- metadata never carries a tool-failure banner, and the
convention permits normalizing a metadata key by hand (secrets-hygiene rule 6)
only because the gate has to be able to SEE it first.

The sweep also ventilates a third class, ``DEGRADED_HINT`` (#11692): the two
soft "non disponible / not available" motifs, which on an absolute sweep are
the large majority of hits and are mostly DELIBERATE fallback banners. They
stay inside TOOL_FAILURE_PATTERNS for the gate (a 0 -> N jump on a branch is
still signal) but are reported in their own count by ``--all`` and never
summed into the TOOL_FAILURE total -- so an advisory sweep no longer reads
as a cleanup backlog that is mostly noise.

A third axis, ``CAPABILITY_DOWNGRADE`` (#14603), is ADVISORY and never gates:
a re-execution on a machine without the capability the notebook was written
for (GPU -> CPU) produces well-formed output -- "Device : cpu" is a correct
execution report, not a failure banner, so the two gating classes are blind
to it BY DESIGN. What makes the downgrade invisible rather than merely
unclassified is the second half-turn: the witness line printed under
``if gpu_available:`` disappears at the same time, so the output diff looks
exactly like a legitimate re-execution. The finding is the COUPLE on one
cell with byte-identical source: capability value regression AND
witness-line disappearance. Founding replay: #14262 (be6a8c7f3b9e ->
0ea56ae0f, GenAI/Audio 02-4-Demucs cells 10/31, cuda + "VRAM utilisee" ->
cpu, VRAM gone) -- a state that existed TRANSIENTLY on the #14262 branch
while the gate read 0 regressed; the branch's own final GPU re-exec (merged
as 15c205323) restored cuda, which main still carries. The replay pair
documents what this axis would have flagged had the branch merged mid-leg.
A deliberate documented CPU run (RECOVERABLE-MACHINE verdict in the PR
body) passes: the lift is written in the report line itself.

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
#
# DEGRADED_HINT_PATTERNS are the two soft motifs inherited unmeasured from
# check_render_volume_delta._UNAVAILABLE_PATTERNS (#11692): on a fresh sweep
# they are ~93% of the absolute hits, and they are overwhelmingly DELIBERATE
# outputs -- the secrets-hygiene "'configuree' if key else '(non configuree)'"
# shape and designed batch-mode fallbacks. They stay inside
# TOOL_FAILURE_PATTERNS because the GATE counts them in delta (0 -> N on a
# branch is still a signal worth seeing) and the founding-commit replay
# depends on that; the --all SWEEP alone ventilates them out so an advisory
# total does not read as a cleanup backlog that is 93% noise.
DEGRADED_HINT_PATTERNS = (
    re.compile(r"non\s+disponible", re.IGNORECASE),
    re.compile(r"not\s+available", re.IGNORECASE),
)
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
    *DEGRADED_HINT_PATTERNS,
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

# --- benign banners: matched above, and NOT a tool failure -----------------
# The emitter says in the same breath that it fell back to a WORKING
# implementation. The transformers fast-path banner is a PERFORMANCE notice
# -- identical outputs, slower kernel -- and it is already committed on main
# in PT_03 and PT_05, merged as the normal state of the PostTraining series
# (2 occurrences repo-wide, measured 2026-08-19). Blocking PT_02 for carrying
# the same line would send an author to build a CUDA kernel in order to
# silence a warning that changed nothing in the notebook (render-volume delta
# base -> head on #11439: zero loss, PT_02 gains 440 B of widget output).
#
# The exception is LITERAL and narrow on purpose. A general "falling back"
# allowlist would swallow the founding incident itself: its .NET helper ALSO
# fell back -- to a path that destroyed the SVG. Banners are stripped from a
# COPY of the text before matching, so a genuine failure sharing the same
# stream still fires (asserted by --self-test).
BENIGN_BANNERS = (
    re.compile(
        r"\[transformers\]\s*The fast path is not available because one of "
        r"the required library is not installed\.\s*"
        r"Falling back to torch implementation\.",
        re.IGNORECASE),
    # Sandbox interception report (GenAI/Texte 12/13/14, #12508): the confined
    # executor DEMONSTRATES the interception of an import outside its
    # whitelist, and the demo's committed output carries the intercepted
    # exception's class name as DATA -- the word "ImportError" printed by the
    # report line, not a tool that failed to load. The prefix is emitted only
    # by the sandbox runner itself (executer_tests_detaille in 12/13/14); a
    # genuine missing-module failure never carries it. Same regime as the
    # transformers banner: literal, narrow, and a real failure in the same
    # stream still fires (asserted by --self-test).
    re.compile(
        r"echec de chargement intercepte : ImportError: module non autorise"
        r" dans le bac a sable : \S+[^\n]*",
        re.IGNORECASE),
)

# --- class 2: absolute path of the executing machine ------------------------
MACHINE_PATH_PATTERNS = (
    # Windows drive-letter path with at least two segments: D:\dev\CoursIA
    # A >=2-char first segment kills the escaped-newline FP -- an LLM answer
    # carrying a literal backslash-n pair after "n:" read as a Windows path
    # (its first "segment" was the single letter n). Real drive paths never
    # have a one-character segment.
    # BS + BS is the regex source for "one literal backslash": a single BS
    # here would escape the following brace and require a literal "{1,2}"
    # in the text -- a pattern that matches nothing and raises nothing. The
    # witness below is what caught exactly that, before this shipped.
    re.compile("[A-Za-z]:" + BS + BS + "{1,2}"
               + "[^" + BS + BS + '"\\s]{2,60}'
               + BS + BS + "{1,2}"
               + "[^" + BS + BS + '"\\s]{2,60}'),
    re.compile(r"/home/[A-Za-z0-9_.-]{2,32}/"),
    re.compile(r"/Users/[A-Za-z0-9_.-]{2,32}/"),
    re.compile(r"/mnt/[a-z]/[A-Za-z0-9_.-]{2,32}/"),
)

# A web URL is data, not a path of the executing machine. University
# personal pages live under /home/<user>/ on the SERVER
# (https://www.ccs.neu.edu/home/<user>/...), and an LLM answer that cites one
# carries it verbatim: measured on #18567, GenAI/Texte 06, where a web-search
# summary cited a course PDF and the gate reported a machine path. URLs are
# removed from a COPY of the text before path matching, as banners are before
# failure matching. Two forms stay visible on purpose: file:// URLs (they ARE
# local paths) and URLs of a local server (localhost, 127.0.0.1, 0.0.0.0),
# whose path can mirror the executing machine's tree.
_WEB_URL = re.compile(
    r"https?://(?!(?:localhost|127\.0\.0\.1|0\.0\.0\.0)(?:[:/]|$))"
    r"[^\s\"'<>)\]]+",
    re.IGNORECASE)


def _path_probe(text):
    """Copy of ``text`` without its web URLs, for MACHINE_PATH matching."""
    return _WEB_URL.sub(" ", text)


_PATH_WITNESSES = (
    "D:" + BS + "dev" + BS + "CoursIA-2-c1301-231-fbpy" + BS + "MyIA.AI.Notebooks",
    "/home/agent/CoursIA/MyIA.AI.Notebooks",
    "/Users/jsboige/CoursIA/scripts",
)

# --- class 3 (ADVISORY, never gates): capability downgrade -------------------
# #14603. Each half of the couple alone is legitimate: a value can move on a
# same-tier machine swap, a witness line can vanish in an honest output
# change reviewed as code. Only the couple on an UNCHANGED-SOURCE cell says
# "same code, executed elsewhere, with less capability".
#
# Closed, witnessed order table. cuda > cpu is the measured instance
# (#14262); fp16 -> fp32 and device-count -> 0 are the same FORM but have no
# witnessed pair in the repo yet -- extend only with a witness + its replay
# (the pattern-set philosophy above: a class that cannot be shown to fire is
# indistinguishable from one that is unplugged).
CAPABILITY_VALUE_RE = re.compile(
    r"\bdevice\s*[:=]\s*['\"]?(cuda(?:\s*:\s*\d+)?|cpu)\b", re.IGNORECASE)
CAPABILITY_ORDER = {"cuda": 2, "cpu": 1}

# Witness lines: measured on origin/main 2026-09-04 ("VRAM utilisee" x53,
# "GB VRAM" x144 inside GPU-name lines, "GPU : <Cap>" x36). The issue also
# names "CUDA device" / "Using device": zero committed occurrences -- not
# shipped without a witness.
CAPABILITY_WITNESS_PATTERNS = (
    re.compile(r"VRAM\s+utilis.e", re.IGNORECASE),
    re.compile(r"\d+(?:\.\d+)?\s*GB\s+VRAM", re.IGNORECASE),
    re.compile(r"GPU\s*[:=]\s*[A-Z]"),
)

# Founding downgrade replay (#14603): the CPU re-exec of #14262. Expected
# floor measured firsthand: 02-4-Demucs cells 10 and 31 regress
# (cuda + VRAM -> cpu, VRAM gone) while cell 4 was restored mid-range
# (net cuda -> cuda, must NOT fire -- the upgrade guard below is what keeps
# the restoration from being re-flagged in the 39f96fb82..0ea56ae0f
# direction). The degraded head is branch-side history of the squash-merged
# PR -- absent from any fresh clone (fetch-depth: 0 carries refs/heads
# only) -- so the replay pair is pinned as a fixture carrying the real
# cells verbatim, never read from git objects that may not be there.
DOWNGRADE_REPLAY_FIXTURE = "demucs_downgrade_pair_14603.json"
SELF_TEST_MIN_DOWNGRADE = 2


def _cell_output_text(cell):
    """Concatenated textual output of one code cell (stream, text/plain,
    traceback) -- the per-cell view of what output_texts yields per output."""
    parts = []
    for out in cell.get("outputs", []) or []:
        kind = out.get("output_type")
        if kind == "stream":
            text = out.get("text", "")
            parts.append("".join(text) if isinstance(text, list) else str(text))
        elif kind in ("execute_result", "display_data"):
            plain = (out.get("data", {}) or {}).get("text/plain")
            if plain is not None:
                parts.append("".join(plain) if isinstance(plain, list)
                             else str(plain))
        elif kind == "error":
            parts.append("\n".join(str(x) for x in (out.get("traceback", [])
                                                    or [])))
    return "\n".join(parts)


def _cell_source(cell):
    src = cell.get("source", "")
    return "".join(src) if isinstance(src, list) else str(src)


def _capability_values(text):
    """Set of normalised capability values named in an output text
    (subset of CAPABILITY_ORDER keys)."""
    values = set()
    for m in CAPABILITY_VALUE_RE.finditer(text):
        values.add(m.group(1).lower().split(":")[0].strip())
    return {v for v in values if v in CAPABILITY_ORDER}


def _witness_count(text):
    return sum(len(p.findall(text)) for p in CAPABILITY_WITNESS_PATTERNS)


def capability_downgrades(base_nb, head_nb):
    """Advisory findings (#14603): one per cell whose source is byte-identical
    between base and head, whose best capability class strictly DROPPED, and
    from which every witness line vanished. See the class-3 block above for
    why the couple -- not either half -- is the finding."""
    findings = []
    if not base_nb or not head_nb:
        return findings
    base_cells = base_nb.get("cells", []) or []
    head_cells = head_nb.get("cells", []) or []
    for i in range(min(len(base_cells), len(head_cells))):
        b_cell, h_cell = base_cells[i], head_cells[i]
        if b_cell.get("cell_type") != "code" or h_cell.get("cell_type") != "code":
            continue
        if _cell_source(b_cell) != _cell_source(h_cell):
            continue
        b_text, h_text = _cell_output_text(b_cell), _cell_output_text(h_cell)
        b_best = max((CAPABILITY_ORDER[v]
                      for v in _capability_values(b_text)), default=0)
        h_best = max((CAPABILITY_ORDER[v]
                      for v in _capability_values(h_text)), default=0)
        if not b_best > h_best:
            continue
        b_wit, h_wit = _witness_count(b_text), _witness_count(h_text)
        if b_wit > 0 and h_wit == 0:
            findings.append({
                "cell": i,
                "base": "/".join(sorted(_capability_values(b_text))) or "(absent)",
                "head": "/".join(sorted(_capability_values(h_text))) or "(absent)",
                "witness_lost": b_wit,
            })
    return findings


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


def metadata_texts(nb):
    """Yield (location_label, text) for every string-valued metadata key.

    Document-level and cell-level surfaces the output-only scan cannot see.
    A key is scanned because its VALUE is a string -- no name whitelist -- so
    the next metadata key a re-execution leaks is caught the first time it is
    introduced, not after somebody names it.

    ``metadata.papermill.input_path`` / ``output_path`` are repo-relative or
    basename (a pre-commit hook + secrets-hygiene rule 6) and so never match
    the machine-path patterns (verified on the 1234 notebooks, issue #14513
    precaution 1).

    location_label: ``doc:<key>`` for document metadata, ``cell[<i>]:<key>``
    for cell metadata.
    """
    md = nb.get("metadata", {}) or {}
    if isinstance(md, dict):
        for k, v in md.items():
            if isinstance(v, str) and v:
                yield "doc:" + str(k), v
    for i, cell in enumerate(nb.get("cells", []) or []):
        cmd = cell.get("metadata", {}) or {}
        if isinstance(cmd, dict):
            for k, v in cmd.items():
                if isinstance(v, str) and v:
                    yield "cell[%d]:%s" % (i, str(k)), v


def scan(nb, base_nb=None):
    """{class: [(location, matched_text), ...]} for one notebook.

    ``base_nb`` is the same notebook at the merge base, when one exists. It is
    consulted only by the DECLARED_FALLBACK exemption (#18916): a declared
    banner whose base cell carried a substantial output is a capability loss,
    not a demo fallback. The BASE side is never scanned with a base of its own
    (see ``compare``), so the ratchet's base counts keep their historical
    classification and cannot be inflated by the branch under judgement.

    ``location`` is a cell index for output hits, or a metadata descriptor
    (``doc:<key>`` / ``cell[<i>]:<key>``) for metadata hits. Only
    MACHINE_PATH is extended to metadata (issue #14513): metadata does not
    carry tool-failure banners, and the machine-path metadata class is what a
    re-execution leaks.
    """
    found = {"TOOL_FAILURE": [], "MACHINE_PATH": [], "DECLARED_FALLBACK": []}
    if not nb:
        return found
    for idx, text in output_texts(nb):
        if not text:
            continue
        probe = text
        for _ban in BENIGN_BANNERS:
            probe = _ban.sub(" ", probe)
        # A hard pattern fires FIRST and is never exemptible (#18916): a real
        # tool failure in the same stream as a declared demo banner stays a
        # TOOL_FAILURE -- including ImportError, which sits AFTER the soft
        # motifs in the tuple and would otherwise be masked by the exemption.
        soft_hit = hard_hit = None
        for pat in TOOL_FAILURE_PATTERNS:
            m = pat.search(probe)
            if not m:
                continue
            if pat in DEGRADED_HINT_PATTERNS:
                if soft_hit is None:
                    soft_hit = m.group(0)
            else:
                hard_hit = m.group(0)
                break
        if hard_hit:
            found["TOOL_FAILURE"].append((idx, hard_hit[:120]))
        elif soft_hit:
            if _declared_fallback(nb, idx, text, soft_hit, base_nb):
                found["DECLARED_FALLBACK"].append((idx, soft_hit[:120]))
            else:
                found["TOOL_FAILURE"].append((idx, soft_hit[:120]))
        path_probe = _path_probe(text)
        for pat in MACHINE_PATH_PATTERNS:
            for m in pat.finditer(path_probe):
                found["MACHINE_PATH"].append((idx, m.group(0)[:120]))
    # #14513: a machine path can also sit in document/cell metadata, invisible
    # to the output-only loop above -- the exact hole that let PT_11c's
    # metadata.path pass the gate green while the branch still carried the
    # path (#14272 / #13891). Scan string-valued metadata too, so the gate
    # sees the surface the convention (secrets-hygiene rule 6) allows fixing.
    for loc, text in metadata_texts(nb):
        path_probe = _path_probe(text)
        for pat in MACHINE_PATH_PATTERNS:
            for m in pat.finditer(path_probe):
                found["MACHINE_PATH"].append((loc, m.group(0)[:120]))
    return found


def _is_degraded_hint(match_text):
    """Ventilation --all (#11692): True if a TOOL_FAILURE hit's extracted
    text IS one of the two soft motifs. The extract is the match of the
    FIRST pattern that fired, and no substantial pattern's match contains a
    soft motif as substring, so this is a faithful discriminator. Used by
    the sweep only -- the gate keeps both classes merged by design."""
    return any(p.search(match_text) for p in DEGRADED_HINT_PATTERNS)


# Demo-mode stub marker (#18916): Lean-10 prints its deliberate skips under a
# literal [SKIP] prefix, both from literal banners and from f-strings that
# interpolate the caught exception -- the form a literal anchor cannot see.
SKIP_MARK = "[SKIP]"


def _base_cell_for(base_nb, cell):
    """La meme cellule (par ``id``) dans le carnet de base, ou None.

    L'``id`` est la cle stable entre deux revisions d'un carnet ; l'index ne
    l'est pas (une cellule inseree decale tout ce qui suit). Une cellule sans
    ``id`` -- ou absente de la base -- rend None : la base n'apporte alors
    aucune preuve, et l'exemption garde son sens historique.
    """
    cid = cell.get("id") if isinstance(cell, dict) else None
    if not cid or not base_nb:
        return None
    for other in base_nb.get("cells", []) or []:
        if isinstance(other, dict) and other.get("id") == cid:
            return other
    return None


def _substantial_output(cell):
    """True si la cellule porte une sortie qui n'est pas qu'une banniere.

    Test employe par la condition de base de ``_declared_fallback``. Deux
    formes de contenu comptent :

    - du texte dont au moins une LIGNE ne porte aucun des motifs doux -- une
      banniere ``Graphviz non disponible : rendu du graphe saute`` est donc
      ecartee **ligne a ligne**, pas par suppression du seul motif (qui
      laisserait ``Graphviz  : rendu du graphe saute``, non vide) ;
    - une donnee non textuelle (``image/svg+xml``, ``image/png``, ``text/html``)
      -- un rendu n'a pas toujours de replique ``text/plain``, et l'ignorer
      rouvrirait le trou sur les seules figures.
    """
    for out in cell.get("outputs", []) or []:
        data = out.get("data") or {}
        for mime, value in data.items():
            if mime == "text/plain":
                continue
            if value:
                return True
    kept = []
    for line in _cell_output_text(cell).splitlines():
        if not line.strip():
            continue
        if any(p.search(line) for p in DEGRADED_HINT_PATTERNS):
            continue
        kept.append(line)
    probe = "\n".join(kept)
    for ban in BENIGN_BANNERS:
        probe = ban.sub(" ", probe)
    return bool(probe.strip())


def _in_fallback(cell):
    """True si la cellule porte deja un motif doux en sortie (#19697).

    Une cellule de repli execute son chemin normal AVANT d'echouer : ses
    lignes d'echo (``Inpainting: '...'``, ``Soumission du workflow...``)
    rendent sa sortie ``substantial`` au sens du test ci-dessus sans que ce
    soient des rendus remplaces. La condition de base de ``_declared_fallback``
    ne peut donc pas se lire seule : repli a la base = exemption conservee.
    """
    return any(p.search(_cell_output_text(cell))
               for p in DEGRADED_HINT_PATTERNS)


def _declared_fallback(nb, idx, out_text, matched, base_nb=None):
    """True si une occurrence DOUCE est un fallback DECLARE par la cellule (#18916).

    Le mode demo de Lean-10 (#18893) stubbe lean_dojo absent : chaque cellule
    stubbee imprime une banniere 'non disponible' / 'not available' DELIBEREE,
    et le ratchet la comptait comme TOOL_FAILURE 0 -> N. Le diagnostic C.4 de
    la PR etait CAUSE_DOCUMENTED_ONLY : la sortie dit exactement ce que la
    source declare. Deux ancres, chacune suffit :

    (a) la sous-chaine matchee vit en LITTERAL dans la source -- le print de
        garde du stub l'imprime depuis la source ;
    (b) la source imprime le marqueur [SKIP] et la sortie le porte -- le cas
        d'un stub qui interpole l'exception (``print(f"[SKIP] ...: {e}")``),
        dont la banniere n'est pas un litteral de la source.

    Fail-safe conservateur : toute divergence (chaine absente de la source,
    marqueur absent d'un cote) laisse le hit en TOOL_FAILURE. Les motifs DURS
    ne passent jamais ici -- scan() leur donne priorite meme dans un stream
    stubbe, donc une vraie panne a cote d'une banniere demo reste visible.

    Condition de base (review ai-01 sur #19038, affinee #19697). Les deux
    ancres ci-dessus ne distinguent pas un mode demo DECLARE d'une degradation
    SUBIE a la re-execution : toute cellule a ``try/except`` porte sa banniere
    en litteral dans sa source, les deux tiennent dans la meme ligne. Quand
    ``base_nb`` est fourni et que la meme cellule (par ``id``) portait une
    sortie substantielle ET hors repli a la base, le hit reste TOOL_FAILURE :
    la banniere a REMPLACE un rendu, c'est une perte de capacite (#3473 /
    #11685), pas un repli documente. Une cellule nouvelle, ou deja en repli
    a la base, garde l'exemption -- y compris quand la sortie de repli de la
    base porte des lignes d'echo pre-echec (``Inpainting: '...'``, soumission
    du workflow) : ce sont la sortie normale du chemin de repli, pas des
    rendus remplaces (#19697, faux positif mesure sur 01-5b-Qwen-Image-Edit).
    """
    cells = nb.get("cells", []) or []
    if not (0 <= idx < len(cells)):
        return False
    cell = cells[idx]
    src = _cell_source(cell)
    declared = ((matched and matched in src)
                or (SKIP_MARK in src and SKIP_MARK in out_text))
    if not declared:
        return False
    base_cell = _base_cell_for(base_nb, cell)
    if (base_cell is not None and _substantial_output(base_cell)
            and not _in_fallback(base_cell)):
        return False
    return True


def _sample_location(loc):
    """Rend la localisation d'un echantillon telle qu'elle a ete produite.

    Un hit d'output porte un index de cellule entier -> ``cell[7]``. Un hit de
    metadata porte deja son propre label (``doc:<cle>`` ou ``cell[<i>]:<cle>``,
    cf. ``metadata_texts()``) -> l'imprimer verbatim. Sans ce tri, un hit
    metadata de document sortait ``cell[doc:path]`` et un hit metadata de
    cellule ``cell[cell[3]:papermill]`` : lisible, mais mal etiquete.
    """
    if isinstance(loc, str):
        return loc
    return "cell[" + str(loc) + "]"


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
        # The base side is scanned without a base of its own: its counts keep
        # their historical classification, so a branch cannot lower the bar by
        # reclassifying the reference it is measured against.
        b = scan(base_nb)
        h = scan(head_nb, base_nb=base_nb)
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
        # DECLARED_FALLBACK (#18916): soft motifs whose banner is printed BY
        # THE CELL'S OWN SOURCE (demo-mode stubs). Advisory only -- never in
        # the gating loop above, so a branch adding stubs does not regress.
        df_b, df_h = len(b["DECLARED_FALLBACK"]), len(h["DECLARED_FALLBACK"])
        row["classes"]["DECLARED_FALLBACK"] = {
            "base": df_b, "head": df_h, "delta": df_h - df_b}
        # Advisory axis (#14603): needs a base blob, never gates.
        row["capability_downgrades"] = (capability_downgrades(base_nb, head_nb)
                                        if base_nb is not None else [])
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
                   "Backtracking: 49/201/295 appels",
                   # LLM-generated code sample: literal backslash-n ESCAPES in
                   # the response text are data, not drive paths -- the
                   # 2-char minimum segment quantifier keeps them out.
                   r"pour 1..n:\n\ndef fizzbuzz(n):\n    result = []"):
        hit = ([p.pattern for p in TOOL_FAILURE_PATTERNS if p.search(benign)]
               + [p.pattern for p in MACHINE_PATH_PATTERNS if p.search(benign)])
        if hit:
            failures.append("benign text matched " + str(hit) + ": "
                            + repr(benign))

    # URL controls (#18567): a cited web page under /home/<user>/ is silent,
    # while a local-server URL, a file:// URL and a bare path sitting next to
    # a web URL still fire.
    web_cite = ("4. RAG vs Fine-tuning: "
                "https://www.ccs.neu.edu/home/alina/classes/Fall2024/Lecture11.pdf")
    if any(p.search(_path_probe(web_cite)) for p in MACHINE_PATH_PATTERNS):
        failures.append("web URL read as a machine path: " + repr(web_cite))
    for leak in ("http://localhost:8888/files/home/agent/CoursIA/x.ipynb",
                 "file:///home/agent/CoursIA/x.ipynb",
                 "voir https://example.org/a puis /home/agent/CoursIA/y.py"):
        if not any(p.search(_path_probe(leak)) for p in MACHINE_PATH_PATTERNS):
            failures.append("machine path hidden by the URL filter: "
                            + repr(leak))


    # Benign banner: matched by "not available", neutralised by
    # BENIGN_BANNERS -- and it must NOT mask a real failure in the same
    # stream. Both directions asserted: an exception that only proves it
    # silences is indistinguishable from a hole.
    _banner = ("[transformers] The fast path is not available because one of "
               "the required library is not installed. Falling back to torch "
               "implementation. To install follow https://github.com/fla-org/"
               "flash-linear-attention#installation")

    def _one(text):
        return scan({"cells": [{"cell_type": "code", "outputs": [
            {"output_type": "stream", "text": text}]}]})["TOOL_FAILURE"]

    if _one(_banner):
        failures.append("benign transformers fast-path banner still fires")
    if not _one(_banner + "\nbash: dot: command not found"):
        failures.append("benign banner masked a real failure in the same "
                        "stream")

    # Sandbox interception banner: same two-direction control. The banner
    # must be neutralised when alone, but must NOT hide a genuine missing
    # module elsewhere in the same stream.
    _sandbox = ("(4) import os  : (0/2)  echec de chargement intercepte : "
                "ImportError: module non autorise dans le bac a sable : os")
    if _one(_sandbox):
        failures.append("benign sandbox interception banner still fires")
    if not _one(_sandbox + "\nModuleNotFoundError: No module named 'simanneal'"):
        failures.append("sandbox banner masked a real failure in the same "
                        "stream")

    # Declared fallback (#18916): a demo-mode stub whose banner is printed BY
    # THE CELL'S OWN SOURCE is a DECLARED_FALLBACK, not a TOOL_FAILURE. Two
    # anchors (literal substring, [SKIP] marker on both sides), and the
    # negative direction for each: without the declaration the soft motif
    # still fires, and a real failure next to a declared banner still fires
    # -- an exemption that only proves it silences is indistinguishable
    # from a hole.
    _stub_src = "print('[SKIP] LeanDojo non disponible')"
    _stub_interp = ("try:\n    import lean_dojo\n"
                    "except Exception as e:\n"
                    "    print(f'[SKIP] LeanRunner indisponible: {e}')")

    def _scan1(source, out_text):
        return scan({"cells": [{"cell_type": "code", "source": source,
                                "outputs": [{"output_type": "stream",
                                             "text": out_text}]}]})

    _lit = _scan1(_stub_src, "[SKIP] LeanDojo non disponible")
    if _lit["TOOL_FAILURE"] or len(_lit["DECLARED_FALLBACK"]) != 1:
        failures.append("literal-source demo stub not exempted: "
                        + repr(_lit))
    _int = _scan1(_stub_interp,
                  "[SKIP] LeanRunner indisponible: LeanDojo not available. "
                  "Install with: pip install lean-dojo")
    if _int["TOOL_FAILURE"] or len(_int["DECLARED_FALLBACK"]) != 1:
        failures.append("interpolated [SKIP] demo stub not exempted: "
                        + repr(_int))
    _undeclared = _scan1("print(result)", "Graphviz non disponible")
    if len(_undeclared["TOOL_FAILURE"]) != 1 or _undeclared["DECLARED_FALLBACK"]:
        failures.append("undeclared soft motif exempted (hole): "
                        + repr(_undeclared))
    _mixed = _scan1(_stub_src,
                    "[SKIP] LeanDojo non disponible\n"
                    "bash: dot: command not found")
    if not _mixed["TOOL_FAILURE"]:
        failures.append("declared stub masked a real failure in the same "
                        "stream: " + repr(_mixed))

    # Base-conditioned exemption (#19038 review, ai-01). The two anchors above
    # cannot tell a declared demo stub from a degradation SUFFERED at
    # re-execution: every try/except cell carries its banner as a literal in
    # its own source. A banner that REPLACES a real output is a capability
    # loss and must stay a TOOL_FAILURE.
    _graphviz_src = ("try:\n"
                     "    import graphviz\n"
                     "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
                     "except ImportError:\n"
                     "    print('Graphviz non disponible : rendu du graphe "
                     "saute')")
    _banner = [{"output_type": "stream",
                "text": "Graphviz non disponible : rendu du graphe saute"}]
    _render = [{"output_type": "display_data",
                "data": {"image/svg+xml": "<svg/>",
                         "text/plain": "<graphviz.Digraph object>"}}]

    def _cid(cid, source, outputs):
        return {"cell_type": "code", "id": cid, "source": source,
                "outputs": outputs}

    _base_render = {"cells": [_cid("c-gv", _graphviz_src, _render)]}
    _head_banner = {"cells": [_cid("c-gv", _graphviz_src, _banner)]}

    _replaced = scan(_head_banner, base_nb=_base_render)
    if len(_replaced["TOOL_FAILURE"]) != 1 or _replaced["DECLARED_FALLBACK"]:
        failures.append("a banner replacing a real base render was exempted "
                        "(hole): " + repr(_replaced))
    # Direction that must KEEP the exemption: already in fallback at base.
    _already = scan(_head_banner,
                    base_nb={"cells": [_cid("c-gv", _graphviz_src, _banner)]})
    if _already["TOOL_FAILURE"] or len(_already["DECLARED_FALLBACK"]) != 1:
        failures.append("a cell already in fallback at base lost its "
                        "exemption: " + repr(_already))
    # #19697: same direction, but the base fallback run carries pre-failure
    # echo lines ("Inpainting: '...'", "Soumission du workflow...") that make
    # it substantial. The echoes are the normal output of the degraded path,
    # not a replaced render -- the exemption must hold. Measured on
    # 01-5b-Qwen-Image-Edit-2509 cell-10: byte-identical banner at base and
    # head, ratchet FAIL 0 -> 1 on a nav-line-only diff.
    _echo_src = ("try:\n"
                 "    print(\"Inpainting: 'un ordinateur portable'\")\n"
                 "    print('Soumission du workflow...')\n"
                 "    api.post(workflow)\n"
                 "except Exception:\n"
                 "    print('API non disponible: Exception')\n"
                 "    print('Workflow defini - necessite API ComfyUI active')")
    _echo_banner = [{"output_type": "stream",
                     "text": "Inpainting: 'un ordinateur portable'\n"
                             "Soumission du workflow...\n"
                             "API non disponible: Exception\n"
                             "Workflow defini - necessite API ComfyUI active"}]
    _echoed = scan({"cells": [_cid("c-echo", _echo_src, _echo_banner)]},
                   base_nb={"cells": [_cid("c-echo", _echo_src, _echo_banner)]})
    if _echoed["TOOL_FAILURE"] or len(_echoed["DECLARED_FALLBACK"]) != 1:
        failures.append("a fallback-with-echoes base lost its exemption "
                        "(#19697): " + repr(_echoed))
    # ... and a cell that is NEW at head (no base carrier).
    _new = scan({"cells": [_cid("c-new", _graphviz_src, _banner)]},
                base_nb=_base_render)
    if _new["TOOL_FAILURE"] or len(_new["DECLARED_FALLBACK"]) != 1:
        failures.append("a cell new at head lost its exemption: "
                        + repr(_new))
    # A base render stored only as a mime (no text/plain repr) still counts.
    _mime = scan(_head_banner, base_nb={"cells": [
        _cid("c-gv", _graphviz_src,
             [{"output_type": "display_data",
               "data": {"image/svg+xml": "<svg/>"}}])]})
    if len(_mime["TOOL_FAILURE"]) != 1:
        failures.append("a base render without a text/plain repr was not "
                        "seen: " + repr(_mime))

    # Capability axis (#14603): witnesses first, then the couple controls.
    # A witness line the patterns do not match is a hole by construction.
    for witness_line in ("VRAM utilisee : 0.64 GB",
                         "GPU : NVIDIA GeForce RTX 3090 (24.0 GB VRAM)"):
        if not any(p.search(witness_line)
                   for p in CAPABILITY_WITNESS_PATTERNS):
            failures.append("capability witness line unmatched: "
                            + repr(witness_line))
    for probe, expected in (("Mode : batch, Device : cuda", {"cuda"}),
                            ("Device = cpu", {"cpu"}),
                            ("torch.device('cuda:0')", set())):
        got = _capability_values(probe)
        if got != expected:
            failures.append("capability values " + repr(got) + " != "
                            + repr(expected) + " on " + repr(probe))

    def _nb_cell(source, out_text):
        return {"cells": [{"cell_type": "code", "source": source,
                           "outputs": [{"output_type": "stream",
                                        "text": out_text}]}]}

    _gpu_src = "print(info)\nprint(f'VRAM utilisee : {v:.2f} GB')"
    _couple = capability_downgrades(
        _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.64 GB"),
        _nb_cell(_gpu_src, "Device : cpu"))
    if len(_couple) != 1 or _couple[0]["base"] != "cuda":
        failures.append("couple (value regressed + witness gone + same "
                        "source) not flagged: " + repr(_couple))
    # Legit re-exec: same tier, values wiggle -- the everyday case.
    if capability_downgrades(
            _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.64 GB"),
            _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.63 GB")):
        failures.append("legit GPU re-exec flagged as capability downgrade")
    # Source changed: the move is a CODE change, reviewed as code.
    if capability_downgrades(
            _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.64 GB"),
            _nb_cell(_gpu_src + "\nprint('cpu fallback')",
                     "Device : cpu")):
        failures.append("changed-source downgrade flagged (must be reviewed "
                        "as code, not by this axis)")
    # Value alone: witness line still printed -- not the couple.
    if capability_downgrades(
            _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.64 GB"),
            _nb_cell(_gpu_src, "Device : cpu\nVRAM utilisee : 0.00 GB")):
        failures.append("value-only regression flagged (couple incomplete)")
    # Witness alone: value did not regress -- not the couple.
    if capability_downgrades(
            _nb_cell(_gpu_src, "Device : cuda\nVRAM utilisee : 0.64 GB"),
            _nb_cell(_gpu_src, "Device : cuda")):
        failures.append("witness-only disappearance flagged (couple "
                        "incomplete)")
    # Upgrade (restoration direction of #14262): must stay silent.
    if capability_downgrades(
            _nb_cell(_gpu_src, "Device : cpu"),
            _nb_cell(_gpu_src,
                     "Device : cuda\nVRAM utilisee : 0.64 GB")):
        failures.append("capability UPGRADE flagged (restoration must pass)")

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

    # #14513 replay: the metadata-only leak of #14272 / #13891, the defect
    # this extension exists to close. c4b99a3ec4 is the PT_11c head whose
    # metadata.path still carried the machine path (one document-level
    # MACHINE_PATH hit); 109cf4eb2 removed it (zero). The original output-only
    # scan reported 0 regressed on BOTH -- it cannot see metadata -- so a
    # predicate that fires on the base and stays silent on the head is the
    # proof of the fix, not a synthetic witness. Both commits are branch-side
    # history of a squash-merged PR and are absent from a fresh clone
    # (fetch-depth 0), so guard with cat-file exactly like the founding replay.
    c4b99a3ec4 = "c4b99a3ec49cda31057630ffb67802c026e75cbf"
    c109cf4eb = "109cf4eb219a7b5d0f566aaa47fda9540bba9926"
    if (git("cat-file", "-e", c4b99a3ec4, cwd=cwd) is None
            or git("cat-file", "-e", c109cf4eb, cwd=cwd) is None):
        print("SKIP #14513 replay: c4b99a3ec4/c109cf4eb not in this clone")
    else:
        nb_path = ("MyIA.AI.Notebooks/GenAI/PostTraining/"
                   "PT_11c_grpo_qwen17_rlvr.ipynb")
        base_nb = read_notebook_at(c4b99a3ec4, nb_path, cwd=cwd)
        head_nb = read_notebook_at(c109cf4eb, nb_path, cwd=cwd)
        b_meta = [loc for loc, _ in scan(base_nb)["MACHINE_PATH"]
                  if isinstance(loc, str)]
        h_meta = [loc for loc, _ in scan(head_nb)["MACHINE_PATH"]
                  if isinstance(loc, str)]
        print("replay #14513: metadata-path hits "
              + str(len(b_meta)) + " -> " + str(len(h_meta)))
        if "doc:path" not in b_meta:
            failures.append("#14513 replay: metadata.path not seen in base ("
                            + repr(b_meta) + ")")
        if h_meta:
            failures.append("#14513 replay: metadata machine path still in "
                            "head (" + repr(h_meta) + ")")

    # Second replay (#14603): the GPU -> CPU re-exec of #14262, pinned as a
    # fixture (see DOWNGRADE_REPLAY_FIXTURE). The two gating classes read
    # 0 regressed on this exact pair while the diff carried cuda -> cpu +
    # VRAM-line disappearance on unchanged-source cells -- the hole this
    # axis exists to close. Refuses to pass if the replay comes back
    # empty, same contract as the founding replay above -- and unlike a
    # git-object replay it cannot silently skip in a fresh clone.
    fixture_path = (Path(__file__).resolve().parent / "tests" / "fixtures"
                    / DOWNGRADE_REPLAY_FIXTURE)
    try:
        blob = json.loads(fixture_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        blob = None
        failures.append("downgrade replay fixture unreadable ("
                        + str(fixture_path) + "): " + str(exc))
    if blob is not None:
        n_down = len(capability_downgrades({"cells": blob["base_cells"]},
                                           {"cells": blob["head_cells"]}))
        print("replay fixture " + DOWNGRADE_REPLAY_FIXTURE + ": "
              + str(len(blob["base_cells"])) + " cells, "
              + "CAPABILITY_DOWNGRADE " + str(n_down))
        if n_down < SELF_TEST_MIN_DOWNGRADE:
            failures.append("downgrade replay CAPABILITY_DOWNGRADE "
                            + str(n_down) + " < "
                            + str(SELF_TEST_MIN_DOWNGRADE) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses matched, benign text silent, replays fire")
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
        # Name what was measured. --all reads the WORKING TREE, so its answer
        # is only as current as the checkout -- and a stale tree returns a
        # smaller, cleaner, wrong sweep without raising anything. Measured
        # while building this file: a sweep run one commit behind origin/main
        # reported the two founding notebooks as clean, because the commit
        # that broke them was not in the tree yet.
        head = (git("rev-parse", "HEAD") or "?").strip()[:12]
        behind = (git("rev-list", "--count", "HEAD..origin/main")
                  or "?").strip()
        dirty = "dirty" if (git("status", "--porcelain", "--", "*.ipynb")
                            or "").strip() else "clean"
        provenance = ("tree HEAD " + head + " | " + behind
                      + " commit(s) behind origin/main | notebooks " + dirty)
        rows = []
        for path in all_notebooks():
            found = scan(read_notebook_at(None, path))
            if (found["TOOL_FAILURE"] or found["MACHINE_PATH"]
                    or found["DECLARED_FALLBACK"]):
                # Ventilation (#11692): soft-motif hits leave the
                # TOOL_FAILURE count and are reported as DEGRADED_HINT --
                # never summed back. #18916: the soft hits whose banner is
                # printed by the cell's own source (demo stubs) ventilate
                # further into DECLARED_FALLBACK.
                tool = [(c, t) for c, t in found["TOOL_FAILURE"]
                        if not _is_degraded_hint(t)]
                hint = [(c, t) for c, t in found["TOOL_FAILURE"]
                        if _is_degraded_hint(t)]
                rows.append({
                    "notebook": path,
                    "TOOL_FAILURE": [{"cell": c, "match": t}
                                     for c, t in tool],
                    "DEGRADED_HINT": [{"cell": c, "match": t}
                                      for c, t in hint],
                    "DECLARED_FALLBACK": [{"cell": c, "match": t}
                                          for c, t in
                                          found["DECLARED_FALLBACK"]],
                    "MACHINE_PATH": [{"cell": c, "match": t}
                                     for c, t in found["MACHINE_PATH"]]})
        total_tool = sum(len(r["TOOL_FAILURE"]) for r in rows)
        total_hint = sum(len(r["DEGRADED_HINT"]) for r in rows)
        total_declared = sum(len(r["DECLARED_FALLBACK"]) for r in rows)
        total_path = sum(len(r["MACHINE_PATH"]) for r in rows)
        if args.as_json:
            print(json.dumps({"mode": "sweep", "provenance": provenance,
                              "head": head, "behind_origin_main": behind,
                              "worktree": dirty, "notebooks": len(rows),
                              "hits": {"TOOL_FAILURE": total_tool,
                                       "DEGRADED_HINT": total_hint,
                                       "DECLARED_FALLBACK": total_declared,
                                       "MACHINE_PATH": total_path},
                              "rows": rows}, indent=2, ensure_ascii=False))
        else:
            print("ADVISORY sweep [" + provenance + "]")
            print(str(len(rows)) + " notebooks carry failure text, degraded "
                  "hints or machine paths in committed outputs")
            # #11692: the sweep names what it measures. TOOL_FAILURE is the
            # substantial backlog; DEGRADED_HINT (deliberate "non disponible"
            # banners) is reported for visibility and NEVER added to it.
            # #18916: DECLARED_FALLBACK is the subset whose banner the cell
            # source itself prints (demo stubs) -- documented, not owed.
            print("TOOL_FAILURE " + str(total_tool)
                  + " | DEGRADED_HINT " + str(total_hint)
                  + " (reported, not summed) | DECLARED_FALLBACK "
                  + str(total_declared) + " | MACHINE_PATH "
                  + str(total_path))
            for r in rows:
                print("  " + r["notebook"]
                      + "  tool=" + str(len(r["TOOL_FAILURE"]))
                      + " hint=" + str(len(r["DEGRADED_HINT"]))
                      + " declared=" + str(len(r["DECLARED_FALLBACK"]))
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
                        print("     " + _sample_location(s["cell"]) + " "
                              + s["match"])
        if bad:
            print("\nCause is on the executing machine, not in the notebook: "
                  "install the missing tool and RE-EXECUTE. Never hand-edit a "
                  "committed output (Stop & Repair, secrets-hygiene rule 6).")
        downgrades = [(r["notebook"], r["capability_downgrades"])
                      for r in rows if r.get("capability_downgrades")]
        if downgrades:
            n_cells = sum(len(d) for _, d in downgrades)
            print("\nADVISORY CAPABILITY_DOWNGRADE (" + str(n_cells)
                  + " cell(s)) -- byte-identical source, executed with less "
                  "capability, witness line gone. Not gating (#14603):")
            for path, ds in downgrades:
                for d in ds:
                    print("  " + path + " cell[" + str(d["cell"]) + "] "
                          + d["base"] + " -> " + d["head"])
            print("  Lift: a deliberate, documented CPU run (RECOVERABLE-"
                  "MACHINE verdict in the PR body) passes -- state it there "
                  "and the reviewer acknowledges this line. Otherwise "
                  "re-execute on the capable machine; never hand-edit the "
                  "output (Stop & Repair).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
