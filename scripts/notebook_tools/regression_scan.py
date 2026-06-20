#!/usr/bin/env python3
"""Notebook health-regression detector (temporal git-diff + CI guard).

Why this exists
---------------
The two existing snapshot scanners (forensic_scan.py, diagnose_broken.py) only
see *hard* failures (output_type=="error", execution_count is None). They miss
the *soft* environment-degradation regressions that the #3164 fidelity wave
surfaced: a token-starved reasoning cell (tokens billed, empty content), a
"> Graphviz non disponible" fallback caveat, a "Skipped" Tweety output, an
OPTIMAL->FEASIBLE solver downgrade. Those land in category A_ALL_EXEC_OK and
slip through every existing audit (the axis-2 blind spot, cf
docs reference + memory audit-output-health-axis).

This tool adds two things the others lack:
  1. a SOFT-degradation marker layer (scans output text, not just error type);
  2. a TEMPORAL git-history walk that pinpoints WHEN/WHICH-COMMIT a notebook
     went from healthy to degraded (and whether it was later repaired).

Honest boundary: this detects OUTPUT-HEALTH degradation (axis-2). It does NOT
judge prose-vs-output fabrication (axis-1) -- that needs semantic judgment and
stays a human/bot review job. No "fidelity verified" claim is implied.

Modes
-----
    # SNAPSHOT (default) -- who is degraded at HEAD
    python regression_scan.py
    python regression_scan.py --series GenAI --json /tmp/health.json

    # HISTORY -- full per-notebook git walk: when/which-commit each regression
    python regression_scan.py --history
    python regression_scan.py --history --series GenAI --since "14 days ago"

    # GUARD -- CI gate: fail if a changed notebook went healthy->degraded
    python regression_scan.py --guard --base origin/main --head HEAD \
        --paths MyIA.AI.Notebooks/GenAI/.../foo.ipynb

Pure stdlib. Local git only (git log / git show) -- never gh.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"
ALLOWLIST_PATH = SCRIPT_DIR / "regression_allowlist.json"

# Reuse the sibling scanners' building blocks (do not re-implement).
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
try:
    from diagnose_broken import ERROR_PATTERNS, extract_errors
    from forensic_scan import EXCLUDE_DIRS, is_excluded, get_series
except ImportError as exc:  # pragma: no cover - defensive
    print(
        f"ERROR: cannot import sibling scanners (diagnose_broken/forensic_scan): {exc}",
        file=sys.stderr,
    )
    raise

# --------------------------------------------------------------------------- #
# Severity model
# --------------------------------------------------------------------------- #
SEV_WEIGHT = {"HIGH": 4, "MED": 2, "LOW": 0}

# Map diagnose_broken's ERROR_PATTERNS categories to a regression family.
# MISSING_DEP / KERNEL_ERROR / API_KEY are all Regle-F recoverable -> ENV.
ERROR_CATEGORY_FAMILY = {
    "MISSING_DEP": "ENV_DEGRADATION",
    "KERNEL_ERROR": "ENV_DEGRADATION",
    "API_KEY": "ENV_DEGRADATION",
    "RUNTIME_ERROR": "CODE_ERROR",
    "UNKNOWN": "CODE_ERROR",
}

# SOFT markers: (compiled regex, cause, family, severity). Scanned on the
# concatenated text of a code cell's OUTPUTS (what existing scanners ignore).
# Order matters only for which cause is reported first; all matches are kept.
SOFT_MARKERS = [
    (r"content['\"]?\s*[:=]\s*None|<empty>|finish_reason['\"]?\s*[:=]\s*['\"]length",
     "TOKEN_STARVE", "ENV_DEGRADATION", "HIGH"),
    (r"Graphviz non disponible|Rendu Graphviz|dot not found|dot:\s*command not found|ExecutableNotFound|failed to execute .*dot",
     "GRAPHVIZ_PATH", "ENV_DEGRADATION", "HIGH"),
    (r"MiniZinc non disponible|solver (?:not available|non disponible)|JVM .*non disponible|Tweety non disponible|ComfyUI non disponible",
     "TOOL_MISSING", "ENV_DEGRADATION", "HIGH"),
    (r"ImportError|ModuleNotFoundError|No module named|cannot import name",
     "MISSING_DEP", "ENV_DEGRADATION", "HIGH"),
    # API_ENDPOINT: a bare "401"/"403" matched SVG path coordinates and pixel
    # data (e.g. Infer factor-graph SVGs: x="403", 207,-403.25) -> the numeric
    # codes are only a signal when an HTTP/status/error keyword sits next to them.
    (r"\bUnauthorized\b|\bForbidden\b"
     r"|(?:HTTP|status|code|error|erreur|Client Error)[^\n]{0,15}\b40[13]\b"
     r"|\b40[13]\b[^\n]{0,15}(?:Forbidden|Unauthorized|Client Error)"
     r"|ConnectionError|ConnectionRefused|ConnectionResetError|Max retries exceeded"
     r"|Failed to establish a new connection|Name or service not known|ECONNREFUSED"
     # Provider / env-var NAMES alone appear in SUCCESS logs ("OPENAI_API_KEY
     # valide", "GET https://huggingface.co") -> only flag them when a failure
     # word sits within 25 chars.
     r"|(?:OPENAI_API|ANTHROPIC_API|HUGGINGFACE|HF_TOKEN|api[_-]?key)\w*"
     r"[^\n]{0,25}(?:non configur|manquant|missing|not set|not configured"
     r"|invalid|invalide|absent|erreur|\berror\b|failed|\bechou|unavailable)",
     "API_ENDPOINT", "ENV_DEGRADATION", "HIGH"),
    # SOLVER_DOWNGRADE: bare "UNSAT" is the EXPECTED result in SAT/SMT/logic
    # notebooks (theorem proofs: "negation = unsat => VALIDE", Arrow/Sen
    # demonstrations, crafted pigeonhole) -> never a degradation. Only an
    # explicit invalidity verdict (a solution was expected and the check failed)
    # or an INFEASIBLE instance counts.
    (r"Solution valide\s*[:=]\s*False|is_valid\(\)\s*[:=]\s*False"
     r"|solution\s+invalide|invalid solution|\bINFEASIBLE\b",
     "SOLVER_DOWNGRADE", "SOLVER", "HIGH"),
    (r"\bSkipped\b|\bnon disponible\b|\bindisponible\b",
     "TOOL_MISSING", "ENV_DEGRADATION", "HIGH"),
    (r"fallback|falling back|mode d[eé]grad[eé]|\bdegraded\b",
     "FALLBACK", "ENV_DEGRADATION", "MED"),
]
SOFT_MARKERS = [(re.compile(p, re.IGNORECASE), c, f, s) for p, c, f, s in SOFT_MARKERS]

# Benign output lines that LOOK like a degradation but are by-design (batch-mode
# widget skip, library "how to install" boilerplate). Dropped before soft-marker
# scanning so they do not produce false positives.
BENIGN_LINE = re.compile(
    r"mode interactif non disponible|ex[eé]cution non[- ]interactive|non[- ]interactive"
    r"|if .*program is not installed|install graphviz \(see",
    re.IGNORECASE,
)


def _scannable(text: str) -> str:
    """Drop benign lines before soft-marker scanning."""
    return "\n".join(ln for ln in text.splitlines() if not BENIGN_LINE.search(ln))


# Caveat-prose in MARKDOWN cells: weak correlating signal (someone documented a
# degradation). LOW severity, never makes a notebook DEGRADED on its own.
CAVEAT_PROSE = re.compile(
    r"Graphviz non disponible|MiniZinc non disponible|\bnon disponible\b|\bSkipped\b|fallback",
    re.IGNORECASE,
)

# Reproducibility regression: absolute machine paths leaked into the notebook
# (the #3436 papermill-abs-path class). Scanned over the whole notebook JSON.
ABSPATH_MARKER = re.compile(
    r"[A-Za-z]:[\\/]+Users[\\/]+|/mnt/[a-z]/Users/|/tmp/[^\"]*papermill|/home/[^\"]*/AppData",
)

REPAIR_HINT = {
    "TOKEN_STARVE": "raise max_completion_tokens >= 1000 (4000 for reasoning) + re-run",
    "GRAPHVIZ_PATH": "put dot on PATH / FactorGraphHelper.ResolveDotPath (#3546) + re-render",
    "TOOL_MISSING": "install the missing tool (MiniZinc / pin Tweety) + re-run",
    "MISSING_DEP": "pip/conda install the missing module + re-run",
    "API_ENDPOINT": "complete .env with a reachable endpoint+key + re-run",
    "SOLVER_DOWNGRADE": "fix instance feasibility OR demonstrate genuine infeasibility (allowlist + evidence)",
    "FALLBACK": "restore the primary path (env/tool) + re-run",
    "NEVER_EXEC": "execute the notebook before commit (C.2)",
    "NO_OUTPUT": "re-execute; confirm the cell really produces no output",
    "PAPERMILL_ABSPATH": "scrub_papermill_paths.py",
}


# --------------------------------------------------------------------------- #
# Health classification
# --------------------------------------------------------------------------- #
def _output_text(cell: dict) -> str:
    """Concatenate all textual payload of a code cell's outputs."""
    chunks = []
    for out in cell.get("outputs", []):
        ot = out.get("output_type")
        if ot == "stream":
            t = out.get("text", "")
            chunks.append("".join(t) if isinstance(t, list) else str(t))
        elif ot in ("execute_result", "display_data"):
            data = out.get("data", {})
            for key in ("text/plain", "text/markdown", "text/html"):
                v = data.get(key)
                if v:
                    chunks.append("".join(v) if isinstance(v, list) else str(v))
        elif ot == "error":
            chunks.append(out.get("ename", ""))
            chunks.append(out.get("evalue", ""))
            tb = out.get("traceback", [])
            chunks.append("\n".join(tb) if isinstance(tb, list) else str(tb))
    return "\n".join(chunks)


def _has_source(cell: dict) -> bool:
    src = cell.get("source", "")
    if isinstance(src, list):
        src = "".join(src)
    return bool(src.strip())


def classify_cell_health(cell: dict, idx: int, skip_structural: bool = False) -> list[dict]:
    """Return a list of degradation markers for one code cell (empty = healthy).

    Structural markers (NEVER_EXEC / NO_OUTPUT) are emitted at LOW severity: on
    their own they do not flip a notebook to DEGRADED (execution coverage is
    already owned by forensic_scan.py / notebook-execution-required.yml). They
    still matter in HISTORY mode, where a NEW structural cause between two
    revisions (had output -> none, executed -> null) is a real transition.
    """
    markers: list[dict] = []
    if cell.get("cell_type") != "code" or not _has_source(cell):
        return markers

    # Structural: never executed / no output (LOW -- see docstring).
    if not skip_structural:
        if cell.get("execution_count") is None:
            markers.append({"cell": idx, "cause": "NEVER_EXEC",
                            "family": "STRUCTURAL", "severity": "LOW"})
        elif not cell.get("outputs"):
            markers.append({"cell": idx, "cause": "NO_OUTPUT",
                            "family": "STRUCTURAL", "severity": "LOW"})

    text = _output_text(cell)

    # Hard errors -> reuse diagnose_broken's ERROR_PATTERNS for the cause.
    has_error = any(o.get("output_type") == "error" for o in cell.get("outputs", []))
    if has_error:
        cause = "UNKNOWN"
        for pattern, category in ERROR_PATTERNS:
            if re.search(pattern, text, re.IGNORECASE):
                cause = category
                break
        markers.append({"cell": idx, "cause": cause,
                        "family": ERROR_CATEGORY_FAMILY.get(cause, "CODE_ERROR"),
                        "severity": "HIGH"})

    # Soft markers -> the axis-2 signals the error scanners miss.
    # Scan only after dropping benign by-design lines (batch widget skip etc.).
    scan_text = _scannable(text)
    for rx, cause, family, sev in SOFT_MARKERS:
        m = rx.search(scan_text)
        if m:
            markers.append({"cell": idx, "cause": cause, "family": family,
                            "severity": sev, "snippet": _snippet(scan_text, m)})
    return markers


def _snippet(text: str, match: re.Match) -> str:
    a = max(0, match.start() - 30)
    b = min(len(text), match.end() + 30)
    return text[a:b].replace("\n", " ").strip()[:90]


def notebook_health(nb: dict, raw: str | None = None) -> dict:
    """Aggregate a notebook's health. Worst cell wins. score >0 => degraded."""
    markers: list[dict] = []
    code_idx = 0
    md_caveats = 0
    # QC quantbooks (qc_reference) run only on QC Cloud -> a missing local
    # execution is by-design, not a regression. Skip their structural markers
    # (same exemption forensic_scan.py applies via the REFERENCE category).
    skip_structural = nb.get("metadata", {}).get("qc_reference") is True
    for cell in nb.get("cells", []):
        ct = cell.get("cell_type")
        if ct == "code":
            markers.extend(classify_cell_health(cell, code_idx, skip_structural))
            code_idx += 1
        elif ct == "markdown":
            src = cell.get("source", "")
            src = "".join(src) if isinstance(src, list) else str(src)
            if CAVEAT_PROSE.search(src):
                md_caveats += 1

    # Reproducibility: abs-path leak anywhere in the notebook JSON.
    blob = raw if raw is not None else json.dumps(nb, ensure_ascii=False)
    if ABSPATH_MARKER.search(blob):
        markers.append({"cell": -1, "cause": "PAPERMILL_ABSPATH",
                        "family": "REPRO", "severity": "LOW"})

    score = sum(SEV_WEIGHT[m["severity"]] for m in markers)
    causes = sorted({m["cause"] for m in markers})
    families = sorted({m["family"] for m in markers})
    verdict = "DEGRADED" if any(m["severity"] in ("HIGH", "MED") for m in markers) else "HEALTHY"
    return {
        "verdict": verdict,
        "score": score,
        "n_markers": len(markers),
        "markers": markers,
        "causes": causes,
        "families": families,
        "md_caveats": md_caveats,
    }


# --------------------------------------------------------------------------- #
# Git helpers (local only)
# --------------------------------------------------------------------------- #
def _git(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


def git_revisions(relpath: str, since: str | None = None) -> list[dict]:
    """Commits that touched relpath, oldest->newest: {sha, date, author}."""
    args = ["log", "--follow", "--reverse", "--format=%H\x1f%cI\x1f%an"]
    if since:
        args.append(f"--since={since}")
    args += ["--", relpath]
    cp = _git(args)
    revs = []
    for line in cp.stdout.splitlines():
        parts = line.split("\x1f")
        if len(parts) == 3:
            revs.append({"sha": parts[0], "date": parts[1], "author": parts[2]})
    return revs


def git_show_notebook(rev: str, relpath: str) -> tuple[dict | None, str | None]:
    """Parse the notebook at <rev>:<relpath>. (None, None) if absent/unparsable."""
    cp = _git(["show", f"{rev}:{relpath}"])
    if cp.returncode != 0 or not cp.stdout:
        return None, None
    try:
        return json.loads(cp.stdout), cp.stdout
    except (json.JSONDecodeError, ValueError):
        return None, None


# --------------------------------------------------------------------------- #
# Allowlist
# --------------------------------------------------------------------------- #
def load_allowlist() -> list[dict]:
    if not ALLOWLIST_PATH.exists():
        return []
    try:
        data = json.loads(ALLOWLIST_PATH.read_text(encoding="utf-8"))
        return data.get("acknowledged", []) if isinstance(data, dict) else data
    except (json.JSONDecodeError, OSError):
        return []


def is_allowlisted(relpath: str, cause: str, allow: list[dict]) -> dict | None:
    rp = relpath.replace("\\", "/")
    for entry in allow:
        ep = str(entry.get("path", "")).replace("\\", "/")
        if ep and (rp.endswith(ep) or ep.endswith(rp)):
            causes = entry.get("cause")
            if causes in (None, "*") or cause == causes or (
                isinstance(causes, list) and cause in causes
            ):
                return entry
    return None


# --------------------------------------------------------------------------- #
# Notebook discovery
# --------------------------------------------------------------------------- #
def _git_tracked_files() -> set[str] | None:
    """Return set of git-tracked relative paths, or None if not in a git repo.

    Mirrors generate_catalog.py:_git_tracked_files so the axis-2 census never
    reports on gitignored notebooks (e.g. partner-course lean-workspace/ clones
    that live on disk but are never committed -> false-positive degradations).
    """
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "MyIA.AI.Notebooks/"],
            capture_output=True, text=False, cwd=str(REPO_ROOT),
        )
        if result.returncode != 0:
            return None
        return set(result.stdout.decode("utf-8").strip("\x00").split("\x00"))
    except FileNotFoundError:
        return None


def discover(root: Path, series: str | None,
             git_tracked_only: bool = False) -> list[Path]:
    nbs = sorted(p for p in root.rglob("*.ipynb") if not is_excluded(p))
    if series:
        nbs = [p for p in nbs if get_series(p, root) == series]
    if git_tracked_only:
        tracked = _git_tracked_files()
        if tracked is not None:
            nbs = [p for p in nbs if rel(p) in tracked]
    return nbs


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


# --------------------------------------------------------------------------- #
# Mode: SNAPSHOT
# --------------------------------------------------------------------------- #
def run_snapshot(root: Path, series: str | None, allow: list[dict],
                 git_tracked_only: bool = False) -> dict:
    results = []
    for nb_path in discover(root, series, git_tracked_only=git_tracked_only):
        try:
            raw = nb_path.read_text(encoding="utf-8")
            nb = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError, OSError):
            continue
        h = notebook_health(nb, raw)
        rp = rel(nb_path)
        h["path"] = rp
        h["series"] = get_series(nb_path, root)
        # Demote allowlisted causes.
        ack = [c for c in h["causes"] if is_allowlisted(rp, c, allow)]
        h["acknowledged"] = ack
        if ack and set(h["causes"]) <= set(ack):
            h["verdict"] = "ACKNOWLEDGED"
        results.append(h)
    return {"results": results}


def render_snapshot(data: dict) -> str:
    res = data["results"]
    degraded = [r for r in res if r["verdict"] == "DEGRADED"]
    degraded.sort(key=lambda r: r["score"], reverse=True)
    ack = [r for r in res if r["verdict"] == "ACKNOWLEDGED"]

    lines = ["# Notebook health snapshot (axis-2)", ""]
    lines.append(f"Scanned: {len(res)}  |  DEGRADED: {len(degraded)}  |  "
                 f"ACKNOWLEDGED: {len(ack)}  |  HEALTHY: {len(res) - len(degraded) - len(ack)}")
    lines.append("")

    cause_counts: Counter = Counter()
    family_counts: Counter = Counter()
    for r in degraded:
        for m in r["markers"]:
            if m["severity"] in ("HIGH", "MED"):
                cause_counts[m["cause"]] += 1
                family_counts[m["family"]] += 1

    if family_counts:
        lines += ["## By family", "", "| Family | Markers |", "|--------|---------|"]
        for fam, n in family_counts.most_common():
            lines.append(f"| {fam} | {n} |")
        lines += ["", "## By cause", "", "| Cause | Markers | Repair |", "|-------|---------|--------|"]
        for cause, n in cause_counts.most_common():
            lines.append(f"| {cause} | {n} | {REPAIR_HINT.get(cause, '-')} |")
        lines.append("")

    if degraded:
        lines += ["## Degraded notebooks (worst first)", "",
                  "| Score | Series | Notebook | Causes |",
                  "|-------|--------|----------|--------|"]
        for r in degraded:
            name = r["path"].split("/")[-1]
            lines.append(f"| {r['score']} | {r['series']} | {name} | {', '.join(r['causes'])} |")
        lines.append("")

    if ack:
        lines += ["## Acknowledged (allowlisted genuine degradations)", ""]
        for r in ack:
            lines.append(f"- {r['path']} ({', '.join(r['acknowledged'])})")
        lines.append("")

    lines += ["---", "_Axis-2 output-health only. Prose-vs-output fidelity (axis-1) "
              "is not judged here -- that stays a human/bot review job._"]
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Mode: HISTORY
# --------------------------------------------------------------------------- #
def _walk_one(nb_path: Path, root: Path, since: str | None) -> dict | None:
    relpath = rel(nb_path)
    revs = git_revisions(relpath, since)
    if not revs:
        return None
    timeline = []
    for r in revs:
        nb, raw = git_show_notebook(r["sha"], relpath)
        if nb is None:
            continue
        h = notebook_health(nb, raw)
        # Score-driving causes only (HIGH/MED). LOW structural causes flip-flop
        # across re-exec cycles and would otherwise generate spurious noise.
        bad = {m["cause"] for m in h["markers"] if m["severity"] in ("HIGH", "MED")}
        timeline.append({"sha": r["sha"][:9], "date": r["date"][:10],
                         "author": r["author"], "score": h["score"],
                         "verdict": h["verdict"], "causes": bad})
    if not timeline:
        return None

    # A transition is recorded only on a SCORE change (i.e. a HIGH/MED marker
    # appeared or cleared) -- not on LOW structural churn.
    transitions = []
    for prev, cur in zip(timeline, timeline[1:]):
        if cur["score"] > prev["score"]:
            transitions.append({"kind": "REGRESSION", "sha": cur["sha"],
                                "date": cur["date"], "author": cur["author"],
                                "added": sorted(cur["causes"] - prev["causes"]),
                                "score": f"{prev['score']}->{cur['score']}"})
        elif cur["score"] < prev["score"]:
            transitions.append({"kind": "RECOVERY", "sha": cur["sha"],
                                "date": cur["date"], "author": cur["author"],
                                "removed": sorted(prev["causes"] - cur["causes"]),
                                "score": f"{prev['score']}->{cur['score']}"})

    regressions = [t for t in transitions if t["kind"] == "REGRESSION"]
    if not regressions and timeline[-1]["score"] == 0:
        return None  # always healthy, nothing to report

    return {
        "path": relpath,
        "series": get_series(nb_path, root),
        "current_score": timeline[-1]["score"],
        "current_verdict": timeline[-1]["verdict"],
        "current_causes": sorted(timeline[-1]["causes"]),
        "n_revisions": len(timeline),
        "transitions": transitions,
        "regressions": regressions,
    }


def run_history(root: Path, series: str | None, since: str | None,
                workers: int, git_tracked_only: bool = False) -> dict:
    nbs = discover(root, series, git_tracked_only=git_tracked_only)
    print(f"History-walk over {len(nbs)} notebooks ({workers} workers)...",
          file=sys.stderr)
    results = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for i, out in enumerate(ex.map(lambda p: _walk_one(p, root, since), nbs), 1):
            if i % 50 == 0:
                print(f"  {i}/{len(nbs)}...", file=sys.stderr)
            if out:
                results.append(out)
    return {"results": results}


def render_history(data: dict) -> str:
    res = data["results"]
    # Currently-degraded regressions first, then by most recent regression.
    res.sort(key=lambda r: (r["current_score"], len(r["regressions"])), reverse=True)
    still = [r for r in res if r["current_score"] > 0]
    repaired = [r for r in res if r["current_score"] == 0]

    lines = ["# Notebook regression history (temporal git-walk)", ""]
    lines.append(f"Notebooks with >=1 regression in history: {len(res)}  |  "
                 f"still degraded at HEAD: {len(still)}  |  repaired since: {len(repaired)}")
    lines.append("")

    if still:
        lines += ["## STILL DEGRADED at HEAD (repair, do not consecrate)", ""]
        for r in still:
            lines.append(f"### {r['path']}  (score {r['current_score']}, "
                         f"{', '.join(r['current_causes'])})")
            for t in r["regressions"]:
                add = ", ".join(t["added"]) or "score-up"
                lines.append(f"  - REGRESSED {t['date']} `{t['sha']}` ({t['author']}): "
                             f"{add}  [{t['score']}]")
            for cause in r["current_causes"]:
                hint = REPAIR_HINT.get(cause)
                if hint:
                    lines.append(f"    -> {cause}: {hint}")
            lines.append("")

    if repaired:
        lines += ["## Repaired since (regress -> recovery, validates the fix)", ""]
        for r in repaired:
            regs = "; ".join(f"{t['date']} {','.join(t['added']) or 'score-up'}"
                             for t in r["regressions"])
            lines.append(f"- {r['path']} -- was: {regs}")
        lines.append("")

    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Mode: GUARD (CI)
# --------------------------------------------------------------------------- #
def run_guard(base: str, head: str, paths: list[str], allow: list[dict]) -> int:
    failures = []
    for p in paths:
        relpath = rel(Path(p))
        if relpath.startswith("COURSE_CATALOG") or "CATALOG-STATUS" in relpath:
            continue
        if is_excluded(Path(relpath)):
            continue

        base_nb, base_raw = git_show_notebook(base, relpath)
        if head in ("HEAD", "WORKTREE") and (REPO_ROOT / relpath).exists():
            try:
                head_raw = (REPO_ROOT / relpath).read_text(encoding="utf-8")
                head_nb = json.loads(head_raw)
            except (OSError, json.JSONDecodeError):
                head_nb, head_raw = git_show_notebook(head, relpath)
        else:
            head_nb, head_raw = git_show_notebook(head, relpath)
        if head_nb is None:
            continue

        head_h = notebook_health(head_nb, head_raw)
        base_score = notebook_health(base_nb, base_raw)["score"] if base_nb else 0

        if head_h["score"] > base_score:
            new_bad = [m for m in head_h["markers"] if m["severity"] in ("HIGH", "MED")]
            blocking = [m for m in new_bad if not is_allowlisted(relpath, m["cause"], allow)]
            if blocking:
                failures.append({"path": relpath, "delta": f"{base_score}->{head_h['score']}",
                                 "markers": blocking})

    if not failures:
        print("regression-guard: OK -- no notebook went healthy->degraded.")
        return 0

    print("regression-guard: FAIL -- health regression(s) detected:\n")
    for f in failures:
        print(f"  {f['path']}  (score {f['delta']})")
        for m in f["markers"]:
            hint = REPAIR_HINT.get(m["cause"], "")
            loc = f"cell {m['cell']}" if m["cell"] >= 0 else "notebook"
            print(f"    - [{m['severity']}] {m['cause']} @ {loc}  -> {hint}")
    print("\nRepair the cause (Regle F) + re-run, or allowlist a genuinely-external\n"
          "degradation in scripts/notebook_tools/regression_allowlist.json with evidence,\n"
          "or apply the 'regression-accepted' PR label for a demonstrated case.")
    return 1


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--history", action="store_true", help="temporal git-walk mode")
    ap.add_argument("--guard", action="store_true", help="CI gate mode")
    ap.add_argument("--base", help="guard: base ref (e.g. origin/main)")
    ap.add_argument("--head", default="HEAD", help="guard: head ref (default HEAD/worktree)")
    ap.add_argument("--paths", nargs="*", default=[], help="guard: changed notebook paths")
    ap.add_argument("--series", help="restrict to one series (e.g. GenAI)")
    ap.add_argument("--since", help="history: git date window (e.g. '14 days ago')")
    ap.add_argument("--root", default=str(NOTEBOOKS_DIR), help="notebook root")
    ap.add_argument("--workers", type=int, default=8, help="history: thread pool size")
    ap.add_argument("--json", dest="json_out", help="also write machine-readable JSON here")
    ap.add_argument("--git-tracked-only", action="store_true",
                    help="restrict discovery to git-tracked notebooks (mirrors "
                         "generate_catalog --git-tracked-only). Excludes gitignored "
                         "on-disk clones (e.g. partner-course lean-workspace/) that "
                         "are never committed and would surface as false-positive "
                         "degradations. Default off for backward compat.")
    args = ap.parse_args()

    allow = load_allowlist()
    root = Path(args.root).resolve()

    if args.guard:
        if not args.base:
            print("ERROR: --guard requires --base", file=sys.stderr)
            return 2
        return run_guard(args.base, args.head, args.paths, allow)

    if args.history:
        data = run_history(root, args.series, args.since, args.workers,
                           git_tracked_only=args.git_tracked_only)
        out = render_history(data)
    else:
        data = run_snapshot(root, args.series, allow,
                            git_tracked_only=args.git_tracked_only)
        out = render_snapshot(data)

    print(out)
    if args.json_out:
        Path(args.json_out).write_text(
            json.dumps(data, indent=2, ensure_ascii=False, default=list),
            encoding="utf-8")
        print(f"\nJSON: {args.json_out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
