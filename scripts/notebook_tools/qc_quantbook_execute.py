"""Execute a QC research quantbook headlessly via lean-cli + Docker + nbconvert.

Recipe validated 2026-05-10 (incident H.7 / forensic T17, ai-01).

Workflow:
  0. **#8734 data-quality pre-flight** -- extract the tickers the notebook requests
     (AddEquity/add_equity/AddForex/AddCrypto) and scan their on-disk daily zips; ABORT
     before Docker if any are STALE or DEGENERATE (forward-fill signature). Bypass:
     `--no-freshness-check`. (yfinance-only notebooks skip this -- not Lean-driven.)
  1. `lean login` once with QC_API_USER_ID + QC_API_TOKEN (Lean CLI stores creds in ~/.lean)
  2. `lean research <project> --detach --no-open --port <port>` from a Lean workspace
     (workspace must contain lean.json + data/ folder, e.g. partner-course-quant-trading/lean-workspace/)
  3. `docker exec <container> jupyter nbconvert --to notebook --execute --inplace
       --ExecutePreprocessor.timeout=N research.ipynb`
  4. Read the in-place modified notebook from the host path (Docker bind-mount)
  5. `docker stop <container>` + `docker rm`

Caveats:
  - The notebook MUST live inside a Lean project folder (sibling to main.py + config.json),
    itself under a Lean workspace (with lean.json + data/).
  - Path inside container is `/Lean/Launcher/bin/Debug/Notebooks/<filename>`.
  - First-run docker pull of `quantconnect/research:latest` is ~2-3 GB.
  - Notebook errors ARE captured via nbconvert (process exits 1 but writes the notebook).
  - Concurrency: each container occupies a port; loop sequentially or pre-allocate ports.
  - A target notebook that is a STUB or SHALLOW (qc_classify) should be transformed into
    a real research notebook BEFORE execution, not just executed.

Usage:
  python scripts/notebook_tools/qc_quantbook_execute.py \
      MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/Multi-Layer-EMA-Researcher \
      --notebook research.ipynb [--port 8889] [--timeout 600]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

LEAN_BIN_CANDIDATES = (
    Path(os.environ.get("APPDATA", "")) / "Python" / "Python312" / "Scripts" / "lean.exe",
    Path(os.environ.get("LOCALAPPDATA", "")) / "Programs" / "Python" / "Python312" / "Scripts" / "lean.exe",
    Path("/usr/local/bin/lean"),
    Path("/usr/bin/lean"),
)


def find_lean() -> str:
    explicit = os.environ.get("LEAN_CLI")
    if explicit and Path(explicit).exists():
        return explicit
    for p in LEAN_BIN_CANDIDATES:
        if p.exists():
            return str(p)
    fallback = shutil.which("lean")
    if fallback:
        return fallback
    raise RuntimeError(
        "lean CLI not found. pip install --user lean OR set LEAN_CLI env var."
    )


def workspace_root(project_dir: Path) -> Path:
    cur = project_dir.resolve()
    while cur != cur.parent:
        if (cur / "lean.json").exists():
            return cur
        cur = cur.parent
    raise RuntimeError(f"No lean.json found above {project_dir}")


def get_container_for_project(project_name: str) -> str | None:
    out = subprocess.run(
        ["docker", "ps", "--filter", "name=lean_cli", "--format", "{{.Names}}"],
        capture_output=True, text=True, check=True,
    )
    candidates = [n for n in out.stdout.splitlines() if n.strip()]
    return candidates[0] if candidates else None


# --- #8734 data-quality pre-flight (presence != freshness != non-degeneracy) ---

# A data-request call (Python QuantBook `add_equity` or C# Lean `AddEquity` and
# forex/crypto/option/security variants) followed by its first quoted symbol.
_SYMBOL_CALL_RE = re.compile(
    r'(?:qb|self|QB)?\s*\.\s*'
    r'(AddEquity|add_equity|AddForex|add_forex|AddCrypto|add_crypto|'
    r'AddSecurity|add_security|AddOption|add_option)'
    r'\s*\(\s*["\']([A-Za-z0-9.\-/]+)["\']'
)
# Asset class inferred from the request method, for daily-zip path resolution.
_METHOD_CLASS: dict[str, str] = {
    "AddEquity": "equity", "add_equity": "equity",
    "AddForex": "forex", "add_forex": "forex",
    "AddCrypto": "crypto", "add_crypto": "crypto",
    "AddSecurity": "equity", "add_security": "equity",
    "AddOption": "equity", "add_option": "equity",
}
# Daily-zip glob per asset class under <workspace>/data/.
_ZIP_GLOBS: dict[str, str] = {
    "equity": "equity/*/daily/{}.zip",
    "forex": "forex/*/daily/{}.zip",
    "crypto": "crypto/*/daily/{}.zip",
}


def extract_requested_symbols(notebook_path: Path) -> dict[str, set[str]]:
    """Return ``{'equity': {...}, 'forex': {...}, 'crypto': {...}}`` of symbols
    the notebook requests via AddEquity / add_equity / AddForex / AddCrypto /
    AddSecurity / AddOption calls.

    Used by the #8734 pre-flight so we only check tickers the quantbook actually
    consumes (not every zip in the workspace). Symbol case is normalised upper.
    """
    out: dict[str, set[str]] = {"equity": set(), "forex": set(), "crypto": set()}
    if not notebook_path.exists():
        return out
    try:
        nb = json.loads(notebook_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return out
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        # Skip full-line comments (Python `#` / C# `//`) so commented-out calls
        # (e.g. `# demo: self.AddEquity("DUMMY")`) are not mined as real requests.
        for line in src.split("\n"):
            if re.match(r"\s*(#|//)", line):
                continue
            for m in _SYMBOL_CALL_RE.finditer(line):
                cls = _METHOD_CLASS.get(m.group(1), "equity")
                out[cls].add(m.group(2).upper())
    return out


def preflight_data_quality(
    ws: Path, symbols: dict[str, set[str]], flat_tail_bars: int = 60,
) -> tuple[int, list[str]]:
    """Scan the requested symbols' daily zips under ``ws/data`` and return
    ``(n_flagged, messages)``.

    A symbol is **flagged** when its on-disk zip is:

    - **DEGENERATE** -- the last ``flat_tail_bars`` closes are identical (Lean
      ``fillDataForward`` output saved to disk, or a vendor-padded series), OR
    - **STALE** -- the last bar is older than a 6-month window (Lean
      ``fillDataForward=True``, the default, will silently forward-fill the tail
      as a constant at runtime).

    Both produce invalid metrics (B&H ~0%, direction ~100%) without any error
    -- the exact #8734 failure mode that invalidated #8714/#8730/#8719.

    Detection reuses ``check_data_freshness.scan_zip`` (single source of truth);
    if that module is not importable, the pre-flight degrades to a no-op (it is
    a guard, not a hard dependency). Symbols with no on-disk zip are not flagged
    here (absence/provisioning is a separate concern -- see #8724).
    """
    messages: list[str] = []
    quantconnect_dir = Path(__file__).resolve().parent.parent / "quantconnect"
    if str(quantconnect_dir) not in sys.path:
        sys.path.insert(0, str(quantconnect_dir))
    try:
        from check_data_freshness import scan_zip  # type: ignore
    except Exception as exc:  # pre-flight is a guard, never a hard failure
        return 0, [f"[freshness] check_data_freshness not importable ({exc}); pre-flight skipped."]

    from datetime import date, timedelta
    threshold = date.today() - timedelta(days=int(6 * 30.4))

    data_dir = ws / "data"
    n_flagged = 0
    seen: set[tuple[str, str]] = set()
    for cls, symset in symbols.items():
        glob_pat = _ZIP_GLOBS.get(cls)
        if not glob_pat or not symset:
            continue
        for sym in sorted(symset):
            if (cls, sym) in seen:
                continue
            seen.add((cls, sym))
            # crypto stems: <sym>.zip plus <sym>_trade / <sym>_quote variants.
            cands = list(data_dir.glob(glob_pat.format(sym)))
            if cls == "crypto":
                cands += list(data_dir.glob(glob_pat.format(sym + "_trade")))
                cands += list(data_dir.glob(glob_pat.format(sym + "_quote")))
            if not cands:
                continue
            zpath = sorted(cands)[-1]
            _first, last, _count, flat_tail = scan_zip(zpath, flat_tail_bars=flat_tail_bars)
            if last is None:
                continue
            if flat_tail:
                n_flagged += 1
                messages.append(
                    f"[freshness] {cls}/{sym}: DEGENERATE -- last {flat_tail_bars} closes "
                    f"identical in {zpath.name}. Forward-fill written to disk or vendor pad "
                    f"-> invalid metrics. See #8734."
                )
            elif last < threshold:
                n_flagged += 1
                messages.append(
                    f"[freshness] {cls}/{sym}: STALE -- last bar {last} predates {threshold}. "
                    f"Lean fillDataForward=True (default) will silently forward-fill the tail "
                    f"as a constant -> invalid metrics. See #8734."
                )
    return n_flagged, messages


def run(
    project_dir: Path, notebook_name: str, port: int, timeout: int,
    freshness_check: bool = True, flat_tail_bars: int = 60,
) -> int:
    lean = find_lean()
    ws = workspace_root(project_dir)
    project_rel = project_dir.resolve().relative_to(ws)
    print(f"[recipe] workspace={ws}", file=sys.stderr)
    print(f"[recipe] project={project_rel}  notebook={notebook_name}", file=sys.stderr)

    env = os.environ.copy()
    env["PYTHONUTF8"] = "1"

    # #8734 data-quality pre-flight: fail fast BEFORE the expensive Docker exec
    # if the notebook's requested tickers have stale or degenerate local data.
    # Producing metrics on degenerate data is the silent failure mode behind
    # #8714/#8730/#8719. Bypass with --no-freshness-check when intentional.
    if freshness_check:
        symbols = extract_requested_symbols(project_dir / notebook_name)
        total = sum(len(s) for s in symbols.values())
        if total:
            print(f"[freshness] pre-flight: {total} requested symbol(s) "
                  f"({dict({k: len(v) for k, v in symbols.items() if v})}) "
                  f"under {ws / 'data'}", file=sys.stderr)
            n_flagged, msgs = preflight_data_quality(ws, symbols, flat_tail_bars=flat_tail_bars)
            for msg in msgs:
                print(msg, file=sys.stderr)
            if n_flagged:
                print(f"[freshness] ABORT: {n_flagged} requested symbol(s) STALE or DEGENERATE. "
                      f"Not launching Docker exec (would produce invalid metrics, #8734). "
                      f"Re-provision the data or bypass with --no-freshness-check.",
                      file=sys.stderr)
                return 3
            print("[freshness] OK: all requested symbols fresh + non-degenerate.",
                  file=sys.stderr)

    print(f"[recipe] launching lean research --detach on port {port}...", file=sys.stderr)
    res = subprocess.run(
        [lean, "research", str(project_rel), "--detach", "--no-open",
         "--no-update", "--port", str(port)],
        cwd=str(ws), env=env, capture_output=True, text=True,
    )
    print(res.stdout, file=sys.stderr)
    if res.returncode != 0:
        print(res.stderr, file=sys.stderr)
        return res.returncode

    time.sleep(2)
    container = get_container_for_project(str(project_rel))
    if not container:
        print("[recipe] FATAL: no lean_cli container running after launch", file=sys.stderr)
        return 2
    print(f"[recipe] container={container}", file=sys.stderr)

    try:
        cmd = [
            "docker", "exec", container, "bash", "-c",
            f"cd /Lean/Launcher/bin/Debug/Notebooks/ && "
            f"jupyter nbconvert --to notebook --execute --inplace --allow-errors "
            f"--ExecutePreprocessor.timeout={timeout} {notebook_name}",
        ]
        print(f"[recipe] exec nbconvert (timeout={timeout}s per cell)...", file=sys.stderr)
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout * 4)
        sys.stderr.write(proc.stderr[-4000:] if proc.stderr else "")
        sys.stdout.write(proc.stdout)
        return proc.returncode
    finally:
        print(f"[recipe] stopping container {container}", file=sys.stderr)
        subprocess.run(["docker", "stop", container], capture_output=True, check=False)
        subprocess.run(["docker", "rm", container], capture_output=True, check=False)


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("project_dir", help="QC project folder (sibling to main.py + research.ipynb)")
    p.add_argument("--notebook", default="research.ipynb")
    p.add_argument("--port", type=int, default=8889)
    p.add_argument("--timeout", type=int, default=600, help="Per-cell timeout (seconds)")
    p.add_argument(
        "--no-freshness-check", action="store_true",
        help="Skip #8734 data-quality pre-flight (stale/degenerate requested tickers).",
    )
    p.add_argument(
        "--freshness-flat-tail-bars", type=int, default=60,
        help="Flat-tail window for the pre-flight (default 60; 0 disables flat-tail).",
    )
    args = p.parse_args()
    return run(
        Path(args.project_dir), args.notebook, args.port, args.timeout,
        freshness_check=not args.no_freshness_check,
        flat_tail_bars=args.freshness_flat_tail_bars,
    )


if __name__ == "__main__":
    sys.exit(main())
