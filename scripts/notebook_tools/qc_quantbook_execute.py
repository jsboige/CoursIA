"""Execute a QC research quantbook headlessly via lean-cli + Docker + nbconvert.

Recipe validated 2026-05-10 (incident H.7 / forensic T17, ai-01).

Workflow:
  1. `lean login` once with QC_API_USER_ID + QC_API_TOKEN (Lean CLI stores creds in ~/.lean)
  2. `lean research <project> --detach --no-open --port <port>` from a Lean workspace
     (workspace must contain lean.json + data/ folder, e.g. ESGF-2026/lean-workspace/)
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
      MyIA.AI.Notebooks/QuantConnect/ESGF-2026/lean-workspace/Multi-Layer-EMA-Researcher \
      --notebook research.ipynb [--port 8889] [--timeout 600]
"""
from __future__ import annotations

import argparse
import os
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


def run(project_dir: Path, notebook_name: str, port: int, timeout: int) -> int:
    lean = find_lean()
    ws = workspace_root(project_dir)
    project_rel = project_dir.resolve().relative_to(ws)
    print(f"[recipe] workspace={ws}", file=sys.stderr)
    print(f"[recipe] project={project_rel}  notebook={notebook_name}", file=sys.stderr)

    env = os.environ.copy()
    env["PYTHONUTF8"] = "1"

    print(f"[recipe] launching lean research --detach on port {port}...", file=sys.stderr)
    res = subprocess.run(
        [lean, "research", str(project_rel), "--detach", "--no-open",
         "--port", str(port)],
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
    args = p.parse_args()
    return run(Path(args.project_dir), args.notebook, args.port, args.timeout)


if __name__ == "__main__":
    sys.exit(main())
