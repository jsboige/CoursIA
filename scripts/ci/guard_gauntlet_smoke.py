#!/usr/bin/env python3
"""Smoke proof pour le pilote guard_gauntlet (issue #15067).

Ce script produit **sur disque** (scratchpad, pas sous ``docs/``) les
sorties verbatim d'un run gauntlet contre un validator **REEL du depot**
(= pas un mini-validator dedie, conformement au REPAIR po-2025 #15073
item 1), en guise de preuve NO_FAULT + HELD + ESCAPED.

Validator cible : ``scripts/check_subprocess_encoding.py`` (gate #12811,
mitigation cp1252 / UnicodeDecodeError des subprocess cp1252).

Cibles :
  - NO_FAULT : module Python SANS violation (subprocess.run sans text=True)
  - HELD     : module baseline SANS violation + fault=replace injectant une
               violation (subprocess.run avec text=True sans encoding=)
  - ESCAPED  : module baseline SANS violation + fault=truncate ; le validator
               ne lit pas la longueur (il detecte text=True/encoding=, pas la
               taille), donc exit=0 sur cible tronquee -> ESCAPED.

Usage ::

    python scripts/ci/guard_gauntlet_smoke.py
    # ecrit <scratchpad>/15067-gauntlet-smoke-<TS>.json avec les 3 sorties

Aucun fichier daté sous ``docs/`` (harness-hygiene #15067 item 5 : la
preuve ephemere va sur le scratchpad, pas dans le repo).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
RUNNER = REPO_ROOT / "scripts" / "ci" / "guard_gauntlet.py"
VALIDATOR = REPO_ROOT / "scripts" / "check_subprocess_encoding.py"


def _run(target: Path, fault: str, replace_content: str) -> dict:
    """Execute un run gauntlet, retourne le JSON stdout + rc."""
    cmd = [
        sys.executable,
        str(RUNNER),
        "--check",
        f'"{sys.executable}" "{VALIDATOR}" {{path}}',
        "--target",
        str(target),
        "--fault",
        fault,
        "--timeout-sec",
        "10",
        "--replace-content",
        replace_content,
    ]
    proc = subprocess.run(
        cmd, cwd=str(REPO_ROOT), env=os.environ.copy(),
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False, timeout=30,
    )
    payload = None
    for ln in proc.stdout.splitlines():
        if ln.strip().startswith("{"):
            payload = json.loads(ln)
            break
    return {
        "fault": fault,
        "replace_content": replace_content,
        "rc": proc.returncode,
        "status": payload["status"] if payload else None,
        "check_exit": payload["check_exit"] if payload else None,
        "original_intact": payload["diagnostics"]["original_intact"] if payload else None,
        "elapsed_sec": payload["diagnostics"]["elapsed_sec"] if payload else None,
        "stderr_human": proc.stderr.strip(),
        "stdout_json": payload,
    }


def main(argv: list[str] | None = None) -> int:
    # Trois cibles jetables : NO_FAULT (saine), HELD (mutation injecte une
    # violation), ESCAPED (truncate, le validator ignore la longueur).
    with tempfile.TemporaryDirectory(prefix="gauntlet-smoke-") as tmp:
        clean = Path(tmp) / "clean.py"
        clean.write_bytes(
            b"import subprocess\n"
            b"subprocess.run(['echo'])\n"
        )
        marker = Path(tmp) / "marker.py"
        marker.write_bytes(
            b"import subprocess\n"
            b"subprocess.run(['echo'])\n"
        )
        trunc = Path(tmp) / "trunc.py"
        trunc.write_bytes(b"# truncate target\n" + b"x" * 1024)

        results = [
            ("NO_FAULT", _run(clean, "none", "")),
            ("HELD", _run(
                marker,
                "replace",
                "import subprocess\n"
                "subprocess.run(['echo'], text=True)\n"
            )),
            ("ESCAPED", _run(trunc, "truncate", "")),
        ]

    out = {
        "issue": "#15067",
        "validator": str(VALIDATOR.relative_to(REPO_ROOT)),
        "validator_strategy": "scripts/check_subprocess_encoding.py -- refuse subprocess.run(..., text=True) sans encoding=",
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "results": [
            {"label": label, **result} for label, result in results
        ],
    }

    # Ecriture sur SCRATCHPAD (hors-repo), pas sous docs/.
    scratch_dir = Path(os.environ.get(
        "TEMP",
        tempfile.gettempdir(),
    )) / "gauntlet-smoke"
    scratch_dir.mkdir(parents=True, exist_ok=True)
    out_path = scratch_dir / f"15067-gauntlet-smoke-{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}.json"
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
