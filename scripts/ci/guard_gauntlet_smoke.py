#!/usr/bin/env python3
"""Smoke proof pour le pilote guard_gauntlet (issue #15067).

Ce script produit **sur disque** les sorties verbatim d'un run gauntlet
contre un mini-validator fichier-par-fichier integre au repo, en guise
de preuve HELD + ESCAPED + NO_FAULT.

Usage (depuis la racine du repo) ::

    python scripts/ci/guard_gauntlet_smoke.py
    # ecrit docs/ci/15067-gauntlet-smoke-<TS>.json avec les 3 sorties

Le validator integre est ``scripts/ci/_gauntlet_demo_validator.py`` :
un mini-check qui refuse tout fichier contenant le marqueur ``@FAIL_HELD``.
C'est volontairement hors domaine (le depot n'utilise pas ce marqueur),
donc NO_FAULT doit passer et HELD doit etre declenche par l'injection.
ESCAPED est verifie en injectant un fault hors de la portee du check
(le check ne lit pas la longueur, le truncate passe inapercu).
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
VALIDATOR = REPO_ROOT / "scripts" / "ci" / "_gauntlet_demo_validator.py"


def _ensure_validator() -> None:
    """Cree le mini-validator (hors du repo code path par defaut)."""
    body = '''#!/usr/bin/env python3
"""Mini-validator pour proof gauntlet (#15067).

Lit un fichier (sys.argv[1]) et :
  - exit 0 si le contenu NE contient PAS le marqueur "@FAIL_HELD"
  - exit 1 si le contenu CONTIENT le marqueur
N'inspecte PAS la longueur du fichier (=> ESCAPED sous fault=truncate).
"""
import sys
TARGET = b"@FAIL_HELD"
try:
    data = open(sys.argv[1], "rb").read()
except Exception as exc:
    print(f"validator error: {exc}", file=sys.stderr)
    sys.exit(2)
sys.exit(1 if TARGET in data else 0)
'''
    if not VALIDATOR.exists() or VALIDATOR.read_text(encoding="utf-8") != body:
        VALIDATOR.write_text(body, encoding="utf-8")


def _run(target: Path, fault: str, content: str) -> dict:
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
        content,
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
        "replace_content": content,
        "rc": proc.returncode,
        "status": payload["status"] if payload else None,
        "check_exit": payload["check_exit"] if payload else None,
        "original_intact": payload["diagnostics"]["original_intact"] if payload else None,
        "elapsed_sec": payload["diagnostics"]["elapsed_sec"] if payload else None,
        "stderr_human": proc.stderr.strip(),
        "stdout_json": payload,
    }


def main(argv: list[str] | None = None) -> int:
    _ensure_validator()

    # Trois cibles jetables : NO_FAULT (saine), HELD (marqueur injecte),
    # ESCAPED (truncate, le validator ne lit pas la longueur).
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / "clean.txt"
        clean.write_bytes(b"# clean file\nno marker here\n")
        marker = Path(tmp) / "marker.txt"
        marker.write_bytes(b"# file with marker\n@FAIL_HELD should fail\n")
        trunc = Path(tmp) / "trunc.txt"
        trunc.write_bytes(b"# truncate target\n" + b"x" * 1024)

        results = [
            ("NO_FAULT", _run(clean, "none", "")),
            ("HELD", _run(marker, "replace", "@FAIL_HELD injected by smoke proof\n")),
            ("ESCAPED", _run(trunc, "truncate", "")),
        ]

    out = {
        "issue": "#15067",
        "validator": str(VALIDATOR.relative_to(REPO_ROOT)),
        "validator_strategy": "refuse any file containing '@FAIL_HELD'",
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "results": [
            {"label": label, **result} for label, result in results
        ],
    }

    target_dir = REPO_ROOT / "docs" / "ci"
    target_dir.mkdir(parents=True, exist_ok=True)
    out_path = target_dir / f"15067-gauntlet-smoke-{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}.json"
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Wrote {out_path.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
