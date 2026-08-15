"""Render a notebook to standalone HTML via nbconvert, without executing it.

Piste 2 de #10968 : un notebook dont l'output massif fait boucler pandoc sous
Quarto (`echo: true`) est rendu en quelques secondes par nbconvert, qui lit les
outputs committés (jamais de kernel). Ce script rend reproductible cette mesure
et valide le résultat : code visible, images embarquées, wallclock borné.

Usage:
    python render_oversized_nbconvert.py <notebook.ipynb>... [--outdir DIR]
    python render_oversized_nbconvert.py --check <notebook.ipynb>...  # exit 1 si échec

Read-only : le notebook n'est jamais modifié (C.2 / Stop & Repair).
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path


def _html_stats(path: Path) -> dict[str, int]:
    """Compte les marqueurs de structure du HTML nbconvert (lab template)."""
    data = path.read_text(encoding="utf-8", errors="replace")
    return {
        "doctype": int(data.lstrip().startswith("<!DOCTYPE html>")),
        "input_areas": data.count("jp-InputArea"),
        "output_areas": data.count("jp-OutputArea"),
        "images": data.count("data:image"),
        "bytes": len(data.encode("utf-8")),
    }


def render_one(nb: Path, outdir: Path, timeout_s: int = 600) -> dict[str, object]:
    """Rend un notebook via nbconvert (outputs committés, pas d'exécution)."""
    outdir.mkdir(parents=True, exist_ok=True)
    stem = nb.stem
    html = outdir / f"{stem}.html"
    start = time.perf_counter()
    cmd = [
        sys.executable, "-m", "jupyter", "nbconvert",
        "--to", "html", "--output", str(outdir / stem),
        str(nb),
    ]
    try:
        subprocess.run(cmd, check=True, timeout=timeout_s,
                       capture_output=True, text=True)
        wallclock_s = round(time.perf_counter() - start, 2)
    except subprocess.TimeoutExpired:
        return {"notebook": str(nb), "status": "FAIL", "reason": f"timeout>{timeout_s}s",
                "wallclock_s": timeout_s}
    except subprocess.CalledProcessError as exc:
        return {"notebook": str(nb), "status": "FAIL",
                "reason": exc.stderr.strip().splitlines()[-1][:200]
                if exc.stderr else f"exit {exc.returncode}"}
    stats = _html_stats(html)
    ok = (stats["doctype"] == 1 and stats["input_areas"] > 0 and stats["bytes"] > 0)
    return {
        "notebook": str(nb),
        "status": "RENDER_OK" if ok else "FAIL",
        "wallclock_s": wallclock_s,
        "html_bytes": stats["bytes"],
        "code_areas": stats["input_areas"],
        "output_areas": stats["output_areas"],
        "images": stats["images"],
        "html_path": str(html),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notebooks", nargs="+", type=Path,
                        help="notebooks à rendre (outputs committés)")
    parser.add_argument("--outdir", type=Path, default=None,
                        help="répertoire de sortie (défaut: côté du notebook)")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 si un notebook échoue (CI)")
    args = parser.parse_args()

    outdir = args.outdir or Path(".")
    outdir.mkdir(parents=True, exist_ok=True)
    results = [render_one(nb, outdir) for nb in args.notebooks]
    for r in results:
        if r["status"] == "RENDER_OK":
            print(f"RENDER_OK {r['wallclock_s']:>6.1f}s "
                  f"{r['html_bytes']}o {r['code_areas']} code-areas "
                  f"{r['images']} img — {r['notebook']}")
        else:
            print(f"FAIL      {r['reason']} — {r['notebook']}")

    failures = [r for r in results if r["status"] != "RENDER_OK"]
    return 1 if (args.check and failures) else 0


if __name__ == "__main__":
    raise SystemExit(main())
