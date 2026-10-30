#!/usr/bin/env python3
"""Mesure comparative d'un carnet .NET sous plusieurs runtimes isolés.

Pourquoi cet outil
------------------
L'EPIC « .NET 11 — mesure progressive des gains runtime async » (#18695)
compare des versions de runtime, mais jusqu'ici chaque campagne vivait en
copie scratch : aucune mesure n'etait rejouable par une autre lane, et le
temps d'execution d'un carnet n'etait proof par la version de runtime qui
l'avait produit (le runtime affiche par le carnet est une constante de la
machine, pas une donnee de la mesure).

Cet outil rend la comparaison rejouable :

* il **prouve** la version de runtime reellement utilisee, en injectant une
  cellule de sonde qui ecrit ``FrameworkDescription`` dans un fichier, puis
  en le relisant ;
* il **mesure** le carnet sous chaque variante, avec le meme executeur
  canonique (``notebook_tools.py execute --cell-by-cell``), donc la meme
  metric ;
* il **entrelace** les repetitions (A, B, A, B, ...) pour que la derive
  machine ne soit pas attribuuee a une variante ;
* il rend un tableau markdown et un JSON reproductible.

Usage
-----
::

    python scripts/notebook_tools/measure_runtime_variants.py NOTEBOOK \
        --arm "net10=.net-csharp" \
        --arm "net11=.net-csharp-r11" \
        --reps 3 --json resultats.json

Une variante peut declarer un runtime isole, et dans ce cas l'outil genere
un kernelspec jetable (JUPYTER_PATH temporaire) qui vise ce ``DOTNET_ROOT`` :

    --arm "net11=auto@C:/Users/<user>/.dotnet-r11"

Le kernelspec genere lance l'apphost ``dotnet-interactive`` avec
``DOTNET_ROLL_FORWARD=Major`` : un runtime seul (sans SDK) suffit alors que
le muxer ``dotnet`` exigerait un SDK pour lancer un outil global.

Aucune sortie de cellule du carnet cible n'est modifiee : l'execution passe
par ``--cell-by-cell``, qui n'ecrit pas les sorties dans le carnet.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

NOTEBOOK_TOOLS = Path(__file__).resolve().parent / "notebook_tools.py"

ANSI_RE = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
CELLS_RE = re.compile(r"Executed\s+(\d+)\s+cells:\s+(\d+)\s+OK,\s+(\d+)\s+errors")
TOTAL_RE = re.compile(r"Total time:\s*([\d.]+)\s*s")

PROBE_CELL = [
    'var fw = System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription;',
    'var ver = Environment.Version.ToString();',
    'System.IO.File.WriteAllText("{probe_path}", "RUNTIME=" + fw + "\\nRUNTIMEVER=" + ver + "\\n");',
]


class ArmError(RuntimeError):
    """Erreur de configuration d'une variante."""


def find_dotnet_interactive() -> str:
    """Chemin de l'apphost ``dotnet-interactive`` installe en global tool."""
    found = shutil.which("dotnet-interactive")
    if found:
        return found
    home = Path.home()
    for candidate in (home / ".dotnet" / "tools" / "dotnet-interactive.exe",
                      home / ".dotnet" / "tools" / "dotnet-interactive"):
        if candidate.exists():
            return str(candidate)
    raise ArmError(
        "dotnet-interactive introuvable : installez l'outil global "
        "(`dotnet tool install -g Microsoft.dotnet-interactive`) ou passez "
        "--apphost <chemin>."
    )


def write_kernelspec(spec_dir: Path, apphost: str, dotnet_root: str, roll_forward: str) -> Path:
    """Ecrit un kernelspec jetable vise sur un ``DOTNET_ROOT`` isole."""
    spec_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "argv": [apphost, "jupyter", "--default-kernel", "csharp",
                 "{connection_file}", "--http-port-range", "2048-3000"],
        "display_name": ".NET (C#) mesure isolee",
        "language": "C#",
        "env": {"DOTNET_ROOT": dotnet_root, "DOTNET_ROLL_FORWARD": roll_forward},
    }
    (spec_dir / "kernel.json").write_text(
        json.dumps(payload, indent=1), encoding="utf-8"
    )
    return spec_dir


def build_probe_notebook(path: Path, probe_path: Path) -> None:
    """Ecrit un carnet-sonde dont la cellule publie la version de runtime."""
    probe_posix = str(probe_path).replace("\\", "/")
    nb = {
        "cells": [{
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [line.replace("{probe_path}", probe_posix) for line in PROBE_CELL],
        }],
        "metadata": {
            "kernelspec": {"display_name": ".NET (C#)", "language": "C#", "name": ".net-csharp"},
            "language_info": {"name": "C#"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, indent=1), encoding="utf-8")


def run_notebook_tools(notebook: Path, kernel: str, timeout: int, env: dict) -> dict:
    """Execute un carnet via l'organe canonique et en extrait la metrique."""
    cmd = [sys.executable, str(NOTEBOOK_TOOLS), "execute", str(notebook),
           "--cell-by-cell", "--kernel", kernel, "--timeout", str(timeout)]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                          errors="replace", env=env)
    out = ANSI_RE.sub("", proc.stdout or "")
    cells = CELLS_RE.search(out)
    total = TOTAL_RE.search(out)
    return {
        "returncode": proc.returncode,
        "cells_total": int(cells.group(1)) if cells else None,
        "cells_ok": int(cells.group(2)) if cells else None,
        "cells_errors": int(cells.group(3)) if cells else None,
        "total_seconds": float(total.group(1)) if total else None,
        "stdout_tail": "\n".join(out.strip().splitlines()[-12:]),
    }


def probe_runtime(kernel: str, workdir: Path, timeout: int, env: dict) -> str:
    """Execute la sonde et rend la version de runtime observee."""
    probe_nb = workdir / "sonde_runtime.ipynb"
    probe_out = workdir / "runtime_seen.txt"
    if probe_out.exists():
        probe_out.unlink()
    build_probe_notebook(probe_nb, probe_out)
    run_notebook_tools(probe_nb, kernel, timeout, env)
    if not probe_out.exists():
        raise ArmError("la sonde runtime n'a rien ecrit : la variante n'a pas demarre")
    seen = {}
    for line in probe_out.read_text(encoding="utf-8").splitlines():
        if "=" in line:
            key, _, value = line.partition("=")
            seen[key.strip()] = value.strip()
    return seen.get("RUNTIME", "inconnue")


def redact_paths(text: str) -> str:
    """Remplace les prefixes machine (home, repertoire courant) par des formes stables.

    Un artefact commite ne doit pas porter le chemin du poste de mesure :
    la preuve utile est le nom du carnet et la version de runtime, pas
    l'arborescence du siege.
    """
    if not text:
        return text
    home = str(Path.home())
    cwd = str(Path.cwd())
    out = text.replace(home + os.sep, "~/").replace(home, "~")
    if cwd and cwd not in (os.sep, home):
        out = out.replace(cwd + os.sep, "./").replace(cwd, ".")
    return out


def parse_arm(spec: str, apphost: str, tmp_root: Path) -> dict:
    """Decoupe ``label=kernel`` ou ``label=auto@DOTNET_ROOT``."""
    if "=" not in spec:
        raise ArmError(f"variante mal formee : {spec!r} (attendu label=kernel)")
    label, _, value = spec.partition("=")
    label = label.strip()
    value = value.strip()
    arm = {"label": label, "kernel": value, "generated": False, "dotnet_root": None}
    if not value.startswith("."):
        print(f"[AVERTISSEMENT] le nom de kernelspec {value!r} ne commence pas par un point : "
              "cette forme ajoute ~5 s de demarrage par execution et fausse la mesure. "
              "Utilisez un nom de la forme `.net-csharp-<variante>`.", file=sys.stderr)
    if value.startswith("auto@"):
        dotnet_root = value[len("auto@"):]
        if not Path(dotnet_root).is_dir():
            raise ArmError(f"DOTNET_ROOT inexistant : {dotnet_root}")
        # Nom pointé obligatoire : un kernelspec dont le nom ne commence pas
        # par un point ajoute ~5 s de demarrage a CHAQUE execution (mesure :
        # contenu et dossier identiques, 17,5 s pour `mesure-net11` contre
        # 12,4 s pour `.net-csharp-r11e`, 2 repetitions entrelacees, meme
        # runtime .NET 11.0.0-rc.3 prouve dans les deux cas). Le nom entre
        # dans le fichier de connexion que jupyter_client ecrit, et le chemin
        # de resolution de dotnet-interactive differe selon sa forme : la
        # convention `.net-csharp*` est celle des specs du depot.
        kernel_dir = tmp_root / "kernels" / f".net-csharp-{label}"
        write_kernelspec(kernel_dir, apphost, dotnet_root, "Major")
        arm["kernel"] = kernel_dir.name
        arm["generated"] = True
        arm["dotnet_root"] = dotnet_root
    return arm


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Mesure comparative d'un carnet .NET sous plusieurs runtimes isoles."
    )
    parser.add_argument("notebook", help="chemin du carnet .NET a mesurer")
    parser.add_argument("--arm", action="append", required=True,
                        metavar="LABEL=KERNEL",
                        help="variante a mesurer ; repeatable. "
                             "LABEL=auto@<DOTNET_ROOT> genere un kernelspec jetable")
    parser.add_argument("--reps", type=int, default=3, help="repetitions par variante (defaut 3)")
    parser.add_argument("--timeout", type=int, default=300, help="timeout par execution (s)")
    parser.add_argument("--apphost", default=None, help="chemin de dotnet-interactive")
    parser.add_argument("--json", default=None, help="ecrire le resultat en JSON")
    args = parser.parse_args(argv)

    notebook = Path(args.notebook).resolve()
    if not notebook.is_file():
        print(f"carnet introuvable : {notebook}", file=sys.stderr)
        return 2
    if args.reps < 1:
        print("--reps doit etre >= 1", file=sys.stderr)
        return 2

    try:
        apphost = args.apphost or find_dotnet_interactive()
    except ArmError as exc:
        print(str(exc), file=sys.stderr)
        return 2

    tmp_root = Path(tempfile.mkdtemp(prefix="mesure-runtime-"))
    workdir = tmp_root / "travail"
    workdir.mkdir(parents=True, exist_ok=True)
    env = {**os.environ}
    try:
        arms = [parse_arm(spec, apphost, tmp_root) for spec in args.arm]
        if any(arm["generated"] for arm in arms):
            env["JUPYTER_PATH"] = str(tmp_root)

        results = []
        for arm in arms:
            arm["runtime"] = probe_runtime(arm["kernel"], workdir, args.timeout, env)
            arm["reps"] = []
            print(f"[{arm['label']}] runtime detecte : {arm['runtime']}")

        # Entrelacement : A, B, A, B... pour ne pas attribuer la derive
        # machine a une variante privilegiee par l'ordre.
        for rep in range(args.reps):
            for arm in arms:
                run = run_notebook_tools(notebook, arm["kernel"], args.timeout, env)
                run["rep"] = rep + 1
                arm["reps"].append(run)
                print(f"[{arm['label']}] rep {rep + 1}/{args.reps} : "
                      f"{run['cells_ok']}/{run['cells_total']} cellules OK, "
                      f"{run['cells_errors']} erreurs, {run['total_seconds']} s")

        for arm in arms:
            times = [r["total_seconds"] for r in arm["reps"] if r["total_seconds"] is not None]
            arm["times_seconds"] = times
            arm["median_seconds"] = statistics.median(times) if times else None
            arm["min_seconds"] = min(times) if times else None
            arm["max_seconds"] = max(times) if times else None
            arm["all_cells_ok"] = all(r["cells_errors"] == 0 for r in arm["reps"])

        payload = {
            "notebook": redact_paths(str(notebook)),
            "reps": args.reps,
            "apphost": redact_paths(apphost),
            "arms": results or arms,
        }
        for arm in payload["arms"]:
            arm["stdout_tail"] = redact_paths(arm.get("stdout_tail", ""))
            if arm.get("dotnet_root"):
                arm["dotnet_root"] = redact_paths(arm["dotnet_root"])
            for run in arm.get("reps", []):
                run["stdout_tail"] = redact_paths(run.get("stdout_tail", ""))
        if args.json:
            Path(args.json).write_text(json.dumps(payload, indent=2, ensure_ascii=False),
                                        encoding="utf-8")

        print()
        print("| Variante | Runtime detecte | Cellules OK | Erreurs | Temps (s) | Mediane (s) |")
        print("|---|---|---|---|---|---|")
        for arm in arms:
            times = ", ".join(f"{t:.1f}" for t in arm["times_seconds"]) or "—"
            med = f"{arm['median_seconds']:.1f}" if arm["median_seconds"] is not None else "—"
            ok = sum(r["cells_ok"] or 0 for r in arm["reps"])
            total = sum(r["cells_total"] or 0 for r in arm["reps"])
            err = sum(r["cells_errors"] or 0 for r in arm["reps"])
            print(f"| {arm['label']} | {arm['runtime']} | {ok}/{total} | {err} | "
                  f"{times} | {med} |")
        return 0
    except ArmError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    finally:
        shutil.rmtree(tmp_root, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
