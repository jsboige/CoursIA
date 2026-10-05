#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Couverture compagnons bi-OS -- organe de l'item 3 de #10643 (criteres 2-3).

L'acceptance de #10643 portait trois criteres qui "se constatent a la main,
ou ils ne se constatent pas" (corps, section Ce qui reste) :

  2a. chaque ``.ps1`` d'infrastructure P0/P1 a un ``.sh`` compagnon ;
  2b. le compagnon est documente (README croise) ;
  3.  les carnets Setup proposent les deux chemins OS dans leurs cellules.

Cet organe gele l'etat mesure au 2026-10-05 (20/20 in-scope couverts,
1 cross-ref README manquant -- corrige dans la PR qui livre cet organe,
0 carnet Setup windows-only apres calibration du faux positif C#
``RuntimeInformation.IsOSPlatform``, qui EST le geste bi-OS en .NET).

Classes de verdicts :

  - ``uncovered_companion``  .ps1 in-scope sans .sh -- ECHEC (exit 1) ;
  - ``missing_readme_xref``  paire couverte dont le .sh n'apparait dans
    aucun README a <= 2 niveaux -- AVERTISSEMENT ;
  - ``setup_windows_only``   carnet Setup (nom de fichier) dont une cellule
    code invoque Windows (``.ps1``/``powershell``/``winget``/...) sans
    qu'aucune cellule ne porte le chemin Unix -- AVERTISSEMENT.

Hors scope, par l'acceptance meme de l'EPIC : ``Vibe-Coding/``,
``docs/archive/``, ``_archive/``, et les .ps1 Windows par nature
(win-acme, IIS, sondes hotes Windows du runner Linux).

Usage :

    python scripts/ci/check_companion_coverage.py            # rapport complet
    python scripts/ci/check_companion_coverage.py --json     # sortie machine
    python scripts/ci/check_companion_coverage.py --strict   # warnings = exit 1
"""

from __future__ import annotations

import argparse
import json
import posixpath
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Appariements split-naming : le .ps1 et son .sh n'ont pas le meme stem.
# Table du corps de #10643 (mesure 2026-09-02, re-verifiee 2026-10-05).
SPLIT_NAME_PAIRS = {
    "MyIA.AI.Notebooks/GameTheory/scripts/setup_lean4_kernel.ps1":
        "setup_lean4_native.sh",
    "MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_kernel.ps1":
        "setup_wsl_lean4.sh",
    "MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup_wsl_kernel.ps1":
        "setup_wsl_smartcontracts.sh",
}

# Hors scope par prefixe (acceptance de l'EPIC : Vibe-Code et archives).
EXEMPT_PREFIXES = (
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/",
    "docs/archive/",
)

# Hors scope par segment de chemin : conventions _archive/ du depot.
EXEMPT_MARKERS = ("/_archive/",)

# .ps1 Windows par nature : win-acme (certificats Windows), IIS, et les
# sondes cotE hote Windows qui pilotent le runner Linux depuis Windows.
EXEMPT_FILES = {
    "docker-configurations/scripts/setup-win-acme-renewal.ps1",
    "docker-configurations/services/tts-multi/setup-iis-reverse-proxy.ps1",
    "scripts/genai-stack/Configure-IISAuthentication.ps1",
    "scripts/ci/docker/linux-runner/persist/hold-runner.ps1",
    "scripts/ci/docker/linux-runner/persist/host-distress-probe.ps1",
}

# Marqueurs d'invocation OS dans les cellules CODE d'un carnet Setup.
# Volontairement etroits : une mention en prose ("sous Windows...") n'est
# pas une invocation. Le geste bi-OS C# (RuntimeInformation.IsOSPlatform)
# compte comme chemin Unix -- sans lui, Infer-1-Setup serait un faux
# positif (calibre 2026-10-05 avant cablage, regle gate-fp).
WIN_CODE_MARKERS = re.compile(
    r"\.ps1\b|powershell|Set-ExecutionPolicy|winget", re.IGNORECASE)
UNIX_CODE_MARKERS = re.compile(
    r"\.sh\b|bash\b|chmod\s+\+x|apt-get|/usr/bin/"
    r"|OSPlatform\.(OSX|Linux|Create\(\"Linux\"\))|IsOSPlatform",
    re.IGNORECASE)

# Carnets concernes par le critere 3 : point d'entree etudiant.
SETUP_NAME_RE = re.compile(
    r"(setup|install|environnement|environment|installation)", re.IGNORECASE)


def in_scope(ps1_path: str) -> bool:
    """True si un .ps1 releve du perimetre compagnons de l'EPIC."""
    if ps1_path.startswith(EXEMPT_PREFIXES):
        return False
    if any(marker in ps1_path for marker in EXEMPT_MARKERS):
        return False
    return ps1_path not in EXEMPT_FILES


def companion_of(ps1_path: str, sh_set: set[str]) -> str | None:
    """Le compagnon .sh d'un .ps1, par stem identique ou split-naming.

    Renvoie le chemin POSIX du .sh s'il est suivi par git, sinon None.
    """
    directory, basename = posixpath.split(ps1_path)
    stem = basename[:-len(".ps1")]
    if ps1_path in SPLIT_NAME_PAIRS:
        candidate = posixpath.join(directory, SPLIT_NAME_PAIRS[ps1_path])
    else:
        candidate = posixpath.join(directory, stem + ".sh")
    return candidate if candidate in sh_set else None


def has_readme_xref(sh_path: str) -> bool:
    """True si le nom du .sh apparait dans un README voisin.

    Critere 2b : le compagnon est "documente (README croise)". La recherche
    couvre le repertoire du .sh, deux niveaux au-dessus (le README de la
    famille vit souvent plus haut), ET un niveau en-dessous : le README
    d'execution peut vivre dans un sous-repertoire voisin -- mesure sur
    ``run_m7_overnight_sweep.sh``, documente dans ``launchers/README.md``
    alors que le script vit dans le parent direct.
    """
    name = posixpath.basename(sh_path)
    directory = posixpath.dirname(sh_path)
    candidates: list[Path] = []
    walk = directory
    for _ in range(3):  # le repertoire lui-meme + 2 niveaux
        candidates.append(Path(REPO_ROOT) / walk)
        if walk == "":
            break
        walk = posixpath.dirname(walk)
    parent = Path(REPO_ROOT) / directory
    candidates.extend(sorted(p for p in parent.glob("*/") ))
    for readme_dir in candidates:
        for readme in sorted(readme_dir.glob("README*.md")):
            try:
                if name in readme.read_text(encoding="utf-8", errors="replace"):
                    return True
            except OSError:
                continue
    return False


def is_setup_notebook(nb_path: str) -> bool:
    """True si le NOM du carnet en fait un point d'entree Setup/Install."""
    return bool(SETUP_NAME_RE.search(posixpath.basename(nb_path)))


def bios_state(nb: dict) -> str:
    """Classe un carnet : "ok" ou "windows-only" (critere 3).

    windows-only = au moins une cellule CODE invoque Windows ET aucune
    cellule ne porte de chemin Unix (y compris le geste C# IsOSPlatform,
    qui gere les deux OS dans le meme code).
    """
    has_unix = False
    has_win_code = False
    for cell in nb.get("cells", []):
        source = "".join(cell.get("source", []))
        if cell.get("cell_type") == "code" and WIN_CODE_MARKERS.search(source):
            has_win_code = True
        if UNIX_CODE_MARKERS.search(source):
            has_unix = True
    if has_win_code and not has_unix:
        return "windows-only"
    return "ok"


def git_tracked(pattern: str) -> list[str]:
    """Chemins POSIX suivis par git pour un glob donne."""
    result = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-files", pattern],
        capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace")
    return result.stdout.split()


def analyse(ps1_files: list[str], sh_files: list[str],
            notebooks: list[str]) -> dict:
    """Le rapport complet : findings (echec) et warnings."""
    sh_set = set(sh_files)
    findings: list[dict] = []
    warnings: list[dict] = []
    for path in sorted(ps1_files):
        if not in_scope(path):
            continue
        companion = companion_of(path, sh_set)
        if companion is None:
            findings.append({
                "kind": "uncovered_companion",
                "ps1": path,
                "hint": "meme stem .sh, split-naming mappe, ou exemption nommee",
            })
        elif not has_readme_xref(companion):
            warnings.append({
                "kind": "missing_readme_xref",
                "sh": companion,
                "hint": "nommer le .sh dans un README a <= 2 niveaux",
            })
    for path in sorted(notebooks):
        if not is_setup_notebook(path):
            continue
        try:
            nb = json.loads(
                (Path(REPO_ROOT) / path).read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if bios_state(nb) == "windows-only":
            warnings.append({
                "kind": "setup_windows_only",
                "notebook": path,
                "hint": "ajouter le chemin Unix (ou le geste IsOSPlatform)",
            })
    return {
        "in_scope_ps1": sum(1 for p in ps1_files if in_scope(p)),
        "findings": findings,
        "warnings": warnings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Couverture compagnons bi-OS (#10643, criteres 2-3)")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON machine-readable")
    parser.add_argument("--strict", action="store_true",
                        help="les warnings font aussi echouer (exit 1)")
    args = parser.parse_args(argv)

    report = analyse(
        git_tracked("*.ps1"), git_tracked("*.sh"), git_tracked("*.ipynb"))

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(f"In-scope .ps1 : {report['in_scope_ps1']}")
        for warning in report["warnings"]:
            target = warning.get("sh") or warning.get("notebook")
            print(f"WARN [{warning['kind']}] {target} -- {warning['hint']}")
        for finding in report["findings"]:
            print(f"FAIL [{finding['kind']}] {finding['ps1']}"
                  f" -- {finding['hint']}")
        verdict = len(report["findings"]) == 0 and (
            not args.strict or len(report["warnings"]) == 0)
        print("OK: couverture compagnons bi-OS intacte" if verdict
              else "ECHEC: voir les lignes FAIL ci-dessus"
              + (" (--strict)" if args.strict else ""))
    if report["findings"]:
        return 1
    if args.strict and report["warnings"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
