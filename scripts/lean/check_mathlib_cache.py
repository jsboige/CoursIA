#!/usr/bin/env python3
"""Verifie qu'un cache Mathlib est reellement atteignable pour chaque lake Lean.

Pourquoi cet outil existe
-------------------------
Sur Windows, `.lake/packages/mathlib` est presque toujours une **junction** vers un
store partage. Deux outils courants mentent silencieusement dessus :

* `find <lake>/.lake/packages/mathlib -name '*.olean'` (Git Bash) renvoie **0** :
  `find` ne traverse pas les junctions.
* `os.path.islink(chemin)` renvoie **False** : rien ne signale que le repertoire
  est un lien, donc le « 0 » passe pour une mesure de repertoire vide.

Ensemble, les deux fabriquent un verdict « cache purge, cold-build 30 min requis »
a partir d'un cache parfaitement sain. Cette confusion a immobilise une lane Lean
pendant 5 cycles (DM `msg-20260729T055956-n3f4ap`).

Ce script mesure via `os.path.realpath()` + `os.walk()` — les deux seules primitives
qui traversent une junction — et **affiche la resolution** pour que l'operateur voie
le lien plutot que de le deviner.

Usage
-----
    py scripts/lean/check_mathlib_cache.py
    py scripts/lean/check_mathlib_cache.py --json-out cache.json --strict

Advisory par defaut : sort 0 meme avec des lakes froids. `--strict` sort 1.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

# Un Mathlib compile depasse tres largement ce seuil (~8000 oleans en v4.31).
# Un cache partiellement construit ou corrompu tombe en dessous.
MATHLIB_OLEAN_FLOOR = 1000

SKIP_DIRS = {".git", "node_modules", ".lake", ".mathlib-cache", "packages"}


def find_lakes(root: Path, include_worktrees: bool = False) -> list[Path]:
    """Repertoires contenant un lakefile, hors worktrees par defaut."""
    lakes: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        if not include_worktrees and ".claude" in Path(dirpath).parts:
            dirnames[:] = []
            continue
        if "lakefile.lean" in filenames or "lakefile.toml" in filenames:
            lakes.append(Path(dirpath))
    return sorted(lakes)


def count_oleans(real: Path) -> int:
    """Compte les .olean sous `real`. `os.walk` traverse la junction, `find` non."""
    total = 0
    for _, _, filenames in os.walk(real):
        total += sum(1 for f in filenames if f.endswith(".olean"))
    return total


def declares_mathlib(lake: Path) -> bool:
    for name in ("lakefile.lean", "lakefile.toml"):
        path = lake / name
        if path.is_file():
            try:
                if "mathlib" in path.read_text(encoding="utf-8", errors="replace").lower():
                    return True
            except OSError:
                continue
    return False


def analyse_lake(lake: Path, cache: dict[str, int]) -> dict:
    """Verdict pour un lake. `cache` dedoublonne les comptes par realpath.

    Le dedoublonnage n'est pas qu'une optimisation : N lakes junctionnes vers le
    meme store partagent un seul cache physique, et le dire evite de lire le
    rapport comme si chacun avait le sien.
    """
    mathlib = lake / ".lake" / "packages" / "mathlib"
    result: dict = {"lake": str(lake), "declares_mathlib": declares_mathlib(lake)}

    if not mathlib.exists():
        result["status"] = "absent" if result["declares_mathlib"] else "no_mathlib_dep"
        result["oleans"] = 0
        return result

    real = Path(os.path.realpath(mathlib))
    # `islink()` est False sur une junction Windows : c'est la divergence de
    # chemin qui la revele, pas l'API dediee.
    result["junction"] = str(real) != str(mathlib.resolve(strict=False)) or real != mathlib
    result["realpath"] = str(real)

    key = str(real)
    if key not in cache:
        cache[key] = count_oleans(real)
    result["oleans"] = cache[key]
    result["shared_with"] = None  # rempli par l'appelant

    if result["oleans"] >= MATHLIB_OLEAN_FLOOR:
        result["status"] = "ok"
    elif result["oleans"] == 0:
        result["status"] = "cold"
    else:
        result["status"] = "partial"
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo-path", default=".", help="racine du depot")
    parser.add_argument("--json-out", help="ecrire le rapport JSON")
    parser.add_argument("--include-worktrees", action="store_true",
                        help="inclure .claude/worktrees (exclus par defaut)")
    parser.add_argument("--strict", action="store_true",
                        help="sortir 1 si un lake declarant mathlib est froid")
    args = parser.parse_args(argv)

    root = Path(args.repo_path).resolve()
    if not (root / ".git").exists():
        print(f"ERREUR: {root} n'est pas une racine de depot git", file=sys.stderr)
        return 2

    store = root / ".mathlib-cache"
    if store.is_dir():
        toolchains = sorted(p.name for p in store.iterdir() if p.is_dir())
        print(f"Store partage : {store}")
        for tc in toolchains:
            print(f"  toolchain {tc}")
    else:
        print(f"Store partage : ABSENT ({store})")
    print()

    lakes = find_lakes(root, args.include_worktrees)
    cache: dict[str, int] = {}
    results = [analyse_lake(lake, cache) for lake in lakes]

    # Un realpath partage par plusieurs lakes = un seul cache physique.
    by_real: dict[str, list[str]] = {}
    for r in results:
        if r.get("realpath"):
            by_real.setdefault(r["realpath"], []).append(r["lake"])
    for r in results:
        if r.get("realpath"):
            r["shared_with"] = len(by_real[r["realpath"]])

    width = max((len(Path(r["lake"]).name) for r in results), default=20)
    for r in results:
        name = Path(r["lake"]).name.ljust(width)
        if r["status"] == "no_mathlib_dep":
            continue
        flag = "junction" if r.get("junction") else "reel    "
        print(f"  {r['status']:8}  {name}  {r['oleans']:>6} olean  {flag}")

    cold = [r for r in results if r["status"] == "cold"]
    partial = [r for r in results if r["status"] == "partial"]
    ok = [r for r in results if r["status"] == "ok"]
    absent = [r for r in results if r["status"] == "absent"]

    print()
    print(f"Lakes: {len(lakes)} | mathlib ok: {len(ok)} | froid: {len(cold)} | "
          f"partiel: {len(partial)} | non installe: {len(absent)} | "
          f"caches physiques distincts: {len(by_real)}")

    if cold or partial:
        print("\nAvant de conclure 'cache purge', relancer un `lake build` reel :")
        print("  un comptage a 0 via `find` ou `islink` ne prouve rien sur une junction.")

    if args.json_out:
        payload = {"root": str(root), "store": str(store), "store_exists": store.is_dir(),
                   "olean_floor": MATHLIB_OLEAN_FLOOR, "results": results}
        Path(args.json_out).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"\nJSON: {args.json_out}")

    return 1 if (args.strict and (cold or partial)) else 0


if __name__ == "__main__":
    sys.exit(main())
