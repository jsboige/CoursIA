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
* `os.path.exists(chemin)` **suit** le lien : il rend **False** des que la CIBLE a
  disparu. Teste avant la detection du lien, il classe une jonction **pendante**
  en « pas de checkout » — et l'affichage la rend `reel`, c'est-a-dire l'exact
  contraire de la verite. Mesure po-2025 (2026-10-08) : 14 jonctions pendantes
  lues `absent`/`reel`. Detail : `docs/lean/junctions-scan-po-2024.md` §4 « Seconde occurrence consolidée (po-2025) » (mesure intégrale préservée sur le dashboard RooSync workspace-CoursIA, 08/10).

Ensemble, les trois fabriquent un verdict « cache purge, cold-build 30 min requis »
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

    # La detection du lien precede le test d'existence : `exists()` SUIT le lien et
    # rend False des que la CIBLE a disparu. Teste en premier, il classait une
    # jonction pendante en `absent`, et l'affichage ligne ~158 la rendait `reel` --
    # l'inverse de la verite (14 jonctions po-2025, cf junctions-scan-po-2024.md §4, seconde occurrence).
    # `islink()` est False sur une junction Windows : c'est la divergence de chemin
    # qui la revele, pas l'API dediee (`is_junction()` n'existe qu'a partir de 3.12).
    try:
        real = Path(os.path.realpath(mathlib))
        result["junction"] = str(real) != str(mathlib.resolve(strict=False)) or real != mathlib
        # `exists()` leve sur la MEME jonction, et la stdlib n'y peut rien : `Path.exists()`
        # ne rattrape que `ValueError`, pas `OSError` (verifie sur 3.13, trace du
        # 2026-10-27 citant `_abc.py:450`). Les deux sondes vivent donc sous le meme
        # `try` -- garder la premiere seule laissait le scan planter une ligne plus bas.
        reachable = mathlib.exists()
    except OSError as exc:
        # Un `.lake/packages/mathlib` que Windows refuse de suivre
        # (`[WinError 1920] Le systeme ne peut pas acceder au fichier`, mesure le
        # 2026-10-27 sur `.claude/worktrees/agent-a6758d2be08682240/.../calibration_lean`).
        # Sans ce garde, UN lake illisible annulait tout le scan : l'organe se taisait
        # exactement quand le store partage etait casse, c'est-a-dire au moment ou il
        # sert. Un lake non mesurable est desormais rendu `unreadable`, jamais muet.
        result["status"] = "unreadable"
        result["oleans"] = None
        result["unreadable_error"] = f"{type(exc).__name__}: {exc}"
        return result
    if result["junction"]:
        # Cible du lien, meme morte : elle sert au diagnostic. Cle distincte de
        # `realpath`, qui designe un cache PHYSIQUE et alimente le dedoublonnage --
        # une cible disparue n'est pas un cache physique et ne doit pas y entrer.
        result["junction_target"] = str(real)

    if not reachable:
        if result["junction"]:
            # Le lien existe, sa cible a disparu : etat distinct de « aucun checkout »
            # et strictement pire que `cold` -- le chemin se presente comme un paquet
            # installe, mais rien n'est atteignable a travers.
            result["status"] = "dangling"
        else:
            result["status"] = "absent" if result["declares_mathlib"] else "no_mathlib_dep"
        result["oleans"] = 0
        return result

    result["realpath"] = str(real)

    key = str(real)
    if key not in cache:
        try:
            cache[key] = count_oleans(real)
        except OSError as exc:
            # Meme raison que ci-dessus : un arbre illisible ne doit pas annuler
            # le verdict des autres lakes, et ne doit pas passer pour un zero.
            result["status"] = "unreadable"
            result["oleans"] = None
            result["unreadable_error"] = f"{type(exc).__name__}: {exc}"
            return result
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
                        help="sortir 1 si un lake declarant mathlib est froid, "
                             "partiel, pendant ou illisible")
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
        # `oleans` vaut None pour un lake non mesurable : formater None avec `:>6`
        # leverait et ferait taire le rapport entier, c'est-a-dire reproduirait le
        # defaut que `unreadable` corrige, un cran plus loin.
        count = "  n/a " if r["oleans"] is None else f"{r['oleans']:>6}"
        print(f"  {r['status']:8}  {name}  {count} olean  {flag}")

    cold = [r for r in results if r["status"] == "cold"]
    partial = [r for r in results if r["status"] == "partial"]
    ok = [r for r in results if r["status"] == "ok"]
    absent = [r for r in results if r["status"] == "absent"]
    dangling = [r for r in results if r["status"] == "dangling"]
    unreadable = [r for r in results if r["status"] == "unreadable"]

    print()
    print(f"Lakes: {len(lakes)} | mathlib ok: {len(ok)} | froid: {len(cold)} | "
          f"partiel: {len(partial)} | non installe: {len(absent)} | "
          f"jonctions pendantes: {len(dangling)} | "
          f"illisibles: {len(unreadable)} | "
          f"caches physiques distincts: {len(by_real)}")

    if unreadable:
        print("\nLakes ILLISIBLES -- le verdict n'a pas pu etre rendu :")
        for r in unreadable:
            print(f"  {r['lake']}")
            print(f"      {r.get('unreadable_error', 'inconnu')}")
        print("  Ni `ok` ni `froid` : ces lakes sont hors mesure. Corriger l'acces")
        print("  (jonction cassee, droits, worktree disparu) puis relancer.")

    if dangling:
        print("\nJonctions PENDANTES -- le lien existe, sa cible a disparu :")
        print(f"  {len(dangling)} lake(s) portent un chemin `.lake/packages/mathlib`")
        print("  qui se presente comme un paquet installe, mais rien n'est atteignable")
        print("  a travers. Distinct de `froid` (cible presente, store vide) et de")
        print("  `non installe` (aucun lien).")

    if cold or partial or dangling:
        print("\nAvant de conclure 'cache purge', relancer un `lake build` reel :")
        print("  un comptage a 0 via `find` ou `islink` ne prouve rien sur une junction.")

    if args.json_out:
        payload = {"root": str(root), "store": str(store), "store_exists": store.is_dir(),
                   "olean_floor": MATHLIB_OLEAN_FLOOR, "results": results}
        Path(args.json_out).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"\nJSON: {args.json_out}")

    # `dangling` est compte par `--strict` alors que `absent` ne l'est pas : un lake
    # sans checkout est l'etat NORMAL d'un lac jamais construit localement (lake le
    # recuperera), tandis qu'une jonction pendante se presente comme un paquet
    # installe et n'atteint rien -- un `lake build` peut tenter de repeupler le
    # store partage a travers elle (incident fondateur #13962, docstring de
    # setup_shared_mathlib.ps1).
    # `unreadable` rougit aussi, et c'est un choix fail-CLOSED : `--strict` sert de
    # gate, et un lake qu'on n'a pas su lire n'est pas un lake sain -- le compter
    # vert reviendrait a recompenser la panne de l'instrument.
    return 1 if (args.strict and (cold or partial or dangling or unreadable)) else 0


if __name__ == "__main__":
    sys.exit(main())
