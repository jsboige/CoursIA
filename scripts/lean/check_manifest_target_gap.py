#!/usr/bin/env python3
"""Recensement des modules Lean hors de `axiom-target-modules` (classe #8782).

Le manifeste ``scripts/lean/ci_lakes.json`` porte, pour chaque lake de la
matrice ``lean-ci-matrix.yml``, la liste des modules dont le gate d'axiomes
(``lean-axiom.yml``) inspecte les axioms : ``axiom-target-modules``. Une
liste bornee est un **invariant de la couverture** ; une liste qui ne suit
pas l'evolution du lake laisse le gate vert sur une fraction qui s'amincit
sans que rien ne rougisse -- la classe « un vert qui ne mesure rien ».

Ce script **recense** l'ecart : pour chaque lake du manifeste dont la
liste est bornee, les modules ``.lean`` compiles par le lake qui ne
figurent pas dans la liste. Il est **advisory** (exit 0 inconditionnel) :
il mesure, il ne decide pas, et il ne modifie pas le manifeste.

Il lit les **globs du lakefile** (la seule source de verite sur ce que le
lake compile) et compare le module ainsi obtenu a la liste du manifeste.
Le nommage dotted est celui de
``scripts/lean/check_target_coverage.py`` (meme semantique de nommage), et
la lecture des modules existe par ``axiom_coverage.py`` (cote manifeste),
qui mesure l'autre sens -- modules **nommes** qui n'existent pas sur
disque. Les deux organismes mesurent les deux bords de la meme couverture ;
aucun des deux n'est remplace ici.

Trois etats, de sens opposes, jamais confondus dans un chiffre :

1. ``axiom-target-modules: "*"`` -- la liste est **derivee a l'execution**
   (tous les modules du lake) : pas d'ecart possible ;
2. liste explicite -- l'ecart est mesure ;
3. liste absente ou vide -- la jambe Proof integrity **ne tourne pas** pour
   ce lake : ce n'est pas un ecart de liste, c'est une absence de gate, et
   le rapport le dit comme tel.

Usage::

    # Recensement complet (tous les lakes du manifeste)
    python scripts/lean/check_manifest_target_gap.py

    # Un lake, sortie machine
    python scripts/lean/check_manifest_target_gap.py --lake gametheory --json

    # Preuve de soumission d'un module au gate (ligne de commande)
    python scripts/lean/check_manifest_target_gap.py --lake formal_logic --json

Windows / Git Bash : la lecture du manifeste et du lakefile passe par
``Path.read_text`` (aucun appel git), donc aucune conversion de chemin
MSYS n'intervient.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT / "scripts" / "lean") not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT / "scripts" / "lean"))

from check_target_coverage import parse_target_modules  # noqa: E402
from count_code_sorry import scan_file  # noqa: E402

MANIFEST_REL = "scripts/lean/ci_lakes.json"

# Les trois classes `forbidden` de pr-review-discipline.md §B : un module
# ajoute au gate ne doit en porter aucune. `Classical.choice` est
# non-constructif mais legitime : sa presence se WHITELISTE par nom
# explicite, jamais par joker -- le prescreen signale, il ne dispense pas.
_FORBIDDEN_PATTERNS = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
    "Classical.choice": re.compile(r"\bClassical\.choice\b"),
}

_LEAN_LIB_RE = re.compile(r"lean_lib\s+«?([A-Za-z0-9_']+)»?")
_GLOBS_RE = re.compile(r"globs\s*:=\s*#\[(.*?)\]", re.S)
# Le suffixe `+` fait partie de la forme `` `X.+ `` (Lake/Config/Glob.lean :
# `scoped macro:max n:name noWs ".+"`). Sans lui dans la classe de caracteres,
# le token `` `Demo.+ `` etait capture comme ``Demo.`` -- le glob se lisait
# alors `Glob.one "Demo."`, c'est-a-dire un module qui n'existe pas.
_GLOB_TOKEN_RE = re.compile(r"((?:\.submodules\s*)?)`([A-Za-z0-9_'.*+]+)")


def lake_lib_globs(lake_root: Path) -> dict[str, list[str]]:
    """Nom de `lean_lib` -> liste de globs declares, tels qu'ecrits.

    Le lakefile est la seule source de verite sur ce que le lake compile :
    un `.lean` present sur le disque mais absent des globs n'est pas un
    module du lake. On lit donc les globs, pas l'arborescence.
    """
    lakefile = lake_root / "lakefile.lean"
    if not lakefile.is_file():
        return {}
    text = lakefile.read_text(encoding="utf-8")
    # Les commentaires du lakefile citent `lean_lib` et `globs` (historique
    # EPIC #4365) : les lire comme des declarations fait exploser le
    # decoupage en blocs. On les retire avant de parser.
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    libs: dict[str, list[str]] = {}
    for lib_match in _LEAN_LIB_RE.finditer(text):
        name = lib_match.group(1)
        tail = text[lib_match.end():]
        # Le bloc de la lib s arrete a la lib suivante.
        next_lib = _LEAN_LIB_RE.search(tail)
        block = tail[: next_lib.start()] if next_lib else tail
        globs_match = _GLOBS_RE.search(block)
        globs: list[str] = []
        if globs_match:
            globs = [f"{kind.strip()} `{name}`" for kind, name in
                     _GLOB_TOKEN_RE.findall(globs_match.group(1))]
        libs.setdefault(name, [])
        for glob in globs:
            if glob not in libs[name]:
                libs[name].append(glob)
    return libs


def _modules_for_glob(lake_root: Path, glob: str) -> dict[str, Path]:
    """Modules (dotted -> fichier) couverts par un glob de lake.

    Semantique Lake, **verifiee sur la source** (`Lake/Config/Glob.lean`,
    Lean 4.32.0 et 4.34.1) :

    * `` `X `` -> `Glob.one X` : le fichier `X.lean` seul ;
    * `` `X.* `` -> `Glob.andSubmodules X` : ``X.lean`` **et** tous les
      modules sous `X/` — la docstring le dit (« including itself »), et
      `forEachModuleIn` rend `f n` avant les sous-modules ;
    * `` `X.+ `` -> `Glob.submodules X` : les modules sous `X/`, **sans**
      `X.lean` ;
    * `` .submodules `X` `` -> `Glob.submodules X` : comme `X.+`
      (notation pointee sur le constructeur `Glob.submodules`).

    L'erreur qui a fait basculer cet organe (reserve du 11/11) :
    traiter `X.*` comme `X.+` **exclut la racine du glob alors que Lake la
    compile** — les 9 racines de lib de `game_theory_lean` etaient comptees
    comme non compilees, et l'ecart affiche etait faux.
    """
    found: dict[str, Path] = {}
    name = glob.split("`")[1].strip() if "`" in glob else glob.strip()
    prefix_kind = glob.strip().startswith(".submodules")
    if name.endswith(".*"):
        prefix, include_root = name[:-2], True
    elif name.endswith(".+"):
        prefix, include_root = name[:-2], False
    elif name.endswith(".submodules"):
        prefix, include_root = name[: -len(".submodules")], False
    elif prefix_kind:
        prefix, include_root = name, False
    else:
        prefix, include_root = name, None
    if include_root is None:
        candidate = lake_root / f"{name}.lean"
        if candidate.is_file():
            found[name] = candidate
        return found
    if include_root:
        root_file = lake_root / f"{prefix}.lean"
        if root_file.is_file():
            found[prefix] = root_file
    root = lake_root / prefix
    if root.is_dir():
        for path in sorted(root.rglob("*.lean")):
            rel = path.relative_to(root)
            module = prefix + "." + ".".join(rel.with_suffix("").parts)
            found[module] = path
    return found


def compiled_modules(lake_root: Path) -> dict[str, Path]:
    """Dotted module name -> fichier, pour les modules **compiles** par le lake.

    Uniquement les modules atteignables par un glob du lakefile, avec la
    semantique **reelle** de Lake : le glob `X.*` est un
    `Glob.andSubmodules`, qui inclut la racine `X.lean` (« including
    itself ») ; seul `X.+` (ou `.submodules `X``) l'exclut. Exclure la
    racine par erreur ferait compter comme non compilees des modules que
    le lake compile reellement — un ecart faux dans les deux sens.
    """
    modules: dict[str, Path] = {}
    for _lib, globs in lake_lib_globs(lake_root).items():
        for glob in globs:
            modules.update(_modules_for_glob(lake_root, glob))
    return modules


def on_disk_not_compiled(lake_root: Path) -> list[str]:
    """Modules presents sur disque mais atteignables par aucun glob.

    Recense les fichiers `.lean` du lake que le lakefile ne compile pas
    (tombstones, fichiers hors glob) : ils ne doivent pas etre proposes au
    gate, et leur presence explique une partie des ecarts apparents. La
    racine d'une lib compilee par `X.*` n'en fait **pas** partie : Lake la
    compile (cf. `compiled_modules`).
    """
    compiled = set(compiled_modules(lake_root))
    extra: list[str] = []
    for path in sorted(lake_root.rglob("*.lean")):
        rel = path.relative_to(lake_root)
        if rel.parts[0] in {".lake", ".git", "node_modules"}:
            continue
        if rel.name.startswith("lakefile") or rel.name == "lean-toolchain":
            continue
        module = ".".join(rel.with_suffix("").parts)
        if module not in compiled:
            extra.append(module)
    return extra


def module_file_for(lake_root: Path, module: str) -> Path | None:
    rel = module.replace(".", "/")
    candidate = lake_root / f"{rel}.lean"
    return candidate if candidate.is_file() else None


def screen_forbidden(path: Path) -> dict[str, int]:
    """Prescreen source des trois classes `forbidden` (le verdict reste au job)."""
    text = path.read_text(encoding="utf-8", errors="replace")
    return {name: len(pattern.findall(text)) for name, pattern in _FORBIDDEN_PATTERNS.items()}


def sorry_count(path: Path) -> tuple[int, int]:
    """(code_sorry, naive_sorry) pour un fichier, via l'instrument canonique."""
    try:
        _declarations, naive, code = scan_file(path, _REPO_ROOT)
    except Exception:  # pragma: no cover - fichier illisible : on ne compte pas
        return (0, 0)
    return (code, naive)


def measure_lake(entry: dict) -> dict:
    lake = entry.get("lake")
    project_rel = entry.get("project-path")
    raw = (entry.get("axiom-target-modules") or "").strip()

    row: dict = {
        "lake": lake,
        "project-path": project_rel,
        "state": None,
        "targets": sorted(parse_target_modules(raw)) if raw else [],
        "compiled": 0,
        "missing": [],
    }

    if not project_rel:
        row["state"] = "no_project_path"
        return row

    lake_root = _REPO_ROOT / project_rel
    if not lake_root.is_dir():
        row["state"] = "project_path_absent"
        return row

    if not raw:
        # Pas de gate : la jambe Proof integrity ne tourne pas pour ce lake.
        row["state"] = "no_gate"
        row["compiled"] = len(compiled_modules(lake_root))
        return row

    if raw == "*":
        # Liste derivee a l'execution : tous les modules du lake sont vises.
        row["state"] = "full"
        row["compiled"] = len(compiled_modules(lake_root))
        return row

    row["state"] = "bounded"
    compiled = compiled_modules(lake_root)
    row["compiled"] = len(compiled)
    row["not_compiled"] = on_disk_not_compiled(lake_root)
    targets = parse_target_modules(raw)
    for module in sorted(set(compiled) - targets):
        path = compiled[module]
        code_sorry, naive_sorry = sorry_count(path)
        row["missing"].append({
            "module": module,
            "file": str(path.relative_to(_REPO_ROOT)).replace("\\", "/"),
            "code_sorry": code_sorry,
            "naive_sorry": naive_sorry,
            "forbidden": screen_forbidden(path),
        })
    return row


def measure(lakes: list[str] | None = None) -> dict:
    manifest = json.loads((_REPO_ROOT / MANIFEST_REL).read_text(encoding="utf-8"))
    rows = []
    for entry in manifest.get("lakes", []):
        if lakes and entry.get("lake") not in lakes:
            continue
        rows.append(measure_lake(entry))
    return {"manifest": MANIFEST_REL, "lakes": rows}


def _print_human(report: dict) -> None:
    print(f"Recensement des modules hors gate d'axiomes -- {report['manifest']}")
    for row in report["lakes"]:
        state = row["state"]
        if state == "full":
            print(f"  {row['lake']:24} liste derivee a l'execution ('*') : couverture totale")
            continue
        if state == "no_gate":
            print(f"  {row['lake']:24} PAS de gate (liste vide/absente) : "
                  f"{row['compiled']} module(s) compiles hors gate")
            continue
        if state != "bounded":
            print(f"  {row['lake']:24} etat non mesurable : {state}")
            continue
        missing = row["missing"]
        if not missing:
            print(f"  {row['lake']:24} liste bornee : aucun module compile hors liste "
                  f"({row['compiled']} compiles, {len(row['targets'])} cibles)")
            continue
        print(f"  {row['lake']:24} liste bornee : {len(missing)} module(s) compile(s) hors liste "
              f"({row['compiled']} compiles, {len(row['targets'])} cibles)")
        for item in missing:
            forb = item["forbidden"]
            flagged = ", ".join(f"{k}={v}" for k, v in forb.items() if v)
            print(f"      - {item['module']:42} sorry_code={item['code_sorry']:2} "
                  f"naive={item['naive_sorry']:3} {flagged}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Advisory: modules .lean compiles hors de axiom-target-modules (classe #8782)."
    )
    parser.add_argument("--lake", action="append", default=None,
                        help="Nom du lake dans le manifeste (repetable).")
    parser.add_argument("--json", action="store_true", help="Sortie machine.")
    args = parser.parse_args(argv)

    report = measure(args.lake)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        _print_human(report)
    return 0  # advisory : jamais de rouge sur un simple recensement


if __name__ == "__main__":
    raise SystemExit(main())
