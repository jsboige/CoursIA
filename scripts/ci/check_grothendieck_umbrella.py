#!/usr/bin/env python3
"""Grothendieck umbrella FR-only drift guard (#16154).

Organe always-on : compare les imports de `Grothendieck.lean` au disque sous
`Grothendieck/` selon l'invariant FR-only retenu (#16154, option 1) :
  - chaque module FR sur disque est importe (manquant = derive) ;
  - aucun sibling `_en` importe (l'umbrella n'indexe que le FR -- les EN
    restent construits par les `globs := #[`Grothendieck.*`]` du lakefile) ;
  - aucun import fantome (import sans fichier derriere).

Dual-mode : `python scripts/ci/check_grothendieck_umbrella.py --check` (rc 1
sur derive, rapport sur stdout -- l'appel du step always-on) ; sans flag,
rapport humain. Purement local : aucun appel gh, aucun token.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
_LAKE = _REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "grothendieck_lean"
UMBRELLA = _LAKE / "Grothendieck.lean"
MODULES_DIR = _LAKE / "Grothendieck"

_IMPORT_RE = re.compile(r"^import\s+(Grothendieck\.\S+)\s*$", re.MULTILINE)


def _disk_modules(mods_dir: Path) -> set[str]:
    """Modules FR sur disque -> noms `Grothendieck.…` (recursif, `_en` EXCLU)."""
    out: set[str] = set()
    for f in mods_dir.rglob("*.lean"):
        rel = f.relative_to(mods_dir).with_suffix("").as_posix().replace("/", ".")
        if rel.endswith("_en"):
            continue
        out.add("Grothendieck." + rel)
    return out


def _disk_en_modules(mods_dir: Path) -> set[str]:
    """Siblings `_en` sur disque -> noms `Grothendieck.…`."""
    out: set[str] = set()
    for f in mods_dir.rglob("*.lean"):
        rel = f.relative_to(mods_dir).with_suffix("").as_posix().replace("/", ".")
        if rel.endswith("_en"):
            out.add("Grothendieck." + rel)
    return out


def _umbrella_imports(umbrella: Path) -> set[str]:
    return set(_IMPORT_RE.findall(umbrella.read_text(encoding="utf-8")))


def drift(mods_dir: Path, umbrella: Path) -> dict[str, list[str]]:
    imports = _umbrella_imports(umbrella)
    fr = _disk_modules(mods_dir)
    en = _disk_en_modules(mods_dir)
    return {
        "missing_fr": sorted(fr - imports),
        "en_imported": sorted(imports & en),
        "phantom": sorted(imports - fr - en),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on drift")
    args = ap.parse_args(argv)

    d = drift(MODULES_DIR, UMBRELLA)
    n_fr = len(_disk_modules(MODULES_DIR))
    n_en = len(_disk_en_modules(MODULES_DIR))
    n_imp = len(_umbrella_imports(UMBRELLA))

    if not any(d.values()):
        print(
            f"OK -- umbrella FR-only tenu : {n_imp} imports = {n_fr} modules FR, "
            f"0 _en ; {n_en} siblings EN hors index (globs lakefile)."
        )
        return 0

    print(f"DRIFT -- {n_fr} modules FR, {n_en} siblings EN, {n_imp} imports :")
    for axis, items in d.items():
        if items:
            print(f"  {axis}: {', '.join(items)}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
