#!/usr/bin/env python3
"""check_encoding_corruption.py — détecteur de double encodage UTF-8/cp1252 dans les carnets.

Point 3 de #23021. Un carnet commité peut avoir été relu en cp1252 (ou latin-1)
puis ré-encodé en UTF-8 : les caractères accentués et les tirets deviennent des
artefacts visibles (`é` → `Ã©`, `—` → `â€”`, nbsp → `Â `). La corruption est une
corruption de fichier entier : elle touche la source ET les sorties, et elle est
invisible aux organes de perte de contenu (le volume reste identique, seule la
valeur des caractères change).

Signatures détectées (bigrammes de la famille UTF-8→cp1252/latin-1) :

- `Ã` + U+0080..U+00BF  : la famille `é è à è …` (2e octet UTF-8 0x80-0xBF)
- `Â` + U+0080..U+00BF  : nbsp, `°`, `µ`, `·`, `¢`
- `Å€`                  : famille `Š/Ž` (C5 80)
- `â€`                  : famille `— – ' ' " " … „ »` (E2 80)

Ces bigrammes ne sont jamais légitimes en prose française : `â` seul l'est
(château), `â€` non ; `Ã` seul n'apparaît pas en français, `Ã©` non plus.

Usage :

  # Pleine vérification d'un carnet ou d'un répertoire (hook pré-commit, manuel) :
  python scripts/notebook_tools/check_encoding_corruption.py <chemin> [...]

  # Garde CI bloquante : artefacts sur les LIGNES AJOUTÉES des carnets changés
  # par rapport à une référence (formule du fast-lane `{base_ref}`) :
  python scripts/notebook_tools/check_encoding_corruption.py --base origin/main

  # Auto-test interne (fil de fumée du garde) :
  python scripts/notebook_tools/check_encoding_corruption.py --self-test

  # Sortie machine :
  ... --json

Sorties : 0 = propre, 1 = artefacts détectés, 2 = erreur d'usage/lecture.

Exemptions : le littéral `Ã©` est légitime dans la prose qui documente la classe
(docs/, .md) — le détecteur est scopingué aux `.ipynb` et ne la voit pas. Si un
carnet devait porter légitimement un bigramme (cas pathologique), il s'ajoute à
EXEMPT ci-dessous avec sa raison : c'est une décision reviewée, pas un silencing.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Bigrammes de la famille de corruption (cf. docstring).
MOJIBAKE = re.compile(
    r"Ã[\u0080-¿]"  # Ã + 2e octet (é, è, à, …)
    r"|Â[\u0080-¿]"  # Â + 2e octet (nbsp, °, µ, ·, ¢)
    r"|Å€"  # C5 80 (Š, Ž)
    r"|â€"  # E2 80 (—, –, quotes, guillemets, …)
)

# Carnets portant légitimement un bigramme : chemin relatif -> raison.
# Vide au départ : la mesure de référence (2026-10-28, #23021) ne recense que
# les deux carnets corrompus (RL-05, TV-03), qui ne sont pas des exemptions.
EXEMPT: dict[str, str] = {}


def count_in_text(text: str) -> int:
    """Nombre d'artefacts dans une chaîne."""
    return len(MOJIBAKE.findall(text))


def count_in_notebook(path: Path) -> int:
    """Nombre d'artefacts dans un carnet (source, sorties, metadata)."""
    raw = path.read_text(encoding="utf-8")
    return count_in_text(raw)


def iter_notebooks(paths: list[Path]) -> list[Path]:
    """Aplatit fichiers/répertoires vers la liste des .ipynb (triée, dedup)."""
    out: set[Path] = set()
    for p in paths:
        if p.is_dir():
            out.update(p.rglob("*.ipynb"))
        elif p.suffix == ".ipynb":
            out.add(p)
        else:
            # Un fichier non-.ipynb nommé explicitement est une erreur d'usage.
            print(f"ERREUR: {p} n'est pas un .ipynb", file=sys.stderr)
            sys.exit(2)
    return sorted(out)


def _is_exempt(rel: str) -> bool:
    return rel in EXEMPT or rel.replace("\\", "/") in EXEMPT


def check_paths(paths: list[Path]) -> dict[str, int]:
    """Pleine vérification : {chemin relatif: compte} pour les carnets sales."""
    dirty: dict[str, int] = {}
    for nb in iter_notebooks(paths):
        rel = str(nb).replace("\\", "/")
        if _is_exempt(rel):
            continue
        n = count_in_notebook(nb)
        if n:
            dirty[rel] = n
    return dirty


def changed_notebooks(base: str) -> list[str]:
    """Carnets modifiés entre <base>...HEAD (chemins repo-relatifs)."""
    out = subprocess.run(
        ["git", "diff", "--name-only", f"{base}...HEAD", "--", "*.ipynb"],
        capture_output=True,
    )
    if out.returncode != 0:
        err = out.stderr.decode("utf-8", errors="replace").strip()
        print(f"ERREUR: git diff {base}...HEAD a échoué : {err}", file=sys.stderr)
        sys.exit(2)
    # Décodage explicite UTF-8 : text=True decoderait en cp1252 sous Windows et
    # fabriquerait la corruption même que ce détecteur doit mesurer.
    return [l for l in out.stdout.decode("utf-8", errors="replace").splitlines() if l.strip()]


def added_lines_artifacts(repo_root: Path, nb_rel: str, base: str) -> int:
    """Artéfacts sur les LIGNES AJOUTÉES du carnet par rapport à <base>.

    Un carnet ajouté en entier compte toutes ses lignes ; un carnet absent de la
    base (nouveau) est lu en plein.
    """
    nb = repo_root / nb_rel
    if not nb.exists():
        return 0
    out = subprocess.run(
        ["git", "diff", f"{base}...HEAD", "--", nb_rel],
        capture_output=True,
    )
    if out.returncode != 0:
        err = out.stderr.decode("utf-8", errors="replace").strip()
        print(f"ERREUR: git diff {base}...HEAD -- {nb_rel} : {err}", file=sys.stderr)
        sys.exit(2)
    # UTF-8 explicite (cf. changed_notebooks) : jamais text=True ici.
    lines = out.stdout.decode("utf-8", errors="replace").splitlines()
    added = [l[1:] for l in lines if l.startswith("+") and not l.startswith("+++")]
    if not added:
        # Pas de ligne ajoutée lisible (binaire ?) → repli sur la lecture pleine.
        return count_in_notebook(nb)
    # Un .ipynb est du JSON : ajouter un élément de liste ré-écrit la ponctuation
    # de la ligne précédente (virgule de liste), qui apparaît alors en `+` SANS
    # que son contenu ait changé. On ne compte que les lignes ajoutées dont le
    # contenu normalisé n'existe pas déjà côté `-` : la garde cible la matière
    # NOUVELLE, pas le churn de ponctuation.
    def _norm(l: str) -> str:
        return l.strip().rstrip(",").strip()

    removed = {_norm(l[1:]) for l in lines if l.startswith("-") and not l.startswith("---")}
    new_added = [l for l in added if _norm(l) not in removed]
    return count_in_text("\n".join(new_added))


def check_base(base: str) -> dict[str, int]:
    """Garde CI : artefacts sur les lignes ajoutées des carnets changés."""
    repo_root = Path.cwd()
    dirty: dict[str, int] = {}
    for nb_rel in changed_notebooks(base):
        if _is_exempt(nb_rel):
            continue
        n = added_lines_artifacts(repo_root, nb_rel, base)
        if n:
            dirty[nb_rel] = n
    return dirty


def self_test() -> int:
    """Fil de fumée : le pattern attrape la famille et ignore le français sain."""
    positive = "mÃ©taheuristique â€” plateau Â "
    negative = "métaheuristique — plateau château naïve µ ° ¢   "
    ok = count_in_text(positive) == 3 and count_in_text(negative) == 0
    print("SELF-TEST " + ("OK" if ok else "ECHEC"))
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="*", help="fichiers .ipynb ou répertoires")
    ap.add_argument("--base", help="référence git : vérifier les lignes ajoutées des carnets changés")
    ap.add_argument("--self-test", action="store_true", help="auto-test du pattern")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.base:
        dirty = check_base(args.base)
    elif args.paths:
        dirty = check_paths([Path(p) for p in args.paths])
    else:
        ap.error("aucun chemin (ou --base / --self-test)")
        return 2

    if args.json:
        print(json.dumps({"dirty": dirty, "count": len(dirty)}, ensure_ascii=False, indent=1))
    else:
        for rel, n in dirty.items():
            print(f"{rel}: {n} artefact(s) de double encodage")
        if dirty:
            print(f"ENCODING CORRUPTION: {len(dirty)} carnet(s), "
                  f"{sum(dirty.values())} artefact(s)")
        else:
            print("OK: aucun artefact de double encodage")
    return 1 if dirty else 0


if __name__ == "__main__":
    sys.exit(main())
