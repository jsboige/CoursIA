#!/usr/bin/env python3
"""Telecharge le corpus MealPlanning du capstone Z3.Linq (issue #4617).

Le corpus est **trop volumineux pour etre committe** dans le depot. Ce script le
recupere a la demande depuis la branche source, dans `data/meals/` (gitignore),
pour que les notebooks MealPlanner puissent porter fidelement `Dietetique.Load`
(pipeline 2-jointures Ciqual x Recettes) sur des donnees reelles.

Tailles reelles (depuis la source, decompresse) :
  - Ciqual ANSES 2017 : 4 fichiers XML lus par Ciqual.Load = ~46 Mo (dont
    compo ~45 Mo). Le 5e fichier `sources` (~36 Mo) n'est PAS lu -> omis.
  - Recettes (OpenData cantine, JSON) : ~0,9 Mo -- donnee originale.
  - dietetique.json : ~0,36 Mo -- cache pre-calcule de Dietetique.Load.
  - RecipeML (corpus TIERS vendorise, 1986 fichiers) : ~5 Mo -- Slice B uniquement.
  Slice A (Dietetique.Load) = Ciqual + Recettes + dietetique ~= 47 Mo.

Source : MyIntelligenceAgency/Z3.LinqBinding @ EPFdevelopment
         src/Z3.LinqBinding.Demo2/App_data/Meals/   (Demo2 = projet canonique #4617)

Usage :
    python download_meal_data.py                 # tout le corpus
    python download_meal_data.py --areas Recettes dietetique
    python download_meal_data.py --force         # re-telecharge meme si present
    python download_meal_data.py --dest /chemin/data

Strategie : clone git partiel (blobless) + sparse-checkout du seul sous-arbre
Meals — on ne rapatrie que les blobs necessaires, pas l'historique complet.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_URL = "https://github.com/MyIntelligenceAgency/Z3.LinqBinding.git"
BRANCH = "EPFdevelopment"
# Le projet canonique est Demo2 (cf issue #4617 « Demo2/MealPlanning ») : c'est lui
# qui porte le cache `dietetique.json`. Demo et Demo2 partagent le meme code
# MealPlanning et le meme corpus Ciqual/Recettes.
SRC_SUBTREE = "src/Z3.LinqBinding.Demo2/App_data/Meals"

# Sous-ensembles telechargeables. Cles = noms passables a --areas.
# Valeur = LISTE de chemins relatifs sous le sous-arbre Meals ; un chemin termine
# par "/" est un dossier (copie recursive), sinon un fichier isole.
#
# PROVENANCE (important) :
#   - Ciqual + Recettes = donnees *originales* du demo MealPlanning (ANSES + OpenData
#     cantine). Ce sont les seules necessaires a `Dietetique.Load` (jointure 2-voies).
#   - RecipeML N'EST PAS une donnee du demo d'origine : c'est un corpus *tiers*
#     (RecipeML / archive type Squirrel) vendorise dans la branche EPFdevelopment
#     sous `RecipeMLArchive00001` (1986 fichiers, sous-ensemble). Il sert au scale-up
#     (Slice B), pas a la jointure Ciqual x Recettes.
#
# Ciqual : on ne recupere QUE les 4 fichiers que `Ciqual.Load` lit reellement
# (const/alim_grp/alim/compo, table ANSES 2017-11-21). Le 5e fichier du dossier,
# `sources_2017 11 21.xml` (~36 Mo), n'est jamais charge par le demo : on l'omet
# volontairement (~46 Mo au lieu de ~83 Mo). La table 2017 = 2807 aliments x 61
# constituants ; le gros fichier est `compo` (~45 Mo, valeurs aliment x constituant).
AREAS: dict[str, list[str]] = {
    "Ciqual": [
        "Ciqual/const_2017 11 21.xml",      # constituants (nutriments) -- ~12 Ko
        "Ciqual/alim_grp_2017 11 21.xml",   # groupes d'aliments       -- ~70 Ko
        "Ciqual/alim_2017 11 21.xml",       # aliments                 -- ~1,4 Mo
        "Ciqual/compo_2017 11 21.xml",      # compositions aliment x constituant -- ~45 Mo
    ],
    "Recettes": ["Recettes/"],           # denrees/plats/menus OpenData cantine (JSON) -- original
    "RecipeML": ["RecipeML/"],           # corpus TIERS vendorise (RecipeMLArchive00001, 1986 fichiers)
    "dietetique": ["dietetique.json"],   # cache pre-calcule de Dietetique.Load (~366 Ko)
}


def _run(cmd: list[str], cwd: Path | None = None) -> None:
    """Lance une commande, leve une exception explicite en cas d'echec."""
    result = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError(
            f"echec : {' '.join(cmd)}\nstdout: {result.stdout}\nstderr: {result.stderr}"
        )


def _human(num_bytes: int) -> str:
    for unit in ("o", "Ko", "Mo", "Go"):
        if num_bytes < 1024 or unit == "Go":
            return f"{num_bytes:.1f} {unit}"
        num_bytes /= 1024
    return f"{num_bytes:.1f} Go"


def _dir_size(path: Path) -> int:
    if path.is_file():
        return path.stat().st_size
    return sum(f.stat().st_size for f in path.rglob("*") if f.is_file())


def _area_targets(dest: Path, area: str) -> list[Path]:
    """Chemins cibles locaux pour tous les elements d'une zone."""
    return [dest / rel.rstrip("/") for rel in AREAS[area]]


def download(dest: Path, areas: list[str], force: bool) -> None:
    dest.mkdir(parents=True, exist_ok=True)

    # Filtre : ne re-telecharge pas une zone deja presente sauf --force.
    # Une zone est "presente" si TOUS ses elements existent localement.
    to_fetch = []
    for area in areas:
        targets = _area_targets(dest, area)
        if all(t.exists() for t in targets) and not force:
            size = sum(_dir_size(t) for t in targets)
            print(f"[skip] {area} deja present ({_human(size)}) - --force pour ecraser")
        else:
            to_fetch.append(area)
    if not to_fetch:
        print("Rien a telecharger. Corpus deja complet.")
        return

    # Patterns sparse-checkout en mode --no-cone (style .gitignore, ancres a la
    # racine du depot). Le mode cone par defaut ne sait pas inclure un FICHIER
    # isole (ex: dietetique.json directement sous Meals) ; --no-cone le permet.
    sparse_patterns = []
    for a in to_fetch:
        for rel in AREAS[a]:
            is_dir = rel.endswith("/")
            sparse_patterns.append(f"/{SRC_SUBTREE}/{rel.rstrip('/')}" + ("/" if is_dir else ""))

    with tempfile.TemporaryDirectory(prefix="z3meals_") as tmp:
        tmp_path = Path(tmp)
        print(f"Clone partiel (blobless) de {REPO_URL}@{BRANCH} ...")
        _run([
            "git", "clone", "--filter=blob:none", "--sparse",
            "--branch", BRANCH, "--depth", "1", REPO_URL, str(tmp_path / "repo"),
        ])
        repo = tmp_path / "repo"
        print(f"Sparse-checkout : {', '.join(to_fetch)}")
        _run(["git", "sparse-checkout", "set", "--no-cone", *sparse_patterns], cwd=repo)

        src_root = repo / SRC_SUBTREE
        for area in to_fetch:
            fetched = 0
            for rel in AREAS[area]:
                clean = rel.rstrip("/")
                src = src_root / clean
                target = dest / clean
                if not src.exists():
                    print(f"[warn] {area}: {clean} introuvable a la source ({src}) - ignore")
                    continue
                if target.exists():
                    shutil.rmtree(target) if target.is_dir() else target.unlink()
                target.parent.mkdir(parents=True, exist_ok=True)
                if src.is_dir():
                    shutil.copytree(src, target)
                else:
                    shutil.copy2(src, target)
                fetched += 1
            size = sum(_dir_size(t) for t in _area_targets(dest, area) if t.exists())
            print(f"[ok]  {area} -> {fetched} element(s) ({_human(size)})")

    print(f"\nCorpus disponible dans : {dest.resolve()}")
    print(f"Taille totale : {_human(_dir_size(dest))}")


def main(argv: list[str] | None = None) -> int:
    default_dest = Path(__file__).resolve().parent / "data" / "meals"
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--areas", nargs="+", choices=sorted(AREAS), default=sorted(AREAS),
        help="sous-ensembles a telecharger (defaut : tous)",
    )
    parser.add_argument("--dest", type=Path, default=default_dest, help=f"dossier cible (defaut : {default_dest})")
    parser.add_argument("--force", action="store_true", help="re-telecharge meme si deja present")
    args = parser.parse_args(argv)

    try:
        download(args.dest, args.areas, args.force)
    except RuntimeError as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
