#!/usr/bin/env python3
"""Telecharge le corpus MealPlanning du capstone Z3.Linq (issue #4617).

Le corpus est **trop volumineux pour etre committe** dans le depot. Ce script le
recupere a la demande dans `data/meals/` (gitignore), pour porter fidelement
`Dietetique.Load` (pipeline 2-jointures Ciqual x Recettes + matching lexical)
sur des donnees reelles.

Deux sources, deux mecanismes :

  - **Ciqual = source OFFICIELLE ANSES, table 2025** (recherche.data.gouv.fr,
    Dataverse, DOI 10.57745/RDMHWY, licence etalab 2.0). Telechargement HTTP
    direct des 4 fichiers XML lus par `Ciqual.Load` (const/alim_grp/alim/compo,
    dates 2025-11-03). Le 5e fichier `sources` (~0,9 Mo) n'est PAS lu -> omis.
    Le schema 2025 est identique au 2017 (meme structure <TABLE><CONST>...,
    memes champs) : un simple renommage de fichiers suffit cote loader.
    Table 2025 = 3484 aliments x 74 constituants ; le gros fichier est
    `compo_2025_11_03.xml` (~69 Mo, valeurs aliment x constituant).

  - **Recettes + RecipeML = depuis le fork** MyIntelligenceAgency/Z3.LinqBinding
    @ EPFdevelopment, projet Demo2 (clone git partiel blobless + sparse-checkout).
      * Recettes : denrees/plats/menus OpenData cantine (JSON) -- donnee du demo.
      * RecipeML : corpus TIERS "Squirrel's RecipeML Archive" (993 recettes XML,
        10 batches, ~2,3 Mo) -- vendorise dans le fork. PAS une donnee du demo
        d'origine ; reserve au scale-up (Slice B). Mirrors publics plus petits :
        JimSaiya/eXist-recipes (403), mark-dunn/exist-db-recipes (27).
        Pour la convergence-a-tres-grande-echelle (#4617 Part 4), fallback geant :
        HuggingFace `mbien/recipe_nlg` (RecipeNLG, ~2,2 M recettes) -- a brancher
        si les 993 du Squirrel archive sont insuffisantes.

Le cache `dietetique.json` n'est PAS telecharge : c'est un artefact runtime que
le notebook regenere via `Dietetique.Load` sur les donnees 2025 (l'ancien cache
du fork etait calcule sur la table 2017 -> obsolete).

Usage :
    python download_meal_data.py                 # Ciqual 2025 + Recettes + RecipeML
    python download_meal_data.py --areas Ciqual  # table ANSES 2025 seule
    python download_meal_data.py --areas Recettes RecipeML
    python download_meal_data.py --force         # re-telecharge meme si present
    python download_meal_data.py --dest /chemin/data
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

# --- Source officielle ANSES : table Ciqual 2025 (recherche.data.gouv.fr) -------
# Acces fichier-par-fichier via l'API Dataverse "access/datafile" + DOI du fichier.
DATAVERSE_ACCESS = (
    "https://entrepot.recherche.data.gouv.fr/api/access/datafile/"
    ":persistentId?persistentId="
)
CIQUAL_DATASET_DOI = "doi:10.57745/RDMHWY"  # dataset complet (reference)
# Seuls les 4 fichiers que `Ciqual.Load` lit reellement (sources_2025 omis).
CIQUAL_2025_FILES: dict[str, str] = {
    "const_2025_11_03.xml":    "doi:10.57745/FWSPCX",   # constituants  -- ~18 Ko
    "alim_grp_2025_11_03.xml": "doi:10.57745/FMNIUZ",   # groupes       -- ~80 Ko
    "alim_2025_11_03.xml":     "doi:10.57745/OH8KXC",   # aliments      -- ~1,58 Mo
    "compo_2025_11_03.xml":    "doi:10.57745/O73GDX",   # compositions  -- ~69,2 Mo
    # sources_2025_11_03.xml (doi:10.57745/3MVEOJ, ~0,9 Mo) : non lu -> omis.
}

# --- Source fork : Recettes + RecipeML (git sparse-checkout) --------------------
REPO_URL = "https://github.com/MyIntelligenceAgency/Z3.LinqBinding.git"
BRANCH = "EPFdevelopment"
# Demo2 = projet canonique (#4617 « Demo2/MealPlanning »).
SRC_SUBTREE = "src/Z3.LinqBinding.Demo2/App_data/Meals"
# Zones recuperees depuis le fork. Valeur = liste de chemins relatifs sous Meals
# (un chemin termine par "/" = dossier copie recursivement).
FORK_AREAS: dict[str, list[str]] = {
    "Recettes": ["Recettes/"],   # denrees/plats/menus OpenData cantine (JSON) -- original
    "RecipeML": ["RecipeML/"],   # Squirrel's RecipeML Archive (993 recettes, tiers) -- Slice B
}

ALL_AREAS = ["Ciqual", *FORK_AREAS]


def _run(cmd: list[str], cwd: Path | None = None) -> None:
    """Lance une commande, leve une exception explicite en cas d'echec."""
    result = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError(
            f"echec : {' '.join(cmd)}\nstdout: {result.stdout}\nstderr: {result.stderr}"
        )


def _human(num_bytes: float) -> str:
    for unit in ("o", "Ko", "Mo", "Go"):
        if num_bytes < 1024 or unit == "Go":
            return f"{num_bytes:.1f} {unit}"
        num_bytes /= 1024
    return f"{num_bytes:.1f} Go"


def _dir_size(path: Path) -> int:
    if path.is_file():
        return path.stat().st_size
    if not path.exists():
        return 0
    return sum(f.stat().st_size for f in path.rglob("*") if f.is_file())


def _ciqual_present(dest: Path) -> bool:
    ciqual = dest / "Ciqual"
    return all((ciqual / name).exists() for name in CIQUAL_2025_FILES)


def download_ciqual(dest: Path) -> None:
    """Telecharge la table Ciqual 2025 officielle (4 fichiers) via Dataverse HTTP."""
    ciqual_dir = dest / "Ciqual"
    ciqual_dir.mkdir(parents=True, exist_ok=True)
    print(f"Ciqual 2025 (ANSES / recherche.data.gouv.fr, {CIQUAL_DATASET_DOI}) :")
    for name, doi in CIQUAL_2025_FILES.items():
        url = DATAVERSE_ACCESS + doi
        target = ciqual_dir / name
        try:
            with urllib.request.urlopen(url, timeout=120) as resp:  # noqa: S310 (URL fixe ANSES)
                data = resp.read()
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError(f"telechargement Ciqual '{name}' ({url}) : {exc}") from exc
        target.write_bytes(data)
        print(f"  [ok] {name} ({_human(len(data))})")


def download_fork(dest: Path, areas: list[str]) -> None:
    """Recupere les zones fork (Recettes/RecipeML) via clone partiel + sparse."""
    sparse_patterns = []
    for a in areas:
        for rel in FORK_AREAS[a]:
            is_dir = rel.endswith("/")
            sparse_patterns.append(f"/{SRC_SUBTREE}/{rel.rstrip('/')}" + ("/" if is_dir else ""))

    with tempfile.TemporaryDirectory(prefix="z3meals_") as tmp:
        repo = Path(tmp) / "repo"
        print(f"Clone partiel (blobless) de {REPO_URL}@{BRANCH} ...")
        _run([
            "git", "clone", "--filter=blob:none", "--sparse",
            "--branch", BRANCH, "--depth", "1", REPO_URL, str(repo),
        ])
        print(f"Sparse-checkout : {', '.join(areas)}")
        _run(["git", "sparse-checkout", "set", "--no-cone", *sparse_patterns], cwd=repo)

        src_root = repo / SRC_SUBTREE
        for area in areas:
            count = 0
            for rel in FORK_AREAS[area]:
                clean = rel.rstrip("/")
                src = src_root / clean
                target = dest / clean
                if not src.exists():
                    print(f"[warn] {area}: {clean} introuvable a la source ({src}) - ignore")
                    continue
                if target.exists():
                    shutil.rmtree(target) if target.is_dir() else target.unlink()
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copytree(src, target) if src.is_dir() else shutil.copy2(src, target)
                count += 1
            print(f"  [ok] {area} -> {count} element(s) ({_human(_dir_size(dest / area))})")


def download(dest: Path, areas: list[str], force: bool) -> None:
    dest.mkdir(parents=True, exist_ok=True)

    do_ciqual = "Ciqual" in areas
    fork_to_fetch = [a for a in areas if a in FORK_AREAS]

    # Filtre presence (sauf --force).
    if do_ciqual and _ciqual_present(dest) and not force:
        print(f"[skip] Ciqual deja present ({_human(_dir_size(dest / 'Ciqual'))}) - --force pour ecraser")
        do_ciqual = False
    kept = []
    for a in fork_to_fetch:
        target = dest / a
        if target.exists() and not force:
            print(f"[skip] {a} deja present ({_human(_dir_size(target))}) - --force pour ecraser")
        else:
            kept.append(a)
    fork_to_fetch = kept

    if not do_ciqual and not fork_to_fetch:
        print("Rien a telecharger. Corpus deja complet.")
        return

    if do_ciqual:
        download_ciqual(dest)
    if fork_to_fetch:
        download_fork(dest, fork_to_fetch)

    print(f"\nCorpus disponible dans : {dest.resolve()}")
    print(f"Taille totale : {_human(_dir_size(dest))}")


def main(argv: list[str] | None = None) -> int:
    default_dest = Path(__file__).resolve().parent / "data" / "meals"
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--areas", nargs="+", choices=ALL_AREAS, default=ALL_AREAS,
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
