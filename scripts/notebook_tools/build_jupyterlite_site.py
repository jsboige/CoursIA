"""Construit le site JupyterLite du lot Python (pli 2.2 de l'Epic #27543).

Le lot n'est **jamais** une liste tenue a la main : il est RECALCULE depuis le
critere d'eligibilite du pli 2.1 (`pyodide_eligibility.py`, meme source de
verite). Ce script :

1. recalcule les verdicts puis le lot (`select_lot`) ;
2. stage chaque carnet du lot dans `files/` du site source (le repertoire
   de contenus), par nom de fichier -- la convention du site mesure au pli
   2.1 ; le chemin d'origine est conserve dans le manifeste ; les **modules
   locaux de la serie** importes par un carnet sont poses a cote de lui ;
3. lance `jupyter lite build` (le site est un artefact, jamais une version) ;
4. verifie que le site construit publie **exactement** le lot (ni carnet
   manquant, ni carnet etranger, ni module local absent) ;
5. ecrit `manifest.json` : pour chaque carnet du lot, son chemin dans le
   depot, sa serie et ses URLs publiques -- `lab` (ouverture et execution
   dans le navigateur) et `files` (le carnet brut, verifiable par HTTP).

Le manifeste est l'artefact de verite du garde post-deploiement
(`scripts/ci/check_jupyterlite_lot.py`) : il dit ce qui doit etre en ligne.

Usage :

    python scripts/notebook_tools/build_jupyterlite_site.py \\
        --taille 8 \\
        --source-dir .tmp/lite-site \\
        --output-dir .tmp/lite-site/_output \\
        --base-url /CoursIA
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pyodide_eligibility import (  # noqa: E402
    NotebookVerdict,
    analyse_notebook,
    git_ls_files,
    is_active_notebook,
    is_python_notebook,
    load_pyodide_lock,
    load_wheel_cache,
)
from pyodide_eligibility_report import select_lot  # noqa: E402
from pyodide_suffisance import roue_pure, suffisance_carnet  # noqa: E402

#: Racine du site JupyterLite dans le site Quarto publie.
SOUS_DOSSIER = "jupyterlite"

#: Emplacement relatif du manifeste dans le site construit.
NOM_MANIFESTE = "manifest.json"

#: Regle de selection du lot, recopiee de l'organe de critere (2.1).
REGLE_LOT = ("une serie par tour, series par ordre alphabetique ; preference aux carnets "
             "sans roue pure a installer, puis sans lecture de fichier du depot")


def racine_depot() -> Path:
    """Racine du depot (deux niveaux au-dessus de scripts/notebook_tools/)."""
    return Path(__file__).resolve().parents[2]


def lock_par_defaut(root: Path) -> Path:
    """Fichier `pyodide-lock.json` de la distribution Pyodide."""
    return root / "docs" / "reference" / "pyodide-lock.json"


def cache_par_defaut(root: Path) -> Path:
    """Cache des sondes PyPI (presence d'une roue pure)."""
    return root / "docs" / "reference" / "pyodide-wheel-cache.json"


# ---------------------------------------------------------------------------
# Recalcul du lot
# ---------------------------------------------------------------------------


def verdicts(root: Path,
             lock_path: Optional[Path] = None,
             cache_path: Optional[Path] = None,
             probe: bool = False) -> List[NotebookVerdict]:
    """Recalcule les verdicts d'eligibilite des carnets Python du depot.

    Meme pipeline que l'organe de critere (2.1) : `git ls-files`, filtre des
    carnets actifs, analyse, famille Python. Aucun acces reseau sans
    `--probe-pypi`.
    """
    pyodide_packages, _lock_info = load_pyodide_lock(lock_path)
    wheel_cache = load_wheel_cache(cache_path)
    stdlib_names = set(sys.stdlib_module_names)

    out: List[NotebookVerdict] = []
    for rel in git_ls_files(root, ["*.ipynb"]):
        if not is_active_notebook(rel):
            continue
        verdict = analyse_notebook(root, rel, pyodide_packages, wheel_cache,
                                   stdlib_names, probe)
        if not is_python_notebook(verdict):
            continue
        out.append(verdict)
    return out


def lot(root: Path,
        taille: int,
        lock_path: Optional[Path] = None,
        cache_path: Optional[Path] = None,
        probe: bool = False) -> List[NotebookVerdict]:
    """Le lot du deploiement, recalcule depuis le critere."""
    return select_lot(verdicts(root, lock_path, cache_path, probe), taille)


# ---------------------------------------------------------------------------
# Suffisance au bundle (organe natif : le critere de 2.1)
# ---------------------------------------------------------------------------


def suffisance(root: Path, lot_notebooks: Sequence[NotebookVerdict],
                pyodide_packages: Dict[str, str],
                stdlib_names: Set[str],
                wheel_cache: Optional[Dict[str, Dict[str, object]]] = None
                ) -> Tuple[List[Tuple[NotebookVerdict, List]],
                           List[Tuple[str, List[str]]]]:
    """Repartit le lot du critere en **lot publie** et refus motives.

    La regle est celle du critere (pli 2.1) : le deploiement ne la reecrit
    pas, il **l'importe** (`pyodide_suffisance`). Le bundle publie des
    fichiers et n'installe rien : un import n'est fourni que par la
    distribution Pyodide, par une installation du carnet lui-meme, ou par un
    module de la serie livre avec le carnet -- dont les propres dependances
    sont satisfaites.

    Ce que le deploiement ajoute au critere n'est pas une regle : c'est la
    **consequence** de la regle. Le critere refuse un carnet insuffisant
    (motif `suffisance`) ; le deploiement, qui doit garantir que tout carnet
    publie s'execute, refuse le meme carnet et **pose les modules locaux**
    qu'il embarque -- le critere les declare embarquables, le deploiement les
    pose.

    Rend `(publie, refus)` : `publie` porte `(verdict, modules)`, `refus`
    porte `(chemin, [raisons])`.
    """
    publie: List[Tuple[NotebookVerdict, List]] = []
    refus: List[Tuple[str, List[str]]] = []
    cache = wheel_cache or {}
    for verdict in lot_notebooks:
        rel = verdict.path.replace("\\", "/")
        suff = suffisance_carnet(
            root, rel, pyodide_packages, stdlib_names,
            est_roie_pure=lambda pack: roue_pure(pack, cache, False))
        problemes = [p.detail for p in suff.problemes]
        if problemes:
            refus.append((rel, problemes))
        else:
            publie.append((verdict, suff.modules))
    return publie, refus


# ---------------------------------------------------------------------------
# Mise en place du site source
# ---------------------------------------------------------------------------


def stage(root: Path, lot_notebooks: Sequence[NotebookVerdict],
          source_dir: Path) -> Dict[str, object]:
    """Copie dans `files/` (le repertoire de contenus) le lot et ses modules.

    Chez JupyterLite, le repertoire `files/` du site source EST le repertoire
    de contenus : la construction le recopie tel quel dans `files/` du site
    construit, et c'est de la que le carnet s'ouvre (`?path=<fichier>`).

    Les carnets sont poses **par nom de fichier** : c'est la convention du
    site mesure au pli 2.1 (`?path=<fichier>.ipynb`), celle que le pilote
    d'execution sait ouvrir. Le chemin d'origine est conserve dans le
    manifeste, qui fait la correspondance nom de fichier -> carnet du depot.

    Deux carnets homonymes de series differentes ne peuvent pas coexister
    dans le lot : la construction echoue plutot que de publier l'un des deux
    sous le nom de l'autre.

    Les **modules locaux de la serie** importes par un carnet du lot sont
    poses a plat, a cote du carnet : le carnet les cherche lui-meme dans son
    repertoire (`sys.path.insert` sur le dossier du module trouve). Sans eux,
    le carnet publie echoue a l'import -- le critere les declare
    embarquables, le deploiement doit les embarquer.

    `files/` est **remis a zero** avant la pose : un site reconstruit doit
    publier exactement le lot, pas le lot plus les restes d'une construction
    anterieure (un carnet sorti du lot resterait en ligne sans etre dans le
    manifeste -- le garde ne le verrait pas).

    Rend un dictionnaire : `carnets` (noms de fichier poses), `modules`
    (nom pose -> chemin relatif source), `modules_par_carnet`.

    `lot_notebooks` est la liste des couples `(verdict, modules)` produite
    par `suffisance()` : les modules a embarquer sont deja decides (et
    verifies) la.
    """
    source_dir.mkdir(parents=True, exist_ok=True)
    ancien = source_dir / "files"
    if ancien.is_dir():
        shutil.rmtree(ancien)
    poses: List[str] = []
    vus: Dict[str, str] = {}
    modules: Dict[str, str] = {}
    modules_par_carnet: Dict[str, List[str]] = {}
    for verdict, modules_du_carnet in lot_notebooks:
        rel = verdict.path.replace("\\", "/")
        source = root / rel
        if not source.is_file():
            raise FileNotFoundError("carnet du lot absent : %s" % rel)
        nom = Path(rel).name
        if nom in vus:
            raise ValueError("deux carnets du lot ont le meme nom (%s) : %s et %s"
                             % (nom, vus[nom], rel))
        vus[nom] = rel
        cible = source_dir / "files" / nom
        cible.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, cible)
        poses.append(nom)

        embarques: List[str] = []
        for nom_module, chemin_module, est_paquet in modules_du_carnet:
            cle = nom_module if est_paquet else nom_module + ".py"
            if cle in modules:
                if modules[cle] != chemin_module:
                    raise ValueError(
                        "deux modules locaux homonymes dans le lot (%s) : %s et %s"
                        % (cle, modules[cle], chemin_module))
                embarques.append(cle)
                continue
            source_module = root / chemin_module
            cible_module = source_dir / "files" / cle
            if est_paquet:
                shutil.copytree(source_module, cible_module)
            else:
                shutil.copy2(source_module, cible_module)
            modules[cle] = chemin_module
            embarques.append(cle)
        modules_par_carnet[rel] = embarques
    return {"carnets": poses, "modules": modules,
            "modules_par_carnet": modules_par_carnet}


def verifier_contenu(output_dir: Path, poses: Sequence[str],
                     modules: Optional[Dict[str, str]] = None) -> List[str]:
    """Verifie que le site construit publie **exactement** le lot.

    Ecarts signales : un carnet du lot absent du site construit, un carnet
    en trop (un reste d'une construction anterieure), un module local
    embarque absent. Sans cette verification, un site « correct » peut cacher
    un carnet etranger -- et le manifeste, seul verifie par le garde, ne le
    verrait pas.
    """
    anomalies: List[str] = []
    publie = output_dir / "files"
    if not publie.is_dir():
        return ["le site construit ne contient pas de repertoire files/"]
    presents = {p.relative_to(publie).as_posix() for p in publie.rglob("*.ipynb")}
    attendus = set(poses)
    for manquant in sorted(attendus - presents):
        anomalies.append("carnet du lot absent du site construit : %s" % manquant)
    for en_trop in sorted(presents - attendus):
        anomalies.append("carnet hors lot present dans le site construit : %s" % en_trop)
    for cle in sorted(modules or {}):
        if not (publie / cle).exists():
            anomalies.append("module local embarque absent du site construit : %s" % cle)
    return anomalies


def verifier_base_url(base: str) -> str:
    """Verifie que le prefixe du site est une URL d'origine, et le rend normalise.

    Mesure : sous Git Bash (MSYS), l'argument `--base-url /CoursIA` est
    converti en chemin Windows (`C:/Program Files/Git/CoursIA`). Le manifeste
    publie portait alors des URL de la forme `C:/Program Files/Git/CoursIA/...`
    -- des liens morts que le garde post-deploiement aurait rapportes comme
    casses, pour une cause qui n'a rien a voir avec le lot. On refuse donc un
    prefixe qui n'est pas un chemin absolu-racine.
    """
    base = (base or "").strip()
    if not base:
        return ""
    if "\\" in base or ":" in base:
        raise ValueError(
            "prefixe de site invalide : %r (un chemin Windows, ou une URL "
            "convertie par MSYS, ne peut pas servir de prefixe de site ; "
            "attendu : /Nom-du-depot)" % base)
    if not base.startswith("/"):
        raise ValueError(
            "prefixe de site invalide : %r (attendu : /Nom-du-depot)" % base)
    return base.rstrip("/")


def urls(base: str, nom: str) -> Dict[str, str]:
    """URLs publiques des deux formes du carnet.

    `lab` ouvre le carnet dans JupyterLite (execution dans le navigateur) ;
    `files` sert le carnet brut -- c'est cette URL que le garde post-deploiement
    sonde, et c'est elle qui prouve que le carnet est reellement publie.
    """
    base = (base or "").rstrip("/")
    return {
        "lab": "%s/%s/lab/index.html?path=%s" % (base, SOUS_DOSSIER, nom),
        "files": "%s/%s/files/%s" % (base, SOUS_DOSSIER, nom),
    }


def manifeste(lot_notebooks: Sequence[NotebookVerdict], base: str,
              modules_par_carnet: Optional[Dict[str, List[str]]] = None,
              source: str = "critere-pyodide-2.1") -> Dict[str, object]:
    """Construit le manifeste du deploiement (artefact de verite du garde)."""
    modules_par_carnet = modules_par_carnet or {}
    carnets = []
    for verdict in lot_notebooks:
        rel = verdict.path.replace("\\", "/")
        nom = Path(rel).name
        carnets.append({
            "chemin": rel,
            "fichier": nom,
            "serie": verdict.series,
            "sous_serie": verdict.subseries,
            "noyau": verdict.kernel,
            "cellules_code": verdict.code_cells,
            "paquets_pyodide": sorted({p.split("==")[0] for p in verdict.pyodide_packages}),
            "modules_locaux": sorted(modules_par_carnet.get(rel, [])),
            **urls(base, nom),
        })
    return {
        "source": source,
        "regle": REGLE_LOT,
        "taille": len(carnets),
        "carnets": carnets,
    }


def ecrire_manifeste(manifeste_data: Dict[str, object], chemin: Path) -> Path:
    """Ecrit le manifeste dans le site construit (JSON stable, UTF-8)."""
    chemin.parent.mkdir(parents=True, exist_ok=True)
    texte = json.dumps(manifeste_data, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
    with chemin.open("w", encoding="utf-8", newline="\n") as fh:
        fh.write(texte)
    return chemin


# ---------------------------------------------------------------------------
# Construction JupyterLite
# ---------------------------------------------------------------------------


def commande_build(python: Optional[str] = None) -> List[str]:
    """Commande de construction JupyterLite, resolue sans dependre du PATH.

    Preference au `jupyter-lite` installe **a cote de l'interpreteur** : le
    site doit etre construit par l'environnement qui porte le noyau Pyodide,
    pas par un `jupyter` d'un autre environnement trouve sur le PATH.
    """
    python = python or sys.executable
    dossier = Path(python).resolve().parent
    for nom in ("jupyter-lite", "jupyter-lite.exe", "jupyterlite",
                "jupyterlite.exe", "jupyter", "jupyter.exe"):
        candidat = dossier / nom
        if candidat.is_file():
            if nom.startswith("jupyter-lite") or nom.startswith("jupyterlite"):
                return [str(candidat), "build"]
            return [str(candidat), "lite", "build"]
    trouve = shutil.which("jupyter-lite") or shutil.which("jupyter")
    if trouve:
        if trouve.endswith("jupyter-lite") or trouve.endswith("jupyterlite"):
            return [trouve, "build"]
        return [trouve, "lite", "build"]
    raise RuntimeError(
        "aucune commande `jupyter lite build` trouvee (ni a cote de %s, ni dans le PATH) ; "
        "installer jupyterlite-core et jupyterlite-pyodide-kernel dans cet environnement"
        % python)


def construire(source_dir: Path, output_dir: Path,
               python: Optional[str] = None,
               apps: Optional[Sequence[str]] = None) -> List[str]:
    """Lance `jupyter lite build` et rend les lignes de journal.

    `--lite-dir` est explicite : sans lui, la construction prend le repertoire
    courant comme racine du projet, et le site construit ne contient aucun
    carnet (mesure : `contents: 0 files`, aucun `files/` dans la sortie).

    Une construction qui echoue est une construction ratee : l'appelant leve.
    """
    commande = commande_build(python)
    if apps:
        commande = commande + ["--apps", ",".join(apps)]
    commande = commande + ["--lite-dir", str(source_dir),
                           "--output-dir", str(output_dir), str(source_dir)]
    # Le repertoire de contenus du site construit est **remis a zero** avant
    # la construction : la construction y recopie `files/`, mais elle ne
    # retire pas ce qu'une construction anterieure y avait laisse (mesure :
    # un `files/MyIA.AI.Notebooks/` d'un lot anterieur a survécu au
    # changement de mise en page -- il aurait ete publie en plus du lot).
    contenu = output_dir / "files"
    if contenu.is_dir():
        shutil.rmtree(contenu)
    # `cwd` = le site source : la base de travail de JupyterLite (doit) y
    # ecrit `.jupyterlite.doit.db` -- elle ne doit pas atterrir a la racine
    # du depot.
    res = subprocess.run(commande, capture_output=True, text=True,
                         encoding="utf-8", errors="replace", check=False,
                         cwd=str(source_dir))
    journal = [ligne for ligne in (res.stdout or "").splitlines() if ligne.strip()]
    if res.returncode != 0:
        detail = (res.stderr or res.stdout or "")[-2000:]
        raise RuntimeError("jupyter lite build a echoue (rc=%d) :\n%s"
                           % (res.returncode, detail))
    return journal


# ---------------------------------------------------------------------------
# Point d'entree
# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--repo", default=None, help="racine du depot (defaut : auto)")
    parser.add_argument("--taille", type=int, default=8,
                        help="taille du lot (defaut : 8)")
    parser.add_argument("--source-dir", default=None,
                        help="site source (staging dans files/)")
    parser.add_argument("--output-dir", default=None,
                        help="site construit (sortie de `jupyter lite build`)")
    parser.add_argument("--base-url", default="",
                        help="prefixe du site publie (ex. /CoursIA)")
    parser.add_argument("--pyodide-lock", default=None)
    parser.add_argument("--wheel-cache", default=None)
    parser.add_argument("--probe-pypi", action="store_true",
                        help="sonder PyPI pour les paquets absents du lock (reseau)")
    parser.add_argument("--sans-build", action="store_true",
                        help="stager et ecrire le manifeste sans construire le site")
    parser.add_argument("--python", default=None,
                        help="interpreteur dont l'environnement porte JupyterLite")
    args = parser.parse_args(argv)

    root = Path(args.repo).resolve() if args.repo else racine_depot()
    lock_path = Path(args.pyodide_lock).resolve() if args.pyodide_lock else lock_par_defaut(root)
    cache_path = Path(args.wheel_cache).resolve() if args.wheel_cache else cache_par_defaut(root)

    source_dir = Path(args.source_dir).resolve() if args.source_dir else root / ".tmp" / "lite-site"
    output_dir = Path(args.output_dir).resolve() if args.output_dir else source_dir / "_output"

    lot_notebooks = lot(root, args.taille, lock_path, cache_path, args.probe_pypi)
    if not lot_notebooks:
        print("lot vide : aucun carnet eligible (critere 2.1) -- rien a deployer",
              file=sys.stderr)
        return 1

    # Regle de suffisance : tout carnet publie doit pouvoir s'executer dans
    # le bundle. Un carnet dont un module local exige un paquet absent de la
    # distribution Pyodide n'est pas publie ; le motif est inscrit dans le
    # manifeste (rien n'est ecarte en silence).
    pyodide_packages, _lock_info = load_pyodide_lock(lock_path)
    wheel_cache = load_wheel_cache(cache_path)
    stdlib_names = set(sys.stdlib_module_names)
    publie, refus = suffisance(root, lot_notebooks, pyodide_packages,
                               stdlib_names, wheel_cache)

    poses = stage(root, publie, source_dir)
    try:
        base_url = verifier_base_url(args.base_url)
    except ValueError as erreur:
        print("PREFIXE DE SITE : %s" % erreur, file=sys.stderr)
        return 2
    data = manifeste([v for v, _m in publie], base_url,
                      poses["modules_par_carnet"])
    data["refuses"] = [{"chemin": chemin, "motifs": motifs}
                       for chemin, motifs in refus]
    data["taille_candidat"] = len(lot_notebooks)

    if args.sans_build:
        manifeste_path = output_dir / NOM_MANIFESTE
        ecrire_manifeste(data, manifeste_path)
        print("lot : %d carnets publies sur %d candidats (stages, pas de construction)"
              % (len(publie), len(lot_notebooks)))
        for chemin, motifs in refus:
            print("  REFUS %s : %s" % (chemin, " ; ".join(motifs)))
        for c in data["carnets"]:
            print("  - %s [%s] %s" % (c["chemin"], c["serie"], c["lab"]))
        return 0

    journal = construire(source_dir, output_dir, args.python)
    anomalies = verifier_contenu(output_dir, poses["carnets"], poses["modules"])
    if anomalies:
        for anomalie in anomalies:
            print("ANOMALIE %s" % anomalie, file=sys.stderr)
        return 1
    # Le manifeste est ecrit APRÈS la construction : la construction peut
    # remettre a zero le repertoire de sortie, et un manifeste ecrit avant
    # dispararait avec.
    manifeste_path = ecrire_manifeste(data, output_dir / NOM_MANIFESTE)
    print("lot : %d carnets publies sur %d candidats -- site construit dans %s"
          % (len(publie), len(lot_notebooks), output_dir))
    for chemin, motifs in refus:
        print("  REFUS %s : %s" % (chemin, " ; ".join(motifs)))
    for c in data["carnets"]:
        print("  - %s [%s] %s" % (c["chemin"], c["serie"], c["lab"]))
        for cle in c["modules_locaux"]:
            print("      module local embarque : %s" % cle)
    print("manifeste : %s" % manifeste_path)
    if journal:
        print("--- journal de construction (5 dernieres lignes) ---")
        for ligne in journal[-5:]:
            print("  %s" % ligne)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
