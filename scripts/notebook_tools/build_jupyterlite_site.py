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
    GPU_MODULES,
    GPU_PACKAGES,
    MODULE_TO_PACKAGE,
    NETWORK_MODULES,
    NotebookVerdict,
    analyse_notebook,
    collect_imports,
    git_ls_files,
    is_active_notebook,
    is_python_notebook,
    load_pyodide_lock,
    load_wheel_cache,
    local_modules,
    notebook_sources,
    series_of,
    top_level_module,
)
from pyodide_eligibility_report import select_lot  # noqa: E402

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
# Modules locaux de la serie (a embarquer avec le carnet)
# ---------------------------------------------------------------------------

#: Dossiers ignores dans la recherche des modules locaux.
_SKIP_DIRS = {".git", ".tmp", "node_modules", "__pycache__", ".venv", "venv",
              ".pytest_cache", ".mypy_cache", "build", "dist", ".claude"}


def _dossiers_candidats(dossier: Path, series_root: Path, root: Path) -> List[Path]:
    """Dossiers ou peut se trouver un module local, du plus proche au plus lointain.

    La montee est **bornee** : elle s'arrete a la racine de la serie, et au
    pire a la racine du depot. Sans cette borne, un carnet pose directement
    sous la racine de sa serie fait monter la recherche jusqu'a la racine du
    systeme de fichiers -- et la construction y passe des heures.
    """
    candidats: List[Path] = [dossier]
    for parent in dossier.parents:
        candidats.append(parent)
        if parent == series_root or parent == root:
            break
    return candidats


def _chercher_module(dossier: Path, nom: str) -> Optional[Tuple[Path, bool]]:
    """Cherche le module `nom` dans `dossier` : (chemin, est_paquet)."""
    direct = dossier / (nom + ".py")
    if direct.is_file():
        return direct, False
    paquet = dossier / nom
    if (paquet / "__init__.py").is_file():
        return paquet, True
    trouves: List[Tuple[int, Path, bool]] = []
    for base, dirs, files in os.walk(dossier):
        dirs[:] = [d for d in dirs if d not in _SKIP_DIRS and not d.startswith(".")]
        profondeur = len(Path(base).relative_to(dossier).parts)
        for nom_fichier in files:
            if nom_fichier == nom + ".py":
                trouves.append((profondeur, Path(base) / nom_fichier, False))
        for d in dirs:
            if d == nom and (Path(base) / d / "__init__.py").is_file():
                trouves.append((profondeur, Path(base) / d, True))
    if not trouves:
        return None
    trouves.sort(key=lambda entree: entree[0])
    return trouves[0][1], trouves[0][2]


def _source_du_module(root: Path, rel_path: str, nom: str) -> Optional[Tuple[Path, bool]]:
    """Emplacement du module local `nom` pour le carnet `rel_path`.

    La recherche est limitee a la **serie** du carnet : c'est la seule
    partie du depot que le bundle publie (avec le carnet).
    """
    path = root / rel_path
    series_root = root / "MyIA.AI.Notebooks" / series_of(rel_path)
    for dossier in _dossiers_candidats(path.parent, series_root, root):
        trouve = _chercher_module(dossier, nom)
        if trouve is not None:
            return trouve
    return None


#: Installation d'un paquet **par le carnet lui-meme** : le bundle n'installe
#: rien, mais un carnet peut installer une roue pure a l'execution
#: (`micropip.install("...")`, `%pip install ...`, `!pip install ...`).
_INSTALL_RE = re.compile(
    r"micropip\.install\s*\(\s*[\"']([A-Za-z0-9_.\-]+)[\"']"
    r"|%\s*pip\s+install\s+([A-Za-z0-9_.\-]+)"
    r"|!\s*pip\s+install\s+([A-Za-z0-9_.\-]+)",
    re.IGNORECASE)


def _normalise(nom: str) -> str:
    """Nom de paquet normalise (PyPI accepte `scikit-learn` et `sklearn`)."""
    return nom.replace("-", "_").lower()


def paquets_installes_par_le_carnet(sources: Sequence[str]) -> Set[str]:
    """Paquets que le carnet installe lui-meme au moment de l'execution.

    C'est la seule voie par laquelle une roue pure absente de la
    distribution peut devenir disponible dans le bundle : le carnet
    l'installe. Sans cette trace, la dependance est **absente** -- le
    bundle ne l'installera pas a la place du carnet.
    """
    installs: Set[str] = set()
    for texte in sources:
        for trouve in _INSTALL_RE.finditer(texte):
            nom = trouve.group(1) or trouve.group(2) or trouve.group(3)
            if nom:
                installs.add(nom.replace("-", "_").lower())
    return installs


def imports_non_satisfaits(source: Path, pyodide_packages: Dict[str, str],
                            stdlib_names: Set[str], resolver, vus: Set[str],
                            chaine: Tuple[str, ...] = (),
                            installs: Optional[Set[str]] = None) -> List[str]:
    """Imports d'un module local que la distribution Pyodide ne fournit pas.

    Le bundle publie des **fichiers**, il n'installe rien : une dependance
    d'un module local embarque doit donc faire partie de la **distribution**
    (verrou Pyodide), et non etre une roue pure que le carnet installerait
    lui-meme.

    Mesure : le carnet `Causalite-06` importe `dowhy_iv_organs`, qui importe
    `dowhy` ; `dowhy` n'est pas dans la distribution -> le carnet echoue en
    navigation (`ModuleNotFoundError: No module named 'dowhy'`), meme une
    fois le module embarque.

    `installs` porte les paquets que le carnet installe lui-meme : ils sont
    disponibles a l'execution, donc ils satisfont la dependance.
    """
    problemes: List[str] = []
    cle = str(source)
    if cle in vus:
        return problemes
    vus.add(cle)
    installs = installs or set()
    fichier = source / "__init__.py" if source.is_dir() else source
    if not fichier.is_file():
        return problemes
    texte = fichier.read_text(encoding="utf-8", errors="replace")
    for module in sorted(collect_imports([texte])):
        top = top_level_module(module)
        if top in stdlib_names:
            continue
        if top in GPU_MODULES or top in GPU_PACKAGES:
            problemes.append("%s : GPU" % (" -> ".join(chaine + (module,))))
            continue
        if top in NETWORK_MODULES:
            problemes.append("%s : reseau" % (" -> ".join(chaine + (module,))))
            continue
        package = MODULE_TO_PACKAGE.get(top, top)
        if package in pyodide_packages:
            continue
        if _normalise(package) in installs or _normalise(top) in installs:
            continue
        local = resolver(top)
        if local is None:
            problemes.append("%s : absent de la distribution"
                              % " -> ".join(chaine + (module,)))
            continue
        problemes.extend(imports_non_satisfaits(
            local[0], pyodide_packages, stdlib_names, resolver, vus,
            chaine + (module,), installs))
    return problemes


def modules_et_problemes(root: Path, rel_path: str,
                          pyodide_packages: Dict[str, str],
                          stdlib_names: Set[str]) -> Tuple[List[Tuple[str, str, bool]],
                                                           List[str]]:
    """Modules locaux que le carnet importe, et dependances non satisfaites.

    Le critere d'eligibilite (pli 2.1) considere qu'un module Python de la
    serie du carnet est **embarquable** dans le bundle JupyterLite : ce n'est
    pas un motif de refus. Le deploiement doit donc l'embarquer pour de
    vrai -- sinon le carnet publie echoue a l'import. Mesure : le carnet
    `Causalite-06` du lot echoue en navigation
    (`ModuleNotFoundError: dowhy_iv_organs`), parce que seul le carnet etait
    pose dans le site.

    La meme regle s'applique aux **imports du carnet lui-meme** : le bundle
    publie des fichiers et n'installe rien, donc un import qui n'est ni dans
    la distribution, ni installe par le carnet, n'est pas satisfait. Le
    critere, lui, accepte une roue pure presente dans son cache : le
    deploiement est plus strict, et c'est lui qui publie. L'alignement des
    deux est porte par l'Epic (le critere doit dire ce que le bundle livre).

    Rende le couple `([(nom, chemin relatif, est_paquet)], [raisons])`.
    """
    path = root / rel_path
    with path.open(encoding="utf-8") as fh:
        nb = json.load(fh)
    sources = notebook_sources(nb)
    imports = collect_imports(sources)
    series_root = root / "MyIA.AI.Notebooks" / series_of(rel_path)
    local, elsewhere = local_modules(root, path, series_root)
    installs = paquets_installes_par_le_carnet(sources)

    modules: List[Tuple[str, str, bool]] = []
    problemes: List[str] = []
    vus: Set[str] = set()

    def resolver(nom: str):
        return _source_du_module(root, rel_path, nom)

    for module in sorted(set(imports)):
        top = top_level_module(module)
        if top in stdlib_names:
            continue
        if top in GPU_MODULES or top in GPU_PACKAGES:
            problemes.append("%s : GPU" % module)
            continue
        if top in NETWORK_MODULES:
            problemes.append("%s : reseau" % module)
            continue
        package = MODULE_TO_PACKAGE.get(top, top)
        if package in pyodide_packages:
            continue
        if _normalise(package) in installs or _normalise(top) in installs:
            # Le carnet installe lui-meme la roue : elle sera disponible.
            continue
        if top in local or module in local:
            nom = top if top in local else module
            emplacement = resolver(nom)
            if emplacement is None:
                problemes.append("%s : module local introuvable" % nom)
                continue
            source, est_paquet = emplacement
            modules.append((nom, source.relative_to(root).as_posix(), est_paquet))
            problemes.extend(imports_non_satisfaits(
                source, pyodide_packages, stdlib_names, resolver, vus, (nom,),
                installs))
            continue
        if top in elsewhere:
            # Le bundle ne livre que la serie du carnet : un module d'une
            # autre serie ne sera pas dans le site -> l'import echoue.
            problemes.append("%s : module hors serie non livre par le bundle"
                              % module)
            continue
        problemes.append("%s : absent de la distribution" % module)
    return modules, problemes


def suffisance(root: Path, lot_notebooks: Sequence[NotebookVerdict],
                pyodide_packages: Dict[str, str],
                stdlib_names: Set[str]) -> Tuple[List[Tuple[NotebookVerdict, List]],
                                                 List[Tuple[str, List[str]]]]:
    """Repartit le lot du critere en **lot publie** et refus motives.

    Le critere d'eligibilite (pli 2.1) dit quels carnets sont candidats : un
    carnet qui importe un module de sa serie est candidat. Le deploiement, lui,
    doit garantir que tout carnet **publie** s'execute : il verifie donc que
    chaque import du carnet -- et chaque dependance des modules locaux
    qu'il embarque -- est bien fourni par la distribution Pyodide (ou
    installe par le carnet lui-meme). Un carnet qui echoue a cette
    verification n'est pas publie -- et le motif est inscrit dans le
    manifeste.

    Rend `(publie, refus)` : `publie` porte `(verdict, modules)`, `refus`
    porte `(chemin, [raisons])`.
    """
    publie: List[Tuple[NotebookVerdict, List]] = []
    refus: List[Tuple[str, List[str]]] = []
    for verdict in lot_notebooks:
        rel = verdict.path.replace("\\", "/")
        modules, problemes = modules_et_problemes(root, rel, pyodide_packages,
                                                   stdlib_names)
        if problemes:
            refus.append((rel, problemes))
        else:
            publie.append((verdict, modules))
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
    stdlib_names = set(sys.stdlib_module_names)
    publie, refus = suffisance(root, lot_notebooks, pyodide_packages, stdlib_names)

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
