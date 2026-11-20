#!/usr/bin/env python3
"""Manifeste des dependances par famille de noyau (Pli 1.1, issue #27544).

Le Pli 1.1 consiste a savoir, avant de construire une image d'apprentissage
(Pli 1.2), ce que cette image doit contenir et ce qui en reste exclu. Ce script
produit cette table depuis le depot seul.

Sources, toutes locales
-----------------------
* ``git ls-files`` : la liste des fichiers suivis (carnets et fichiers de
  dependances). Rien n'est lu hors de l'arbre de travail.
* ``COURSE_CATALOG.generated.json`` : les drapeaux ``requires_gpu``,
  ``requires_api``, ``requires_cloud`` et ``requires_wsl`` de chaque carnet,
  produits par l'organe de catalogue du depot. Le manifeste ne reimplemente pas
  cette detection : il la consomme.
* Le ``kernelspec`` reel de chaque carnet, lu dans le fichier (voir
  :func:`read_kernelspec`), pour la famille de noyau.

Aucune requete reseau n'est emise : le script est utilisable hors ligne et rend
un resultat reproductible (pas d'horodatage ni de SHA dans la sortie, afin que
``--check`` reste stable d'un commit a l'autre).

Regles de verdict (premiere regle satisfaite, dans cet ordre)
------------------------------------------------------------
1. ``exclu`` / ``gpu`` : au moins la moitie des carnets du groupe declarent
   ``requires_gpu`` (:data:`GPU_MAJORITY_RATIO`). Un carnet GPU isole dans une
   serie CPU ne definit pas la serie ; au-dela de la moitie, le GPU est le mode
   d'execution dominant du groupe. Le compte exact reste visible dans la colonne
   ``GPU``.
2. ``exclu`` / ``licence`` : le groupe declare un paquet de
   :data:`RESTRICTED_PACKAGES` (solveur commercial a licence nominative).
3. ``exclu`` / ``taille`` : l'empreinte estimee des **fichiers propres** du
   groupe depasse ``--budget-mb`` (2000 Mo par defaut). Le socle d'une serie est
   paye une fois pour toute la serie : le compter dans chaque sous-groupe
   comparerait des depenses qui ne s'additionnent pas. Les empreintes sont des
   ordres de grandeur d'installation, pas des mesures ; la table est dans
   :data:`PACKAGE_FOOTPRINT_MB` et un paquet inconnu compte pour
   :data:`DEFAULT_PACKAGE_FOOTPRINT_MB`.
4. ``service optionnel`` : au moins un carnet declare ``requires_cloud``. Le
   groupe depend d'un service reseau (ComfyUI, vLLM, QuantConnect Cloud) qui vit
   hors image et que le Pli 1.5 rend optionnel ; ses paquets restent necessaires,
   car le carnet tourne localement et appelle le service.
5. ``inclus`` : sinon.

La colonne ``WSL`` dit combien de carnets du groupe exigent WSL (noyaux Lean) :
ils ne tournent pas dans l'image, sans que cela change le verdict sur les
paquets du groupe.

Portee d'un fichier de dependances
----------------------------------
* un fichier nomme ``requirements.txt`` / ``environment.yml`` a la racine d'une
  serie est le **socle** de la serie : il s'applique a tous ses sous-groupes ;
* un fichier qualifie (``requirements-audio.txt``) s'attache au sous-groupe dont
  le dossier porte ce qualificatif (``GenAI/Audio``), a defaut au dossier qui le
  contient ;
* tout autre fichier s'attache au groupe de son propre dossier.

Usage
-----
::

    python scripts/notebook_tools/kernel_dependency_manifest.py --format both
    python scripts/notebook_tools/kernel_dependency_manifest.py --write
    python scripts/notebook_tools/kernel_dependency_manifest.py --check

``--write`` ecrit ``docker-configurations/notebook-runner/kernel-manifest.md``
et ``.json`` ; ``--check`` compare l'existant a une regeneration et sort en 1 si
les fichiers ont derive.
"""

from __future__ import annotations

import argparse
import json
import posixpath
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

# ---------------------------------------------------------------------------
# Constantes de politique (mesurees ou documentees, jamais devinees)
# ---------------------------------------------------------------------------

DEFAULT_REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_ROOT = "MyIA.AI.Notebooks"
CATALOG_NAME = "COURSE_CATALOG.generated.json"

OUTPUT_DIR = Path("docker-configurations/notebook-runner")
OUTPUT_MD = OUTPUT_DIR / "kernel-manifest.md"
OUTPUT_JSON = OUTPUT_DIR / "kernel-manifest.json"

DEPENDENCY_FILE_RE = re.compile(r"^(requirements.*\.txt|environment.*\.ya?ml)$", re.IGNORECASE)
REQUIREMENT_LINE_RE = re.compile(
    r"^(?P<name>[A-Za-z0-9][A-Za-z0-9._-]*)"
    r"\s*(?:\[(?P<extras>[^\]]*)\])?"
    r"\s*(?P<operator>===|==|~=|>=|<=|>|<|!=)?"
    r"\s*(?P<version>[^\s,;#]*)"
)
ENVIRONMENT_ITEM_RE = re.compile(r"^\s*-\s*(?P<item>\S.*?)\s*$")

#: Familles de noyau reconnues. L'ordre est celui du rendu.
KERNEL_FAMILIES = ("python", "csharp", "lean", "rust", "other")

#: Regles de classification d'un nom de kernelspec, appliquees dans l'ordre.
#: Les noyaux Lean sont testes avant les noyaux Python : ``python3-lean`` est un
#: noyau Python (carnets Python qui embarquent du Lean), ``lean4-wsl`` un noyau
#: Lean.
KERNEL_FAMILY_RULES: tuple[tuple[str, str], ...] = (
    ("lean4", "lean"),
    ("leandojo", "lean"),
    ("csharp", "csharp"),
    ("rust", "rust"),
    ("python", "python"),
    ("py3", "python"),
    ("pyphi", "python"),
    ("conda", "python"),
    ("torch", "python"),
)

#: Residue mesure sur l'arbre (2026-11-20) : noms de noyaux qu'aucune regle
#: ci-dessus ne classe, tous servis par un interprete Python.
KERNEL_FAMILY_EXPLICIT: dict[str, str] = {
    "basicpitch-t4": "python",
    "coursia-drift": "python",
    "coursia-ml-training": "python",
    "coursia-py313": "python",
    "coursia-py313-argu": "python",
    "dia-tts": "python",
    "difflogic-sl12": "python",
    "gametheory-wsl": "python",
    "global-3.13": "python",
    "gsplat310": "python",
    "ict-py313": "python",
    "mert2-gpu": "python",
    "pipecat-kokoro": "python",
    "py310-gpu": "python",
    "py311-po2028": "python",
    "python3-coursia2": "python",
    "python3-sc16-concrete-wsl": "python",
    "rvc-wsl": "python",
    "sheetsage2-gpu": "python",
    "smartcontracts": "python",
}

#: Paquets a licence non redistribuable dans une image publique.
RESTRICTED_PACKAGES: dict[str, str] = {
    "cplex": "solveur commercial IBM CPLEX, licence nominative",
    "docplex": "client du solveur commercial IBM CPLEX, licence nominative",
    "gurobipy": "solveur commercial Gurobi, licence nominative",
    "mosek": "solveur commercial MOSEK, licence nominative",
}

#: Empreinte installee approximee, en Mo. Ordres de grandeur des roues
#: publiques, arrondis : la valeur sert a trancher un budget d'image, pas a
#: remplacer une mesure de `docker image inspect`.
PACKAGE_FOOTPRINT_MB: dict[str, int] = {
    "accelerate": 10,
    "bitsandbytes": 120,
    "dask": 20,
    "datasets": 40,
    "diffusers": 25,
    "faiss-cpu": 40,
    "faiss-gpu": 110,
    "gradio": 90,
    "gymnasium": 12,
    "imageio-ffmpeg": 25,
    "jax": 120,
    "jaxlib": 120,
    "jupyter": 20,
    "librosa": 15,
    "matplotlib": 30,
    "moviepy": 25,
    "mujoco": 25,
    "nltk": 12,
    "numpy": 25,
    "onnxruntime": 70,
    "onnxruntime-gpu": 320,
    "opencv-python": 80,
    "pandas": 70,
    "peft": 8,
    "pydantic": 20,
    "pyspark": 320,
    "pytest": 8,
    "python-dotenv": 1,
    "pytorch-lightning": 15,
    "ray": 220,
    "scikit-image": 45,
    "scikit-learn": 90,
    "scipy": 70,
    "sentence-transformers": 15,
    "spacy": 70,
    "streamlit": 50,
    "tensorflow": 800,
    "torch": 900,
    "torch-geometric": 10,
    "torchaudio": 20,
    "torchvision": 40,
    "transformers": 70,
    "trl": 8,
    "wandb": 35,
    "xformers": 220,
    "z3-solver": 45,
}

DEFAULT_PACKAGE_FOOTPRINT_MB = 3
DEFAULT_IMAGE_BUDGET_MB = 2000

#: Fenetres de lecture en fin de fichier pour retrouver ``kernelspec``. Les
#: sorties volumineuses repoussent la metadonnee loin de la fin : mesure du
#: 2026-11-20, 10 carnets sur 1939 ne la portent dans aucune fenetre.
KERNELSPEC_TAIL_WINDOWS = (64 * 1024, 512 * 1024, 4 * 1024 * 1024)


# ---------------------------------------------------------------------------
# Modeles
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class PackageSpec:
    """Une declaration de paquet, telle qu'ecrite dans un fichier de deps."""

    name: str
    operator: str
    version: str
    source: str


@dataclass
class NotebookInfo:
    """Un carnet suivi, avec son noyau et ses besoins declares."""

    path: str
    kernel: str | None = None
    family: str = "other"
    requires_gpu: bool = False
    requires_api: bool = False
    requires_cloud: bool = False
    requires_wsl: bool = False


@dataclass
class GroupEntry:
    """Un groupe (serie, sous-serie) de la table."""

    serie: str
    sous_serie: str
    notebooks: list[NotebookInfo] = field(default_factory=list)
    dependency_files: list[str] = field(default_factory=list)
    inherited_files: list[str] = field(default_factory=list)
    packages: list[PackageSpec] = field(default_factory=list)
    verdict: str = ""
    motif: str = ""

    @property
    def label(self) -> str:
        return f"{self.serie}/{self.sous_serie}"


# ---------------------------------------------------------------------------
# Lecture du depot
# ---------------------------------------------------------------------------


def git_ls_files(root: Path) -> list[str]:
    """Rend les chemins suivis par git, en POSIX, tries.

    Un seul appel a ``git`` : le script ne consulte ensuite que le disque.
    """
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        capture_output=True,
        check=True,
    )
    return sorted(item for item in result.stdout.decode("utf-8").split("\0") if item)


def group_key(path: str) -> tuple[str, str]:
    """Rend ``(serie, sous_serie)`` d'un chemin du depot.

    La sous-serie est le **premier** composant de dossier apres la serie : un
    decoupage plus fin fragmentait la table en 254 lignes pour 78 sous-series
    reelles (mesure du 2026-11-20), sans rien apprendre sur les dependances.
    Un fichier a la racine d'une serie tombe dans ``(racine)``.
    """
    parts = path.split("/")
    if len(parts) < 2:
        return "(racine)", "(racine)"
    if parts[0] == NOTEBOOK_ROOT:
        if len(parts) <= 2:
            return NOTEBOOK_ROOT, "(racine)"
        return parts[1], (parts[2] if len(parts) > 3 else "(racine)")
    return parts[0], (parts[1] if len(parts) > 2 else "(racine)")


def series_root(serie: str) -> str:
    """Rend le prefixe de dossier d'une serie."""
    return f"{serie}/"


# ---------------------------------------------------------------------------
# Kernelspec
# ---------------------------------------------------------------------------


def read_kernelspec(path: Path) -> tuple[str | None, str | None]:
    """Rend ``(name, language)`` du ``kernelspec`` d'un carnet.

    Le bloc ``metadata`` est en fin de document JSON ; on le cherche donc par
    fenetres croissantes depuis la fin, ce qui evite de charger en memoire les
    carnets de plusieurs dizaines de Mo. Les carnets ou le bloc reste
    introuvable rendent ``(None, None)`` — 10 cas mesures sur 1939.
    """
    try:
        size = path.stat().st_size
    except OSError:
        return None, None
    for window in KERNELSPEC_TAIL_WINDOWS:
        start = max(0, size - window)
        try:
            with path.open("rb") as handle:
                handle.seek(start)
                chunk = handle.read()
        except OSError:
            return None, None
        index = chunk.rfind(b'"kernelspec"')
        if index >= 0:
            return _parse_kernelspec(chunk[index:])
    try:
        chunk = path.read_bytes()
    except OSError:
        return None, None
    index = chunk.rfind(b'"kernelspec"')
    if index < 0:
        return None, None
    return _parse_kernelspec(chunk[index:])


def _parse_kernelspec(chunk: bytes) -> tuple[str | None, str | None]:
    """Extrait ``name`` et ``language`` du fragment qui commence a ``kernelspec``."""
    text = chunk[:4000].decode("utf-8", "replace")

    def field(name: str) -> str | None:
        match = re.search(rf'"{name}"\s*:\s*"([^"]*)"', text)
        return match.group(1) if match else None

    return field("name"), field("language")


def classify_family(name: str | None, language: str | None = None) -> str:
    """Rend la famille de noyau d'un nom de kernelspec.

    La correspondance est volontairement grossiere : elle sert a choisir une
    base d'image, pas a valider un kernelspec.
    """
    if not name:
        lowered_language = (language or "").lower()
        if "c#" in lowered_language or "csharp" in lowered_language:
            return "csharp"
        if "lean" in lowered_language:
            return "lean"
        if "python" in lowered_language:
            return "python"
        return "other"
    lowered = name.strip().lower()
    if lowered in KERNEL_FAMILY_EXPLICIT:
        return KERNEL_FAMILY_EXPLICIT[lowered]
    for needle, family in KERNEL_FAMILY_RULES:
        if needle in lowered:
            return family
    return "other"


# ---------------------------------------------------------------------------
# Analyse des fichiers de dependances
# ---------------------------------------------------------------------------


def parse_dependency_file(path: Path, source: str, seen: set[Path] | None = None) -> list[PackageSpec]:
    """Rend les declarations d'un fichier ``requirements`` ou ``environment``.

    Les inclusions ``-r`` sont suivies (chemins relatifs au fichier) ; les
    options, index, URL de VCS et marqueurs d'environnement sont ignores — ils
    ne decrivent pas un paquet.
    """
    seen = seen or set()
    resolved = path.resolve()
    if resolved in seen or not path.is_file():
        return []
    seen.add(resolved)
    try:
        text = path.read_text(encoding="utf-8-sig", errors="replace")
    except OSError:
        return []
    lowered = path.name.lower()
    if lowered.endswith((".yml", ".yaml")):
        return _parse_environment_yaml(text, path, source, seen)
    return _parse_requirements_text(text, path, source, seen)


def _parse_requirements_text(
    text: str, path: Path, source: str, seen: set[Path]
) -> list[PackageSpec]:
    specs: list[PackageSpec] = []
    for raw_line in text.splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith(("-r ", "--requirement")):
            target = line.split(maxsplit=1)[-1].split("=", 1)[-1].strip()
            if target:
                specs.extend(
                    parse_dependency_file(path.parent / target, f"{source} -> {target}", seen)
                )
            continue
        if line.startswith("-"):
            continue
        if "://" in line or line.startswith(("git+", "hg+", "svn+")):
            continue
        line = line.split(";", 1)[0].strip()
        match = REQUIREMENT_LINE_RE.match(line)
        if not match:
            continue
        specs.append(
            PackageSpec(
                name=normalise_name(match.group("name")),
                operator=match.group("operator") or "",
                version=(match.group("version") or "").rstrip(","),
                source=source,
            )
        )
    return specs


def _parse_environment_yaml(text: str, path: Path, source: str, seen: set[Path]) -> list[PackageSpec]:
    """Analyse minimale d'un ``environment.yml`` : pas de dependance a PyYAML.

    Deux formes sont reconnues : les items de la liste ``dependencies`` et le
    sous-bloc ``pip:`` qu'elle peut contenir.
    """
    specs: list[PackageSpec] = []
    in_dependencies = False
    in_pip = False
    pip_indent: int | None = None
    for raw_line in text.splitlines():
        if not raw_line.strip() or raw_line.lstrip().startswith("#"):
            continue
        indent = len(raw_line) - len(raw_line.lstrip())
        line = raw_line.split("#", 1)[0].rstrip()
        if not in_dependencies:
            if line.strip() == "dependencies:":
                in_dependencies = True
            continue
        item_match = ENVIRONMENT_ITEM_RE.match(line)
        if not item_match:
            if line.strip() and indent == 0:
                in_dependencies = False
                in_pip = False
            continue
        item = item_match.group("item").strip()
        if item in ("pip:", "- pip:") or item.rstrip(":") == "pip":
            in_pip = True
            pip_indent = indent
            continue
        if in_pip and pip_indent is not None and indent <= pip_indent:
            in_pip = False
        if in_pip:
            match = REQUIREMENT_LINE_RE.match(item.split(";", 1)[0].strip())
            if match:
                specs.append(
                    PackageSpec(
                        name=normalise_name(match.group("name")),
                        operator=match.group("operator") or "",
                        version=(match.group("version") or "").rstrip(","),
                        source=source,
                    )
                )
            continue
        # Forme conda : `numpy=1.24` (un seul `=`) ou `numpy 1.24`.
        conda = re.match(r"^([A-Za-z0-9][A-Za-z0-9._-]*)\s*[= ]\s*([0-9][^\s]*)", item)
        if conda:
            specs.append(
                PackageSpec(
                    name=normalise_name(conda.group(1)),
                    operator="==",
                    version=conda.group(2),
                    source=source,
                )
            )
            continue
        plain = re.match(r"^([A-Za-z0-9][A-Za-z0-9._-]*)$", item)
        if plain:
            specs.append(PackageSpec(normalise_name(plain.group(1)), "", "", source))
    return specs


def normalise_name(name: str) -> str:
    """Normalise un nom de paquet PyPI (PEP 503)."""
    return re.sub(r"[-_.]+", "-", name.strip().lower())


# ---------------------------------------------------------------------------
# Portee des fichiers de dependances
# ---------------------------------------------------------------------------


def tracked_directories(files: Iterable[str]) -> set[str]:
    """Rend l'ensemble des dossiers qui contiennent au moins un fichier suivi."""
    directories: set[str] = set()
    for path in files:
        directory = posixpath.dirname(path)
        while directory and directory not in directories:
            directories.add(directory)
            directory = posixpath.dirname(directory)
    return directories


def attach_dependency_file(path: str, directories: set[str]) -> tuple[str, str]:
    """Rend ``(serie, sous_serie)`` du groupe auquel un fichier de deps s'attache.

    Le qualificatif eventuel du nom (``requirements-audio.txt`` -> ``audio``)
    designe un sous-dossier voisin du dossier porteur ; a defaut le fichier
    reste dans le groupe de son propre dossier.
    """
    own_group = group_key(path)
    directory = posixpath.dirname(path)
    stem = posixpath.splitext(posixpath.basename(path))[0].lower()
    for prefix in ("requirements-", "environment-"):
        if stem.startswith(prefix):
            qualifier = stem[len(prefix) :]
            break
    else:
        return own_group
    if not qualifier or qualifier in ("optional", "dev", "test", "base"):
        return own_group
    candidates = [
        child
        for child in directories
        if posixpath.dirname(child) == directory
        and posixpath.basename(child).lower().replace("_", "-").startswith(qualifier.replace("_", "-"))
    ]
    if len(candidates) == 1:
        return group_key(posixpath.join(candidates[0], "_"))
    return own_group


def is_series_base(path: str) -> bool:
    """Vrai si le fichier est le socle d'une serie (racine de serie, nom nu)."""
    stem = posixpath.splitext(posixpath.basename(path))[0].lower()
    if stem not in ("requirements", "environment"):
        return False
    _, sous_serie = group_key(path)
    return sous_serie == "(racine)"


# ---------------------------------------------------------------------------
# Construction du manifeste
# ---------------------------------------------------------------------------


def load_catalog(root: Path) -> dict[str, dict]:
    """Charge le catalogue et l'indexe par chemin relatif a ``MyIA.AI.Notebooks``."""
    path = root / CATALOG_NAME
    if not path.is_file():
        return {}
    try:
        entries = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(entries, list):
        return {}
    return {entry.get("path", ""): entry for entry in entries if isinstance(entry, dict)}


def build_notebook_info(root: Path, path: str, catalog: dict[str, dict]) -> NotebookInfo:
    """Rend l'information d'un carnet : noyau reel et besoins du catalogue."""
    kernelspec_name, kernelspec_language = read_kernelspec(root / path)
    entry = catalog.get(path[len(NOTEBOOK_ROOT) + 1 :]) if path.startswith(NOTEBOOK_ROOT + "/") else None
    kernel = kernelspec_name or (entry or {}).get("kernel")
    info = NotebookInfo(path=path, kernel=kernel, family=classify_family(kernelspec_name, kernelspec_language))
    if entry:
        info.requires_gpu = bool(entry.get("requires_gpu"))
        info.requires_api = bool(entry.get("requires_api"))
        info.requires_cloud = bool(entry.get("requires_cloud"))
        info.requires_wsl = bool(entry.get("requires_wsl"))
    return info


def build_groups(root: Path) -> tuple[list[GroupEntry], dict[str, int]]:
    """Construit la table par (serie, sous-serie) et les compteurs globaux."""
    files = git_ls_files(root)
    directories = tracked_directories(files)
    catalog = load_catalog(root)

    notebooks = [path for path in files if path.endswith(".ipynb")]
    all_dependency_files = [
        path for path in files if DEPENDENCY_FILE_RE.match(posixpath.basename(path))
    ]
    # Les fichiers hors de l'arbre des carnets servent l'outillage du depot ou des
    # images de service : ils ne decrivent aucun environnement de carnet et
    # n'entrent donc ni dans la table ni dans le manifeste (voir la section
    # dediee du rendu Markdown).
    dependency_files = [
        path for path in all_dependency_files if path.startswith(NOTEBOOK_ROOT + "/")
    ]
    out_of_scope = [
        {
            "path": path,
            "packages": len({spec.name for spec in parse_dependency_file(root / path, path)}),
        }
        for path in all_dependency_files
        if not path.startswith(NOTEBOOK_ROOT + "/")
    ]

    groups: dict[tuple[str, str], GroupEntry] = {}

    def group_for(key: tuple[str, str]) -> GroupEntry:
        if key not in groups:
            groups[key] = GroupEntry(serie=key[0], sous_serie=key[1])
        return groups[key]

    for path in notebooks:
        group_for(group_key(path)).notebooks.append(build_notebook_info(root, path, catalog))

    bases: dict[str, tuple[tuple[str, str], str]] = {}
    attachments: list[tuple[tuple[str, str], str]] = []
    for path in dependency_files:
        key = attach_dependency_file(path, directories)
        attachments.append((key, path))
        group_for(key).dependency_files.append(path)
        if is_series_base(path):
            bases[key[0]] = (key, path)

    for key, entry in groups.items():
        serie, sous_serie = key
        base = bases.get(serie)
        if base and base[0] != key:
            entry.inherited_files.append(base[1])

    for entry in groups.values():
        specs: list[PackageSpec] = []
        for relative in entry.dependency_files:
            specs.extend(parse_dependency_file(root / relative, relative))
        for relative in entry.inherited_files:
            specs.extend(parse_dependency_file(root / relative, f"{relative} (socle de serie)"))
        entry.packages = specs

    stats = {
        "notebooks": len(notebooks),
        "dependency_files": len(dependency_files),
        "dependency_files_hors_perimetre": len(out_of_scope),
        "groups": len(groups),
    }
    return (
        sorted(groups.values(), key=lambda item: (item.serie, item.sous_serie)),
        stats,
        out_of_scope,
    )


# ---------------------------------------------------------------------------
# Verdicts
# ---------------------------------------------------------------------------


def package_footprint_mb(name: str) -> int:
    """Rend l'empreinte estimee d'un paquet, en Mo."""
    return PACKAGE_FOOTPRINT_MB.get(name, DEFAULT_PACKAGE_FOOTPRINT_MB)


def group_footprint_mb(entry: GroupEntry) -> int:
    """Rend l'empreinte estimee du groupe, socle de serie compris."""
    return sum(package_footprint_mb(name) for name in {spec.name for spec in entry.packages})


def own_footprint_mb(entry: GroupEntry, root: Path) -> int:
    """Rend l'empreinte estimee des seuls fichiers propres au groupe.

    Le socle d'une serie est paye une fois pour toute la serie : le compter dans
    chaque sous-groupe ferait apparaitre la meme depense autant de fois qu'il y a
    de sous-series, et le budget comparerait des choses qui ne s'additionnent
    pas. Le budget s'applique donc a l'increment propre du groupe.
    """
    names: set[str] = set()
    for relative in entry.dependency_files:
        names.update(spec.name for spec in parse_dependency_file(root / relative, relative))
    return sum(package_footprint_mb(name) for name in names)


#: Part de carnets GPU a partir de laquelle un groupe est un groupe GPU. Un
#: carnet GPU isole dans une serie CPU ne definit pas la serie ; la moitie est
#: le seuil ou le GPU devient le mode d'execution dominant du groupe. Le compte
#: exact reste visible dans la colonne ``GPU`` de la table.
GPU_MAJORITY_RATIO = 0.5


def decide_verdict(entry: GroupEntry, budget_mb: int, root: Path) -> tuple[str, str]:
    """Applique les regles de verdict documentees dans la docstring du module."""
    if entry.notebooks:
        gpu = sum(1 for notebook in entry.notebooks if notebook.requires_gpu)
        if gpu / len(entry.notebooks) >= GPU_MAJORITY_RATIO:
            return "exclu", "gpu"
    restricted = sorted({spec.name for spec in entry.packages} & set(RESTRICTED_PACKAGES))
    if restricted:
        return "exclu", "licence"
    if own_footprint_mb(entry, root) > budget_mb:
        return "exclu", "taille"
    if any(notebook.requires_cloud for notebook in entry.notebooks):
        return "service optionnel", "service"
    return "inclus", ""


def apply_verdicts(entries: Sequence[GroupEntry], budget_mb: int, root: Path) -> None:
    for entry in entries:
        entry.verdict, entry.motif = decide_verdict(entry, budget_mb, root)


# ---------------------------------------------------------------------------
# Resolution des versions
# ---------------------------------------------------------------------------


def version_key(version: str) -> tuple[int, ...] | None:
    """Rend une cle comparable pour une version numerique, sinon ``None``."""
    if not version:
        return None
    parts = re.findall(r"\d+", version)
    if not parts:
        return None
    return tuple(int(part) for part in parts[:4])


def _compare(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    width = max(len(left), len(right))
    left = left + (0,) * (width - len(left))
    right = right + (0,) * (width - len(right))
    return (left > right) - (left < right)


def satisfies(version: str, operator: str, constraint: str) -> bool | None:
    """Vrai si ``version`` satisfait ``operator constraint`` ; ``None`` si indecidable."""
    if operator in ("", "!=") or not constraint:
        return True if operator == "" else None
    current, bound = version_key(version), version_key(constraint)
    if current is None or bound is None:
        return None
    if operator == "===":
        return version.strip() == constraint.strip()
    if operator == "~=":
        if len(bound) < 2:
            return None
        upper = bound[:-1]
        upper = upper[:-1] + (upper[-1] + 1,) if len(upper) >= 1 else (bound[0] + 1,)
        return _compare(current, bound) >= 0 and _compare(current, upper) < 0
    comparison = _compare(current, bound)
    if operator == "==":
        return comparison == 0
    if operator == ">=":
        return comparison >= 0
    if operator == ">":
        return comparison > 0
    if operator == "<=":
        return comparison <= 0
    if operator == "<":
        return comparison < 0
    return None


def format_constraint(operator: str, version: str) -> str:
    return f"{operator}{version}" if operator and version else "(non borne)"


def resolve_package(
    name: str, occurrences: Sequence[PackageSpec]
) -> tuple[str, list[dict]]:
    """Rend ``(pin_retenu, conflits)`` pour un paquet.

    Le pin retenu est le ``==`` quand il existe et satisfait les bornes des
    autres fichiers ; sinon la borne basse la plus haute. Les conflits durs
    (intersection vide) sont rendus a part, avec une resolution proposee.
    """
    conflicts: list[dict] = []
    constraints = [
        (spec, format_constraint(spec.operator, spec.version))
        for spec in occurrences
        if spec.operator and spec.version
    ]
    distinct = sorted({text for _, text in constraints})
    pinned = sorted({spec.version for spec in occurrences if spec.operator in ("==", "===")})
    sources = sorted({spec.source for spec in occurrences})

    if len(pinned) > 1:
        resolution = max(pinned, key=lambda value: version_key(value) or ())
        conflicts.append(
            {
                "package": name,
                "kind": "pins-exacts-divergents",
                "detail": "plusieurs fichiers epinglent des versions differentes",
                "constraints": distinct,
                "sources": sources,
                "resolution": f"retenir {resolution} (la plus recente) et revalider les series qui epinglaient les autres",
            }
        )
    for version in pinned:
        violated = [
            (spec, text)
            for spec, text in constraints
            if spec.operator not in ("==", "===")
            and satisfies(version, spec.operator, spec.version) is False
        ]
        if violated:
            conflicts.append(
                {
                    "package": name,
                    "kind": "pin-contredit-une-borne",
                    "detail": f"le pin {version} ne satisfait pas " + ", ".join(
                        f"{text} ({spec.source})" for spec, text in violated
                    ),
                    "constraints": distinct,
                    "sources": sources,
                    "resolution": f"retenir {version} et corriger "
                    + " et ".join(text for _, text in violated)
                    + ", ou abandonner le pin",
                }
            )

    lows = [
        (version_key(spec.version), spec.version, spec.operator)
        for spec in occurrences
        if spec.operator in (">=", ">") and version_key(spec.version)
    ]
    highs = [
        (version_key(spec.version), spec.version, spec.operator)
        for spec in occurrences
        if spec.operator in ("<=", "<") and version_key(spec.version)
    ]
    if lows and highs:
        low = max(lows, key=lambda item: item[0] or ())
        high = min(highs, key=lambda item: item[0] or ())
        comparison = _compare(low[0] or (), high[0] or ())
        if comparison > 0 or (comparison == 0 and (low[2] == ">" or high[2] == "<")):
            conflicts.append(
                {
                    "package": name,
                    "kind": "bornes-disjointes",
                    "detail": f"borne basse {low[1]} incompatible avec borne haute {high[1]}",
                    "constraints": distinct,
                    "sources": sources,
                    "resolution": f"retenir une version strictement posterieure a {low[1]} et anterieure a {high[1]} est impossible : arbitrer la contrainte a relacher",
                }
            )

    if pinned:
        if len(pinned) == 1 and not any(
            conflict["package"] == name and conflict["kind"] == "pin-contredit-une-borne"
            for conflict in conflicts
        ):
            return f"=={pinned[0]}", conflicts
        return f"=={max(pinned, key=lambda value: version_key(value) or ())}", conflicts
    if lows:
        best = max(lows, key=lambda item: item[0] or ())
        return f"{best[2]}{best[1]}", conflicts
    if highs:
        best = min(highs, key=lambda item: item[0] or ())
        return f"{best[2]}{best[1]}", conflicts
    return "(non borne)", conflicts


def consolidate(entries: Sequence[GroupEntry]) -> tuple[dict[str, dict], list[dict]]:
    """Consolide les paquets des groupes retenus et rend les conflits."""
    per_package: dict[str, list[PackageSpec]] = defaultdict(list)
    declared_by: dict[str, set[str]] = defaultdict(set)
    for entry in entries:
        if entry.verdict.startswith("exclu"):
            continue
        own_sources = set(entry.dependency_files)
        for spec in entry.packages:
            per_package[spec.name].append(spec)
            # ``declared_by`` nomme les groupes dont un fichier PROPRE declare le
            # paquet : les groupes qui heritent du socle de serie ne sont pas
            # listes, sinon un paquet du socle apparaitrait declare par quinze
            # sous-series qui ne l'ont pas ecrit.
            if spec.source in own_sources:
                declared_by[spec.name].add(entry.label)

    manifest: dict[str, dict] = {}
    conflicts: list[dict] = []
    for name in sorted(per_package):
        pin, package_conflicts = resolve_package(name, per_package[name])
        distinct = sorted(
            {
                format_constraint(spec.operator, spec.version)
                for spec in per_package[name]
                if spec.operator and spec.version
            }
        )
        manifest[name] = {
            "pin": pin,
            "declared_by": sorted(declared_by[name]),
            "constraints": distinct,
            "sources": sorted({spec.source for spec in per_package[name]}),
            "footprint_mb": package_footprint_mb(name),
        }
        conflicts.extend(package_conflicts)
    return manifest, conflicts


def divergences(manifest: dict[str, dict]) -> list[dict]:
    """Rend les paquets dont les series divergent (plus d'une contrainte)."""
    result: list[dict] = []
    for name, data in sorted(manifest.items()):
        if len(data["constraints"]) > 1:
            result.append(
                {
                    "package": name,
                    "pin": data["pin"],
                    "constraints": data["constraints"],
                    "declared_by": data["declared_by"],
                    "resolution": f"retenir {data['pin']} : c'est la contrainte la plus exigeante, elle satisfait les autres",
                }
            )
    return result


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------


def build_payload(root: Path, budget_mb: int) -> dict:
    """Construit le manifeste complet (structure serialisable)."""
    entries, stats, out_of_scope = build_groups(root)
    apply_verdicts(entries, budget_mb, root)
    manifest, conflicts = consolidate(entries)

    family_counts: Counter[str] = Counter()
    kernel_counts: Counter[str] = Counter()
    family_series: dict[str, set[str]] = defaultdict(set)
    for entry in entries:
        for notebook in entry.notebooks:
            family_counts[notebook.family] += 1
            kernel_counts[notebook.kernel or "(sans kernelspec)"] += 1
            family_series[notebook.family].add(entry.serie)

    return {
        "schema": 1,
        "issue": 27544,
        "sources": {
            "inventaire": "git ls-files (arbre de travail, aucun appel reseau)",
            "besoins": CATALOG_NAME,
            "kernelspec": "lecture du bloc metadata de chaque carnet",
        },
        "budget_mb": budget_mb,
        "totals": {
            **stats,
            "packages_distincts_declares": len(
                {spec.name for entry in entries for spec in entry.packages}
            ),
            "packages_retenus": len(manifest),
            "conflits": len(conflicts),
            "empreinte_manifeste_mb": sum(data["footprint_mb"] for data in manifest.values()),
        },
        "kernel_families": {
            family: {
                "notebooks": family_counts[family],
                "series": sorted(family_series[family]),
            }
            for family in KERNEL_FAMILIES
            if family_counts[family]
        },
        "kernel_names": dict(sorted(kernel_counts.items(), key=lambda item: (-item[1], item[0]))),
        "out_of_scope": out_of_scope,
        "groups": [
            {
                "serie": entry.serie,
                "sous_serie": entry.sous_serie,
                "notebooks": len(entry.notebooks),
                "kernel_families": dict(
                    sorted(Counter(notebook.family for notebook in entry.notebooks).items())
                ),
                "kernel_names": dict(
                    sorted(
                        Counter(
                            notebook.kernel or "(sans kernelspec)" for notebook in entry.notebooks
                        ).items()
                    )
                ),
                "requires_gpu": sum(1 for notebook in entry.notebooks if notebook.requires_gpu),
                "requires_api": sum(1 for notebook in entry.notebooks if notebook.requires_api),
                "requires_cloud": sum(
                    1 for notebook in entry.notebooks if notebook.requires_cloud
                ),
                "requires_wsl": sum(1 for notebook in entry.notebooks if notebook.requires_wsl),
                "dependency_files": entry.dependency_files,
                "inherited_files": entry.inherited_files,
                "packages": len({spec.name for spec in entry.packages}),
                "footprint_mb": group_footprint_mb(entry),
                "own_footprint_mb": own_footprint_mb(entry, root),
                "verdict": entry.verdict,
                "motif": entry.motif,
            }
            for entry in entries
        ],
        "manifest": manifest,
        "conflicts": conflicts,
        "divergences": divergences(manifest),
    }


def _md_escape(value: object) -> str:
    return str(value).replace("|", "\\|")


def _format_footprint(group: dict) -> str:
    """Rend l'empreinte d'un groupe, avec son increment propre entre parentheses."""
    total = group["footprint_mb"]
    own = group["own_footprint_mb"]
    return f"{total} (+{own})" if own else str(total)


def render_markdown(payload: dict, budget_mb: int) -> str:
    """Rend le manifeste en Markdown."""
    totals = payload["totals"]
    lines: list[str] = []
    add = lines.append

    add("# Manifeste des dependances par famille de noyau")
    add("")
    add(
        "Genere par `python scripts/notebook_tools/kernel_dependency_manifest.py --write` "
        "(Pli 1.1, issue #27544). Ne pas editer a la main : regenerer."
    )
    add("")
    add("## Sources")
    add("")
    add("| Source | Usage |")
    add("|---|---|")
    add(f"| `git ls-files` | inventaire des carnets et des fichiers de dependances |")
    add(f"| `{CATALOG_NAME}` | `requires_gpu`, `requires_api`, `requires_cloud`, `requires_wsl` |")
    add("| bloc `metadata.kernelspec` de chaque carnet | famille de noyau |")
    add("")
    add(f"Aucun appel reseau. Budget d'image applique : **{budget_mb} Mo**.")
    add("")
    add("## Chiffres")
    add("")
    add("| Mesure | Valeur |")
    add("|---|---|")
    add(f"| Carnets suivis | {totals['notebooks']} |")
    add(f"| Fichiers de dependances | {totals['dependency_files']} |")
    add(f"| Groupes serie / sous-serie | {totals['groups']} |")
    add(f"| Paquets distincts declares | {totals['packages_distincts_declares']} |")
    add(f"| Paquets retenus dans le manifeste | {totals['packages_retenus']} |")
    add(f"| Conflits de versions | {totals['conflits']} |")
    add(f"| Empreinte estimee du manifeste | {totals['empreinte_manifeste_mb']} Mo |")
    add("")

    add("## Familles de noyau")
    add("")
    add("| Famille | Carnets | Series |")
    add("|---|---|---|")
    for family, data in payload["kernel_families"].items():
        add(f"| {family} | {data['notebooks']} | {_md_escape(', '.join(data['series']))} |")
    add("")
    add("Noms de kernelspec rencontres :")
    add("")
    add("| Noyau | Carnets |")
    add("|---|---|")
    for name, count in payload["kernel_names"].items():
        add(f"| `{_md_escape(name)}` | {count} |")
    add("")
    unknown = payload["kernel_names"].get("unknown", 0)
    if unknown:
        add(
            f"{unknown} carnets ne portent aucun `kernelspec` lisible, et le catalogue les "
            "classe aussi `unknown` : leur famille est `other`. Leur noyau reste a "
            "determiner ; ils restent dans la table avec leur groupe."
        )
        add("")

    add("## Table par serie et sous-serie")
    add("")
    add(
        "| Serie | Sous-serie | Carnets | Noyau | GPU | API | Cloud | WSL | Deps | Mo | Verdict |"
    )
    add("|---|---|---:|---|---:|---:|---:|---:|---:|---:|---|")
    for group in payload["groups"]:
        kernels = ", ".join(f"{key} ({value})" for key, value in group["kernel_names"].items())
        verdict = group["verdict"] + (f" ({group['motif']})" if group["motif"] else "")
        add(
            "| {serie} | {sous} | {nb} | {kernels} | {gpu} | {api} | {cloud} | {wsl} | {deps} | {mo} | {verdict} |".format(
                serie=_md_escape(group["serie"]),
                sous=_md_escape(group["sous_serie"]),
                nb=group["notebooks"],
                kernels=_md_escape(kernels),
                gpu=group["requires_gpu"],
                api=group["requires_api"],
                cloud=group["requires_cloud"],
                wsl=group["requires_wsl"],
                deps=len(group["dependency_files"]) + len(group["inherited_files"]),
                mo=_format_footprint(group),
                verdict=verdict,
            )
        )
    add("")
    add(
        "`GPU`, `API`, `Cloud` et `WSL` comptent les carnets du groupe qui declarent le besoin ; "
        "`Deps` compte les fichiers de dependances propres et herites du socle de serie ; "
        "`Mo` est l'empreinte installee estimee, socle de serie compris, et `(+N)` l'increment "
        "propre du groupe au-dela de ce socle."
    )
    add("")

    add("## Fichiers de dependances hors perimetre")
    add("")
    add(
        "Ces fichiers ne decrivent aucun environnement de carnet : ils servent l'outillage du "
        "depot ou des images de service. Ils n'entrent ni dans la table ni dans le manifeste, "
        "et sont listes ici pour que rien ne disparaisse en silence."
    )
    add("")
    if payload["out_of_scope"]:
        add("| Fichier | Paquets |")
        add("|---|---:|")
        for item in payload["out_of_scope"]:
            add(f"| `{_md_escape(item['path'])}` | {item['packages']} |")
    else:
        add("Aucun fichier hors perimetre.")
    add("")

    add("## Exclusions et motifs")
    add("")
    by_motif: dict[str, list[dict]] = defaultdict(list)
    optional: list[dict] = []
    for group in payload["groups"]:
        if group["verdict"] == "exclu":
            by_motif[group["motif"]].append(group)
        elif group["verdict"] == "service optionnel":
            optional.append(group)
    if not by_motif and not optional:
        add("Aucune exclusion : tous les groupes sont inclus.")
        add("")
    for motif in ("gpu", "taille", "licence", "conflit de versions"):
        groups = by_motif.get(motif, [])
        add(f"### Motif `{motif}` — {len(groups)} groupe(s)")
        add("")
        if not groups:
            add("Aucun groupe exclu pour ce motif.")
            add("")
            continue
        add("| Groupe | Carnets | GPU | Mo | Justification |")
        add("|---|---:|---:|---:|---|")
        for group in groups:
            if motif == "gpu":
                justification = (
                    f"{group['requires_gpu']} carnets sur {group['notebooks']} declarent "
                    "`requires_gpu` : le GPU est le mode d'execution dominant du groupe"
                )
            elif motif == "taille":
                justification = (
                    f"empreinte estimee {group['footprint_mb']} Mo > budget {budget_mb} Mo"
                )
            elif motif == "licence":
                justification = "declaration d'un paquet a licence non redistribuable"
            else:
                justification = "conflit de versions non resolvable automatiquement"
            add(
                f"| {_md_escape(group['serie'])}/{_md_escape(group['sous_serie'])} | "
                f"{group['notebooks']} | {group['requires_gpu']} | {group['footprint_mb']} | {justification} |"
            )
        add("")
    add(f"### Services optionnels (Pli 1.5) — {len(optional)} groupe(s)")
    add("")
    if optional:
        add("| Groupe | Carnets cloud | Service attendu |")
        add("|---|---:|---|")
        for group in optional:
            add(
                f"| {_md_escape(group['serie'])}/{_md_escape(group['sous_serie'])} | "
                f"{group['requires_cloud']} | hors image : le carnet attend un service reseau |"
            )
        add("")
    else:
        add("Aucun groupe dans ce cas.")
        add("")

    add("## Poids du manifeste")
    add("")
    heaviest = sorted(
        payload["manifest"].items(), key=lambda item: -item[1]["footprint_mb"]
    )[:10]
    add("| Paquet | Mo | Groupes qui le declarent |")
    add("|---|---:|---:|")
    for name, data in heaviest:
        add(f"| `{name}` | {data['footprint_mb']} | {len(data['declared_by'])} |")
    add("")
    add(
        f"L'empreinte estimee du manifeste consolide est de {totals['empreinte_manifeste_mb']} Mo, "
        f"pour un budget unitaire de {budget_mb} Mo applique a l'increment propre de chaque groupe. "
        "L'ecart est une information, pas un defaut du manifeste : c'est au Pli 1.2 de decider "
        "s'il scinde l'image ou s'il cible un sous-ensemble des groupes inclus."
    )
    add("")

    add("## Manifeste consolide")
    add("")
    add(
        "Seule source de paquets de l'image d'apprentissage (Pli 1.2) : elle installe "
        "exactement cette table et rien d'autre."
    )
    add("")
    add(f"{len(payload['manifest'])} paquets, dans l'ordre alphabetique.")
    add("")
    add("| Paquet | Version retenue | Declare par | Contraintes rencontrees |")
    add("|---|---|---|---|")
    for name, data in payload["manifest"].items():
        add(
            f"| `{name}` | `{data['pin']}` | {_md_escape(', '.join(data['declared_by']))} | "
            f"{_md_escape(', '.join(data['constraints']) or '(aucune)')} |"
        )
    add("")

    add("## Conflits de versions")
    add("")
    conflicts = payload["conflicts"]
    if not conflicts:
        add("Aucun conflit dur : aucune contrainte n'est contredite par une autre.")
        add("")
    else:
        add("| Paquet | Type | Detail | Resolution proposee |")
        add("|---|---|---|---|")
        for conflict in conflicts:
            add(
                f"| `{conflict['package']}` | {conflict['kind']} | "
                f"{_md_escape(conflict['detail'])} | {_md_escape(conflict['resolution'])} |"
            )
        add("")

    add("## Divergences de bornes")
    add("")
    add(
        "Un paquet declare par plusieurs series avec des contraintes differentes n'est pas un "
        "conflit : c'est la contrainte la plus exigeante qui est retenue. Chaque ligne dit "
        "lesquelles."
    )
    add("")
    diverged = payload["divergences"]
    if not diverged:
        add("Aucune divergence.")
        add("")
    else:
        add("| Paquet | Version retenue | Contraintes | Series |")
        add("|---|---|---|---|")
        for item in diverged:
            add(
                f"| `{item['package']}` | `{item['pin']}` | "
                f"{_md_escape(', '.join(item['constraints']))} | "
                f"{_md_escape(', '.join(item['declared_by']))} |"
            )
        add("")

    add("## Consommation par l'image 1.2")
    add("")
    add(
        "Contrat du Pli 1.2 : le `Dockerfile` de `docker-configurations/notebook-runner` "
        "prendra ses paquets de `kernel-manifest.json` (cle `manifest`), sans liste "
        "paralleve. Aujourd'hui le `Dockerfile` porte encore sa propre liste : c'est le "
        "Pli 1.2 qui la remplace. Apres ce remplacement, un paquet absent du manifeste "
        "n'entre pas dans l'image, et ajouter un paquet se fait par un fichier "
        "`requirements` du depot puis par regeneration de ce manifeste."
    )
    add("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Point d'entree
# ---------------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo-root", type=Path, default=DEFAULT_REPO_ROOT, help="racine du depot")
    parser.add_argument(
        "--format",
        choices=("md", "json", "both"),
        default="both",
        help="format ecrit sur la sortie standard",
    )
    parser.add_argument(
        "--budget-mb",
        type=int,
        default=DEFAULT_IMAGE_BUDGET_MB,
        help="budget d'empreinte de l'image, en Mo (defaut : %(default)s)",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help=f"ecrit {OUTPUT_MD} et {OUTPUT_JSON} a la place de la sortie standard",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="sort en 1 si les fichiers versionnes divergent du depot",
    )
    parser.add_argument("--quiet", action="store_true", help="n'affiche rien hors erreur")
    args = parser.parse_args(argv)

    root: Path = args.repo_root.resolve()
    payload = build_payload(root, args.budget_mb)
    markdown = render_markdown(payload, args.budget_mb)
    as_json = json.dumps(payload, ensure_ascii=False, indent=1, sort_keys=False) + "\n"

    if args.check:
        stale: list[str] = []
        for relative, expected in ((OUTPUT_MD, markdown), (OUTPUT_JSON, as_json)):
            path = root / relative
            if not path.is_file() or path.read_text(encoding="utf-8") != expected:
                stale.append(str(relative))
        if stale:
            print("Manifeste perime : " + ", ".join(stale), file=sys.stderr)
            print(
                "Regenerer : python scripts/notebook_tools/kernel_dependency_manifest.py --write",
                file=sys.stderr,
            )
            return 1
        if not args.quiet:
            print("Manifeste a jour.")
        return 0

    if args.write:
        for relative, content in ((OUTPUT_MD, markdown), (OUTPUT_JSON, as_json)):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8", newline="\n")
        if not args.quiet:
            print(f"Ecrit {OUTPUT_MD} et {OUTPUT_JSON} ({len(payload['groups'])} groupes, {len(payload['manifest'])} paquets)")
        return 0

    if args.format in ("md", "both"):
        sys.stdout.write(markdown)
    if args.format == "both":
        sys.stdout.write("\n---\n\n")
    if args.format in ("json", "both"):
        sys.stdout.write(as_json)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())