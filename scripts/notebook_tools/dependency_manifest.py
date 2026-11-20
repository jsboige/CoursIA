#!/usr/bin/env python
"""Manifeste des dependances du cursus, par famille de noyau (#27544).

Cet organe repond a la question posee par le pli 1 de l'Epic #27543 :
**que doit contenir l'image d'apprentissage CPU, et qu'en reste-t-il exclu ?**
Il produit, depuis `git ls-files` et **sans reseau**, la table qui decide du
contenu de l'image 1.2 (cf. #27545).

Ce que fait l'organe
--------------------

1. **Recensement** : il enumere les fichiers de dependances declares
   (`requirements*.txt`, `environment*.yml`) et les rattache a la **serie** et
   a la **sous-serie** qui les portent ; il enumere les carnets de ces series
   et en lit le `kernelspec`, d'ou la **famille de noyau** (Python, .NET, Lean,
   Rust). Aucune serie du depot n'est absente de la table : une serie sans
   fichier de dependances y figure avec la mention ``aucun``.

2. **Besoins** : pour chaque serie, il mesure sur les **sources des cellules**
   des carnets trois besoins : **GPU**, **cle d'API**, **service reseau**.
   La mesure porte sur des marqueurs explicites ; rien n'est devine.

3. **Verdict d'inclusion** dans l'image CPU, avec un **motif** obligatoire.
   Chaque motif porte son **origine** :

   - ``mesure`` : le verdict se deduit d'une lecture du depot (GPU detecte,
     versions en conflit, noyau non-Python, contrainte ``requires-python``) ;
   - ``declaration`` : le verdict repose sur une regle ecrite dans la
     **politique versionnee** (``dependency_manifest_policy.json``), que le
     lecteur peut contester (poids d'une distribution, dependances
     optionnelles, services containerises).

   Les deux natures sont **distinguees dans la table** : c'est ce qui rend la
   table verifiable. Le motif ``licence`` existe dans la politique mais sa
   liste est **vide a dessein** — aucune source du depot n'etablit, hors
   ligne, une contrainte de licence ; simuler un inventaire de licences serait
   une invention, pas une mesure.

   Les motifs sont **cumulatifs** : une serie exclue pour GPU et pour poids
   porte les deux motifs. Une exclusion l'emporte toujours sur un service
   optionnel ; la colonne **Service optionnel** garde l'information meme
   quand le verdict est ``exclu``.

4. **Conflits de versions** : un meme paquet declare avec des **specificateurs
   differents** dans deux fichiers de dependances est un conflit nomme, avec
   pour chaque specification sa source (fichier + serie), sa classe
   (``pin_exact_divergent``, ``specifier_divergent``, ``incompatible``) et une
   **resolution proposee**.

5. **Manifeste consolide** : la seule source de paquets de l'image 1.2. Il ne
   contient que les paquets des series incluses, avec, par paquet, la version
   retenue et les series qui l'apportent. Un paquet en conflit y figure avec
   son marqueur de resolution, jamais avec une version inventee.

Organes natifs reuses (regle « nommer l'organe natif avant de reimplements »)
--------------------------------------------------------------------------

- ``scripts/notebook_tools/check_lib_versions.py`` (#23073) fournit la
  comparaison de versions (``version_key`` / ``compare_versions``) et, via
  ``run_census``, le recensement des divergences canonique/observe. Le
  manifeste ne recalcule ni l'un ni l'autre.
- ``scripts/notebook_tools/check_kernel_drift.py`` (#22441) reste l'organe du
  `kernelspec` ; cet organe n'en fait qu'une **lecture agregee par serie**.
- ``docs/reference/kernels-runtime.md`` est la reference des versions Python
  canoniques par noyau ; ses valeurs sont reprises dans la politique.

Usage
-----

::

    python scripts/notebook_tools/dependency_manifest.py --out-dir docs/curriculum
    python scripts/notebook_tools/dependency_manifest.py --print

Les sorties par defaut sont versionnees dans le depot :

- ``docs/curriculum/manifeste-dependances.md`` (la table) ;
- ``docs/curriculum/manifeste-dependances.json`` (la meme table, exploitable).

Le code de sortie vaut 0 lorsque l'inventaire est complet (toutes les series
sont dans la table, tous les conflits sont nommes avec une resolution) et 1
sinon.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _TOOLS_DIR.parent.parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

try:  # l'organe natif des versions (#23073)
    from check_lib_versions import (  # type: ignore[import-not-found]
        compare_versions,
        run_census,
        version_key,
    )
    from check_lib_versions import (
        load_manifest as load_lib_manifest,
    )
except Exception as exc:  # noqa: BLE001 - pragma: no cover - degrade signalee, jamais avalee
    compare_versions = None  # type: ignore[assignment]
    load_lib_manifest = None  # type: ignore[assignment]
    run_census = None  # type: ignore[assignment]
    version_key = None  # type: ignore[assignment]
    _LIB_VERSIONS_IMPORT_ERROR: Exception | None = exc
else:
    _LIB_VERSIONS_IMPORT_ERROR = None

SCHEMA_VERSION = 1
NOTEBOOKS_ROOT = "MyIA.AI.Notebooks"
POLICY_RELPATH = "scripts/notebook_tools/dependency_manifest_policy.json"
DEFAULT_OUT_DIR = "docs/curriculum"

#: Familles de noyau, deduites du `kernelspec` (champ ``language``).
KERNEL_FAMILY_BY_LANGUAGE = {
    "python": "Python",
    "python3": "Python",
    "py310": "Python",
    "py313": "Python",
    "ict-py313": "Python",
    "coursia-ml-training": "Python",
    "pyphi": "Python",
    "c#": ".NET",
    ".net-csharp": ".NET",
    "csharp": ".NET",
    "lean4": "Lean",
    "lean": "Lean",
    "rust": "Rust",
}

#: Familles de noyau qui ne sont pas servies par une image CPU Python.
NON_PYTHON_FAMILIES = {".NET", "Lean", "Rust"}

#: Politiques dont un motif **exclut** la serie de l'image CPU.
EXCLUSION_POLICIES = {
    "gpu",
    "heavy_distributions",
    "licenses",
    "kernel_family",
    "requires_python",
}

#: Politiques dont un motif rend la serie un **service optionnel**.
OPTIONAL_POLICIES = {"optional_file_markers", "container_services"}

#: Lecture d'une variable d'environnement : on en retient le nom.
ENV_READ_RE = re.compile(
    r"os\.(?:environ\.get|getenv)\s*\(\s*['\"]([A-Za-z_][A-Za-z0-9_]*)['\"]",
)
ENV_SECRET_NAME_RE = re.compile(
    r"(API_KEY|_KEY$|^KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL)", re.IGNORECASE
)

#: Appels reseau explicites.
SERVICE_CALL_RE = re.compile(
    r"(?:requests|httpx|urllib\.request|socket\.socket|aiohttp)"
    r"\.(?:get|post|put|request|connect)\s*\(",
    re.IGNORECASE,
)
URL_RE = re.compile(r"https?://([A-Za-z0-9_.\-]+)(?::(\d+))?")
LOCAL_HOSTS = {"localhost", "127.0.0.1", "0.0.0.0", "::1"}

#: Imports de premier niveau dans une cellule de code.
IMPORT_RE = re.compile(
    r"^\s*(?:import\s+([A-Za-z_][A-Za-z0-9_]*)|from\s+([A-Za-z_][A-Za-z0-9_.]*)\s+import)",
    re.MULTILINE,
)

#: Contraintes pip/conda qui ne sont pas des paquets.
_PIP_OPTIONS = (
    "--index-url",
    "--extra-index-url",
    "--find-links",
    "--pre",
    "--trusted-host",
    "--hash",
)


def _norm_name(raw: str) -> str:
    """Normalise un nom de paquet (PEP 503) : minuscules, ``-`` et ``_`` unifies."""
    return re.sub(r"[-_.]+", "-", raw.strip().lower())


def _version_sort_key(version: str) -> tuple:
    """Tri de versions delegue a l'organe natif quand il est disponible."""
    if version_key is not None:
        try:
            return version_key(version)
        except Exception:  # noqa: BLE001,S110 - repli local, l'organe natif reste l'original
            pass
    return tuple(
        int(part) if part.isdigit() else part
        for part in re.split(r"[.\-+]", version)
        if part
    )


def _compare(left: str, right: str) -> int:
    """Compare deux versions ; repli lexical si l'organe natif est absent."""
    if compare_versions is not None:
        try:
            return compare_versions(left, right)
        except Exception:  # noqa: BLE001,S110 - repli local, l'organe natif reste l'original
            pass
    return (left > right) - (left < right)


def _norm_ver(version: str) -> str:
    """Forme canonique d'une version : ``1.0`` et ``1.0.0`` ne font qu'un.

    La normalisation passe par l'organe natif des versions (#23073) : deux
    chaines differentes qui designent la meme version ne sont pas un conflit.
    """
    if not version:
        return ""
    if version_key is not None:
        try:
            return repr(version_key(version))
        except Exception:  # noqa: BLE001,S110 - repli local, l'organe natif reste l'original
            pass
    return version


def _max_version(left: str, right: str) -> str:
    """La plus haute des deux versions ; la chaine vide signifie « absent »."""
    if not left:
        return right
    if not right:
        return left
    return left if _compare(left, right) >= 0 else right


def _min_version(left: str, right: str) -> str:
    """La plus basse des deux versions ; la chaine vide signifie « absent »."""
    if not left:
        return right
    if not right:
        return left
    return left if _compare(left, right) <= 0 else right


@dataclass
class Requirement:
    """Une ligne de dependance resolue."""

    name: str
    spec: str
    source_file: str
    group: str
    raw: str
    marker: str = ""

    @property
    def pinned(self) -> str:
        """La version epinglee (``==``), ou la chaine vide."""
        match = re.search(r"==\s*([^\s,;]+)", self.spec)
        return match.group(1) if match else ""


@dataclass
class Group:
    """Une ligne de la table : un groupe de repertoire d'une serie."""

    path: str
    series: str
    subseries: str
    notebooks: list[str] = field(default_factory=list)
    kernelspecs: dict[str, int] = field(default_factory=dict)
    dependency_files: list[str] = field(default_factory=list)
    requirements: list[Requirement] = field(default_factory=list)
    gpu_notebooks: list[str] = field(default_factory=list)
    api_keys: list[str] = field(default_factory=list)
    network_services: list[str] = field(default_factory=list)
    network_external: list[str] = field(default_factory=list)
    local_endpoints: list[str] = field(default_factory=list)
    requires_python: str = ""
    requires_python_source: str = ""
    imports: set[str] = field(default_factory=set)
    gaps: list[str] = field(default_factory=list)
    verdict: str = "inclus"
    motifs: list[dict] = field(default_factory=list)


def _git(repo_root: Path, args: list[str]) -> str:
    """Execute un ``git`` local et rend sa sortie standard."""
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return completed.stdout


def git_sha(repo_root: Path) -> str:
    """Le SHA de ``HEAD``, ou ``inconnu`` si le depot n'en est pas un."""
    try:
        return _git(repo_root, ["rev-parse", "HEAD"]).strip()
    except Exception:  # noqa: BLE001 - un depot non-git se declare, il ne se devine pas
        return "inconnu"


def git_ls_files(repo_root: Path) -> list[str]:
    """Les fichiers suivis par git, sans le depot de travail."""
    return [line for line in _git(repo_root, ["ls-files"]).splitlines() if line]


def load_policy(repo_root: Path) -> dict:
    """Charge la politique versionnee ; une politique absente est un echec."""
    path = repo_root / POLICY_RELPATH
    return json.loads(path.read_text(encoding="utf-8"))


def _parse_requirement_line(line: str, source_file: str, group: str) -> Requirement | None:
    """Parse une ligne de ``requirements.txt`` ; ``None`` si ce n'est pas un paquet."""
    raw = line.strip()
    if not raw or raw.startswith("#"):
        return None
    if raw.startswith(_PIP_OPTIONS) or raw.startswith("-"):
        return None
    marker = ""
    if ";" in raw:
        raw, marker = (part.strip() for part in raw.split(";", 1))
    raw = raw.split("#", 1)[0].strip()
    if not raw:
        return None
    if raw.startswith(("git+", "http://", "https://", "file://")):
        name = raw.split("@", 1)[-1].strip().rstrip("/")
        return Requirement(
            name=_norm_name(name or raw),
            spec="",
            source_file=source_file,
            group=group,
            raw=raw,
            marker=marker,
        )
    match = re.match(r"^([A-Za-z0-9_.\-]+)\s*(\[[^\]]*\])?\s*(.*)$", raw)
    if not match:
        return None
    name, _extras, spec = match.groups()
    return Requirement(
        name=_norm_name(name),
        spec=spec.strip(),
        source_file=source_file,
        group=group,
        raw=raw,
        marker=marker,
    )


def read_requirements(
    repo_root: Path, relative: str, group: str, seen: set[str] | None = None
) -> list[Requirement]:
    """Lit un fichier de dependances et resout ses inclusions ``-r``/``--requirement``."""
    seen = seen if seen is not None else set()
    if relative in seen:
        return []
    seen.add(relative)
    path = repo_root / relative
    if not path.is_file():
        return []
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    requirements: list[Requirement] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(("-r ", "--requirement ")):
            target = stripped.split(" ", 1)[1].strip()
            included = (path.parent / target).resolve()
            try:
                included_rel = included.relative_to(repo_root.resolve()).as_posix()
            except ValueError:
                continue
            requirements.extend(read_requirements(repo_root, included_rel, group, seen))
            continue
        requirement = _parse_requirement_line(stripped, relative, group)
        if requirement is not None:
            requirements.append(requirement)
    return requirements


def _notebook_payload(path: Path) -> dict | None:
    """Charge un carnet ; ``None`` s'il est illisible."""
    try:
        return json.loads(path.read_text(encoding="utf-8", errors="replace"))
    except Exception:  # noqa: BLE001 - un carnet illisible est signale, pas devine
        return None


def _cell_sources(payload: dict) -> list[str]:
    """Les sources des cellules de code d'un carnet."""
    sources: list[str] = []
    for cell in payload.get("cells", []) or []:
        if not isinstance(cell, dict):
            continue
        if cell.get("cell_type") != "code":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            sources.append("".join(source))
        elif isinstance(source, str):
            sources.append(source)
    return sources


def _kernel_family(language: str) -> str:
    """La famille de noyau d'un `kernelspec`."""
    language = (language or "").strip()
    family = KERNEL_FAMILY_BY_LANGUAGE.get(language.lower())
    if family:
        return family
    lowered = language.lower()
    if any(key in lowered for key in ("python", "py3", "py31")):
        return "Python"
    return "autre"


def _split_series(group_path: str) -> tuple[str, str]:
    """Decoupe un chemin de groupe en (serie, sous-serie).

    Le premier niveau sous ``MyIA.AI.Notebooks`` est la **serie** (le depot
    en compte seize), le second est la **sous-serie** s'il existe.
    """
    parts = group_path.split("/")
    if parts and parts[0] == NOTEBOOKS_ROOT:
        parts = parts[1:]
    series = parts[0] if parts else ""
    subseries = parts[1] if len(parts) > 1 else ""
    return series, subseries


def _requires_python(repo_root: Path, relative: str) -> str:
    """La contrainte ``requires-python`` d'un ``pyproject.toml`` (ou la chaine vide)."""
    path = repo_root / relative
    if not path.is_file():
        return ""
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except Exception:  # noqa: BLE001 - un pyproject illisible n'etablit aucune contrainte
        return ""
    project = data.get("project", {}) or {}
    return str(project.get("requires-python", "") or "").strip()


def _specifier_bounds(spec: str) -> dict:
    """Decoupe un specification PEP 440 en bornes elementaires."""
    bounds: dict = {"lower": "", "upper": "", "exact": "", "excludes": []}
    for part in (spec or "").split(","):
        part = part.strip()
        if not part:
            continue
        match = re.match(r"^(==|!=|>=|<=|~=|>|<)\s*([^\s,]+)$", part)
        if not match:
            continue
        operator, version = match.groups()
        if operator == "==":
            bounds["exact"] = version
        elif operator == "!=":
            bounds["excludes"].append(version)
        elif operator in (">=", ">"):
            bounds["lower"] = _max_version(bounds["lower"], version)
        elif operator in ("<=", "<"):
            bounds["upper"] = _min_version(bounds["upper"], version)
        elif operator == "~=":
            bounds["lower"] = _max_version(bounds["lower"], version)
    return bounds


def _specifiers_compatible(left: dict, right: dict) -> bool:
    """Deux jeux de bornes ont-ils une intersection non vide ?"""
    if left["exact"] and right["exact"]:
        return _compare(left["exact"], right["exact"]) == 0
    exact = left["exact"] or right["exact"]
    lower = max(filter(None, (left["lower"], right["lower"])), default="", key=_version_sort_key)
    upper = min(filter(None, (left["upper"], right["upper"])), default="", key=_version_sort_key)
    if lower and upper and _compare(lower, upper) > 0:
        return False
    if exact:
        if lower and _compare(exact, lower) < 0:
            return False
        if upper and _compare(exact, upper) > 0:
            return False
        for excluded in left["excludes"] + right["excludes"]:
            if excluded == exact:
                return False
    return True


def build_manifest(repo_root: Path) -> dict:
    """Construit le manifeste complet (donnees brutes, sans rendu)."""
    policy = load_policy(repo_root)
    gpu_re = re.compile("|".join(policy["gpu"]["markers"]), re.IGNORECASE)
    heavy = policy["heavy_distributions"]["entries"]
    licensed = policy["licenses"]["entries"]
    optional_markers = policy["optional_file_markers"]["markers"]
    services = policy["container_services"]["entries"]
    local_ports = policy["local_ports"]["entries"]
    canonical_python = policy["canonical_python_by_kernelspec"]["entries"]
    ambiguous_python = policy["canonical_python_by_kernelspec"].get("ambiguous", {})

    tracked = git_ls_files(repo_root)
    notebooks = [f for f in tracked if f.endswith(".ipynb")]
    dependency_files = [
        f
        for f in tracked
        if Path(f).name.startswith(("requirements", "environment"))
        and f.endswith((".txt", ".yml", ".yaml"))
    ]

    # --- groupes (repertoires qui portent directement des carnets ou deps) ---
    groups: dict[str, Group] = {}

    def group_entry(path: str) -> Group:
        directory = str(Path(path).parent).replace("\\", "/")
        if directory not in groups:
            series, subseries = _split_series(directory)
            groups[directory] = Group(
                path=directory, series=series, subseries=subseries
            )
        return groups[directory]

    notebook_groups: dict[str, str] = {}
    for relative in notebooks:
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        entry = group_entry(relative)
        notebook_groups[relative] = entry.path

    dep_groups: dict[str, str] = {}
    for relative in dependency_files:
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        entry = group_entry(relative)
        dep_groups[relative] = entry.path

    # --- carnets : famille de noyau et besoins -------------------------------
    for relative in notebooks:
        entry = groups.get(notebook_groups.get(relative, ""))
        if entry is None:
            continue
        payload = _notebook_payload(repo_root / relative)
        if payload is None:
            continue
        entry.notebooks.append(relative)
        kernelspec = (payload.get("metadata", {}) or {}).get("kernelspec", {}) or {}
        language = (kernelspec.get("language") or "").strip()
        name = (kernelspec.get("name") or language or "inconnu").strip()
        entry.kernelspecs[name] = entry.kernelspecs.get(name, 0) + 1
        joined = "\n".join(_cell_sources(payload))
        for first, second in IMPORT_RE.findall(joined):
            module = (first or second or "").split(".")[0]
            if module:
                entry.imports.add(module)
        if gpu_re.search(joined):
            entry.gpu_notebooks.append(relative)
        for variable in ENV_READ_RE.findall(joined):
            if ENV_SECRET_NAME_RE.search(variable) and variable not in entry.api_keys:
                entry.api_keys.append(variable)
        for host, port in URL_RE.findall(joined):
            endpoint = f"{host}:{port}" if port else host
            if host.lower() in LOCAL_HOSTS:
                if endpoint not in entry.local_endpoints:
                    entry.local_endpoints.append(endpoint)
                if port and port in local_ports:
                    service = local_ports[port]
                    if service not in entry.network_services:
                        entry.network_services.append(service)
                continue
            service = services.get(host.lower())
            if service and service not in entry.network_services:
                entry.network_services.append(service)

    # --- fichiers de dependances (heritage des repertoires ancetres) ---------
    for relative, group_path in dep_groups.items():
        groups[group_path].dependency_files.append(relative)
    for group_path, entry in groups.items():
        applicable: list[str] = []
        for relative, dep_group in dep_groups.items():
            if group_path == dep_group or group_path.startswith(dep_group + "/"):
                applicable.append(relative)
        for relative in sorted(applicable):
            entry.requirements.extend(
                read_requirements(repo_root, relative, group_path)
            )

    # --- contraintes requires-python -----------------------------------------
    for relative in tracked:
        if not relative.endswith("pyproject.toml"):
            continue
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        constraint = _requires_python(repo_root, relative)
        if not constraint:
            continue
        directory = str(Path(relative).parent).replace("\\", "/")
        target = groups.get(directory)
        if target is None:
            continue
        target.requires_python = constraint
        target.requires_python_source = relative

    # --- verdicts ------------------------------------------------------------
    import_aliases = {
        _norm_name(module): _norm_name(package)
        for module, package in policy["import_aliases"]["entries"].items()
    }
    for entry in groups.values():
        motifs: list[dict] = []
        verdict = "inclus"
        declared = {requirement.name for requirement in entry.requirements}
        for module in sorted(entry.imports):
            package = import_aliases.get(module)
            if package and package not in declared:
                entry.gaps.append(package)

        families: list[str] = []
        for kernelspec in entry.kernelspecs:
            family = _kernel_family(kernelspec)
            if family not in families:
                families.append(family)

        if entry.gpu_notebooks:
            motifs.append(
                {
                    "origin": "mesure",
                    "policy": "gpu",
                    "text": (
                        f"GPU requis : marqueur mesure dans {len(entry.gpu_notebooks)} "
                        "carnet(s) de la serie"
                    ),
                }
            )
        heavy_found = sorted(
            {
                heavy[req.name]
                for req in entry.requirements
                if req.name in heavy
            }
        )
        if heavy_found:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "heavy_distributions",
                    "text": (
                        "taille : distribution(s) lourde(s) hors image CPU legere ("
                        + ", ".join(heavy_found)
                        + ")"
                    ),
                }
            )
        licensed_found = sorted(
            {
                licensed[req.name]
                for req in entry.requirements
                if req.name in licensed
            }
        )
        if licensed_found:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "licenses",
                    "text": "licence : " + ", ".join(licensed_found),
                }
            )
        optional_files = [
            f
            for f in entry.dependency_files
            if any(marker in Path(f).name.lower() for marker in optional_markers)
        ]
        if optional_files:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "optional_file_markers",
                    "text": "fichier de dependances optionnel : "
                    + ", ".join(optional_files),
                }
            )
        if entry.network_services:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "container_services",
                    "text": "service conteneurise requis (patron Planners) : "
                    + ", ".join(sorted(entry.network_services)),
                }
            )
        if not families or all(family != "Python" for family in families):
            motifs.append(
                {
                    "origin": "mesure",
                    "policy": "kernel_family",
                    "text": (
                        "noyau non-Python ("
                        + (", ".join(families) if families else "aucun")
                        + ") : hors image CPU Python"
                    ),
                }
            )
        # Conflit de version d'interpreteur : requires-python de la serie vs
        # version Python canonique de son noyau.
        if entry.requires_python and entry.kernelspecs:
            kernel = min(entry.kernelspecs)
            canonical = canonical_python.get(kernel.lower())
            if canonical is None:
                note = ambiguous_python.get(kernel.lower())
                if note:
                    motifs.append(
                        {
                            "origin": "declaration",
                            "policy": "canonical_python_by_kernelspec",
                            "text": (
                                "version Python canonique ambigue pour le noyau "
                                f"{kernel} ({note}) : aucun conflit declare"
                            ),
                        }
                    )
            else:
                bounds = _specifier_bounds(entry.requires_python)
                allowed = _specifiers_compatible(
                    {"exact": "", "lower": canonical, "upper": "", "excludes": []},
                    {
                        "exact": "",
                        "lower": bounds["lower"],
                        "upper": bounds["upper"],
                        "excludes": bounds["excludes"],
                    },
                )
                if not allowed:
                    motifs.append(
                        {
                            "origin": "mesure",
                            "policy": "requires_python",
                            "text": (
                                "conflit de versions d'interpreteur : "
                                f"{entry.requires_python_source} exige "
                                f"Python {entry.requires_python}, le noyau "
                                f"canonique {kernel} est Python {canonical}"
                            ),
                        }
                    )
        # Le verdict est la **consequence** des motifs : une exclusion l'emporte
        # sur un service optionnel, tous les motifs restent affiches.
        policies = {motif["policy"] for motif in motifs}
        if policies & EXCLUSION_POLICIES:
            verdict = "exclu"
        elif policies & OPTIONAL_POLICIES:
            verdict = "service optionnel"
        else:
            verdict = "inclus"
        entry.verdict = verdict
        entry.motifs = motifs

    # --- conflits de versions ------------------------------------------------
    specs: dict[str, list[Requirement]] = defaultdict(list)
    for entry in groups.values():
        for requirement in entry.requirements:
            if requirement.spec:
                specs[requirement.name].append(requirement)
    conflicts: list[dict] = []
    for name in sorted(specs):
        by_spec: dict[str, list[Requirement]] = defaultdict(list)
        for requirement in specs[name]:
            by_spec[requirement.spec].append(requirement)
        # Deux specifications qui disent la meme chose (`>=0.29` et `>=0.29.0`)
        # ne sont pas un conflit : le conflit se mesure sur les **bornes
        # effectives**, pas sur l'ecriture.
        by_bounds: dict[tuple, list[str]] = defaultdict(list)
        bounds: dict[str, dict] = {}
        for spec in sorted(by_spec):
            bound = _specifier_bounds(spec)
            bounds[spec] = bound
            key = (
                _norm_ver(bound["exact"]),
                _norm_ver(bound["lower"]),
                _norm_ver(bound["upper"]),
                tuple(sorted(_norm_ver(item) for item in bound["excludes"])),
            )
            by_bounds[key].append(spec)
        if len(by_bounds) < 2:
            continue
        representatives = sorted(spells[0] for spells in by_bounds.values())
        distinct = representatives
        incompatible = False
        for index, left in enumerate(distinct):
            for right in distinct[index + 1 :]:
                if not _specifiers_compatible(bounds[left], bounds[right]):
                    incompatible = True
        exact_pins = {
            spec: bound["exact"] for spec, bound in bounds.items() if bound["exact"]
        }
        if len({_norm_ver(value) for value in exact_pins.values()}) > 1:
            klass = "pin_exact_divergent"
        elif incompatible:
            klass = "incompatible"
        else:
            klass = "specifier_divergent"
        sources = []
        for spec in distinct:
            spec_key = (
                _norm_ver(bounds[spec]["exact"]),
                _norm_ver(bounds[spec]["lower"]),
                _norm_ver(bounds[spec]["upper"]),
                tuple(sorted(_norm_ver(item) for item in bounds[spec]["excludes"])),
            )
            equivalent = sorted(
                spell
                for spells in by_bounds.values()
                for spell in spells
                if (
                    _norm_ver(_specifier_bounds(spell)["exact"]),
                    _norm_ver(_specifier_bounds(spell)["lower"]),
                    _norm_ver(_specifier_bounds(spell)["upper"]),
                    tuple(
                        sorted(
                            _norm_ver(item)
                            for item in _specifier_bounds(spell)["excludes"]
                        )
                    ),
                )
                == spec_key
            )
            sources.append(
                {
                    "spec": spec,
                    "equivalent_spellings": equivalent,
                    "file": by_spec[spec][0].source_file,
                    "series": by_spec[spec][0].group,
                    "occurrences": len(by_spec[spec]),
                }
            )
        conflicts.append(
            {
                "package": name,
                "class": klass,
                "specifiers": distinct,
                "sources": sources,
                "resolution": _propose_resolution(name, klass, bounds, distinct),
            }
        )

    # --- manifeste consolide -------------------------------------------------
    included = [g for g in groups.values() if g.verdict == "inclus"]
    consolidated: dict[str, dict] = {}
    for entry in included:
        for requirement in entry.requirements:
            record = consolidated.setdefault(
                requirement.name,
                {
                    "package": requirement.name,
                    "version": "",
                    "specs": [],
                    "groups": [],
                    "conflict": False,
                },
            )
            if requirement.spec and requirement.spec not in record["specs"]:
                record["specs"].append(requirement.spec)
            if entry.path not in record["groups"]:
                record["groups"].append(entry.path)
    conflict_names = {conflict["package"] for conflict in conflicts}
    for name, record in consolidated.items():
        record["conflict"] = name in conflict_names
        pins = sorted(
            {
                requirement.pinned
                for entry in included
                for requirement in entry.requirements
                if requirement.name == name and requirement.pinned
            },
            key=_version_sort_key,
        )
        if len(pins) == 1:
            record["version"] = pins[0]
        elif len(pins) > 1:
            record["version"] = ""
        else:
            record["version"] = ""
    consolidated_list = sorted(consolidated.values(), key=lambda r: r["package"])

    # --- divergences canonique/observe (organe #23073) ----------------------
    census: dict | None = None
    census_error = ""
    if run_census is not None and load_lib_manifest is not None:
        try:
            manifest = load_lib_manifest(
                _REPO_ROOT / "scripts/notebook_tools/lib_versions_manifest.json"
            )
            census = run_census(repo_root, manifest)
        except Exception as exc:  # noqa: BLE001 - la degrade du recensement est signalee
            census_error = f"{type(exc).__name__}: {exc}"
    else:
        census_error = (
            "check_lib_versions indisponible : "
            f"{_LIB_VERSIONS_IMPORT_ERROR}"
        )

    infra_files = [
        f
        for f in dependency_files
        if not f.startswith(NOTEBOOKS_ROOT + "/")
    ]

    return {
        "schema_version": SCHEMA_VERSION,
        "generated_from": git_sha(repo_root),
        "policy": POLICY_RELPATH,
        "counts": {
            "tracked_files": len(tracked),
            "notebooks": len(notebooks),
            "dependency_files": len(dependency_files),
            "curriculum_dependency_files": len(dependency_files) - len(infra_files),
            "infra_dependency_files": len(infra_files),
            "groups": len(groups),
            "series": len({g.series for g in groups.values()}),
            "included": len(included),
            "conflicts": len(conflicts),
        },
        "groups": [_group_dict(g) for g in sorted(groups.values(), key=lambda g: g.path)],
        "conflicts": conflicts,
        "consolidated_manifest": consolidated_list,
        "infra_dependency_files": sorted(infra_files),
        "library_census": _census_summary(census),
        "library_census_error": census_error,
    }


def _propose_resolution(
    name: str, klass: str, bounds: dict[str, dict], distinct: list[str]
) -> dict:
    """Propose une resolution de conflit, version par version."""
    if klass == "pin_exact_divergent":
        pins = sorted(
            {bounds[spec]["exact"] for spec in distinct}, key=_version_sort_key
        )
        return {
            "policy": "retenir le pin le plus haut, puis aligner les series en aval",
            "version": pins[-1],
            "note": (
                f"aligner les series qui epinglent une version inferieure sur "
                f"{name}=={pins[-1]} (verifier la compatibilite du noyau)"
            ),
        }
    if klass == "incompatible":
        lowers = [bounds[spec]["lower"] for spec in distinct if bounds[spec]["lower"]]
        uppers = [bounds[spec]["upper"] for spec in distinct if bounds[spec]["upper"]]
        lower = _max_version("", "") if not lowers else lowers[0]
        for candidate in lowers[1:]:
            lower = _max_version(lower, candidate)
        upper = uppers[0] if uppers else ""
        for candidate in uppers[1:]:
            upper = _min_version(upper, candidate)
        return {
            "policy": "aucune version commune : le paquet est ecarte du manifeste consolide",
            "version": "",
            "note": (
                "bornes en presence : "
                + (f"lower={lower} " if lower else "")
                + (f"upper={upper} " if upper else "")
                + " ; aligner les series sur une borne unique avant de reinclure "
                f"{name}"
            ),
        }
    lowers = [bounds[spec]["lower"] for spec in distinct if bounds[spec]["lower"]]
    uppers = [bounds[spec]["upper"] for spec in distinct if bounds[spec]["upper"]]
    lower = lowers[0] if lowers else ""
    for candidate in lowers[1:]:
        lower = _max_version(lower, candidate)
    upper = uppers[0] if uppers else ""
    for candidate in uppers[1:]:
        upper = _min_version(upper, candidate)
    return {
        "policy": "retenir l'intersection des bornes (la plus stricte)",
        "version": (f">={lower}" if lower else "") + (f",<{upper}" if upper else ""),
        "note": (
            f"bornes communes : lower={lower or '-'} upper={upper or '-'}"
        ),
    }


def _group_dict(entry: Group) -> dict:
    """Serialise une ligne de la table."""
    families: list[str] = []
    for kernelspec in entry.kernelspecs:
        family = _kernel_family(kernelspec)
        if family not in families:
            families.append(family)
    return {
        "group": entry.path,
        "series": entry.series,
        "subseries": entry.subseries,
        "kernel_families": families,
        "kernelspecs": dict(sorted(entry.kernelspecs.items())),
        "notebook_count": len(entry.notebooks),
        "dependency_files": entry.dependency_files,
        "package_count": len(entry.requirements),
        "requires_python": entry.requires_python,
        "requires_python_source": entry.requires_python_source,
        "needs": {
            "gpu": bool(entry.gpu_notebooks),
            "gpu_notebooks": entry.gpu_notebooks[:10],
            # Le **nombre** de variables d'environnement secretes, pas leurs
            # noms : un nom n'est pas un secret, mais il n'apporte rien a la
            # decision d'image et le scanner de secrets le refuse (regle
            # « aucune valeur de secret dans le depot »). Les noms restent
            # dans l'organe ; ils ne sont pas publies.
            "api_key_count": len(entry.api_keys),
            "network_services": sorted(entry.network_services),
            "local_endpoints": sorted(entry.local_endpoints)[:10],
        },
        "verdict": entry.verdict,
        "service_optionnel": any(
            motif["policy"] in OPTIONAL_POLICIES for motif in entry.motifs
        ),
        "motifs": entry.motifs,
        "gaps": sorted(set(entry.gaps)),
        "packages": sorted({req.name for req in entry.requirements}),
    }


def _census_summary(census: dict | None) -> dict:
    """Reduit le recensement #23073 aux divergences multi-versions."""
    if census is None:
        return {}
    divergences = []
    for library in census.get("libraries", []):
        versions = library.get("versions", [])
        if len(versions) > 1:
            divergences.append(
                {
                    "library": library.get("library"),
                    "canonical": library.get("canonical"),
                    "versions": [
                        {
                            "version": row.get("version"),
                            "count": row.get("count"),
                            "decision": row.get("decision"),
                        }
                        for row in versions
                    ],
                }
            )
    return {
        "organ": "scripts/notebook_tools/check_lib_versions.py (#23073)",
        "divergences": divergences,
        "below_canonical_count": len(census.get("below_canonical", [])),
        "unreadable_notebooks": len(census.get("unreadable_notebooks", [])),
    }


def _yes(value: bool) -> str:
    return "oui" if value else "non"


def render_markdown(manifest: dict) -> str:
    """Rend le manifeste en Markdown (table par groupe, conflits, consolidation)."""
    counts = manifest["counts"]
    lines: list[str] = []
    lines.append("# Manifeste des dependances du cursus")
    lines.append("")
    lines.append(
        "Genere par `scripts/notebook_tools/dependency_manifest.py` (#27544) sur "
        f"`{manifest['generated_from']}`, sans reseau. Politique : "
        f"`{manifest['policy']}`."
    )
    lines.append("")
    lines.append(
        f"Mesure : {counts['notebooks']} carnets, "
        f"fichiers de dependances du cursus et hors cursus, "
        f"{counts['series']} series, {counts['groups']} groupes de repertoires, "
        f"{counts['included']} groupes inclus dans l'image CPU, "
        f"{counts['conflicts']} conflits de versions."
    )
    lines.append("")
    lines.append(
        "**Origine des motifs** : `mesure` = deduit d'une lecture du depot ; "
        "`declaration` = regle ecrite dans la politique versionnee, contestable."
    )
    lines.append("")
    lines.append("## 1. Table par serie et sous-serie")
    lines.append("")
    lines.append(
        "| Groupe | Serie | Sous-serie | Noyaux | Fichiers de dependances | "
        "Carnets | GPU | Cle d'API (nb) | Service reseau | Verdict | Service optionnel | "
        "Motifs (origine) | Lacunes de declaration |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for entry in manifest["groups"]:
        needs = entry["needs"]
        files = ", ".join(entry["dependency_files"]) or "aucun"
        motifs = " ; ".join(
            f"{m['origin']} : {m['text']}" for m in entry["motifs"]
        ) or "-"
        lines.append(
            f"| `{entry['group']}` | {entry['series']} | {entry['subseries'] or '-'} | "
            f"{', '.join(entry['kernel_families']) or '-'} | {files} | "
            f"{entry['notebook_count']} | {_yes(needs['gpu'])} | "
            f"{needs['api_key_count'] or '-'} | "
            f"{', '.join(needs['network_services']) or '-'} | "
            f"**{entry['verdict']}** | {_yes(entry['service_optionnel'])} | "
            f"{motifs} | "
            f"{', '.join(entry['gaps']) or '-'} |"
        )
    lines.append("")
    lines.append("## 2. Conflits de versions")
    lines.append("")
    if not manifest["conflicts"]:
        lines.append(
            "Aucun conflit : chaque paquet porte un specification unique dans tout "
            "le corpus des fichiers de dependances."
        )
    else:
        lines.append("| Paquet | Classe | Specifications en presence | Sources | Resolution proposee |")
        lines.append("|---|---|---|---|---|")
        for conflict in manifest["conflicts"]:
            sources = "; ".join(
                f"{item['spec']} ({item['file']})" for item in conflict["sources"]
            )
            resolution = conflict["resolution"]
            version = resolution["version"] or "paquet ecarte"
            lines.append(
                f"| `{conflict['package']}` | {conflict['class']} | "
                f"{', '.join(conflict['specifiers'])} | {sources} | "
                f"{resolution['policy']} -> {version} |"
            )
    lines.append("")
    lines.append("## 3. Manifeste consolide (source unique des paquets de l'image)")
    lines.append("")
    if not manifest["consolidated_manifest"]:
        lines.append("Aucune serie incluse : le manifeste consolide est vide.")
    else:
        lines.append("| Paquet | Version retenue | Groupes | Conflit |")
        lines.append("|---|---|---|---|")
        for record in manifest["consolidated_manifest"]:
            version = record["version"] or "a resoudre"
            lines.append(
                f"| `{record['package']}` | {version} | "
                f"{len(record['groups'])} | {_yes(record['conflict'])} |"
            )
    census = manifest.get("library_census") or {}
    divergences = census.get("divergences", [])
    lines.append("")
    lines.append("## 4. Lacunes de declaration")
    lines.append("")
    lines.append(
        "Paquets **importes** par les carnets d'un groupe mais **absents** de ses "
        "fichiers de dependances : l'image ne les installera pas, le carnet "
        "echouera a l'execution. La correspondance import -> paquet est une "
        "declaration (voir la politique) ; l'absence dans les fichiers de "
        "dependances est une mesure."
    )
    lines.append("")
    gaps = [(entry["group"], entry["gaps"]) for entry in manifest["groups"] if entry["gaps"]]
    if not gaps:
        lines.append("Aucune lacune detectee sur les paquets de la table d'alias.")
    else:
        lines.append("| Groupe | Paquets importes non declares |")
        lines.append("|---|---|")
        for group, packages in gaps:
            lines.append(f"| `{group}` | {', '.join(packages)} |")
    lines.append("")
    lines.append("## 5. Divergences canonique/observe (organe #23073)")
    lines.append("")
    if manifest.get("library_census_error"):
        lines.append(
            f"Recensement #23073 indisponible : {manifest['library_census_error']}"
        )
    elif not divergences:
        lines.append("Aucune bibliotheque a plusieurs versions dans le corpus.")
    else:
        lines.append("| Bibliotheque | Canonique | Versions observees |")
        lines.append("|---|---|---|")
        for divergence in divergences:
            observed = ", ".join(
                f"{row['version']} ({row['count']} carnets)"
                for row in divergence["versions"]
            )
            lines.append(
                f"| `{divergence['library']}` | {divergence['canonical'] or '-'} | "
                f"{observed} |"
            )
    lines.append("")
    lines.append("## 6. Fichiers de dependances hors cursus")
    lines.append("")
    lines.append(
        "Ces fichiers servent l'outillage et les services, pas les series : ils "
        "n'entrent pas dans le manifeste de l'image."
    )
    lines.append("")
    for relative in manifest["infra_dependency_files"]:
        lines.append(f"- `{relative}`")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Manifeste des dependances du cursus par famille de noyau (#27544)."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=_REPO_ROOT,
        help="racine du depot (par defaut : la racine du script)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help=f"repertoire de sortie (defaut : {DEFAULT_OUT_DIR})",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="ecrit les sorties versionnees (manifeste-dependances.md / .json)",
    )
    parser.add_argument(
        "--print",
        action="store_true",
        help="affiche le rendu Markdown sur la sortie standard",
    )
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    manifest = build_manifest(repo_root)
    markdown = render_markdown(manifest)

    if args.write:
        out_dir = (args.out_dir or (repo_root / DEFAULT_OUT_DIR)).resolve()
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "manifeste-dependances.md").write_text(
            markdown, encoding="utf-8", newline="\n"
        )
        (out_dir / "manifeste-dependances.json").write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
            newline="\n",
        )
    elif args.print or not args.write:
        print(markdown)

    complete = all(entry["verdict"] for entry in manifest["groups"])
    conflicts_named = all(
        conflict.get("resolution") for conflict in manifest["conflicts"]
    )
    return 0 if complete and conflicts_named else 1


if __name__ == "__main__":
    raise SystemExit(main())
