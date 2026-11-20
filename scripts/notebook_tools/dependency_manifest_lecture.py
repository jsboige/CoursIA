#!/usr/bin/env python
"""Module lecture de l'organe manifeste des dependances (#27544).

Scission du 20/11 (#26364, cliquet de taille des scripts) : le module
d'origine depassait le plafond des scripts neufs. Les responsabilites
sont separees, la facade `dependency_manifest.py` garde le chemin
d'appel et re-expose l'API.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tomllib
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


SCHEMA_VERSION = 2
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

#: Appels reseau explicites. La liste couvre les entrees HTTP usuelles ;
#: un appel dont la cible n'est pas lisible dans la ligne n'etablit rien :
#: il est compte comme appel a cible dynamique.
SERVICE_CALL_RE = re.compile(
    r"(?:requests|httpx|urllib\.request|socket\.socket|aiohttp)"
    r"\.(?:get|post|put|request|connect|urlopen)\s*\(",
    re.IGNORECASE,
)
URL_RE = re.compile(r"https?://([A-Za-z0-9_.\-]+)(?::(\d+))?")
#: URL dont le port est une constante interpolee (``f"http://localhost:{PORT}"``).
URL_TEMPLATE_RE = re.compile(
    r"https?://([A-Za-z0-9_.\-]+):\{([A-Za-z_][A-Za-z0-9_]*)\}"
)
#: Constante numerique d'un carnet (``FD_API_PORT = 8200``) : elle rend le
#: port lisible quand l'URL l'interpole au lieu de l'ecrire en dur.
INT_CONST_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(\d{1,5})\s*$", re.MULTILINE
)
LOCAL_HOSTS = {"localhost", "127.0.0.1", "0.0.0.0", "::1"}

#: Suffixes des fichiers de code **compagnons** d'un carnet : un carnet peut
#: appeler un moteur vivant dans un fichier de sa serie (le pont Fast Downward
#: en C#). Le service que ce fichier appelle est alors un besoin du carnet.
COMPANION_CODE_SUFFIXES = (".py", ".cs")
#: Mention d'un fichier de code dans une source : `X.cs`, `x_y.py` ou un
#: nom de module en `snake_case` (le pont Cite sans son extension).
CODE_MENTION_RE = re.compile(
    r"[A-Za-z0-9_\-]{3,}\.(?:py|cs)\b|\b[a-z0-9]+(?:_[a-z0-9]+)+\b"
)
#: Taille maximale lue pour un fichier compagnon : au-dela, le fichier n'est
#: pas un moteur de carnet, il ne doit pas peser sur la mesure.
COMPANION_MAX_BYTES = 512 * 1024

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


def _version_organ():
    """L'organe natif des versions, resolu au moment de l'appel.

    La facade `dependency_manifest.py` re-expose `version_key` : un patch
    pose sur la facade (le test du repli de normalisation s'appuie dessus)
    doit continuer d'agir sur la lecture. La resolution se fait donc au
    moment de l'appel, et non au moment de l'import.
    """
    facade = sys.modules.get("dependency_manifest")
    if facade is not None:
        return getattr(facade, "version_key", version_key)
    return version_key


def _version_sort_key(version: str) -> tuple:
    """Tri de versions delegue a l'organe natif quand il est disponible."""
    organ = _version_organ()
    if organ is not None:
        try:
            return organ(version)
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


#: Normalisations de version faites en repli local (organe natif absent ou en
#: erreur). Le repli compare les chaines brutes : il invente des conflits.
#: Le compteur est remis a zero au debut de chaque construction de manifeste.
_VERSION_FALLBACK_CALLS: list[str] = []


def _norm_ver(version: str) -> str:
    """Forme canonique d'une version : ``1.0`` et ``1.0.0`` ne font qu'un.

    La normalisation passe par l'organe natif des versions (#23073) : deux
    chaines differentes qui designent la meme version ne sont pas un conflit.

    Si l'organe natif est absent, le repli compare les chaines brutes et
    **invente** des conflits (`numpy>=0.29` contre `numpy>=0.29.0`). Le repli
    est donc compte et divilogue : un conflit mesure en repli est suspect.
    """
    if not version:
        return ""
    organ = _version_organ()
    if organ is not None:
        try:
            return repr(organ(version))
        except Exception:  # noqa: BLE001,S110 - repli local, l'organe natif reste l'original
            pass
    _VERSION_FALLBACK_CALLS.append(version)
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
    requires_python_constraints: list[dict] = field(default_factory=list)
    kernel_families: list[str] = field(default_factory=list)
    kernel_families_source: str = ""
    imports: set[str] = field(default_factory=set)
    gaps: list[str] = field(default_factory=list)
    service_calls: int = 0
    dynamic_service_calls: int = 0
    companion_files: list[str] = field(default_factory=list)
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
    """Les fichiers suivis par git, sans le depot de travail.

    ``git ls-files`` **C-quote** les chemins non-ASCII par defaut : le chemin
    ressort entre guillemets avec des echappements octaux
    (``"Cr\\303\\251ateur"``), ne finit donc plus par son extension, et
    disparait de l'inventaire. On neutralise le quoting
    (``core.quotePath=false``) et on lit la sortie NUL-separee : un chemin
    accentue reste un chemin.
    """
    output = _git(repo_root, ["-c", "core.quotePath=false", "ls-files", "-z"])
    return [path for path in output.split("\0") if path]


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


def _descendant_families(group_path: str, groups: dict) -> list[str]:
    """Les familles de noyau des sous-repertoires d'un groupe.

    Un repertoire qui ne porte **directement** aucun carnet porte neanmoins
    des dependances : sa famille de noyau n'est pas « non-Python », elle est
    celle de ses sous-repertoires. La lire, c'est une mesure ; la supposer
    absente, c'est inventer une exclusion.
    """
    families: list[str] = []
    prefix = group_path + "/"
    for other in groups.values():
        if not other.path.startswith(prefix):
            continue
        for kernelspec in other.kernelspecs:
            family = _kernel_family(kernelspec)
            if family not in families:
                families.append(family)
    return families


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


def _python_constraints(repo_root: Path, relative: str) -> list[tuple[str, str]]:
    """Les contraintes d'interpreteur declarees par un ``pyproject.toml``.

    Deux champs portent une contrainte, et ils ne disent pas la meme chose :
    ``project.requires-python`` est le **plancher d'installation** du
    paquet, ``tool.coursia.pinned_env.requires-python`` est l'**env de la
    serie** -- celle dans laquelle les carnets tournent reellement. Cette
    derniere prime sur la premiere (cf. ``check_kernel_drift``), et c'est
    elle qu'il faut confronter au noyau canonique : lire la seule premiere
    ferait passer pour compatible un env que la serie n'utilise pas.

    Rend ``[(champ, contrainte)]`` ; une liste vide si le fichier est absent
    ou illisible -- une absence de declaration n'etablit aucune contrainte.
    """
    path = repo_root / relative
    if not path.is_file():
        return []
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except Exception:  # noqa: BLE001 - un pyproject illisible n'etablit aucune contrainte
        return []
    found: list[tuple[str, str]] = []
    project = data.get("project", {}) or {}
    value = str(project.get("requires-python", "") or "").strip()
    if value:
        found.append(("project.requires-python", value))
    pinned = (data.get("tool", {}) or {}).get("coursia", {}) or {}
    pinned = pinned.get("pinned_env", {}) or {}
    value = str(pinned.get("requires-python", "") or "").strip()
    if value:
        found.append(("tool.coursia.pinned_env.requires-python", value))
    return found


def _int_constants(source: str) -> dict[str, str]:
    """Les constantes numeriques d'une source (``FD_API_PORT = 8200``)."""
    return {name: value for name, value in INT_CONST_RE.findall(source)}


def _endpoints(source: str) -> list[tuple[str, str]]:
    """Les ``(hote, port)`` vises par une source.

    Le port est lu soit en dur dans l'URL, soit dans une constante
    interpolee que la source declare. Une URL a port non resolu est rendue
    avec un port vide : elle est comptee comme endpoint local sans service
    (le service n'est pas identifiable), jamais comme un port devine.
    """
    constants = _int_constants(source)
    found: list[tuple[str, str]] = []
    for match in URL_RE.finditer(source):
        host, port = match.group(1), match.group(2)
        if not port and source[match.end() :].startswith(":{"):
            # URL a port interpole : le motif de gabarit le traite.
            continue
        found.append((host, port))
    for host, name in URL_TEMPLATE_RE.findall(source):
        value = constants.get(name, "")
        if value:
            found.append((host, value))
    return found


def _service_calls(source: str) -> tuple[int, int]:
    """Les appels de service d'une source : ``(total, cible non identifiable)``.

    Un appel est a **cible non identifiable** quand sa ligne ne porte aucune
    URL : la cible est alors une variable, le lecteur ne peut pas nommer le
    service. C'est une mesure, pas une supposition.
    """
    total = 0
    dynamic = 0
    lines = source.splitlines()
    for index, line in enumerate(lines):
        hits = SERVICE_CALL_RE.findall(line)
        if not hits:
            continue
        total += len(hits)
        if "http" not in line.lower():
            dynamic += len(hits)
    return total, dynamic


def _companion_sources(repo_root: Path, names: set[str]) -> list[tuple[str, str]]:
    """Les sources des fichiers de code **compagnons** cites par un carnet.

    Un carnet appelle parfois son moteur dans un fichier de sa serie (le pont
    Fast Downward en C#). Le service que ce fichier appelle est un besoin du
    carnet, pas un detail du fichier : sans cette lecture, le manifeste
    declare une serie autonome alors qu'elle appelle un service du depot.

    Rend ``[(chemin relatif, source)]`` ; un fichier absent, trop gros ou
    illisible est ignore -- il n'etablit alors aucun besoin.
    """
    found: list[tuple[str, str]] = []
    for relative in sorted(names):
        path = repo_root / relative
        try:
            if not path.is_file() or path.stat().st_size > COMPANION_MAX_BYTES:
                continue
            found.append((relative, path.read_text(encoding="utf-8", errors="replace")))
        except OSError:
            continue
    return found


