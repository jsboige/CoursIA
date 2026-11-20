"""Eligibility des carnets Python pour une execution dans le navigateur (Pyodide).

Ce script classe les carnets Python actifs du depot selon leur eligibilite a
JupyterLite. Un carnet est eligible si, et seulement si :

1. il ne demande aucun GPU ;
2. il ne demande aucune cle d'API ;
3. il ne demande aucun service reseau ;
4. tous ses imports sont soit dans la bibliotheque standard, soit des modules
   locaux du depot, soit des paquets Pyodide, soit des paquets PyPI qui
   existent en roue pure (``py3-none-any``).

Le critere est ecrit ici, en un seul endroit, pour etre relu a chaque
regeneration du site : c'est le fichier qui fait foi, pas une liste maintenue
a la main.

Sorties : tableau Markdown (par serie) et JSON detaille (par carnet).

Sources utilisees, toutes locales ou explicitement demandees :

- ``git ls-files`` : liste des carnets suivis (aucun acces reseau) ;
- le fichier ``pyodide-lock.json`` de la distribution Pyodide : liste
  autoritaire des paquets disponibles dans le navigateur, avec leur version ;
- le cache ``pyodide-pypi-wheels.json`` versionne : resultat des sondes PyPI
  sur la presence d'une roue pure (sonde optionnelle, ``--probe-pypi``).

Usage :

    python scripts/notebook_tools/pyodide_eligibility.py --format md
    python scripts/notebook_tools/pyodide_eligibility.py --format json --out table.json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

# ---------------------------------------------------------------------------
# Regles du critere (source de verite unique)
# ---------------------------------------------------------------------------

#: Paquets dont l'execution dans le navigateur est impossible sans accelerateur.
GPU_PACKAGES: Set[str] = {
    "torch",
    "tensorflow",
    "tensorflow_gpu",
    "jax",
    "jaxlib",
    "cupy",
    "cupy-cuda12x",
    "onnxruntime-gpu",
    "pynvml",
    "cupy-cuda11x",
}

#: Modules dont l'import suffit a disqualifier un carnet pour GPU.
GPU_MODULES: Set[str] = {
    "torch",
    "tensorflow",
    "jax",
    "cupy",
    "pynvml",
    "onnxruntime",
}

#: Correspondance nom de module importe -> nom de paquet PyPI. Les entrees de
#: ce dictionnaire sont declarees, pas mesurees : elles traduisent une
#: convention de nommage, pas un etat du depot.
MODULE_TO_PACKAGE: Dict[str, str] = {
    "PIL": "pillow",
    "cv2": "opencv-python",
    "skimage": "scikit-image",
    "sklearn": "scikit-learn",
    "sklearn.linear_model": "scikit-learn",
    "sklearn.metrics": "scikit-learn",
    "sklearn.model_selection": "scikit-learn",
    "sklearn.preprocessing": "scikit-learn",
    "sklearn.cluster": "scikit-learn",
    "sklearn.decomposition": "scikit-learn",
    "sklearn.datasets": "scikit-learn",
    "sklearn.ensemble": "scikit-learn",
    "sklearn.neighbors": "scikit-learn",
    "sklearn.tree": "scikit-learn",
    "sklearn.feature_extraction": "scikit-learn",
    "sklearn.utils": "scikit-learn",
    "yaml": "pyyaml",
    "bs4": "beautifulsoup4",
    "dotenv": "python-dotenv",
    "serial": "pyserial",
    "attr": "attrs",
    "dateutil": "python-dateutil",
    "jwt": "pyjwt",
    "OpenSSL": "pyopenssl",
    "Crypto": "pycryptodome",
    "docx": "python-docx",
    "pptx": "python-pptx",
    "fitz": "pymupdf",
    "z3": "z3-solver",
    "lxml": "lxml",
    "mpl_toolkits": "matplotlib",
    "IPython": "ipython",
    "google": "google-api-python-client",
    "azure": "azure",
    "torchvision": "torchvision",
    "torchaudio": "torchaudio",
    "psycopg2": "psycopg2-binary",
}

#: Modules Python dont l'import signale une dependence reseau ou systeme.
#: Hotes dont l'occurrence est une **reference** et non un appel : une URL de
#: documentation, un exemple de docstring, un URI de schema. Leur presence ne
#: rend pas un carnet dependant d'un service reseau.
DOC_HOSTS: Set[str] = {
    "example.org",
    "example.com",
    "example.net",
    "www.example.com",
    "github.com",
    "www.github.com",
    "raw.githubusercontent.com",
    "docs.python.org",
    "pypi.org",
    "www.w3.org",
    "schema.org",
    "creativecommons.org",
    "spdx.org",
    "www.gnu.org",
    "arxiv.org",
    "doi.org",
}

#: Jeton qui montre qu'une URL est **appelee** (et non simplement citee).
NET_CALL_TOKENS: Tuple[str, ...] = (
    "requests.", "httpx.", "urlopen", "urllib.", "socket.", "aiohttp",
    "read_csv", "read_json", "read_html", "urlretrieve", "download",
    "fetch(", "get(", "post(", "put(", "open(", "Client(",
)

#: Prefixes de langages de requetes qui citent un URI sans l'appeler.
PREFIX_LINE_RE = re.compile(r"^\s*(?:PREFIX|@prefix|BASE)\b", re.IGNORECASE)

NETWORK_MODULES: Set[str] = {
    "requests",
    "httpx",
    "aiohttp",
    "urllib3",
    "socket",
    "ftplib",
    "smtplib",
    "telnetlib",
    "xmlrpc",
    "boto3",
    "paramiko",
    "pyserial",
}

#: Modules dont l'import signale un acces disque ou une dependance native
#: qui n'a pas de sens dans un navigateur (pas un motif d'exclusion a part
#: entiere, mais un signal de refus "import absent" via la sonde de roue pure).
NATIVE_HINT_MODULES: Set[str] = {
    "multiprocessing",
    "sqlite3",
    "win32api",
    "pywinauto",
    "psutil",
    "resource",
    "fcntl",
    "signal",
}

#: Motifs d'exclusion, dans l'ordre de presentation du rapport.
MOTIFS: Tuple[str, ...] = ("gpu", "cle", "reseau", "import_absent")

#: Nom du fichier companion qui porte le detail carnet par carnet des refus.
REFUS_TSV_NAME = "pyodide-refus.tsv"

#: Prefixes de noms de variables d'environnement traites comme des cles.
API_KEY_PATTERN = re.compile(
    r"(API_?KEY|_KEY$|^KEY$|TOKEN|SECRET|PASSWORD|CREDENTIAL|ACCESS_KEY)",
    re.IGNORECASE,
)

#: Expressions d'import, en-tete de cellule ou en fin de ligne.
IMPORT_FROM_RE = re.compile(r"^\s*from\s+([A-Za-z_][A-Za-z0-9_.]*)\s+import\b")
IMPORT_PLAIN_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)")
URL_RE = re.compile(r"https?://([A-Za-z0-9_.:-]+)")
GETENV_RE = re.compile(
    r"""(?:os\.getenv|os\.environ\.get|environ\.get|os\.environ)\s*[\(\[]\s*["']([A-Za-z0-9_]+)["']"""
)
ENVIRON_INDEX_RE = re.compile(r"""environ\s*\[\s*["']([A-Za-z0-9_]+)["']""")
LOCALHOST_RE = re.compile(r"(?:localhost|127\.0\.0\.1)\D{0,10}(\d{2,5})")
#: Lectures de fichiers du depot : information pour le choix du lot execute
#: dans le navigateur (un carnet qui lit un CSV n'est pas autosuffisant).
FILE_READ_RE = re.compile(
    r"""(?:open|read_csv|read_json|read_parquet|read_excel|load|np\.load|loadtxt|"
    r"genfromtxt|to_csv|savefig)\s*\(\s*[\"']([^\"']+)[\"']""")


def repo_root() -> Path:
    """Racine du depot (deux niveaux au-dessus de scripts/notebook_tools/)."""
    return Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# Lecture du depot
# ---------------------------------------------------------------------------


def git_ls_files(root: Path, patterns: Sequence[str]) -> List[str]:
    """Fichiers suivis par git correspondant aux motifs donnes."""
    args = ["git", "-C", str(root), "ls-files", "-z", "--"] + list(patterns)
    res = subprocess.run(args, capture_output=True, text=True, encoding="utf-8",
                         errors="replace", check=False)
    if res.returncode != 0:
        raise RuntimeError("git ls-files a echoue : %s" % res.stderr.strip()[:400])
    return [p for p in res.stdout.split("\0") if p]


def is_active_notebook(path: str) -> bool:
    """Un carnet actif est un carnet suivi, hors sortie, traduction et archive.

    Le perimetre reprend celui du census de l'Epic #27543 : hors ``_output``,
    hors ``_en``, hors ``_archive``.
    """
    name = path.replace("\\", "/")
    if name.endswith("_output.ipynb"):
        return False
    if "/_archive/" in name or name.startswith("_archive/"):
        return False
    if re.search(r"/_en/", name) or name.endswith("_en.ipynb"):
        return False
    if ".ipynb_checkpoints" in name:
        return False
    return True


def series_of(path: str) -> str:
    """Serie d'appartenance d'un carnet (troisieme composante du chemin)."""
    parts = path.replace("\\", "/").split("/")
    if len(parts) > 3 and parts[0] == "MyIA.AI.Notebooks":
        return parts[2]
    return "/".join(parts[:2]) if len(parts) > 1 else parts[0]


def subseries_of(path: str) -> str:
    """Sous-serie d'un carnet, ou la serie elle-meme si elle n'en a pas."""
    parts = path.replace("\\", "/").split("/")
    if len(parts) > 3 and parts[0] == "MyIA.AI.Notebooks":
        return parts[3] if len(parts) > 4 else parts[2]
    return series_of(path)


# ---------------------------------------------------------------------------
# Analyse d'un carnet
# ---------------------------------------------------------------------------


@dataclass
class NotebookVerdict:
    """Verdict d'eligibilite pour un carnet."""

    path: str
    series: str
    subseries: str
    kernel: str
    eligible: bool
    motifs: List[str] = field(default_factory=list)
    gpu_detail: List[str] = field(default_factory=list)
    key_detail: List[str] = field(default_factory=list)
    network_detail: List[str] = field(default_factory=list)
    missing_imports: List[str] = field(default_factory=list)
    pyodide_packages: List[str] = field(default_factory=list)
    pure_wheels: List[str] = field(default_factory=list)
    stdlib_count: int = 0
    local_count: int = 0
    local_hors_serie: List[str] = field(default_factory=list)
    local_files: List[str] = field(default_factory=list)
    code_cells: int = 0
    error: Optional[str] = None

    def to_dict(self) -> Dict[str, object]:
        return {
            "path": self.path,
            "series": self.series,
            "subseries": self.subseries,
            "kernel": self.kernel,
            "eligible": self.eligible,
            "motifs": sorted(set(self.motifs)),
            "gpu_detail": sorted(set(self.gpu_detail)),
            "key_detail": sorted(set(self.key_detail)),
            "network_detail": sorted(set(self.network_detail)),
            "missing_imports": sorted(set(self.missing_imports)),
            "pyodide_packages": sorted(set(self.pyodide_packages)),
            "pure_wheels": sorted(set(self.pure_wheels)),
            "stdlib_count": self.stdlib_count,
            "local_count": self.local_count,
            "local_hors_serie": sorted(set(self.local_hors_serie)),
            "local_files": sorted(set(self.local_files)),
            "code_cells": self.code_cells,
            "error": self.error,
        }


def notebook_sources(nb: Dict[str, object]) -> List[str]:
    """Textes des cellules de code d'un notebook."""
    out: List[str] = []
    for cell in nb.get("cells") or []:
        if not isinstance(cell, dict):
            continue
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source")
        if isinstance(src, list):
            out.append("".join(src))
        elif isinstance(src, str):
            out.append(src)
    return out


def top_level_module(module: str) -> str:
    """Nom de paquet de premier niveau d'un module importe."""
    return module.split(".")[0]


def collect_imports(sources: Iterable[str]) -> Set[str]:
    """Modules importes par les cellules de code."""
    found: Set[str] = set()
    for text in sources:
        for line in text.splitlines():
            m = IMPORT_FROM_RE.match(line)
            if m:
                found.add(m.group(1))
                continue
            m = IMPORT_PLAIN_RE.match(line)
            if m:
                found.add(m.group(1))
    return found


def local_modules(root: Path, notebook: Path, series_root: Path) -> Tuple[Set[str], Set[str]]:
    """Modules Python presents dans la serie du carnet, et ailleurs dans le depot.

    Un carnet est souvent accompagne de ses helpers ; ces modules sont
    embarquables dans le bundle JupyterLite et ne sont pas un refus.

    Retourne le couple ``(modules de la serie, modules du depot hors serie)``.
    Un module de la serie est embarquable tel quel ; un module trouve
    ailleurs dans le depot existe mais n'est pas livre par defaut, il est
    signale a part plutot que traite comme un import absent.
    """
    in_series: Set[str] = set()
    for directory in {notebook.parent, notebook.parent.parent, notebook.parent.parent.parent}:
        if not directory.is_dir():
            continue
        try:
            for entry in directory.iterdir():
                if entry.is_file() and entry.suffix == ".py":
                    in_series.add(entry.stem)
        except OSError:
            continue
    try:
        rel = notebook.relative_to(series_root)
        depth = len(rel.parts) - 1
    except ValueError:
        depth = 0
    for parent in list(notebook.parents)[: depth + 1]:
        if not parent.is_dir():
            continue
        try:
            for entry in parent.rglob("*.py"):
                in_series.add(entry.stem)
        except OSError:
            continue
    elsewhere = repo_python_modules(root) - in_series
    return in_series, elsewhere


_REPO_MODULE_CACHE: Dict[str, Set[str]] = {}


def repo_python_modules(root: Path) -> Set[str]:
    """Noms de modules Python presents dans le depot (index unique, mis en cache)."""
    key = str(root)
    if key in _REPO_MODULE_CACHE:
        return _REPO_MODULE_CACHE[key]
    names: Set[str] = set()
    skip = {".git", ".tmp", "node_modules", "__pycache__", ".venv", "venv",
            ".pytest_cache", ".mypy_cache", "build", "dist", ".claude"}
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in skip and not d.startswith(".")]
        for name in files:
            if name.endswith(".py"):
                names.add(name[:-3])
    _REPO_MODULE_CACHE[key] = names
    return names


def load_pyodide_lock(path: Optional[Path]) -> Tuple[Dict[str, str], Dict[str, object]]:
    """Charge ``pyodide-lock.json`` : paquets Pyodide et versions.

    Retourne le dictionnaire ``nom de paquet -> version`` et les metadonnees
    du lock (version de Pyodide, date). Un lock absent ne rend pas le script
    muet : il rend les paquets Pyodide inconnus, et le rapport le dit.
    """
    if path is None or not path.is_file():
        return {}, {"lock": None, "note": "aucun pyodide-lock.json fourni"}
    with path.open(encoding="utf-8") as fh:
        data = json.load(fh)
    packages = data.get("packages") or {}
    out: Dict[str, str] = {}
    for name, meta in packages.items():
        version = meta.get("version") if isinstance(meta, dict) else None
        out[name] = version or ""
    lock_meta = data.get("info") if isinstance(data.get("info"), dict) else {}
    info = {
        "lock": str(path),
        "pyodide_version": lock_meta.get("version") or data.get("version") or "",
        "abi_version": lock_meta.get("abi_version") or "",
        "python": lock_meta.get("python") or "",
        "arch": lock_meta.get("arch") or "",
        "platform": lock_meta.get("platform") or "",
        "package_count": len(out),
    }
    return out, info


def lock_description(lock_info: Dict[str, object]) -> str:
    """Decrit la source de verite des paquets, telle que le lock la porte.

    Le fichier `pyodide-lock.json` ne porte pas toujours une version de
    distribution : on rend donc les metadonnees qu'il contient reellement
    (ABI, version de Python, cible), plutot qu'une version supposee.
    """
    bits: List[str] = []
    if lock_info.get("pyodide_version"):
        bits.append("distribution %s" % lock_info["pyodide_version"])
    if lock_info.get("abi_version"):
        bits.append("ABI %s" % lock_info["abi_version"])
    if lock_info.get("python"):
        bits.append("Python %s" % lock_info["python"])
    if lock_info.get("arch"):
        bits.append(str(lock_info["arch"]))
    if lock_info.get("platform"):
        bits.append(str(lock_info["platform"]))
    return ", ".join(bits) if bits else "metadonnees absentes"


def load_wheel_cache(path: Optional[Path]) -> Dict[str, Dict[str, object]]:
    """Charge le cache des sondes PyPI (presence d'une roue pure)."""
    if path is None or not path.is_file():
        return {}
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)


def probe_pypi(package: str, cache: Dict[str, Dict[str, object]], timeout: float = 20.0) -> Dict[str, object]:
    """Sonde PyPI : le paquet existe-t-il en roue pure ?

    Le resultat est memorise dans le cache : la sonde est faite une fois par
    paquet, puis le site se regenere sans reseau.
    """
    import urllib.error
    import urllib.request

    url = "https://pypi.org/pypi/%s/json" % package
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as exc:  # reseau indisponible : verdict neutre
        return {"pure_wheel": False, "checked": "", "error": str(exc)[:200]}
    files = (data.get("urls") or [])
    pure = any(str(f.get("filename", "")).endswith("-py3-none-any.whl") or
               str(f.get("filename", "")).endswith("-py2.py3-none-any.whl")
               for f in files)
    return {
        "pure_wheel": bool(pure),
        "checked": data.get("info", {}).get("upload_time_iso_8601", "")[:10],
        "version": data.get("info", {}).get("version", ""),
        "error": "",
    }


def analyse_notebook(
    root: Path,
    rel_path: str,
    pyodide_packages: Dict[str, str],
    wheel_cache: Dict[str, Dict[str, object]],
    stdlib_names: Set[str],
    probe: bool,
) -> NotebookVerdict:
    """Applique le critere a un carnet et rend son verdict."""
    path = root / rel_path
    verdict = NotebookVerdict(
        path=rel_path,
        series=series_of(rel_path),
        subseries=subseries_of(rel_path),
        kernel="",
        eligible=False,
    )
    try:
        with path.open(encoding="utf-8") as fh:
            nb = json.load(fh)
    except Exception as exc:
        verdict.error = "lecture impossible : %s" % str(exc)[:160]
        verdict.motifs.append("import_absent")
        return verdict

    ks = (nb.get("metadata") or {}).get("kernelspec") or {}
    verdict.kernel = ks.get("name") or ""

    sources = notebook_sources(nb)
    imports = collect_imports(sources)
    series_root = root / "MyIA.AI.Notebooks" / verdict.series
    local, elsewhere = local_modules(root, path, series_root)

    for module in sorted(imports):
        top = top_level_module(module)
        if top in stdlib_names:
            verdict.stdlib_count += 1
            continue
        if top in local or module in local:
            verdict.local_count += 1
            continue
        if top in elsewhere:
            verdict.local_count += 1
            verdict.local_hors_serie.append(module)
            continue
        if top in GPU_MODULES or top in GPU_PACKAGES:
            verdict.motifs.append("gpu")
            verdict.gpu_detail.append(module)
            continue
        package = MODULE_TO_PACKAGE.get(top, top)
        if package in pyodide_packages:
            verdict.pyodide_packages.append("%s==%s" % (package, pyodide_packages[package]))
            continue
        entry = wheel_cache.get(package)
        if entry is None and probe:
            entry = probe_pypi(package, wheel_cache)
            wheel_cache[package] = entry
        if entry and entry.get("pure_wheel"):
            verdict.pure_wheels.append(package)
            continue
        verdict.motifs.append("import_absent")
        verdict.missing_imports.append(module)

    # GPU declenche aussi par le contenu des cellules.
    for text in sources:
        if "nvidia-smi" in text or "torch.cuda" in text:
            verdict.motifs.append("gpu")
            verdict.gpu_detail.append("usage CUDA explicite")
            break

    # Cles d'API : noms de variables seulement, jamais de valeur.
    for text in sources:
        for name in GETENV_RE.findall(text) + ENVIRON_INDEX_RE.findall(text):
            if API_KEY_PATTERN.search(name):
                verdict.motifs.append("cle")
                verdict.key_detail.append(name)
        if re.search(r"\b(?:input|getpass)\s*\(\s*[\"'][^\"']*(?:key|token|secret|password)", text, re.IGNORECASE):
            verdict.motifs.append("cle")
            verdict.key_detail.append("saisie interactive de secret")

    # Services reseau : hotes distants **appeles** et ports locaux.
    # Une URL simplement citee (docstring, prefixe SPARQL, URI de schema,
    # hote documentaire) ne rend pas le carnet dependant d'un service : c'est
    # l'appel qui compte, pas la mention.
    for text in sources:
        for line in text.splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            if PREFIX_LINE_RE.match(stripped):
                continue
            hosts = URL_RE.findall(line)
            if not hosts:
                continue
            called = any(token in line for token in NET_CALL_TOKENS)
            assigned = "=" in line and not stripped.startswith(("return", "print"))
            for host in hosts:
                if host in ("localhost", "127.0.0.1") or host.startswith("127."):
                    continue
                if host in DOC_HOSTS:
                    continue
                if not (called or assigned):
                    continue
                verdict.motifs.append("reseau")
                verdict.network_detail.append(host)
        for port in LOCALHOST_RE.findall(text):
            verdict.motifs.append("reseau")
            verdict.network_detail.append("localhost:%s" % port)
    for module in sorted(imports):
        top = top_level_module(module)
        if top in NETWORK_MODULES:
            verdict.motifs.append("reseau")
            verdict.network_detail.append(module)

    for text in sources:
        for name in FILE_READ_RE.findall(text):
            verdict.local_files.append(name)

    verdict.motifs = sorted(set(verdict.motifs))
    verdict.eligible = not verdict.motifs
    verdict.code_cells = len([c for c in (nb.get("cells") or [])
                              if isinstance(c, dict) and c.get("cell_type") == "code"])
    return verdict


# ---------------------------------------------------------------------------
# Rapports
# ---------------------------------------------------------------------------


def build_table(verdicts: Sequence[NotebookVerdict]) -> Dict[str, object]:
    """Table par serie : comptes d'eligibles et de refus par motif."""
    table: Dict[str, Dict[str, object]] = {}
    for v in verdicts:
        row = table.setdefault(
            v.series,
            {
                "carnets": 0,
                "eligibles": 0,
                "refuses": 0,
                "par_motif": {m: 0 for m in MOTIFS},
                "erreurs": 0,
            },
        )
        row["carnets"] = int(row["carnets"]) + 1
        if v.error:
            row["erreurs"] = int(row["erreurs"]) + 1
        if v.eligible:
            row["eligibles"] = int(row["eligibles"]) + 1
        else:
            row["refuses"] = int(row["refuses"]) + 1
            for motif in v.motifs:
                pm = row["par_motif"]
                pm[motif] = int(pm.get(motif, 0)) + 1
    return table


def render_markdown(
    verdicts: Sequence[NotebookVerdict],
    table: Dict[str, Dict[str, object]],
    lock_info: Dict[str, object],
    root: Path,
) -> str:
    """Rend le tableau Markdown et le critere relisible."""
    eligibles = [v for v in verdicts if v.eligible]
    refuses = [v for v in verdicts if not v.eligible]

    lines: List[str] = []
    lines.append("# Eligibilite Pyodide (JupyterLite) des carnets Python")
    lines.append("")
    lines.append("<!-- Genere par scripts/notebook_tools/pyodide_eligibility.py -- ne pas editer a la main. -->")
    lines.append("")
    lines.append("Perimetre : carnets Python suivis par git, hors `_output`, `_en` et `_archive`.")
    lines.append("Census : **%d** carnets Python, **%d** eligibles, **%d** refuses." %
                 (len(verdicts), len(eligibles), len(refuses)))
    lines.append("")
    lines.append("Source de verite des paquets : `pyodide-lock.json` (%s ; %s paquets), complete "
                 "les pure wheels par sonde PyPI "
                 "(`--probe-pypi`, cache versionne). Regeneration : "
                 "`python scripts/notebook_tools/pyodide_eligibility.py --format md "
                 "--out docs/reference/pyodide-eligibilite.md --refus-out "
                 "docs/reference/pyodide-refus.tsv --pyodide-lock <chemin>/pyodide-lock.json "
                 "--probe-pypi`." % (
                     lock_description(lock_info),
                     lock_info.get("package_count", "?")))
    lines.append("")
    lines.append("## Critere d'eligibilite")
    lines.append("")
    lines.append("Un carnet est **eligible** si et seulement si les quatre conditions suivantes sont reunies.")
    lines.append("Ce paragraphe est la source de verite : la regenereation du site s'appuie sur ce critere,")
    lines.append("jamais sur une liste maintenue a la main.")
    lines.append("")
    lines.append("1. **Aucun GPU** : aucun import de `torch`, `tensorflow`, `jax`, `cupy`, `onnxruntime`,")
    lines.append("   ni usage explicite de `torch.cuda` ou de `nvidia-smi`.")
    lines.append("2. **Aucune cle d'API** : aucune variable d'environnement dont le nom ressemble a une")
    lines.append("   cle (`*KEY*`, `*TOKEN*`, `*SECRET*`, `*PASSWORD*`, `*CREDENTIAL*`), ni saisie")
    lines.append("   interactive de secret. Seuls les **noms** sont collectes, jamais les valeurs.")
    lines.append("3. **Aucun service reseau** : aucun appel a un hote distant (`http(s)://`), aucun port")
    lines.append("   local de service, aucun module client reseau (`requests`, `httpx`, `socket`, ...).")
    lines.append("4. **Tous les imports resolus** : chaque import est soit dans la bibliotheque")
    lines.append("   standard, soit un module local du depot (helper du carnet), soit un paquet present")
    lines.append("   dans `pyodide-lock.json`, soit un paquet PyPI existant en roue pure")
    lines.append("   (`py3-none-any`), installable par `micropip` dans le navigateur.")
    lines.append("")
    lines.append("Le refus porte toujours un motif : `gpu`, `cle`, `reseau` ou `import_absent`.")
    lines.append("")
    lines.append("Lock de reference : `%s` (%s, %s paquets)." % (
        os.path.basename(str(lock_info.get("lock"))),
        lock_description(lock_info),
        lock_info.get("package_count", "?")))
    lines.append("")
    lines.append("Les **noms** des variables d'environnement ne sont pas publies : un nom qui ressemble")
    lines.append("a une cle (`*_API_KEY`) fait echouer le scanner de secrets du depot, alors que le nom")
    lines.append("seul n'est pas un secret. Le detail des refus (`pyodide-refus.tsv`) publie donc le")
    lines.append("**nombre** de variables detectees (`cle=N`), pas leurs noms ; les noms restent")
    lines.append("accessibles en local avec `--detail-cle` (sortie a ne pas committer).")
    lines.append("")

    lines.append("## Table par serie")
    lines.append("")
    lines.append("| Serie | Carnets Python | Eligibles | Refuses | dont GPU | dont cle | dont reseau | dont import absent |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for serie in sorted(table):
        row = table[serie]
        pm = row["par_motif"]
        lines.append("| %s | %d | %d | %d | %d | %d | %d | %d |" % (
            serie, row["carnets"], row["eligibles"], row["refuses"],
            pm.get("gpu", 0), pm.get("cle", 0), pm.get("reseau", 0), pm.get("import_absent", 0)))
    lines.append("")

    lines.append("## Carnets eligibles")
    lines.append("")
    lines.append("| Carnet | Serie | Noyau | Imports Pyodide | Roues pures |")
    lines.append("|---|---|---|---|---|")
    for v in sorted(eligibles, key=lambda x: (x.series, x.path)):
        lines.append("| `%s` | %s | %s | %s | %s |" % (
            v.path, v.series, v.kernel or "-",
            ", ".join(sorted(set(v.pyodide_packages))) or "-",
            ", ".join(sorted(set(v.pure_wheels))) or "-"))
    lines.append("")

    lines.append("## Refuses : motifs par serie")
    lines.append("")
    lines.append("Le detail **carnet par carnet** des refus (motif et element declencheur) est dans le")
    lines.append("fichier `%s`, une ligne par carnet refuse." % os.path.basename(REFUS_TSV_NAME))
    lines.append("")
    lines.append("| Serie | Motifs rencontres | Imports absents (les plus frequents) |")
    lines.append("|---|---|---|")
    for serie in sorted(table):
        motifs_seen: Set[str] = set()
        missing: Dict[str, int] = {}
        for v in refuses:
            if v.series != serie:
                continue
            motifs_seen.update(v.motifs)
            for name in v.missing_imports:
                missing[name] = missing.get(name, 0) + 1
        if not motifs_seen:
            continue
        top = sorted(missing.items(), key=lambda kv: (-kv[1], kv[0]))[:6]
        lines.append("| %s | %s | %s |" % (
            serie, ", ".join(sorted(motifs_seen)),
            ", ".join("%s (%d)" % (name, count) for name, count in top) or "-"))
    lines.append("")
    lines.append("Les motifs **se cumulent** : un carnet refuse pour une cle d'API et pour un import")
    lines.append("absent compte dans les deux colonnes de la table par serie.")
    lines.append("")
    return "\n".join(lines)


def sanitize_verdict(data: Dict[str, object], with_key_names: bool = False) -> Dict[str, object]:
    """Retire les noms de variables d'environnement d'un verdict serialise.

    Un nom de variable qui ressemble a une cle (`*_API_KEY`) fait echouer le
    scanner de secrets du depot, alors que le nom seul n'est pas un secret.
    Les sorties versionnees publient donc un **nombre** ; les noms restent
    accessibles en local avec `--detail-cle`.
    """
    if with_key_names:
        return data
    result = dict(data)
    names = result.get("key_detail") or []
    result["key_detail"] = []
    result["cle_n"] = len([n for n in names if n != "saisie interactive de secret"])
    return result


def render_refus_tsv(verdicts: Sequence[NotebookVerdict],
                    with_key_names: bool = False) -> str:
    """Rend le detail des refus : une ligne TSV par carnet refuse.

    Les **noms** des variables d'environnement ne sont pas publies par
    defaut. Un nom qui ressemble a une cle (`*_API_KEY`, `*_PASSWORD`) fait
    echouer le scanner de secrets du depot, alors que le nom seul n'est pas
    un secret : on publie donc le **nombre** de variables detectees, et les
    noms restent accessibles en local avec `--detail-cle` (sortie a ne pas
    committer).
    """
    lines: List[str] = ["# chemin\tserie\tmotifs\tdetail"]
    for v in sorted((x for x in verdicts if not x.eligible), key=lambda x: (x.series, x.path)):
        detail: List[str] = []
        if v.gpu_detail:
            detail.append("gpu=%s" % ",".join(sorted(set(v.gpu_detail))))
        if v.key_detail:
            names = sorted(set(v.key_detail))
            interactive = "saisie interactive de secret" in names
            env_names = [n for n in names if n != "saisie interactive de secret"]
            if with_key_names:
                detail.append("cle=%s" % ",".join(names))
            else:
                detail.append("cle=%d" % len(env_names))
                if interactive:
                    detail.append("cle_interactive")
        if v.network_detail:
            detail.append("reseau=%s" % ",".join(sorted(set(v.network_detail))[:4]))
        if v.missing_imports:
            detail.append("import_absent=%s" % ",".join(sorted(set(v.missing_imports))[:6]))
        if v.error:
            detail.append("erreur=%s" % v.error[:120])
        lines.append("%s\t%s\t%s\t%s" % (
            v.path, v.series, ",".join(v.motifs), ";".join(detail)))
    return "\n".join(lines) + "\n"


def select_lot(verdicts: Sequence[NotebookVerdict], size: int) -> List[NotebookVerdict]:
    """Choisit un lot de carnets eligibles etape par etape, sans tri manuel.

    Regle declaree : on repartit le lot sur des series distinctes (une serie
    par tour, dans l'ordre alphabétique des series), on prefere les carnets
    qui n'ont besoin d'aucune roue pure a installer dans le navigateur, puis
    ceux qui ne lisent aucun fichier du depot. Le lot est donc reproductible
    : il sort du critere, il n'est pas pose a la main.
    """
    eligible = [v for v in verdicts if v.eligible]
    by_series: Dict[str, List[NotebookVerdict]] = {}
    for v in eligible:
        by_series.setdefault(v.series, []).append(v)
    for series in by_series:
        by_series[series].sort(key=lambda v: (len(v.pure_wheels), len(v.local_files),
                                              v.code_cells, v.path))

    chosen: List[NotebookVerdict] = []
    used_paths: Set[str] = set()
    series_order = sorted(by_series)
    while len(chosen) < size and series_order:
        remaining: List[str] = []
        for series in series_order:
            pick = next((v for v in by_series[series] if v.path not in used_paths), None)
            if pick is None:
                continue
            used_paths.add(pick.path)
            chosen.append(pick)
            if len(chosen) >= size:
                break
            remaining.append(series)
        if len(chosen) >= size:
            break
        if not remaining:
            break
        series_order = remaining
    return chosen


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Point d'entree."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--repo", default=None, help="racine du depot (defaut : auto)")
    parser.add_argument("--format", choices=("md", "json"), default="md")
    parser.add_argument("--out", default=None, help="fichier de sortie (defaut : stdout)")
    parser.add_argument("--pyodide-lock", default=None,
                        help="chemin vers pyodide-lock.json de la distribution Pyodide")
    parser.add_argument("--wheel-cache", default=None,
                        help="cache JSON des sondes PyPI (roues pures)")
    parser.add_argument("--probe-pypi", action="store_true",
                        help="sonder PyPI pour les paquets inconnus (reseau)")
    parser.add_argument("--write-cache", default=None,
                        help="ecrire le cache des sondes PyPI dans ce fichier")
    parser.add_argument("--limit-series", default=None,
                        help="ne traiter que cette serie (diagnostic)")
    parser.add_argument("--select-lot", type=int, default=0,
                        help="ecrire un lot de N carnets eligibles (selection par le critere)")
    parser.add_argument("--lot-out", default=None,
                        help="fichier JSON du lot selectionne")
    parser.add_argument("--detail", action="store_true",
                        help="inclure le detail par carnet dans le JSON (volumineux)")
    parser.add_argument("--refus-out", default=None,
                        help="fichier TSV du detail des refus (une ligne par carnet refuse)")
    parser.add_argument("--detail-cle", action="store_true",
                        help="publier les noms des variables d'environnement (usage local : "
                             "sortie a ne pas committer, le scanner de secrets la refuse)")
    args = parser.parse_args(argv)

    root = Path(args.repo).resolve() if args.repo else repo_root()
    lock_path = Path(args.pyodide_lock).resolve() if args.pyodide_lock else None
    cache_path = Path(args.wheel_cache).resolve() if args.wheel_cache else None

    pyodide_packages, lock_info = load_pyodide_lock(lock_path)
    wheel_cache = load_wheel_cache(cache_path)

    stdlib_names = set(sys.stdlib_module_names)

    notebooks = [p for p in git_ls_files(root, ["*.ipynb"]) if is_active_notebook(p)]
    notebooks = [p for p in notebooks if ".ipynb" in p]
    verdicts: List[NotebookVerdict] = []
    for rel in notebooks:
        verdict = analyse_notebook(root, rel, pyodide_packages, wheel_cache,
                                   stdlib_names, args.probe_pypi)
        if verdict.kernel and not verdict.kernel.lower().startswith("python"):
            # Hors famille Python : ni eligible ni refuse, la table ne compte
            # que les carnets Python.
            continue
        if args.limit_series and verdict.series != args.limit_series:
            continue
        verdicts.append(verdict)

    table = build_table(verdicts)
    payload = {
        "criterion": {
            "motivs": list(MOTIFS),
            "regles": [
                "aucun import GPU",
                "aucune cle d'API",
                "aucun service reseau",
                "tous les imports resolvables (stdlib, local, paquet Pyodide, roue pure)",
            ],
        },
        "pyodide": lock_info,
        "depot": str(root),
        "census": {
            "carnets_python": len(verdicts),
            "eligibles": sum(1 for v in verdicts if v.eligible),
            "refuses": sum(1 for v in verdicts if not v.eligible),
        },
        "par_serie": table,
        "eligibles": [
            {
                "chemin": v.path,
                "serie": v.series,
                "noyau": v.kernel,
                "paquets_pyodide": sorted({p.split("==")[0] for p in v.pyodide_packages}),
                "roues_pures": sorted(set(v.pure_wheels)),
            }
            for v in verdicts if v.eligible
        ],
        "detail_complet": "regenere par scripts/notebook_tools/pyodide_eligibility.py --format json --detail",
    }
    if args.detail:
        payload["carnets"] = [sanitize_verdict(v.to_dict(), args.detail_cle) for v in verdicts]

    if args.format == "json":
        text = json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
    else:
        text = render_markdown(verdicts, table, lock_info, root) + "\n"

    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with out_path.open("w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
        print("ecrit : %s (%d caracteres)" % (out_path, len(text)))
    else:
        sys.stdout.write(text)

    if args.select_lot:
        lot = select_lot(verdicts, args.select_lot)
        lot_payload = {
            "regle": ("une serie par tour, series par ordre alphabetique ; preference aux carnets "
                      "sans roue pure a installer, puis sans lecture de fichier du depot"),
            "taille": len(lot),
            "carnets": [sanitize_verdict(v.to_dict(), args.detail_cle) for v in lot],
            "series": sorted({v.series for v in lot}),
        }
        lot_text = json.dumps(lot_payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
        if args.lot_out:
            lot_path = Path(args.lot_out)
            lot_path.parent.mkdir(parents=True, exist_ok=True)
            with lot_path.open("w", encoding="utf-8", newline="\n") as fh:
                fh.write(lot_text)
            print("lot ecrit : %s (%d carnets, %d series)" % (
                lot_path, len(lot), len(lot_payload["series"])))
        else:
            sys.stdout.write(lot_text)

    if args.refus_out:
        refus_path = Path(args.refus_out)
        refus_path.parent.mkdir(parents=True, exist_ok=True)
        refus_text = render_refus_tsv(verdicts, with_key_names=args.detail_cle)
        with refus_path.open("w", encoding="utf-8", newline="\n") as fh:
            fh.write(refus_text)
        refus_count = len([ln for ln in refus_text.splitlines() if not ln.startswith("#")])
        print("refus ecrit : %s (%d lignes)" % (refus_path, refus_count))

    if args.write_cache:
        cache_out = Path(args.write_cache)
        cache_out.parent.mkdir(parents=True, exist_ok=True)
        with cache_out.open("w", encoding="utf-8", newline="\n") as fh:
            json.dump(wheel_cache, fh, indent=1, sort_keys=True, ensure_ascii=False)
        print("cache ecrit : %s (%d paquets)" % (cache_out, len(wheel_cache)))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
