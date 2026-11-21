"""Eligibility des carnets Python pour une execution dans le navigateur (Pyodide).

Ce script classe les carnets Python actifs du depot selon leur eligibilite a
JupyterLite. Un carnet est eligible si, et seulement si :

1. il ne demande aucun GPU ;
2. il ne demande aucune cle d'API ;
3. il ne demande aucun service reseau ;
4. tous ses imports sont **satisfaits par le bundle** : dans la bibliotheque
   standard, dans la distribution Pyodide, installes par le carnet lui-meme,
   ou fournis par un module de sa serie livre avec le carnet -- dont les
   propres dependances sont satisfaites. Le bundle publie des fichiers et
   n'installe rien : une roue pure que le carnet n'installe pas lui-meme
   n'est pas fournie, et un module d'une autre serie n'est pas livre.

Le critere est ecrit ici, en un seul endroit : c'est le fichier qui fait foi,
pas une liste maintenue a la main. Les rendus (Markdown, TSV, lot) vivent dans
``pyodide_eligibility_report.py`` : ce module calcule, l'autre met en forme.

Sources utilisees, toutes locales sauf demande explicite :

- ``git ls-files`` : liste des carnets suivis (aucun acces reseau) ;
- le fichier ``pyodide-lock.json`` de la distribution Pyodide : liste
  autoritaire des paquets disponibles dans le navigateur, avec leur version ;
- une sonde PyPI, **uniquement** avec ``--probe-pypi`` : presence d'une roue
  pure pour un paquet absent du lock. Sans ce drapeau, aucun acces reseau
  n'est fait et le paquet absent est refuse.

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

from pyodide_eligibility_report import (
    MOTIFS,
    build_table,
    render_markdown,
    render_refus_tsv,
    sanitize_verdict,
    select_lot,
)
from pyodide_suffisance import CLASSES, Probleme, roue_pure, suffisance_carnet

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
    language: str = ""
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
    #: Les dependances non satisfaites pour le bundle, classees.
    problemes: List[Probleme] = field(default_factory=list)

    def to_dict(self) -> Dict[str, object]:
        return {
            "path": self.path,
            "series": self.series,
            "subseries": self.subseries,
            "kernel": self.kernel,
            "language": self.language,
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
            "problemes": [{"classe": p.classe, "detail": p.detail}
                          for p in self.problemes],
            "error": self.error,
        }


def is_python_notebook(verdict: NotebookVerdict) -> bool:
    """Le carnet appartient-il a la famille Python ?

    ``language_info.name`` fait foi : c'est la langue du document, declaree par
    le noyau qui l'a execute. Le nom du ``kernelspec`` n'est qu'un repli : il
    nomme un environnement, pas une langue (``coursia-ml-training``,
    ``pyphi``, ``gametheory-wsl`` sont tous des noyaux Python dont le nom ne
    commence pas par « python »). Un carnet qui ne declare ni l'un ni l'autre
    n'est pas compte : le census ne suppose pas Python par defaut.
    """
    for marker in (verdict.language, verdict.kernel):
        if marker:
            return marker.lower().startswith("python")
    return False


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


_SKIP_DIRS = {".git", ".tmp", "node_modules", "__pycache__", ".venv", "venv",
              ".pytest_cache", ".mypy_cache", "build", "dist", ".claude"}


def module_names(directory: Path, recursive: bool) -> Set[str]:
    """Noms importables fournis par un repertoire.

    Un fichier ``.py`` fournit son radical ; un **paquet** (dossier porteur
    d'un ``__init__.py``) fournit son nom de dossier. Sans cette seconde
    regle, ``import ict`` remonte en import absent alors que ``ict/`` est un
    paquet de la serie, livre avec le bundle JupyterLite.
    """
    names: Set[str] = set()
    if recursive:
        for base, dirs, files in os.walk(directory):
            dirs[:] = [d for d in dirs if d not in _SKIP_DIRS and not d.startswith(".")]
            if base != str(directory) and "__init__.py" in files:
                names.add(Path(base).name)
            for name in files:
                if name.endswith(".py") and name != "__init__.py":
                    names.add(name[:-3])
        return names
    try:
        entries = list(directory.iterdir())
    except OSError:
        return names
    for entry in entries:
        try:
            if entry.is_file() and entry.suffix == ".py":
                if entry.stem != "__init__":
                    names.add(entry.stem)
            elif entry.is_dir() and (entry / "__init__.py").is_file():
                names.add(entry.name)
        except OSError:
            continue
    return names


def local_modules(root: Path, notebook: Path, series_root: Path) -> Tuple[Set[str], Set[str]]:
    """Modules Python presents dans la serie du carnet, et ailleurs dans le depot.

    Un carnet est souvent accompagne de ses helpers ; ces modules sont
    embarquables dans le bundle JupyterLite et ne sont pas un refus. Les
    paquets (dossiers a ``__init__.py``) comptent au meme titre que les
    fichiers ``.py``.

    Retourne le couple ``(modules de la serie, modules du depot hors serie)``.
    Un module de la serie est embarquable tel quel ; un module trouve
    ailleurs dans le depot existe mais n'est pas livre par defaut, il est
    signale a part plutot que traite comme un import absent.
    """
    in_series: Set[str] = set()
    for directory in {notebook.parent, notebook.parent.parent, notebook.parent.parent.parent}:
        if not directory.is_dir():
            continue
        in_series |= module_names(directory, recursive=False)
    try:
        rel = notebook.relative_to(series_root)
        depth = len(rel.parts) - 1
    except ValueError:
        depth = 0
    for parent in list(notebook.parents)[: depth + 1]:
        if not parent.is_dir():
            continue
        in_series |= module_names(parent, recursive=True)
    elsewhere = repo_python_modules(root) - in_series
    return in_series, elsewhere


_REPO_MODULE_CACHE: Dict[str, Set[str]] = {}


def repo_python_modules(root: Path) -> Set[str]:
    """Noms de modules Python presents dans le depot (index unique, mis en cache).

    Fichiers ``.py`` et paquets (dossiers a ``__init__.py``) : la meme regle
    que dans la serie, sinon un module livre ailleurs dans le depot serait
    traite comme un import absent.
    """
    key = str(root)
    if key in _REPO_MODULE_CACHE:
        return _REPO_MODULE_CACHE[key]
    names: Set[str] = set()
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in _SKIP_DIRS and not d.startswith(".")]
        if base != str(root) and "__init__.py" in files:
            names.add(Path(base).name)
        for name in files:
            if name.endswith(".py") and name != "__init__.py":
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


def load_wheel_cache(path: Optional[Path]) -> Dict[str, Dict[str, object]]:
    """Charge le cache des sondes PyPI (presence d'une roue pure)."""
    if path is None or not path.is_file():
        return {}
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)


def probe_pypi(package: str, cache: Dict[str, Dict[str, object]], timeout: float = 20.0) -> Dict[str, object]:
    """Sonde PyPI : le paquet existe-t-il en roue pure ?

    Le resultat est memorise dans le cache : la sonde est faite une fois par
    paquet. Sans ``--probe-pypi``, aucune sonde n'est faite.
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

    metadata = nb.get("metadata") or {}
    ks = metadata.get("kernelspec") or {}
    verdict.kernel = ks.get("name") or ""
    info = metadata.get("language_info") or {}
    verdict.language = info.get("name") or ""

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

    # Suffisance : le bundle publie des fichiers et n'installe rien. Un import
    # n'est satisfait que s'il est dans la distribution, s'il est installe
    # par le carnet lui-meme, ou s'il vient d'un module de la serie livre
    # avec le carnet et dont les dependances sont satisfaites. Un module
    # d'une autre serie n'est pas livre par le bundle.
    suff = suffisance_carnet(
        root, rel_path, pyodide_packages, stdlib_names, sources=sources,
        est_roie_pure=lambda pack: roue_pure(pack, wheel_cache, probe))
    verdict.problemes = [p for p in suff.problemes if p.classe in CLASSES]
    if verdict.problemes:
        verdict.motifs.append("suffisance")

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
        if not is_python_notebook(verdict):
            # Hors famille Python (langue declaree, sinon noyau) : ni eligible
            # ni refuse, la table ne compte que les carnets Python.
            continue
        if args.limit_series and verdict.series != args.limit_series:
            continue
        verdicts.append(verdict)

    table = build_table(verdicts)
    payload = {
        "criterion": {
            "motifs": list(MOTIFS),
            "regles": [
                "aucun import GPU",
                "aucune cle d'API",
                "aucun service reseau",
                "tous les imports satisfaits par le bundle (distribution, installation du carnet, module de la serie)",
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
        text = render_markdown(verdicts, table, lock_info) + "\n"

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