#!/usr/bin/env python3
"""
scan_duplicate_test_pairs.py — detecte les fichiers de tests dupliques en appariant
sur le MODULE TESTE (docstring + imports), pas sur le basename.

Issue #14730 point 4. Le recensement #14615 croisait les basenames : un fichier
legacy (scripts/tests/test_extract_titles.py) couvrant deux extracteurs dont les
suites canoniques ont des basenames differents (test_extract_pptx_titles.py /
test_extract_slidev_titles.py) etait structurellement invisible a cette cle.
Une cle de regroupement herite des angles morts du champ sur lequel elle groupe.

Predicat ici : pour chaque fichier test_*.py sous scripts/, extraire les modules
testes, puis grouper par module teste. Une PAIRE DUPLIQUEE VIVANTE = un module
teste par >= 2 fichiers de test distincts.

Un bord « fichier test -> module » nait de (calibration anti-bruit, cf tests) :
  - docstring LEAD (premier paragraphe, la phrase-titre « Tests for ... ») :
    mention du module -> bord sans condition (cas fondateur #14730 : un legacy
    citant DEUX modules par des chemins depuis deplaces) ;
  - docstring CORPS : mention en prose -> bord seulement si affinite de nom
    (stem du module contenu dans le stem du fichier de test) ;
  - import (absolu scripts.* ou nom flat apres sys.path.insert, resolu par
    basename unique) -> bord seulement si affinite de nom — un import sans
    mention peut etre un usage-helper, pas un test.

La resolution d'une mention par basename unique (chemin cite inexistant ou
mention nue) est marquee « +basename » dans l'evidence : la revue voit le
recours. L'instrument EXTRACT, il ne DECIDE pas : chaque paire rendue est un
candidat a trier, pas un verdict de duplication certaine.

Litmus anti-LIGHT : ce script EXTRACT, il ne DECIDE pas. Le verdict final revient
a la revue humaine/agent (consolidation selon le patron #14679, cf #14730).

Usage :
  python scripts/audit/scan_duplicate_test_pairs.py [--repo-root <path>] [--json] [--check]

Sortie :
  humaine (defaut) : une ligne par module en paire + resume
  --json : {"repo_root", "test_files_scanned", "modules_scanned", "pairs": [...]}
  --check : exit 1 si >= 1 paire vivante (CI-ready)
"""

import argparse
import ast
import json
import re
import sys
import warnings
from pathlib import Path

# Mentions "scripts/<chemin>.py" dans une docstring (frontiere non-mot pour ne
# pas tronquer un chemin cite dans une URL ou un chemin plus long).
_DOCSTRING_MODULE_RE = re.compile(
    r"(?<![\w/.-])(scripts/(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_-]+\.py)"
)

_EXCLUDED_DIR_PARTS = {"_archive", "__pycache__", ".lake", "node_modules", "_peters"}


def find_repo_root(start: Path) -> Path:
    for candidate in [start, *start.parents]:
        if (candidate / ".git").exists():
            return candidate
    raise SystemExit(f"Racine git introuvable depuis {start}")


def _is_excluded(path: Path) -> bool:
    return any(part in _EXCLUDED_DIR_PARTS for part in path.parts)


def iter_test_files(repo_root: Path):
    scripts_root = repo_root / "scripts"
    for path in sorted(scripts_root.rglob("test_*.py")):
        if _is_excluded(path.relative_to(repo_root)):
            continue
        yield path


def _module_docstring(tree: ast.Module) -> str:
    return ast.get_docstring(tree) or ""


# Mentions nues « <nom>.py » (sans prefixe scripts/) dans une docstring — les
# docstrings citent souvent le module teste par son seul basename.
_BARE_MENTION_RE = re.compile(r"(?<![\w/.-])([A-Za-z0-9_-]+\.py)")


def build_basename_index(repo_root: Path) -> dict:
    """basename -> chemin resolu UNIQUEMENT si un seul .py de l'arbre le porte.

    Les docstrings et les imports flat (sys.path.insert + from X import) citent
    des modules deplaces ou nus : la resolution par basename unique fait le
    pont, et le +basename de l'evidence signale ce recours a la revue.
    """
    occurrences: dict = {}
    scripts_root = repo_root / "scripts"
    if not scripts_root.is_dir():
        return {}
    for path in scripts_root.rglob("*.py"):
        if _is_excluded(path.relative_to(repo_root)):
            continue
        occurrences.setdefault(path.name, []).append(path.resolve())
    return {name: paths[0] for name, paths in occurrences.items() if len(paths) == 1}


def _docstring_modules(docstring: str, repo_root: Path, basenames: dict, test_stem: str) -> dict:
    """Mentions de modules dans la docstring -> {module: evidence}.

    Lead (premier paragraphe) : c'est la phrase-titre « Tests for ... » —
    mention = bord, sans condition (le cas fondateur #14730 : un legacy citant
    DEUX modules par des chemins depuis deplaces).

    Corps de docstring : mention en prose (« construit sur le meme pattern
    que ... ») — bord seulement si affinite de nom (stem du module contenu
    dans le stem du fichier de test).

    Resolution : chemin cite exact s'il existe, sinon basename unique dans
    l'arbre (docstring+basename le signale a la revue).
    """
    lead, _, body = docstring.partition("\n\n")
    found: dict = {}

    def _resolve(mention: str, evidence_lead: bool) -> None:
        candidate = repo_root / Path(mention)
        name = Path(mention).name
        module = None
        if candidate.is_file():
            module = candidate.resolve()
        elif name in basenames:
            module = basenames[name]
        if module is None:
            return
        if not evidence_lead:
            stem = module.stem
            if stem not in test_stem:
                return
        evidence = "docstring" if candidate.is_file() else "docstring+basename"
        found.setdefault(module, evidence)

    for match in _DOCSTRING_MODULE_RE.findall(lead):
        _resolve(match, evidence_lead=True)
    for bare in _BARE_MENTION_RE.findall(lead):
        if _DOCSTRING_MODULE_RE.search(bare):
            continue
        _resolve(bare, evidence_lead=True)
    for match in _DOCSTRING_MODULE_RE.findall(body):
        _resolve(match, evidence_lead=False)
    for bare in _BARE_MENTION_RE.findall(body):
        if _DOCSTRING_MODULE_RE.search(bare):
            continue
        _resolve(bare, evidence_lead=False)
    return found


def _import_modules(tree: ast.Module, repo_root: Path, basenames: dict, test_stem: str) -> dict:
    """Imports -> {module: evidence}. Un import sans mention de docstring peut
    etre un usage-helper (test_pick_idle_grain importe check_lane_claim sans le
    tester) : bord seulement si affinite de nom. Imports absolus scripts.* et
    noms flat (apres sys.path.insert, resolus par basename unique)."""
    found: dict = {}
    for node in ast.walk(tree):
        names = []
        if isinstance(node, ast.Import):
            names = [alias.name for alias in node.names]
        elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            names = [node.module]
        for name in names:
            module = None
            evidence = None
            if name.startswith("scripts."):
                parts = name.split(".")
                base = repo_root.joinpath(*parts)
                for candidate in (base.with_name(base.name + ".py"), base / "__init__.py"):
                    if candidate.is_file():
                        module = candidate.resolve()
                        evidence = "import"
                        break
            elif "." not in name and f"{name}.py" in basenames:
                module = basenames[f"{name}.py"]
                evidence = "import+basename"
            if module is None:
                continue
            if module.stem not in test_stem:
                continue
            found.setdefault(module, evidence)
    return found


def _is_noise_module(path: Path, repo_root: Path) -> bool:
    """Modules qui ne sont pas des candidats 'module teste'.

    __init__.py, conftest, et tout ce qui vit dans un dossier tests/ (les
    helpers de tests sont importes par beaucoup de suites sans etre testes).
    """
    rel = path.relative_to(repo_root)
    parts = rel.parts
    if path.name in ("__init__.py", "conftest.py"):
        return True
    return "tests" in parts


def tested_modules(test_path: Path, repo_root: Path, basenames: dict) -> dict:
    """Modules testes par un fichier de test -> {module: set(evidences)}."""
    source = test_path.read_text(encoding="utf-8", errors="replace")
    try:
        with warnings.catch_warnings():
            # Les fichiers scans portent parfois des docstrings a sequences
            # d'echappement invalides : bruit de parse, pas notre signal.
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(source)
    except SyntaxError:
        return {}
    test_stem = test_path.stem
    evidences: dict = {}
    for module, evidence in _docstring_modules(
        _module_docstring(tree), repo_root, basenames, test_stem
    ).items():
        if not _is_noise_module(module, repo_root):
            evidences.setdefault(module, set()).add(evidence)
    for module, evidence in _import_modules(tree, repo_root, basenames, test_stem).items():
        if not _is_noise_module(module, repo_root):
            evidences.setdefault(module, set()).add(evidence)
    return evidences


def zone_of(test_path: Path, repo_root: Path) -> str:
    return test_path.parent.relative_to(repo_root).as_posix()


def scan(repo_root: Path) -> dict:
    by_module: dict = {}
    test_files_scanned = 0
    basenames = build_basename_index(repo_root)
    for test_path in iter_test_files(repo_root):
        test_files_scanned += 1
        resolved = test_path.resolve()
        for module, evidences in tested_modules(test_path, repo_root, basenames).items():
            if module == resolved:
                continue
            by_module.setdefault(module, []).append(
                {
                    "test_file": resolved.relative_to(repo_root).as_posix(),
                    "zone": zone_of(test_path, repo_root),
                    "evidence": sorted(evidences),
                }
            )
    pairs = []
    for module in sorted(by_module):
        entries = sorted(by_module[module], key=lambda e: e["test_file"])
        if len({e["test_file"] for e in entries}) >= 2:
            pairs.append(
                {
                    "module": module.relative_to(repo_root).as_posix(),
                    "test_files": entries,
                }
            )
    return {
        "repo_root": str(repo_root),
        "test_files_scanned": test_files_scanned,
        "modules_scanned": len(by_module),
        "pairs": pairs,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--json", action="store_true", dest="as_json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    repo_root = (args.repo_root or find_repo_root(Path(__file__).resolve())).resolve()
    result = scan(repo_root)

    if args.as_json:
        print(json.dumps(result, indent=2))
    else:
        if not result["pairs"]:
            print(
                f"OK : 0 paire dupliquee vivante "
                f"({result['test_files_scanned']} fichiers test, "
                f"{result['modules_scanned']} modules testes)"
            )
        else:
            print(
                f"{len(result['pairs'])} paire(s) dupliquee(s) vivante(s) "
                f"({result['test_files_scanned']} fichiers test scans) :"
            )
            for pair in result["pairs"]:
                print(f"\n  module : {pair['module']}")
                for entry in pair["test_files"]:
                    ev = ", ".join(entry["evidence"])
                    print(f"    - {entry['test_file']}  [{ev}]  (zone {entry['zone']})")
    if args.check and result["pairs"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
