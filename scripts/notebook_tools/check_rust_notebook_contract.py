#!/usr/bin/env python3
"""Contrat des carnets Rust — `:dep` en tête, C.1, C.2 (Pli 3 #27098, point 5).

Un carnet Rust s'exécute sous `evcxr`, un kernel Jupyter qui **compile chaque
cellule**. Trois contraintes en découlent, et chacune a un coût concret déjà
mesuré (`docs/reference/kernels-runtime.md` § Rust) :

1. **`:dep` en tête de carnet.** Un `:dep` ajouté plus bas **recompile tout** et
   **efface les variables typées** des cellules précédentes. Les dépendances se
   déclarent donc dans la **première cellule de code**, et nulle part ailleurs.
   Ce que l'organe refuse : un `:dep` hors de la tête. Ce qu'il ne refuse pas :
   un carnet **sans** aucune dépendance (il n'y a rien à placer) — une absence
   n'est pas un défaut, un `:dep` tardif en est un.

2. **C.1 — pas d'erreur volontaire.** Les équivalents Rust des trois motifs
   Python (`raise NotImplementedError`, `assert False`, `1/0`) sont
   `panic!`, `unimplemented!()`, `todo!()`, `unreachable!()`. Un stub qui
   `panic!()` n'est pas exécutable de bout en bout : le carnet doit tourner
   même avec les exercices non complétés.

3. **C.2 — exécution complète committée.** Chaque cellule de code porte un
   `execution_count` (un entier). Une cellule **sans** sortie n'est pas un
   défaut : sous `evcxr`, une cellule de déclarations (`use`, `:dep`, `fn`)
   n'affiche rien. C'est `execution_count == null` qui trahit une cellule
   jamais exécutée.

Le suffixe `-Rust` et le kernelspec canonique `rust` sont déjà reconnus par le
canon (`naming_canon.KERNEL_LANG_SUFFIXES`) : le point 4 du pli est fait. Cet
organe couvre les points 1, 2 et 3 de la liste « les validateurs ».

Sorties : `0` conforme, `1` au moins un finding (nommé), `2` **panne de
l'instrument** (carnet illisible, diff illisible) — jamais un vert muet.

Usage :

    python scripts/notebook_tools/check_rust_notebook_contract.py <carnet> ...
    python scripts/notebook_tools/check_rust_notebook_contract.py --diff origin/main...HEAD
    python scripts/notebook_tools/check_rust_notebook_contract.py --diff origin/main...HEAD --json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterator

REPO_ROOT = Path(__file__).resolve().parents[2]

# --- Ce qui fait un carnet Rust ---------------------------------------------

RUST_SUFFIX = "-Rust.ipynb"


def is_rust_notebook(path: Path, notebook: dict[str, Any] | None = None) -> bool:
    """Vrai si le carnet est un carnet Rust (suffixe canonique ou kernelspec)."""
    if path.name.endswith(RUST_SUFFIX):
        return True
    if notebook is None:
        return False
    kernelspec = notebook.get("metadata", {}).get("kernelspec", {}) or {}
    return kernelspec.get("language") == "rust" or kernelspec.get("name") == "rust"


# --- Les trois contrôles -----------------------------------------------------

# Une ligne `:dep` : début de ligne, espaces possibles, puis `:dep` et au moins
# un espace. Le commentaire `//` est retiré avant (voir _strip_line_comments).
DEP_LINE = re.compile(r"^\s*:dep\s+\S")

# Les marqueurs d'erreur volontaire côté Rust. `panic!` couvre `panic!(...)` et
# `panic!("...")` ; les trois autres sont des macros d'echec compile-time.
C1_RUST_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bpanic!"), "panic!"),
    (re.compile(r"\bunimplemented!"), "unimplemented!()"),
    (re.compile(r"\btodo!"), "todo!()"),
    (re.compile(r"\bunreachable!"), "unreachable!()"),
)


def _strip_line_comments(source: str) -> str:
    """Retire les commentaires de ligne Rust (`// ...`).

    Un motif cité dans un commentaire n'est pas une erreur : `// TODO etudiant :
    // ne pas panic!()` est un commentaire, pas un appel. Les commentaires de
    bloc (`/* ... */`) sont retires aussi, ligne par ligne, pour la meme raison.
    """
    without_block = re.sub(r"/\*.*?\*/", " ", source, flags=re.DOTALL)
    lines = []
    for line in without_block.splitlines():
        idx = line.find("//")
        lines.append(line if idx < 0 else line[:idx])
    return "\n".join(lines)


def _code_cells(notebook: dict[str, Any]) -> Iterator[tuple[int, dict[str, Any]]]:
    for index, cell in enumerate(notebook.get("cells", []) or []):
        if cell.get("cell_type") == "code":
            yield index, cell


def _cell_source(cell: dict[str, Any]) -> str:
    source = cell.get("source", "")
    if isinstance(source, list):
        return "".join(source)
    return str(source)


def check_notebook(path: Path) -> list[dict[str, Any]]:
    """Renvoie les findings d'un carnet (liste vide = conforme)."""
    findings: list[dict[str, Any]] = []
    try:
        notebook = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{
            "notebook": str(path),
            "code": "NOTEBOOK_ILLISIBLE",
            "cell": None,
            "message": "carnet illisible ({}) : l'instrument ne peut pas juger, "
                       "ce n'est pas un vert".format(exc),
        }]

    if not is_rust_notebook(path, notebook):
        return findings

    # 1. `:dep` en tete, et nulle part ailleurs.
    dep_cells: list[int] = []
    for index, cell in _code_cells(notebook):
        source = _strip_line_comments(_cell_source(cell))
        if any(DEP_LINE.match(line) for line in source.splitlines()):
            dep_cells.append(index)
    if dep_cells:
        first_code = next((i for i, _ in _code_cells(notebook)), None)
        if dep_cells[0] != first_code:
            findings.append({
                "notebook": str(path),
                "code": "DEP_TARDIVE",
                "cell": dep_cells[0],
                "message": "`:dep` dans la cellule {} alors que la premiere cellule "
                           "de code est la cellule {} : un `:dep` tardif recompile "
                           "tout et efface les variables typees.".format(
                               dep_cells[0], first_code),
            })
        for index in dep_cells[1:]:
            findings.append({
                "notebook": str(path),
                "code": "DEP_TARDIVE",
                "cell": index,
                "message": "`:dep` dans la cellule {} : les dependances se "
                           "declarent dans la premiere cellule de code, une "
                           "seule fois.".format(index),
            })

    # 2. C.1 -- pas d'erreur volontaire.
    for index, cell in _code_cells(notebook):
        source = _strip_line_comments(_cell_source(cell))
        for pattern, label in C1_RUST_PATTERNS:
            if pattern.search(source):
                findings.append({
                    "notebook": str(path),
                    "code": "C1_RUST",
                    "cell": index,
                    "message": "`{}` dans la cellule {} : equivalent Rust de "
                               "`raise NotImplementedError` (C.1) -- un stub "
                               "d'exercice ne doit pas faire echouer le carnet "
                               "au moment de l'execution.".format(label, index),
                })

    # 3. C.2 -- execution complete commitee.
    for index, cell in _code_cells(notebook):
        if cell.get("execution_count") is None:
            findings.append({
                "notebook": str(path),
                "code": "C2_EXEC",
                "cell": index,
                "message": "cellule {} sans `execution_count` : elle n'a pas ete "
                           "executee (C.2/H.3).".format(index),
            })

    return findings


def _changed_notebooks(diff_range: str, repo_root: Path) -> list[Path]:
    """Carnets `.ipynb` touches par un range de diff (ajouts et modifications)."""
    proc = subprocess.run(
        ["git", "diff", "--name-only", "-z", "--diff-filter=AM",
         diff_range, "--", "*.ipynb"],
        capture_output=True, cwd=str(repo_root), text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError("git diff illisible pour le range {!r} : {}".format(
            diff_range, proc.stderr.strip() or "code {}".format(proc.returncode)))
    names = [n for n in proc.stdout.split("\0") if n]
    return [repo_root / name for name in names]


def run(notebooks: list[Path], repo_root: Path = REPO_ROOT) -> tuple[int, dict[str, Any]]:
    """Controle un lot de carnets. Retourne (rc, rapport)."""
    findings: list[dict[str, Any]] = []
    errors: list[dict[str, Any]] = []
    checked = 0
    for path in notebooks:
        try:
            exists = path.exists()
        except OSError as exc:  # pragma: no cover - acces refuse
            errors.append({"notebook": str(path), "message": str(exc)})
            continue
        if not exists:
            errors.append({"notebook": str(path),
                           "message": "carnet absent du disque"})
            continue
        checked += 1
        findings.extend(check_notebook(path))
    report = {
        "checked": checked,
        "findings": findings,
        "errors": errors,
        "rc": 1 if findings else (2 if errors else 0),
    }
    return report["rc"], report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("notebooks", nargs="*", help="carnets a controler")
    parser.add_argument("--diff", help="range de diff (ex. origin/main...HEAD)")
    parser.add_argument("--repo-root", default=str(REPO_ROOT),
                        help="racine du depot (pour le diff)")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    notebooks = [Path(n) for n in args.notebooks]
    if args.diff:
        try:
            notebooks.extend(_changed_notebooks(args.diff, repo_root))
        except RuntimeError as exc:
            print(json.dumps({"rc": 2, "error": str(exc)}, ensure_ascii=False))
            return 2
    if not notebooks:
        print(json.dumps({"rc": 0, "checked": 0, "findings": [], "errors": [],
                          "note": "aucun carnet a controler"},
                         ensure_ascii=False))
        return 0

    rc, report = run(notebooks, repo_root=repo_root)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for finding in report["findings"]:
            print("[{code}] {notebook} (cellule {cell}) : {message}".format(
                code=finding["code"], notebook=finding["notebook"],
                cell=finding["cell"], message=finding["message"]))
        for error in report["errors"]:
            print("[ERREUR] {notebook} : {message}".format(
                notebook=error["notebook"], message=error["message"]))
        print("{checked} carnet(s) controle(s), {n} finding(s), {e} erreur(s)".format(
            checked=report["checked"], n=len(report["findings"]),
            e=len(report["errors"])))
    return rc


if __name__ == "__main__":
    sys.exit(main())
