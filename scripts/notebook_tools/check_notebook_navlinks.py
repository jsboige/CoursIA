#!/usr/bin/env python3
"""Check broken relative navigation links INSIDE .ipynb notebook markdown cells.

Pourquoi cet outil existe
-------------------------
`scripts/check_docs_links.py` couvre UNIQUEMENT les fichiers markdown
(CLAUDE.md, docs/, .claude/, README.md). Les liens de navigation « precedent /
suivant » qui vivent dans les cellules markdown des notebooks .ipynb
(pattern `**Navigation** : [<< prev](X.ipynb) | [Index](README.md) | [next >>](Y.ipynb)`)
n'ont AUCUN checker. Deux 404 de ce type viennent d'etre fixes a la main
(PR #6801 Search-15-NetworkX-Csharp prev-dir, #6802 App-18b forward-navlink
deplace vers un autre sous-dossier) — il en reste tres probablement d'autres.

Ce tool parse chaque cellule markdown de chaque notebook pedagogique, extrait
les liens relatifs `[txt](target)` (meme regex que check_docs_links.py), resout
la cible RELATIVEMENT au dossier parent du notebook, et signale les cibles
absentes (404).

Comment ca marche
-----------------
- Scope : `MyIA.AI.Notebooks/**/*.ipynb` (sauf _archives, checkpoints, vendores).
- Pour chaque cellule markdown, on cherche `[text](target)` ou target est un
  chemin relatif (pas http/mailto/#anchor/template).
- La cible est resolue relativement au notebook (pas au repo root) — c'est la
  difference cle avec check_docs_links.py, qui scanne des .md au repo root.
- Les ancres `#...` dans un target `foo.ipynb#section` sont depouillees avant
  la resolution (on verifie juste que le fichier existe).
- Read-only : ne touche aucun notebook. Aucun risque de regression.

Modes (convention check_docs_links.py)
---------------------------------------
    python check_notebook_navlinks.py               # scan complet (exit 1 si broken)
    python check_notebook_navlinks.py --baseline    # ecrit scripts/tests/baseline_nb_navlinks.json
    python check_notebook_navlinks.py --check       # check vs baseline (exit 1 si NEW broken)
    python check_notebook_navlinks.py --family Search  # limiter a une famille
    python check_notebook_navlinks.py NB.ipynb      # un seul notebook
    python check_notebook_navlinks.py --json        # sortie machine
    python check_notebook_navlinks.py --quiet       # sortie minimale (CI)

Exit codes
----------
    0 = tous les liens valides (ou mode --check : aucun NEW broken)
    1 = un ou plusieurs liens casses trouve (ou NEW broken vs baseline)
    2 = erreur d'execution

Voir aussi
----------
- scripts/check_docs_links.py (checker markdown repo-wide, meme convention CLI)
- EPIC #5081 (renumerotation narrative des series — source des deplacements de notebooks)
- PRs #6801 / #6802 (les 2 navlinks .ipynb 404 fixes a la main, cas test)
"""
import argparse
import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# Dossiers a ignorer (archives, vendores, caches)
SKIP_DIRS = {
    ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
    ".ipynb_checkpoints", "_output", ".pytest_cache", "worktrees",
    "foundry-lib",  # lib vendored tierce, pas a nous a fixer
}

BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_nb_navlinks.json"


def _load_submodule_paths():
    """Parse .gitmodules -> liste de Path absolus des sous-modules git.

    Les deep-links pointant DANS un sous-module (ex. `../Z3.Linq/solutions/.../Theorem.cs`)
    sont des 404 LOCAUX quand le sous-module n'est pas `git submodule update --init`,
    mais valides sur GitHub (le sous-module y est resolu). On les exclut donc : ce
    ne sont pas de vrais navlinks casses, juste un checkout local incomplet.
    """
    gitmodules = REPO_ROOT / ".gitmodules"
    paths = []
    if not gitmodules.is_file():
        return paths
    try:
        for line in gitmodules.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line.startswith("path = "):
                rel = line[len("path = "):].strip()
                if rel:
                    paths.append((REPO_ROOT / rel).resolve())
    except OSError:
        pass
    return paths


SUBMODULE_PATHS = _load_submodule_paths()

# Meme pattern que check_docs_links.py : [text](target) relatif seulement.
# On depouille les ancres `#section` apres capture.
LINK_PATTERN = re.compile(
    r"\[([^\]]*)\]\((?!https?://)(?!mailto:)(?!#)([^)\s#]+(?:#[^)\s]*)?)\)"
)


def _should_skip(path: Path) -> bool:
    """True si le notebook est dans un dossier a ignorer."""
    try:
        rel = path.relative_to(REPO_ROOT)
    except ValueError:
        return True
    return any(part in SKIP_DIRS for part in rel.parts)


def _is_checkable_target(target: str, text: str = "") -> bool:
    """Filtre les targets non-fichiers (template vars, absolus, URL, mailto pur).

    Prend aussi le `text` du link pour filtrer les faux positifs :
    - operators modaux Tweety/KaTeX `[](phi)`, `[](p=>q)` (texte vide)
    - self-references code-as-doc `[`Theorem.cs`](Theorem.cs)` (texte == cible)
    """
    if not target:
        return False
    if target.startswith(("{", "<", "http:", "https:", "mailto:", "#", "/")):
        return False
    # On verifie les cibles fichiers (.ipynb, .md, images, .py, etc.). Les dossiers
    # nus termines par '/' ne sont pas des cibles de navlink ; on les skip.
    if target.endswith("/"):
        return False
    # FP 1 : operators modaux / KaTeX `[](phi)`, `[](p)`, `[](p=>q)` — texte vide.
    if text is not None and not text.strip():
        return False
    # FP 2 : cible sans extension NI separateur = pas un chemin fichier
    # (ex. `RollingWindow[T](taille)`, `[](10)` -> target "taille", "10").
    # Un vrai navlink relatif a TOUJOURS une extension (.ipynb/.md/.png...) ou un
    # sous-chemin avec '/'.
    base = target.split("#")[0]
    if "/" not in base and "." not in Path(base).name:
        return False
    # FP 3 : self-reference code-as-doc `[`Theorem.cs`](Theorem.cs)` (texte == cible).
    if text is not None and text.strip().strip("`") == target.strip():
        return False
    # FP 4 : chemins URL-encodes (%2F = /) : liens web encodes, pas working-tree.
    if "%" in target:
        return False
    # Exclure les chemins GitHub-relatifs (remontent au repo root vers /issues/, /pull/,
    # /blob/, /commit/) : ce sont des liens GitHub, pas des fichiers du working tree.
    parts = target.replace("\\", "/").split("/")
    if any(seg in ("issues", "pull", "blob", "commit", "releases", "compare") for seg in parts):
        if target.count("..") >= 2 or any(seg in ("issues", "pull", "blob", "commit")
                                          for seg in parts[:4]):
            return False
    return True


def _is_in_submodule(resolved: Path) -> bool:
    """True si le chemin resolu tombe DANS un sous-module git (deep-link valide GitHub)."""
    try:
        for sm in SUBMODULE_PATHS:
            if resolved == sm or sm in resolved.parents:
                return True
    except (TypeError, ValueError):
        pass
    return False


def _resolve_target(nb_path: Path, target: str) -> Path:
    """Resout target RELATIVEMENT au dossier parent du notebook (pas repo root).

    Depouille l'ancre `#section` avant resolution.
    """
    # separer l'ancre
    if "#" in target:
        target = target.split("#", 1)[0]
    target = unquote(target)
    # Ne PAS lstrip('./') : cela mangerait aussi le '../' parent-dir (bug v1, 721 FP).
    # On ne retire que le prefixe './' explicite (relatif-courant), pas '../'.
    if target.startswith("./"):
        target = target[2:]
    if not target:
        return nb_path  # ancre seule -> le notebook lui-meme (existe)
    # resolu depuis le dossier du notebook
    return (nb_path.parent / target).resolve()


def scan_notebook(nb_path: Path):
    """Retourne la liste des liens casses dans un notebook.

    Chaque lien casse = dict {notebook, cell_idx, line_no, text, target, kind}.
    `kind` = 'nav' (contient precedent/suivant/index/navigation) ou 'link' (autre).
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return None  # illisible : signale comme erreur, pas comme broken

    broken = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", [])
        if isinstance(src, str):
            src = src.splitlines()
        else:
            # liste de fragments -> rejoindre en gardant les fins de ligne pour line_no
            src = "".join(src).splitlines()
        for line_no, line in enumerate(src, start=1):
            for m in LINK_PATTERN.finditer(line):
                text = m.group(1)
                target = m.group(2)
                if not _is_checkable_target(target, text):
                    continue
                resolved = _resolve_target(nb_path, target)
                # FP : deep-link dans un sous-module git (pas checkout localement,
                # mais valide sur GitHub). Skip.
                if SUBMODULE_PATHS and _is_in_submodule(resolved):
                    continue
                if not resolved.exists():
                    low = (text + " " + target).lower()
                    is_nav = any(k in low for k in (
                        "precedent", "précédent", "prec", "préc",
                        "suivant", "suivante", "next", "prev",
                        "navigation", "index", ">>", "<<",
                    ))
                    broken.append({
                        "notebook": str(nb_path.relative_to(REPO_ROOT)).replace("\\", "/"),
                        "cell_idx": idx,
                        "line_no": line_no,
                        "text": text,
                        "target": target,
                        "kind": "nav" if is_nav else "link",
                        "line": line.rstrip(),
                    })
    return broken


def _iter_notebooks(family_filter=None):
    """Genere les chemins de notebooks pedagogiques."""
    if not NOTEBOOKS_ROOT.is_dir():
        return
    for nb in sorted(NOTEBOOKS_ROOT.rglob("*.ipynb")):
        if _should_skip(nb):
            continue
        if family_filter is not None:
            # family = sous-dossier de niveau 1
            try:
                rel = nb.relative_to(NOTEBOOKS_ROOT)
            except ValueError:
                continue
            if len(rel.parts) < 1 or rel.parts[0] != family_filter:
                continue
        yield nb


def run_scan(targets):
    """Scanne une liste de notebooks. Retourne (broken_list, errors_list)."""
    all_broken = []
    errors = []
    for nb in targets:
        result = scan_notebook(nb)
        if result is None:
            errors.append(str(nb.relative_to(REPO_ROOT)).replace("\\", "/"))
            continue
        all_broken.extend(result)
    return all_broken, errors


def _write_baseline(broken):
    """Ecrit le baseline (snapshot courant des broken, suppose connus)."""
    BASELINE_PATH.parent.mkdir(parents=True, exist_ok=True)
    # snapshot deterministe : trie par (notebook, cell_idx, line_no, target)
    snapshot = sorted(
        [{k: b[k] for k in ("notebook", "cell_idx", "line_no", "text", "target", "kind")}
         for b in broken],
        key=lambda x: (x["notebook"], x["cell_idx"], x["line_no"], x["target"]),
    )
    with open(BASELINE_PATH, "w", encoding="utf-8", newline="\n") as f:
        json.dump({"broken_links": snapshot}, f, ensure_ascii=False, indent=2)
        f.write("\n")
    return BASELINE_PATH


def _load_baseline():
    """Charge le baseline existant (ensemble de cles (notebook, cell_idx, line_no, target))."""
    if not BASELINE_PATH.is_file():
        return set()
    try:
        with open(BASELINE_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return set()
    keys = set()
    for b in data.get("broken_links", []):
        keys.add((b["notebook"], b["cell_idx"], b["line_no"], b["target"]))
    return keys


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Verifie les liens relatifs casses dans les cellules markdown des notebooks .ipynb."
    )
    parser.add_argument("notebook", nargs="?", help="Un notebook a scanner (defaut: tous)")
    parser.add_argument("--family", help="Limiter a une famille (ex. Search, Sudoku, ML)")
    parser.add_argument("--baseline", action="store_true",
                        help="Ecrire le baseline (snapshot des broken actuels)")
    parser.add_argument("--check", action="store_true",
                        help="Comparer au baseline ; exit 1 si NEW broken (regression)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON machine-readable")
    parser.add_argument("--quiet", action="store_true", help="Sortie minimale (CI)")
    args = parser.parse_args(argv)

    # collecte des cibles
    if args.notebook:
        p = (REPO_ROOT / args.notebook) if not Path(args.notebook).is_absolute() else Path(args.notebook)
        if not p.is_file():
            print(f"error: notebook introuvable: {args.notebook}", file=sys.stderr)
            return 2
        targets = [p]
    else:
        targets = list(_iter_notebooks(args.family))
        if not targets:
            where = f"famille {args.family!r}" if args.family else "MyIA.AI.Notebooks/"
            print(f"error: aucun notebook trouve sous {where}", file=sys.stderr)
            return 2

    broken, errors = run_scan(targets)

    if args.baseline:
        path = _write_baseline(broken)
        print(f"baseline ecrit: {path} ({len(broken)} liens casses connus)")
        return 0

    if args.check:
        known = _load_baseline()
        new_broken = [b for b in broken
                      if (b["notebook"], b["cell_idx"], b["line_no"], b["target"]) not in known]
        fixed = [k for k in known
                 if not any(b["notebook"] == k[0] and b["cell_idx"] == k[1]
                            and b["line_no"] == k[2] and b["target"] == k[3] for b in broken)]
        if new_broken:
            if not args.quiet:
                print(f"FAIL: {len(new_broken)} NEW broken navlink(s) vs baseline:")
                for b in new_broken:
                    print(f"  {b['notebook']} cell{b['cell_idx']} L{b['line_no']} [{b['kind']}]: "
                          f"[{b['text']}]({b['target']})")
            return 1
        if fixed and not args.quiet:
            print(f"INFO: {len(fixed)} broken link(s) fixed since baseline (update baseline).")
        if not args.quiet:
            print(f"OK: 0 NEW broken navlink vs baseline "
                  f"({len(broken)} connus, {len(targets)} notebook(s) scanne(s)).")
        return 0

    # mode par defaut : liste tous les broken
    if args.json:
        out = {"total_broken": len(broken), "broken": broken, "errors": errors,
               "scanned": len(targets)}
        json.dump(out, sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    else:
        if errors:
            for e in errors:
                print(f"warn: illisible: {e}", file=sys.stderr)
        nav = [b for b in broken if b["kind"] == "nav"]
        other = [b for b in broken if b["kind"] == "link"]
        if not broken:
            print(f"OK: 0 lien casse ({len(targets)} notebook(s) scanne(s)).")
        else:
            print(f"FOUND {len(broken)} lien(s) casse(s) ({len(nav)} navlinks, "
                  f"{len(other)} autres) dans {len(targets)} notebook(s):\n")
            for b in broken:
                print(f"  {b['notebook']} cell{b['cell_idx']} L{b['line_no']} [{b['kind']}]: "
                      f"[{b['text']}]({b['target']})")

    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(main())
