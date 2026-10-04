#!/usr/bin/env python3
"""Convertit les liens `](X.ipynb)` -> `](X.html)` dans les READMEs rendus.

Pourquoi
--------
Le site Pages sert des liens `.html` pour les notebooks rendus par Quarto.
Les READMEs rendus continuent de lier le `.ipynb` brut -> 404 sur Pages
(defaut #13025, 2024-09 ; ~2428 violations mesure 2026-10-03, worktree #18423).

L'instrument `scripts/regen_quarto_render.py --check-readme-links` rend la liste
des violations en 3 classes :
- STALE_LINK : le `.ipynb` cible EST dans la render-list ; le `.html` sibling
  existe. Le README doit pointer vers le `.html`.
- BROKEN : le `.ipynb` cible n'existe pas du tout -> lien mort a corriger
  separement (ne pas auto-convertir en `.html`).
- DEAD_RENDER : un `.html` lie une source qui n'est pas rendue -> le rendu
  n'existera pas, garder en l'etat n'est pas un defaut de conversion.

Cet outil NE convertit QUE les STALE_LINK. Les BROKEN et DEAD_RENDER ne sont
pas du ressort de la conversion de masse.

Ce que l'outil NE touche PAS
----------------------------
- Les liens absolus (`http://`, `https://`, `mailto:`) ou ancrage (`#`) ;
- Les liens `.html` deja corrects (DEAD_RENDER traite separement) ;
- Les liens vers un `.ipynb` hors render-list (population source brute
  documentee par `#11451` / `#11451-archive` ; ne pas convertir) ;
- Les cellules code, blocs de fence (triple backticks), le YAML frontmatter.

Distinction avec `regen_quarto_render.py --check-readme-links`
--------------------------------------------------------------
Ce dernier vise le diagnostic ; le present outil applique la correction
deterministe en `--apply` ou compte en `--check`.

Usage
-----
    python scripts/notebook_tools/fix_ipynb_links.py --check MyIA.AI.Notebooks/SymbolicAI/Tweety
    python scripts/notebook_tools/fix_ipynb_links.py --apply MyIA.AI.Notebooks/SymbolicAI/Tweety

Sortie : 0 si rien a convertir (--check) ou conversion faite (--apply),
1 si des STALE_LINK restent (--check), 2 en cas d'erreur.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Reprend les memes regex que regen_quarto_render.py : capture stricte des
# cibles `.ipynb` ou `.html` dans un lien markdown standard.
_IPYNB_LINK_RE = re.compile(r"\]\(([^)#\s]+\.ipynb)\)")
_HTML_LINK_RE = re.compile(r"\]\(([^)#\s]+\.html)\)")


def _normalise_readme_target(base: Path, href: str) -> str:
    """Return a repository-relative POSIX path with ``..`` resolved."""
    import posixpath
    return posixpath.normpath((base / href).as_posix())


def _is_inside_fence(text: str, pos: int) -> bool:
    """Vrai si la position pos dans text est dans un bloc de code fence.

    Marche par comptage d'ouvertures/fermetures ``` ou ~~~ au-dessus de pos.
    On reste volontairement grossier : si une fence semble ouverte, on considere
    que pos est dedans ; sinon, on n'est pas dans une fence.
    """
    in_fence = False
    fence_re = re.compile(r"^(`{3,}|~{3,})", re.MULTILINE)
    for m in fence_re.finditer(text, 0, pos):
        in_fence = not in_fence
    return in_fence


def fix_readme_links(readme_path: Path, rendered: set[str]) -> tuple[int, int]:
    """Convertit les STALE_LINK dans un README.

    Rend (nb_conversions, nb_violations_apres_legacy). Lis le fichier en mode
    binaire pour preserver les fins de ligne (LF/CRLF), re-ecrit en mode
    binaire apres substitutions.

    Une violation STALE_LINK = un href `.ipynb` qui pointe vers un fichier
    qui EST dans la render-list (donc un `.html` sibling existe).

    On ne touche PAS aux hrefs `.ipynb` hors render-list (UNRENDERED, source
    brute documentee par `#11451`).
    """
    try:
        raw_bytes = readme_path.read_bytes()
    except OSError as exc:
        print(f"ILLISIBLE {readme_path}: {exc}", file=sys.stderr)
        return 0, 0
    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        print(f"ILLISIBLE {readme_path}: {exc}", file=sys.stderr)
        return 0, 0

    base = Path(readme_path).parent
    nb_conversions = 0

    # On collecte les edits (start, end, replacement) en parcourant les matchs,
    # puis on applique de la fin vers le debut pour ne pas invalider les offsets.
    edits: list[tuple[int, int, str]] = []
    for m in _IPYNB_LINK_RE.finditer(text):
        href = m.group(1)
        if href.startswith(("http://", "https://", "#", "mailto:")):
            continue
        if _is_inside_fence(text, m.start()):
            continue
        norm = _normalise_readme_target(base, href)
        if norm in rendered:
            # STALE_LINK : on convertit le href
            new_href = href[:-len(".ipynb")] + ".html"
            # L'edition porte sur le href UNIQUEMENT (pas les `](` autour)
            href_start = m.start(1)
            href_end = m.end(1)
            edits.append((href_start, href_end, new_href))

    if not edits:
        return 0, 0

    # Application des edits en ordre inverse
    edits.sort(key=lambda e: e[0], reverse=True)
    new_text = text
    for (s, e, repl) in edits:
        new_text = new_text[:s] + repl + new_text[e:]

    nb_conversions = len(edits)
    readme_path.write_bytes(new_text.encode("utf-8"))
    return nb_conversions, 0


def count_stale_links(readme_path: Path, rendered: set[str]) -> int:
    """Compte les STALE_LINK dans un README sans rien ecrire."""
    try:
        raw_bytes = readme_path.read_bytes()
    except OSError:
        return 0
    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError:
        return 0

    base = Path(readme_path).parent
    nb = 0
    for m in _IPYNB_LINK_RE.finditer(text):
        href = m.group(1)
        if href.startswith(("http://", "https://", "#", "mailto:")):
            continue
        if _is_inside_fence(text, m.start()):
            continue
        norm = _normalise_readme_target(base, href)
        if norm in rendered:
            nb += 1
    return nb


def iter_readmes(targets: list[str]):
    """Iterate les READMEs dans les targets (fichiers ou repertoires)."""
    for t in targets:
        p = Path(t)
        if p.is_dir():
            for md in sorted(p.rglob("README.md")):
                yield md
        elif p.suffix == ".md":
            yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="ne rien ecrire, compter")
    mode.add_argument("--apply", action="store_true", help="ecrire les conversions")
    ap.add_argument("targets", nargs="+", help="fichiers README.md ou repertoires")
    args = ap.parse_args(argv)

    # Import tardif pour eviter une dep circulaire dans les tests
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from regen_quarto_render import git_tracked_notebooks

    rendered = set(git_tracked_notebooks())

    files = 0
    conv = 0
    for readme in iter_readmes(args.targets):
        if args.apply:
            n, _ = fix_readme_links(readme, rendered)
        else:
            n = count_stale_links(readme, rendered)
        if n:
            files += 1
            conv += n
            verbe = "converti" if args.apply else "a convertir"
            print(f"  {readme.as_posix()} : {n} STALE_LINK {verbe}")

    verbe = "convertis" if args.apply else "a convertir"
    print(f"{conv} STALE_LINK {verbe} dans {files} README(s)")
    if args.check and conv:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())