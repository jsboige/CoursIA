#!/usr/bin/env python3
"""Convertit les liens `](X.html)` -> `](X.ipynb)` dans les READMEs rendus.

Pourquoi (doctrine inversee par #18911, geste 2, 2026-10-09)
------------------------------------------------------------
La navigation de reference est celle de **github.com** : un lien `.ipynb` y
ouvre le notebook dans le viewer. Les rendus Quarto ne sont **pas** committes
(ils n'existent que sur le deploiement Pages), donc un lien `.html` dans un
README de main rend un **404** sur github.com. C'est ce lien-la qui est le
defaut, et c'est au **site** de reecrire les liens `.ipynb` vers leur rendu
(geste 3), pas aux READMEs de s'adapter au site.

Historique : l'outil faisait exactement l'inverse avant le 2026-10-09 (il
convertissait `.ipynb` -> `.html`, classe `STALE_LINK` de #13025/#18970,
~2428 violations). L'arbitrage du user (Concern du 2026-10-08 sur #19897,
decision c.6076029168) a renverse la politique.

Classes actuelles de `scripts/regen_quarto_render.py --check-readme-links` :
- HTML_404 : le lien `.html` pointe une cible absente du depot -> 404 sur
  github.com. **C'est la classe que cet outil corrige**, en repointant vers le
  `.ipynb` sibling quand il existe.
- BROKEN : la cible du lien n'existe pas du tout -> lien mort a corriger
  separement (ne pas auto-convertir).

Ce que l'outil NE touche PAS
----------------------------
- Les liens absolus (`http://`, `https://`, `mailto:`) ou ancrage (`#`) ;
- Les liens `.html` dont le `.ipynb` sibling n'est pas un notebook suivi
  (page HTML autonome, index de site : conversion impossible, hors perimetre) ;
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
1 si des HTML_404 restent (--check), 2 en cas d'erreur.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Memes regex que regen_quarto_render.py : capture stricte des cibles `.ipynb`
# ou `.html` dans un lien markdown standard.
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


def _html_404_hrefs(text: str, base: Path, notebooks: set[str]):
    """Rend les (match, href, sibling) des liens `.html` corrigeables.

    Un lien est corrigeable s'il est relatif, hors fence, et que son `.ipynb`
    sibling est un notebook suivi (`notebooks` = ensemble repo-relative rendu
    par `git_tracked_notebooks()`).
    """
    for m in _HTML_LINK_RE.finditer(text):
        href = m.group(1)
        if href.startswith(("http://", "https://", "#", "mailto:")):
            continue
        if _is_inside_fence(text, m.start()):
            continue
        sibling = href[:-len(".html")] + ".ipynb"
        if _normalise_readme_target(base, sibling) in notebooks:
            yield m, href, sibling


def fix_readme_links(readme_path: Path, notebooks: set[str]) -> tuple[int, int]:
    """Convertit les liens HTML_404 corrigeables dans un README.

    Rend (nb_conversions, nb_violations_apres_legacy). Lis le fichier en mode
    binaire pour preserver les fins de ligne (LF/CRLF), re-ecrit en mode
    binaire apres substitutions.

    Une violation HTML_404 corrigeable = un href `.html` dont le `.ipynb`
    sibling est un notebook suivi : le README doit pointer vers le `.ipynb`
    (le viewer github.com), pas vers un rendu qui n'est pas dans le depot.
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

    # On collecte les edits (start, end, replacement) en parcourant les matchs,
    # puis on applique de la fin vers le debut pour ne pas invalider les offsets.
    edits: list[tuple[int, int, str]] = []
    for m, _href, sibling in _html_404_hrefs(text, base, notebooks):
        # L'edition porte sur le href UNIQUEMENT (pas les `](` autour)
        edits.append((m.start(1), m.end(1), sibling))

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


def count_html_404_links(readme_path: Path, notebooks: set[str]) -> int:
    """Compte les liens HTML_404 corrigeables dans un README sans rien ecrire."""
    try:
        raw_bytes = readme_path.read_bytes()
    except OSError:
        return 0
    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError:
        return 0

    base = Path(readme_path).parent
    return sum(1 for _ in _html_404_hrefs(text, base, notebooks))


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

    # `notebooks` = les notebooks suivis (repo-relative). Depuis l'inversion
    # (#18911), l'ensemble sert a valider le SIBLING `.ipynb` d'un lien `.html`,
    # plus la cible d'un lien `.ipynb`.
    notebooks = set(git_tracked_notebooks())

    files = 0
    conv = 0
    for readme in iter_readmes(args.targets):
        if args.apply:
            n, _ = fix_readme_links(readme, notebooks)
        else:
            n = count_html_404_links(readme, notebooks)
        if n:
            files += 1
            conv += n
            verbe = "converti" if args.apply else "a convertir"
            print(f"  {readme.as_posix()} : {n} HTML_404 {verbe}")

    verbe = "convertis" if args.apply else "a convertir"
    print(f"{conv} HTML_404 {verbe} dans {files} README(s)")
    if args.check and conv:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
