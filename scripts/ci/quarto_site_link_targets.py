#!/usr/bin/env python3
"""Reecrit, dans le HTML RENDU, les liens que le site ne peut pas servir.

Pourquoi (#10921, sous-grain garde/README de series, mesure du 2026-11-10)
------------------------------------------------------------------------
La navigation de reference est celle de github.com (arbitrage user du
2026-10-08, decision c.6076029168 sur #18911) : les READMEs lient les
cibles sous leur forme depot (``X.ipynb``, ``X/``, ``../../.claude/...``)
et c'est au SITE d'adapter au moment du rendu. Quarto reecrit nativement
les cibles du projet (``.ipynb`` rendus), mais deux familles lui echappent
et rendent 404/503 sur Pages alors qu'elles sont correctes sur github.com :

- les liens de REPERTOIRE (``](X/)``) : github.com sert l'arbre, Pages
  n'a pas d'index de repertoire (le README rendu vit a ``X/README.html``) ;
- les liens vers des FICHIERS hors render-list (``../../.claude/rules/..``,
  ``../../.github/workflows/..``, ``.env.example``) : jamais publies.

Mesure du 2026-11-10 (organe check_site_links, 16 README de series) :
674 liens internes, 54 casses dont ~48 liens repertoire et 4 fichiers
hors rendu. Cette passe repare les deux familles dans le HTML rendu,
sans toucher les sources (aucun apply/restore : la passe est post-rendu
sur ``_site/``, les fichiers du depot restent byte-identiques).

Regles de reecriture (idempotentes)
------------------------------------
Pour chaque ``href`` interne d'une page de ``_site/`` :

1. la cible existe dans ``_site/`` ET n'est pas un chemin cache     -> intact ;
2. chemin de repertoire ``X/`` avec ``X/README.html`` rendu         -> ``X/README.html`` ;
3. chemin de repertoire ``X/`` existant dans le depot, sans rendu   -> URL absolue ``tree/main/X`` ;
4. chemin de fichier existant dans le depot, hors render-list      -> URL absolue ``blob/main/<path>`` ;
5. le reste (cible absente du depot ET du site)                     -> intact :
   le garde post-deploiement (check_site_links) le signale -- cette
   passe ne masque jamais un vrai lien mort.

Cible cachee : un chemin dont un composant commence par un point
(``.claude/``, ``.github/``, ``.env.example``) n'est JAMAIS servi par
Pages -- l'artefact publie est produit par ``actions/upload-artifact@v4``
dont l'option ``include-hidden-files`` est a ``false`` (defaut, mesure dans
les logs de deploiement du 2026-11-11). La regle 1 ne doit donc pas
declarer « servable » une cible cachee : ces cibles partent en
``blob/main/`` (regle 4), qui resout sur github.com.

Mesure du 2026-11-11 (organe ``check_site_links`` contre le site servi,
1 833 liens sondes) : sans cette correction, **5 URL** (6 lignes de source)
repondent 404 -- ``.claude/rules/catalog-pr-hygiene.md``,
``.claude/rules/wsl-kernels.md``, ``.github/workflows/catalog-cron.yml``,
``GenAI/.env.example`` et
``ML/DataScienceWithAgents/07-Agent-Orchestration/.env.example``. La passe
les croyait servables parce que Quarto copie dans ``_site/`` les fichiers
locaux lies depuis les README rendus -- copie que l'artefact ne publie
jamais.

Les images (``![...](...)``) et les ``.ipynb`` sont hors perimetre :
les ``.ipynb`` sont la forme de reference (github.com) et Quarto les
reecrit deja ; la population non reecrite est suivie par ailleurs
(#25055, page catalogue). Les URLs absolues et ancres sont ignorees.

Usage
-----
    python scripts/ci/quarto_site_link_targets.py            # applique sur _site/
    python scripts/ci/quarto_site_link_targets.py --check    # liste sans ecrire, rc 1 si reecritures dues
    python scripts/ci/quarto_site_link_targets.py --site-dir _site --repo-root .

Sorties : 0 rien a faire (ou reecrit), 1 reecritures restantes en --check,
2 instrument casse (repertoire _site/ illisible).
"""
from __future__ import annotations

import argparse
import os
import re
import sys
import urllib.parse
from pathlib import Path

GITHUB_BASE = "https://github.com/jsboige/CoursIA"
EXIT_OK = 0
EXIT_PENDING = 1
EXIT_INSTRUMENT = 2

_HREF_RE = re.compile(r'href="([^"]+)"', re.IGNORECASE)
# Cibles consciemment hors perimetre (forme de reference ou suivi ailleurs).
_SKIP_SUFFIXES = (".ipynb",)
_SKIP_SCHEMES = ("http://", "https://", "mailto:", "javascript:", "data:", "tel:")


def _resolve_under(base_dir: Path, href: str) -> Path | None:
    """Normalise (base_dir + href) en chemin relatif a la racine du site.

    ``base_dir`` est le repertoire du fichier HTML rendu, exprime relativement
    a la racine du site (``_site/`` retire). Les ``..`` remontent depuis cette
    profondeur ; un chemin qui depasserait la racine rend None (hors site).
    """
    raw = urllib.parse.unquote(href.split("?")[0].split("#")[0])
    if not raw or raw.startswith("/"):
        return None
    acc = [seg for seg in base_dir.as_posix().split("/") if seg not in ("", ".")]
    for seg in raw.replace("\\", "/").split("/"):
        if seg in ("", "."):
            continue
        if seg == "..":
            if not acc:
                return None
            acc.pop()
        else:
            acc.append(seg)
    return Path(*acc) if acc else None


def _relative_href(from_dir: Path, target: Path) -> str:
    """Href relatif lisible (``Audio/README.html``, ``../x/README.html``)."""
    rel = Path(os.path.relpath(target, from_dir)).as_posix()
    return rel


def _is_hidden(rel: Path) -> bool:
    """Vrai si un composant du chemin commence par un point.

    Une cible cachee n'est jamais publiee par Pages : l'artefact sort de
    ``actions/upload-artifact@v4`` avec ``include-hidden-files: false``
    (defaut, mesure dans les logs de deploiement du 2026-11-11). La
    presence d'une telle cible dans ``_site/`` -- Quarto y copie les
    fichiers locaux lies depuis les README rendus -- ne dit donc rien de
    sa servabilite sur le site publie.
    """
    return any(part.startswith(".") and part not in (".", "..")
               for part in rel.parts)


def rewrite_href(
    href: str,
    html_repo_dir: Path,
    site_root: Path,
    repo_root: Path,
) -> str | None:
    """Rend le remplacement pour un href interne, ou None si intact.

    ``html_repo_dir`` : emplacement du fichier HTML rendu, traduit en
    chemin relatif du depot (``_site/`` retire) -- la resolution d'un
    href relatif dans le rendu mirror celle de la source.
    """
    if href.startswith("#"):
        return None
    low = href.lower()
    if low.startswith(_SKIP_SCHEMES) or low.endswith(_SKIP_SUFFIXES):
        return None
    rel = _resolve_under(html_repo_dir, href)
    if rel is None:
        return None
    norm_href = rel.as_posix()

    # Une cible cachee n'est jamais publiee (artefact upload-artifact@v4,
    # include-hidden-files: false) : sa presence dans _site/ ne la rend pas
    # servable. Elle part donc en blob/main (regle 4) comme tout fichier
    # du depot hors render-list.
    hidden = _is_hidden(rel)

    if not hidden and (site_root / rel).is_file():
        return None  # servable tel quel (un repertoire dans _site/ n'est pas servable)

    # Dir-href : le test s'entend sur le chemin epuice de son fragment et de
    # sa query -- "X/#section" est un lien de repertoire (le rstrip("#") d'une
    # chaine finissant par "section" ne detectait rien). Le fragment est
    # reconduit sur la cible : perdre "#section" casserait la navigation.
    base_href = href.split("#")[0].split("?")[0]
    fragment = href.split("#", 1)[1] if "#" in href else ""
    suffix = f"#{fragment}" if fragment else ""
    is_dir_href = base_href.endswith("/")
    if is_dir_href:
        readme = rel / "README.html"
        if not hidden and (site_root / readme).exists():
            return _relative_href(html_repo_dir, readme) + suffix
        if (repo_root / rel).is_dir():
            return f"{GITHUB_BASE}/tree/main/{norm_href}{suffix}"
        return None

    # Chemin de fichier absent du site : present dans le depot -> blob.
    if (repo_root / rel).is_file():
        return f"{GITHUB_BASE}/blob/main/{norm_href}"
    return None


def process_html(
    html_path: Path,
    site_root: Path,
    repo_root: Path,
    apply: bool,
) -> tuple[int, list[str]]:
    """Reecrit les href d'une page rendue ; rend (reecritures, details)."""
    repo_rel = html_path.relative_to(site_root)
    html_repo_dir = repo_rel.parent
    try:
        text = html_path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        # Sortie Quarto = UTF-8. Une page qui ne decode pas est un signal
        # d'instrument, pas un contenu a reecrire : la laisser intacte plutot
        # que de consoler des octets remplaces (read+write en replace fige
        # la corruption). Le detail la nomme pour le rapport.
        return 0, [f"SKIP non-UTF8: {html_path.name}"]
    changes: list[str] = []

    def sub(m: re.Match[str]) -> str:
        href = m.group(1)
        new = rewrite_href(href, html_repo_dir, site_root, repo_root)
        if new is None or new == href:
            return m.group(0)
        changes.append(f"{href} -> {new}")
        return f'href="{new}"'

    out = _HREF_RE.sub(sub, text)
    if changes and apply:
        html_path.write_text(out, encoding="utf-8")
    return len(changes), changes


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--site-dir", default="_site", help="racine du site rendu")
    ap.add_argument("--repo-root", default=".", help="racine du checkout du depot")
    ap.add_argument(
        "--check", action="store_true",
        help="liste les reecritures dues sans ecrire (rc 1 si non vide)")
    args = ap.parse_args()

    site_root = Path(args.site_dir).resolve()
    repo_root = Path(args.repo_root).resolve()
    if not site_root.is_dir():
        print(f"[site-link-targets] repertoire site introuvable: {site_root}")
        return EXIT_INSTRUMENT

    total = 0
    details: list[str] = []
    for html_path in sorted(site_root.rglob("*.html")):
        n, page_changes = process_html(html_path, site_root, repo_root,
                                        apply=not args.check)
        if page_changes:
            rel = html_path.relative_to(site_root).as_posix()
            details.append(f"{rel}: {n} reecriture(s)")
            details.extend(f"    {c}" for c in page_changes)
            total += n

    verdict = "DUES" if args.check else "APPLIQUEES"
    print(f"[site-link-targets] {total} reecriture(s) {verdict} "
          f"sur {site_root.name}/")
    for line in details:
        print(line)
    if args.check and total:
        return EXIT_PENDING
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
