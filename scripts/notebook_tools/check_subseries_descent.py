#!/usr/bin/env python3
"""Recensement des sous-series descendues mais inachevees (consultatif).

Pour chaque repertoire de serie passe via ``--root``, cet organe mesure, pour
chaque sous-serie (sous-dossier direct contenant au moins un carnet), ce qui
manque a la descente :

- ``readme`` : la sous-serie a-t-elle un README ;
- ``marche`` : le README de la serie racine contient-il un lien vers elle ;
- ``descente`` : un carnet de la numerotation principale de la racine
  contient-il un lien qui descend vers elle (sans objet quand la racine ne
  porte aucun carnet : il n'y a pas de numerotation d'ou descendre) ;
- ``remontee`` : le dernier carnet de la sous-serie remonte-t-il vers le
  README racine ou un carnet de racine ;
- ``capstone`` : un carnet de la serie, hors de la sous-serie (en racine ou
  dans une sous-serie soeur), dont le nom contient ``Capstone``, cite-t-il au
  moins un carnet de la sous-serie (regle 6 de #5081 : le capstone vit dans
  la serie parente et consomme la sous-serie ; modele livre : #18857) ;
- ``ledger`` : le ledger de renommage pointe-t-il vers des cibles disparues ;
- ``traductions`` : les memoires de traduction citent-elles encore un ancien
  nom de fichier renomme.

Consultatif : lecture seule, jamais une gate CI. Sert les issues #20298,
#20316 et #19297.

Ce que cet organe NE certifie PAS : la dimension ``capstone`` est une
convention de nommage plus un lien. Elle ne dit pas que le carnet consomme
reellement la sous-serie (il peut n'en citer qu'un carnet : la couverture est
rendue a cote), ni qu'un carnet de synthese nomme autrement n'en tient pas
lieu -- ``consommateur_max`` nomme le carnet exterieur qui cite le plus de
carnets de la sous-serie, pour que le lecteur tranche. Il ne lit pas les
cellules de code des carnets : seules les cellules markdown sont parcourues
pour les liens.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.parse
from pathlib import Path
from typing import Any

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
LEDGER_DEFAULT = "docs/reference/rename-ledger.tsv"
TRANSLATIONS_DEFAULT = "translations"
TRADUCTIONS_CAP = 20

# Prefixes de cibles ignores par l'extraction de liens.
IGNORED_TARGET_PREFIXES = ("http://", "https://", "mailto:", "#")
# Extensions balayees dans le repertoire des memoires de traduction.
TRANSLATION_EXTS = {".csv", ".json", ".yaml", ".yml", ".tsv", ".md"}

MD_LINK_RE = re.compile(r"\]\(([^)]+)\)")
HREF_RE = re.compile(r'href="([^"]+)"')
NOM_NU_RE = re.compile(r"^(?:[A-Za-z]+-)?\d+[a-z]?$")
PREFIXED_DIR_RE = re.compile(r"^(?P<prefix>[A-Za-z]+)-(?P<num>\d+)-.+$")
ROOT_NB_NAME_RE = re.compile(r"^(?P<prefix>[A-Za-z]+)-(?P<num>\d+)(?P<accretion>[a-z]*)-")
CAPSTONE_NAME_RE = re.compile(r"capstone", re.IGNORECASE)

# Ordre fixe des slugs du champ ``manques``.
MANQUE_SLUGS = (
    "readme",
    "nom-nu",
    "marche",
    "descente",
    "remontee",
    "capstone",
    "ledger",
    "traductions",
)


# ---------------------------------------------------------------------------
# Helpers generaux
# ---------------------------------------------------------------------------

def natural_key(name: str) -> list[Any]:
    """Cle de tri naturel : separe chiffres et non-chiffres.

    ``Dynamics-2-x`` < ``Dynamics-10-x`` ; les zeros non significatifs sont
    ignores (``ICT-05`` == ``ICT-5`` pour le tri).
    """
    return [int(part) if part.isdigit() else part for part in re.split(r"(\d+)", name)]


def _canon(path: str | Path) -> str:
    """Forme canonique pour comparaisons : normpath + normcase."""
    return os.path.normcase(os.path.normpath(str(path)))


def _within(child: str | Path, parent: str | Path) -> bool:
    """Vrai si ``child`` designe ``parent`` lui-meme ou un chemin dessous."""
    c, p = _canon(child), _canon(parent)
    return c == p or c.startswith(p + os.sep)


def _rel_posix(path: Path, repo_root: Path) -> str:
    """Chemin relatif au repo racine, separateurs '/' (absolu en repli)."""
    try:
        return Path(os.path.relpath(path, repo_root)).as_posix()
    except ValueError:
        return Path(path).as_posix()


# ---------------------------------------------------------------------------
# Decouverte des carnets et des sous-series
# ---------------------------------------------------------------------------

def is_notebook_file(path: Path) -> bool:
    """Vrai pour un carnet ``*.ipynb`` hors ``*_output.ipynb`` et checkpoints."""
    name = path.name
    if not name.endswith(".ipynb") or name.endswith("_output.ipynb"):
        return False
    return ".ipynb_checkpoints" not in path.parts


def list_direct_notebooks(directory: Path) -> list[Path]:
    """Carnets directement dans ``directory`` (non recursif), tri naturel."""
    if not directory.is_dir():
        return []
    notebooks = [p for p in directory.iterdir() if p.is_file() and is_notebook_file(p)]
    return sorted(notebooks, key=lambda p: natural_key(p.name))


def is_subseries_dir(path: Path) -> bool:
    """Vrai pour un sous-dossier direct nomme (pas ``_``/``.``) avec carnets."""
    if not path.is_dir():
        return False
    name = path.name
    if name.startswith("_") or name.startswith("."):
        return False
    return any(p.is_file() and is_notebook_file(p) for p in path.iterdir())


def load_notebook(path: Path) -> dict[str, Any] | None:
    """Charge un carnet JSON ; None si illisible (decode ou JSON invalide)."""
    try:
        text = path.read_text(encoding="utf-8")
        data = json.loads(text)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def notebook_markdown(nb: dict[str, Any]) -> str:
    """Texte markdown concatene des cellules markdown (source liste ou str)."""
    parts: list[str] = []
    for cell in nb.get("cells", []):
        if not isinstance(cell, dict) or cell.get("cell_type") != "markdown":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            parts.append("".join(str(s) for s in source))
        elif isinstance(source, str):
            parts.append(source)
    return "\n".join(parts)


def extract_links(text: str, base_dir: Path) -> list[str]:
    """Cibles de liens markdown/HTML resolues relativement a ``base_dir``.

    Collecte les cibles de ``](cible)`` (y compris ``](cible "titre")``) et de
    ``href="cible"``. Ignore http(s)/mailto/#, retire fragment et requete,
    applique ``unquote``, normalise par ``os.path.normpath`` -- sans exiger
    que la cible existe.
    """
    raw_targets: list[str] = []
    for match in MD_LINK_RE.finditer(text):
        inner = match.group(1).strip()
        if inner:
            # `](cible "titre")` : la cible est le premier jeton.
            raw_targets.append(inner.split()[0])
    for match in HREF_RE.finditer(text):
        inner = match.group(1).strip()
        if inner:
            raw_targets.append(inner)
    resolved: list[str] = []
    for target in raw_targets:
        if target.startswith(IGNORED_TARGET_PREFIXES):
            continue
        target = target.split("#", 1)[0].split("?", 1)[0]
        if not target:
            continue
        target = urllib.parse.unquote(target)
        resolved.append(os.path.normpath(os.path.join(str(base_dir), target)))
    return resolved


# ---------------------------------------------------------------------------
# Ledger de renommage et memoires de traduction
# ---------------------------------------------------------------------------

def load_ledger(path: Path) -> list[dict[str, str]]:
    """Lignes du ledger TSV (colonnes ancien/nouveau). Fichier absent : []."""
    if not path.is_file():
        return []
    rows: list[dict[str, str]] = []
    with open(path, encoding="utf-8") as fh:
        fh.readline()  # en-tete : ancien / nouveau / date / lane
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 2 or not parts[0].strip() or not parts[1].strip():
                continue
            rows.append({"ancien": parts[0].strip(), "nouveau": parts[1].strip()})
    return rows


def load_translation_lines(translations_dir: Path) -> dict[str, list[str]]:
    """Lignes des fichiers de memoire de traduction, cle = chemin relatif '/'.

    Repertoire absent : dictionnaire vide (dimension rendue a 0).
    """
    if not translations_dir.is_dir():
        return {}
    lines_by_file: dict[str, list[str]] = {}
    all_files: list[Path] = []
    for dirpath, _dirnames, filenames in os.walk(translations_dir):
        for fname in filenames:
            fpath = Path(dirpath) / fname
            if fpath.suffix.lower() in TRANSLATION_EXTS:
                all_files.append(fpath)
    all_files.sort(key=lambda p: natural_key(str(p)))
    for fpath in all_files:
        with open(fpath, encoding="utf-8", errors="replace") as fh:
            lines_by_file[_rel_posix(fpath, translations_dir)] = fh.read().splitlines()
    return lines_by_file


def _search_translations(old_basename: str, translation_lines: dict[str, list[str]]) -> set[str]:
    """Occurrences ``fichier:ligne`` de l'ancien nom dans les memoires."""
    hits: set[str] = set()
    for rel_file, lines in translation_lines.items():
        for lineno, line in enumerate(lines, 1):
            if old_basename in line:
                hits.add(f"{rel_file}:{lineno}")
    return hits


# ---------------------------------------------------------------------------
# Mesures
# ---------------------------------------------------------------------------

def _papermill_old_name(nb: dict[str, Any], current_name: str) -> bool:
    """Vrai si papermill input/output_path cite un autre nom de fichier."""
    metadata = nb.get("metadata")
    if not isinstance(metadata, dict):
        return False
    papermill = metadata.get("papermill")
    if not isinstance(papermill, dict):
        return False
    for key in ("input_path", "output_path"):
        value = papermill.get(key)
        if not isinstance(value, str) or not value.strip():
            continue
        basename = os.path.basename(value.replace("\\", "/"))
        if basename.endswith("_output.ipynb"):
            basename = basename[: -len("_output.ipynb")] + ".ipynb"
        if basename != current_name:
            return True
    return False


def measure_subseries(
    sub_dir: Path,
    root_dir: Path,
    root_notebooks: list[Path],
    root_readme_links: list[str],
    root_nb_links: dict[str, list[str]],
    ledger_rows: list[dict[str, str]],
    translation_lines: dict[str, list[str]],
    repo_root: Path,
    illisibles: list[str],
    series_nb_links: dict[str, list[str]] | None = None,
) -> dict[str, Any]:
    """Mesure toutes les dimensions d'une sous-serie.

    ``series_nb_links`` : liens de tous les carnets de la serie (racine et
    sous-series soeurs), cle = chemin relatif a ``root_dir``. Absent : seuls
    les carnets de racine sont candidats au capstone.
    """
    sub_name = sub_dir.name
    sub_notebooks = list_direct_notebooks(sub_dir)

    # Dimension 1-2 : carnets et README.
    carnet_count = len(sub_notebooks)
    has_readme = (sub_dir / "README.md").is_file()

    # Dimension 3 : nom nu (nombre seul).
    nom_nu = bool(NOM_NU_RE.match(sub_name))

    # Dimension 4 : marche depuis le README racine.
    marche = sum(1 for target in root_readme_links if _within(target, sub_dir))

    # Dimension 5 : descente depuis un carnet de racine. Sans carnet en
    # racine, la dimension est sans objet (None), pas un manque.
    descente: list[str] | None
    if root_nb_links:
        descente = [
            name
            for name, links in root_nb_links.items()
            if any(_within(target, sub_dir) for target in links)
        ]
        descente.sort(key=natural_key)
    else:
        descente = None

    # Dimension 6 : remontee depuis les carnets de la sous-serie.
    root_readme_canon = _canon(root_dir / "README.md")
    root_notebook_names = {_canon(root_dir / name) for name in root_nb_links}
    remontee_total = 0
    remontee_dernier = False
    last_name = sub_notebooks[-1].name if sub_notebooks else None
    for nb_path in sub_notebooks:
        nb = load_notebook(nb_path)
        if nb is None:
            illisibles.append(_rel_posix(nb_path, repo_root))
            continue
        links = extract_links(notebook_markdown(nb), sub_dir)
        goes_up = any(
            _canon(target) == root_readme_canon or _canon(target) in root_notebook_names
            for target in links
        )
        if goes_up:
            remontee_total += 1
            if nb_path.name == last_name:
                remontee_dernier = True

    # Dimension 6 bis : capstone. Candidats = carnets de la serie hors de la
    # sous-serie ; chacun est compte par le nombre de carnets DISTINCTS de la
    # sous-serie qu'il cite.
    if series_nb_links is None:
        series_nb_links = dict(root_nb_links)
    sub_canon = {_canon(p) for p in sub_notebooks}
    consommateurs: list[tuple[int, str]] = []
    for rel_name, links in series_nb_links.items():
        if _within(root_dir / rel_name, sub_dir):
            continue
        cited = {_canon(target) for target in links} & sub_canon
        if cited:
            consommateurs.append((len(cited), rel_name))
    consommateurs.sort(key=lambda item: (-item[0], natural_key(item[1])))
    capstones = [
        {"carnet": rel_name, "couverture": count}
        for count, rel_name in consommateurs
        if CAPSTONE_NAME_RE.search(os.path.basename(rel_name))
    ]
    consommateur_max = (
        {"carnet": consommateurs[0][1], "couverture": consommateurs[0][0]}
        if consommateurs
        else None
    )

    # Dimension 7 : tete et accretions en racine (comparees en entiers).
    dir_match = PREFIXED_DIR_RE.match(sub_name)
    if dir_match:
        prefix = dir_match.group("prefix")
        number = int(dir_match.group("num"))
        tete_racine: list[str] | None = []
        accretions_racine: list[str] | None = []
        for nb_path in root_notebooks:
            name_match = ROOT_NB_NAME_RE.match(nb_path.name)
            if not name_match or name_match.group("prefix") != prefix:
                continue
            if int(name_match.group("num")) != number:
                continue
            if name_match.group("accretion"):
                accretions_racine.append(nb_path.name)
            else:
                tete_racine.append(nb_path.name)
        tete_racine.sort(key=natural_key)
        accretions_racine.sort(key=natural_key)
    else:
        tete_racine = None
        accretions_racine = None

    # Dimensions 8-9 : ledger et memoires de traduction.
    sub_rel = _rel_posix(sub_dir, repo_root)
    rows_under = [
        row
        for row in ledger_rows
        if row["nouveau"] == sub_rel or row["nouveau"].startswith(sub_rel + "/")
    ]
    ledger_lignes = len(rows_under)
    ancien_values = {row["ancien"] for row in ledger_rows}
    ledger_cibles_disparues = sorted(
        {
            row["nouveau"]
            for row in rows_under
            if not (repo_root / row["nouveau"]).exists() and row["nouveau"] not in ancien_values
        }
    )
    traduction_hits: set[str] = set()
    for row in rows_under:
        old_base = os.path.basename(row["ancien"].replace("\\", "/"))
        new_base = os.path.basename(row["nouveau"].replace("\\", "/"))
        if old_base == new_base:
            continue
        traduction_hits.update(_search_translations(old_base, translation_lines))
    ordered_hits = sorted(traduction_hits, key=natural_key)
    traductions_perimees = ordered_hits[:TRADUCTIONS_CAP]
    traductions_perimees_total = len(ordered_hits)

    # Dimension 10 : metadata papermill qui cite un ancien nom.
    metadata_ancien_nom: list[str] = []
    for nb_path in sub_notebooks:
        nb = load_notebook(nb_path)
        if nb is None:
            continue  # deja signale dans illisibles plus haut
        if _papermill_old_name(nb, nb_path.name):
            metadata_ancien_nom.append(nb_path.name)
    metadata_ancien_nom.sort(key=natural_key)

    # Dimension 11 : manques (ordre fixe) et etat fini.
    conditions = {
        "readme": not has_readme,
        "nom-nu": nom_nu,
        "marche": marche == 0,
        "descente": descente is not None and not descente,
        "remontee": not remontee_dernier,
        "capstone": not capstones,
        "ledger": bool(ledger_cibles_disparues),
        "traductions": traductions_perimees_total > 0,
    }
    manques = [slug for slug in MANQUE_SLUGS if conditions[slug]]

    return {
        "nom": sub_name,
        "chemin": sub_rel,
        "carnets": carnet_count,
        "readme": has_readme,
        "nom_nu": nom_nu,
        "marche": marche,
        "descente": descente,
        "remontee_dernier": remontee_dernier,
        "remontee_total": remontee_total,
        "capstones": capstones,
        "consommateur_max": consommateur_max,
        "tete_racine": tete_racine,
        "accretions_racine": accretions_racine,
        "ledger_lignes": ledger_lignes,
        "ledger_cibles_disparues": ledger_cibles_disparues,
        "traductions_perimees": traductions_perimees,
        "traductions_perimees_total": traductions_perimees_total,
        "metadata_ancien_nom": metadata_ancien_nom,
        "manques": manques,
        "finie": not manques,
    }


def measure_root(
    root_dir: Path,
    repo_root: Path,
    ledger_rows: list[dict[str, str]],
    translation_lines: dict[str, list[str]],
    exclude: frozenset[str] = frozenset(),
) -> tuple[dict[str, Any], list[str]]:
    """Mesure une serie racine ; renvoie (donnees, carnets illisibles).

    ``exclude`` : noms de sous-dossiers directs a ne pas compter comme
    sous-series (un dossier de service qui porte un carnet, par exemple).
    """
    illisibles: list[str] = []
    root_notebooks = list_direct_notebooks(root_dir)

    # Liens du README racine (marche).
    readme_path = root_dir / "README.md"
    readme_links: list[str] = []
    if readme_path.is_file():
        text = readme_path.read_text(encoding="utf-8", errors="replace")
        readme_links = extract_links(text, root_dir)

    # Liens des carnets de racine (descente).
    root_nb_links: dict[str, list[str]] = {}
    for nb_path in root_notebooks:
        nb = load_notebook(nb_path)
        if nb is None:
            illisibles.append(_rel_posix(nb_path, repo_root))
            root_nb_links[nb_path.name] = []
            continue
        root_nb_links[nb_path.name] = extract_links(notebook_markdown(nb), root_dir)

    # Sous-series immediates, tri naturel sur le nom.
    subdirs = [
        p
        for p in sorted(root_dir.iterdir(), key=lambda p: natural_key(p.name))
        if is_subseries_dir(p) and p.name not in exclude
    ]

    # Liens de tous les carnets de la serie (capstone) : racine + sous-series.
    # Un carnet illisible est signale par la mesure de sa sous-serie.
    series_nb_links: dict[str, list[str]] = dict(root_nb_links)
    for sub in subdirs:
        for nb_path in list_direct_notebooks(sub):
            nb = load_notebook(nb_path)
            rel_name = "%s/%s" % (sub.name, nb_path.name)
            series_nb_links[rel_name] = (
                extract_links(notebook_markdown(nb), sub) if nb is not None else []
            )

    sous_series = [
        measure_subseries(
            sub_dir=p,
            root_dir=root_dir,
            root_notebooks=root_notebooks,
            root_readme_links=readme_links,
            root_nb_links=root_nb_links,
            ledger_rows=ledger_rows,
            translation_lines=translation_lines,
            repo_root=repo_root,
            illisibles=illisibles,
            series_nb_links=series_nb_links,
        )
        for p in subdirs
    ]

    data = {
        "root": root_dir.as_posix(),
        "racine_carnets": len(root_notebooks),
        "readme_racine": readme_path.is_file(),
        "sous_series": sous_series,
        "finies": sum(1 for ss in sous_series if ss["finie"]),
        "total": len(sous_series),
    }
    return data, illisibles


# ---------------------------------------------------------------------------
# Rendus
# ---------------------------------------------------------------------------

HEADERS = [
    "Sous-serie",
    "Carnets",
    "README",
    "Marche",
    "Descente",
    "Remontee",
    "Capstone",
    "Accretions en racine",
    "Ledger",
    "Traductions",
    "Manques",
]


def _row_cells(ss: dict[str, Any]) -> list[str]:
    """Cellules texte/markdown d'une ligne de sous-serie."""
    readme = "oui" if ss["readme"] else "non"
    remontee = "oui" if ss["remontee_dernier"] else "non"
    if ss["capstones"]:
        capstone = "oui (%d/%d)" % (ss["capstones"][0]["couverture"], ss["carnets"])
    elif ss["consommateur_max"]:
        capstone = "non (max %d/%d)" % (ss["consommateur_max"]["couverture"], ss["carnets"])
    else:
        capstone = "non"
    if ss["accretions_racine"] is None:
        accretions = "n/a"
    else:
        accretions = str(len(ss["accretions_racine"]))
    ledger = str(ss["ledger_lignes"])
    if ss["ledger_cibles_disparues"]:
        ledger += " (%d disparues)" % len(ss["ledger_cibles_disparues"])
    manques = ", ".join(ss["manques"]) if ss["manques"] else "aucun"
    return [
        ss["nom"],
        str(ss["carnets"]),
        readme,
        str(ss["marche"]),
        "n/a" if ss["descente"] is None else str(len(ss["descente"])),
        remontee,
        capstone,
        accretions,
        ledger,
        str(ss["traductions_perimees_total"]),
        manques,
    ]


def _illisibles_footer(data: dict[str, Any]) -> str:
    if not data["illisibles"]:
        return ""
    return "Carnets illisibles (JSON invalide) : " + ", ".join(data["illisibles"])


def render_markdown(data: dict[str, Any]) -> str:
    """Tableau GitHub markdown, un bloc par racine (a coller dans une issue)."""
    blocks: list[str] = []
    for rd in data["roots"]:
        lines = [
            "**%s** — %d/%d sous-series finies" % (rd["root"], rd["finies"], rd["total"]),
            "",
            "| " + " | ".join(HEADERS) + " |",
            "|" + "---|" * len(HEADERS),
        ]
        for ss in rd["sous_series"]:
            lines.append("| " + " | ".join(_row_cells(ss)) + " |")
        blocks.append("\n".join(lines))
    out = "\n\n".join(blocks)
    footer = _illisibles_footer(data)
    if footer:
        out += "\n\n" + footer
    return out


def render_text(data: dict[str, Any]) -> str:
    """Tableau texte aligne, un bloc par racine."""
    blocks: list[str] = []
    for rd in data["roots"]:
        rows = [_row_cells(ss) for ss in rd["sous_series"]]
        widths = [len(h) for h in HEADERS]
        for row in rows:
            for i, cell in enumerate(row):
                widths[i] = max(widths[i], len(cell))
        lines = ["%s — %d/%d sous-series finies" % (rd["root"], rd["finies"], rd["total"])]
        lines.append("  ".join(h.ljust(widths[i]) for i, h in enumerate(HEADERS)).rstrip())
        for row in rows:
            lines.append("  ".join(c.ljust(widths[i]) for i, c in enumerate(row)).rstrip())
        blocks.append("\n".join(lines))
    out = "\n\n".join(blocks)
    footer = _illisibles_footer(data)
    if footer:
        out += "\n\n" + footer
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Recensement (consultatif) des sous-series descendues mais inachevees."
    )
    parser.add_argument(
        "--root",
        action="append",
        required=True,
        metavar="DIR",
        help="repertoire de serie, relatif au repo racine (repeter pour plusieurs)",
    )
    parser.add_argument(
        "--repo-root",
        default=str(REPO_ROOT_DEFAULT),
        help="repo racine (defaut : racine git du script)",
    )
    parser.add_argument(
        "--ledger",
        default=LEDGER_DEFAULT,
        help="TSV du ledger de renommage, relatif au repo racine",
    )
    parser.add_argument(
        "--translations",
        default=TRANSLATIONS_DEFAULT,
        help="repertoire des memoires de traduction, relatif au repo racine",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="NOM",
        help="sous-dossier direct a ne pas compter comme sous-serie (repeter)",
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--json", action="store_true", help="sortie machine JSON")
    group.add_argument("--markdown", action="store_true", help="tableau markdown par racine")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit 1 si au moins une sous-serie a un manque",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).absolute()
    ledger_rows = load_ledger(repo_root / args.ledger)
    translation_lines = load_translation_lines(repo_root / args.translations)

    roots_data: list[dict[str, Any]] = []
    illisibles: list[str] = []
    for raw in args.root:
        candidate = Path(raw)
        if not candidate.is_absolute():
            candidate = repo_root / candidate
        if not candidate.is_dir():
            print("erreur : --root %s n'est pas un repertoire" % raw, file=sys.stderr)
            return 2
        data, root_illisibles = measure_root(
            candidate, repo_root, ledger_rows, translation_lines, frozenset(args.exclude)
        )
        data["root"] = Path(raw).as_posix()
        roots_data.append(data)
        illisibles.extend(root_illisibles)

    payload = {"roots": roots_data, "illisibles": sorted(set(illisibles))}

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    elif args.markdown:
        print(render_markdown(payload))
    else:
        print(render_text(payload))

    if args.strict and any(ss["manques"] for rd in roots_data for ss in rd["sous_series"]):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
