#!/usr/bin/env python3
"""Garde des listings Quarto : chaque motif `contents:` doit resoudre >= 1 fichier.

Issue #25680 (fille de l'EPIC #10921, critere 5 -- audit visuel du site publie).

Un listing Quarto est declare dans le front matter d'un `index.qmd` ou d'un
`README.md` :

    listing:
      - id: phase1
        contents: "GameTheory-01-Setup-Python.ipynb"
        type: grid

Quarto resout `contents:` relativement au repertoire du fichier source. Si le
motif ne correspond a AUCUN fichier, le listing se rend VIDE : le lecteur voit
une zone blanche sous son titre, et la console du navigateur porte l'erreur
`The list needs to have at least one item on init otherwise you'll have to add
a template.` C'est la classe de defaut mesuree le 2026-11-10 sur les pages
`GameTheory/` et `Probas/` (3 motifs sur 34, captures Playwright a l'appui),
reparee par #25682.

CE QUE CE GARDE APPORTE : aucun organe existant ne voyait cette classe.
`check_site_links.py` teste les LIENS ; un listing vide ne produit AUCUN lien
casse (le conteneur div est vide, il n'y a rien a resoudre) -- le defaut est
invisible aux gardes de liens, aux gardes de catalogue et aux controles de
prose. Ici, chaque motif `contents:` d'un front matter est resolu sur disque et
l'echec est nomme (fichier source, id du listing, motif).

Le garde est volontairement fail-closed sur le PERIMETRE qu'il annonce : tout
listing declare dans un front matter lu est verifie. Un front matter illisible
est une PANNE de l'instrument (exit 2), pas un verdict.

Exit codes :
  0 -- tous les motifs `contents:` resolvent au moins un fichier
  1 -- au moins un motif ne correspond a aucun fichier (raison nommee)
  2 -- instrument casse (front matter illisible, front matter annonce un
       listing que l'instrument ne sait pas lire)
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from dataclasses import dataclass
from typing import Any

import yaml

EXIT_OK = 0
EXIT_BROKEN_LISTING = 1
EXIT_INSTRUMENT = 2

# Repertoires sans front matter de serie : les ignorer evite de parcourir des
# arbres de dependances ou des sorties de rendu.
SKIP_DIRS = frozenset(
    {
        ".git",
        ".github",
        ".quarto",
        ".tmp",
        ".venv",
        "__pycache__",
        "_site",
        "node_modules",
        "site-packages",
        "venv",
    }
)

# Les deux formes de source qui portent des listings dans ce depot.
SOURCE_GLOBS = ("**/index.qmd", "**/README.md")


@dataclass(frozen=True)
class ListingTarget:
    """Une cible de listing : soit un motif glob, soit un chemin de fichier."""

    kind: str  # "glob" | "path"
    value: str


@dataclass(frozen=True)
class BrokenListing:
    """Un motif `contents:` qui ne correspond a aucun fichier."""

    source: str
    listing_id: str
    motif: str
    reason: str

    def to_dict(self) -> dict[str, str]:
        return {
            "source": self.source,
            "listing_id": self.listing_id,
            "motif": self.motif,
            "reason": self.reason,
        }


@dataclass(frozen=True)
class InstrumentError:
    """Une panne de l'instrument : le front matter n'a pas pu etre lu."""

    source: str
    reason: str

    def to_dict(self) -> dict[str, str]:
        return {"source": self.source, "reason": self.reason}


def collect_targets(contents: Any) -> list[ListingTarget]:
    """Extrait les cibles d'un `contents:` Quarto.

    Quarto accepte plusieurs formes, toutes rencontrees dans le depot :
    une chaine, une liste de chaines, une liste de dictionnaires
    (`{id: ..., contents: ...}` ou `{path: ...}`), un dictionnaire de
    dictionnaires, ou un dictionnaire simple.
    """
    targets: list[ListingTarget] = []
    if isinstance(contents, str):
        if contents.strip():
            targets.append(ListingTarget("glob", contents.strip()))
    elif isinstance(contents, list):
        for item in contents:
            targets.extend(collect_targets(item))
    elif isinstance(contents, dict):
        if "contents" in contents:
            targets.extend(collect_targets(contents["contents"]))
        elif "path" in contents:
            value = str(contents["path"]).strip()
            if value:
                targets.append(ListingTarget("path", value))
        else:
            for value in contents.values():
                targets.extend(collect_targets(value))
    return targets


def resolve_target(base: pathlib.Path, target: ListingTarget) -> int:
    """Nombre de fichiers correspondants a une cible, resolue depuis `base`.

    Les motifs contenant `://` sont des URL : Quarto les telecharge, elles ne
    se resolvent pas sur disque -- elles sont comptees comme resolues.
    """
    if "://" in target.value:
        return 1
    if target.kind == "path":
        candidate = base / target.value
        return 1 if candidate.exists() else 0
    if any(char in target.value for char in "*?["):
        return sum(1 for _ in base.glob(target.value))
    return 1 if (base / target.value).exists() else 0


def read_front_matter(path: pathlib.Path) -> dict[str, Any] | None:
    """Lit le front matter YAML d'un fichier, ou None s'il n'y en a pas.

    Leve `yaml.YAMLError` si le front matter est illisible -- l'appelant
    decide si c'est une panne (le fichier annonce un listing) ou un fichier
    sans rapport.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    if not text.startswith("---"):
        return None
    parts = text.split("---", 2)
    if len(parts) < 3:
        return None
    data = yaml.safe_load(parts[1])
    if data is None:
        return {}
    if not isinstance(data, dict):
        raise yaml.YAMLError("front matter non-mapping")
    return data


def iter_source_files(root: pathlib.Path) -> list[pathlib.Path]:
    """Fichiers susceptibles de porter un listing, tries pour un rapport stable.

    Le filtre porte sur les composants du chemin RELATIF a la racine : un
    filtre sur les composants ABSOLUS ecarterait silencieusement tout l'arbre
    des que la racine elle-meme est sous un repertoire de `SKIP_DIRS` (mesure
    du 2026-11-12 : un arbre de controle place sous `.tmp/` rendait
    `listings verifies : 0` et un rc 0 -- un vert qui ne mesurait rien).
    """
    found: set[pathlib.Path] = set()
    for pattern in SOURCE_GLOBS:
        for path in root.glob(pattern):
            relative = path.relative_to(root)
            if any(part in SKIP_DIRS for part in relative.parts):
                continue
            found.add(path)
    return sorted(found)


def scan(root: pathlib.Path) -> tuple[list[BrokenListing], list[InstrumentError], int]:
    """Parcourt l'arbre et mesure les motifs `contents:` non resolus.

    Retourne (broken, instrument_errors, nb_de_listings_verifies).
    """
    broken: list[BrokenListing] = []
    instrument_errors: list[InstrumentError] = []
    checked = 0

    for path in iter_source_files(root):
        try:
            front_matter = read_front_matter(path)
        except (yaml.YAMLError, OSError) as exc:
            # Un front matter illisible n'est une panne que si le fichier
            # annonce un listing : sinon c'est un fichier sans rapport.
            try:
                announces = "listing:" in path.read_text(
                    encoding="utf-8", errors="replace"
                )
            except OSError:
                announces = False
            if announces:
                instrument_errors.append(
                    InstrumentError(
                        source=_relative(path, root),
                        reason=f"front-matter-unreadable:{exc}",
                    )
                )
            continue

        if not front_matter or "listing" not in front_matter:
            continue

        listings = front_matter["listing"]
        if isinstance(listings, dict):
            listings = [listings]
        if not isinstance(listings, list):
            instrument_errors.append(
                InstrumentError(
                    source=_relative(path, root),
                    reason="listing-malformed:ni-liste-ni-dictionnaire",
                )
            )
            continue

        base = path.parent
        for item in listings:
            if not isinstance(item, dict):
                instrument_errors.append(
                    InstrumentError(
                        source=_relative(path, root),
                        reason="listing-malformed:entree-non-mapping",
                    )
                )
                continue
            listing_id = str(item.get("id", "?"))
            for target in collect_targets(item.get("contents")):
                checked += 1
                matched = resolve_target(base, target)
                if matched == 0:
                    broken.append(
                        BrokenListing(
                            source=_relative(path, root),
                            listing_id=listing_id,
                            motif=target.value,
                            reason=f"listing-empty:{listing_id}",
                        )
                    )

    return broken, instrument_errors, checked


def _relative(path: pathlib.Path, root: pathlib.Path) -> str:
    try:
        return str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        return str(path).replace("\\", "/")


def build_report(
    root: pathlib.Path, broken: list[BrokenListing], instrument_errors: list[InstrumentError], checked: int
) -> dict[str, Any]:
    """Rapport structure, partage entre la sortie texte et la sortie JSON."""
    return {
        "root": str(root),
        "checked": checked,
        "broken_count": len(broken),
        "instrument_errors": len(instrument_errors),
        "broken": [item.to_dict() for item in broken],
        "instrument_error_details": [item.to_dict() for item in instrument_errors],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie que chaque motif `contents:` d'un listing Quarto resolve >= 1 fichier."
    )
    default_root = pathlib.Path(__file__).resolve().parents[2]
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=default_root,
        help=f"Racine du depot (defaut : {default_root})",
    )
    parser.add_argument(
        "--json", action="store_true", help="Sortie structuree (JSON) au lieu du rapport texte"
    )
    args = parser.parse_args(argv)

    # Un chemin de serie peut porter des accents : sur un hote cp1252,
    # l'ecriture de la sortie.stdout leverait UnicodeEncodeError et le
    # verdict -- deja calcule -- serait perdu. On force l'UTF-8 tolerant.
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            reconfigure(encoding="utf-8", errors="replace")

    root = args.root.resolve()
    if not root.is_dir():
        print(f"check_quarto_listings: racine introuvable : {root}", file=sys.stderr)
        return EXIT_INSTRUMENT

    broken, instrument_errors, checked = scan(root)
    report = build_report(root, broken, instrument_errors, checked)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"listings verifies : {checked}")
        print(f"listings SANS correspondance sur disque : {len(broken)}")
        for item in broken:
            print(
                f"  {item.source} :: id={item.listing_id} :: motif={item.motif} :: 0 fichier"
            )
        if instrument_errors:
            print(f"panne de l'instrument : {len(instrument_errors)}")
            for item in instrument_errors:
                print(f"  {item.source} :: {item.reason}")

    if instrument_errors:
        return EXIT_INSTRUMENT
    if broken:
        return EXIT_BROKEN_LISTING
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
