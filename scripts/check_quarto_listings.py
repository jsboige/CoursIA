#!/usr/bin/env python3
"""Verifie les motifs `contents:` des listings Quarto suivis par Git.

Les chemins sont resolus depuis le repertoire du document. Les formes prises en
charge sont les chaines, les listes de chaines positives, les dictionnaires
(`{path:}`, `contents` imbrique, dictionnaire de dictionnaires) et les URLs ;
toute autre forme est signalee pour eviter de declarer une couverture
inexistante.

Historique de l'organe (un seul siege, deux etapes) :
- #25944 a ajoute ce fichier et son siege dans l'etape `always-on-guards`
  (toute PR, sans filtre de chemins) ;
- la garde a ete portee dans la voie rapide (#26172), ou la classe etait
  deja couverte : le second organe qu'elle apportait a ete **fusionne dans
  celui-ci** au lieu d'etre ajoute. Ce fichier porte donc les deux apports :
  les formes dict, les URLs, la sortie `--json`, le rc 2 pour une panne de
  l'instrument et le controle positif sur l'arbre reel. Les sources restent
  celles de #25944 (`git ls-files`), plus larges qu'un `index.qmd`/`README.md`,
  et le traitement fail-closed des negations est conserve.

Un listing Quarto vide se rend en zone blanche sous son titre, et la console
porte l'erreur « The list needs to have at least one item on init ». C'est la
classe de defaut mesuree le 2026-11-10 sur les pages `GameTheory/` et
`Probas/` (3 motifs sur 34), reparee par #25682.

Codes de sortie :
  0 -- tous les motifs `contents:` resolvent au moins un fichier
  1 -- au moins un motif ne correspond a aucun fichier (raison nommee)
  2 -- l'instrument ne peut pas conclure (front matter illisible qui annonce
       un listing, racine introuvable) : le verdict est INCONNU, pas un
       verdict de defaut
"""
from __future__ import annotations

import argparse
import glob
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml

EXIT_OK = 0
EXIT_BROKEN_LISTING = 1
EXIT_INSTRUMENT = 2

# Repertoires sans front matter de serie : les ignorer evite de parcourir des
# arbres de dependances ou des sorties de rendu. Le filtre porte sur les
# composants du chemin RELATIF a la racine : un filtre sur les composants
# ABSOLUS ecarterait silencieusement tout l'arbre des que la racine elle-meme
# est sous un repertoire de cette liste (mesure du 2026-11-12 : un arbre place
# sous `.tmp/` rendait `listings verifies : 0` et un rc 0 -- un vert qui ne
# mesurait rien).
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

# Les suffixes de sources retenues : plus larges que `index.qmd`/`README.md`
# (toute page `.qmd` et tout `.md` suivi par Git peut porter un front matter
# de listing).
SOURCE_SUFFIXES = (".qmd", ".md")


@dataclass(frozen=True)
class Finding:
    """Un constat du garde : un listing vide, ou une panne de l'instrument."""

    source: str
    listing_id: str
    motif: str
    reason: str
    instrument: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "source": self.source,
            "listing_id": self.listing_id,
            "motif": self.motif,
            "reason": self.reason,
            "instrument": self.instrument,
        }

    def message(self) -> str:
        if self.instrument:
            return f"{self.source}: {self.reason}"
        return f"{self.source}: listing {self.listing_id}: {self.reason}"


@dataclass(frozen=True)
class Target:
    """Une cible de listing : soit un motif glob, soit un chemin, soit une URL."""

    kind: str  # "glob" | "path" | "url"
    value: str


def collect_targets(contents: Any) -> list[Target]:
    """Extrait les cibles d'un `contents:` Quarto.

    Quarto accepte plusieurs formes, toutes rencontrees dans le depot : une
    chaine, une liste de chaines, une liste de dictionnaires (`{id: ...,
    contents: ...}` ou `{path: ...}`), un dictionnaire de dictionnaires, ou un
    dictionnaire simple. Une forme non reconnue est **ignoree ici** et
    signalee plus haut comme non prise en charge : elle ne doit jamais
    compter comme un listing resolu.
    """
    targets: list[Target] = []
    if isinstance(contents, str):
        value = contents.strip()
        if value:
            kind = "url" if "://" in value else "glob"
            targets.append(Target(kind, value))
    elif isinstance(contents, list):
        for item in contents:
            targets.extend(collect_targets(item))
    elif isinstance(contents, dict):
        if "contents" in contents:
            targets.extend(collect_targets(contents["contents"]))
        elif "path" in contents:
            value = str(contents["path"]).strip()
            if value:
                kind = "url" if "://" in value else "path"
                targets.append(Target(kind, value))
        else:
            for value in contents.values():
                targets.extend(collect_targets(value))
    return targets


def resolve_target(base: Path, target: Target) -> int:
    """Nombre de fichiers correspondants a une cible, resolue depuis `base`.

    Les URLs ne se resolvent pas sur disque -- Quarto les telecharge -- elles
    sont comptees comme resolues.
    """
    if target.kind == "url":
        return 1
    if target.kind == "path":
        return 1 if (base / target.value).exists() else 0
    if any(char in target.value for char in "*?["):
        return sum(1 for _ in base.glob(target.value))
    return 1 if (base / target.value).exists() else 0


def list_sources(root: Path) -> list[Path]:
    """Fichiers suivis par Git pouvant porter un front matter de listing.

    Les sources sont celles de `git ls-files` (toute page `.qmd` et tout
    `.md` **suivi**, donc hors archive non suivi et hors arbre de sortie).
    Sur une racine qui n'est pas un depot Git -- un arbre de test -- la
    liste descendante prend le relais, avec le meme filtrage de repertoires.
    """
    try:
        top = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        toplevel = Path(top.stdout.strip()).resolve() if top.returncode == 0 else None
    except OSError:
        toplevel = None
    if toplevel is not None and toplevel == root.resolve():
        raw = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.qmd", "*.md"],
            capture_output=True,
            check=False,
        ).stdout.decode("utf-8", errors="replace")
        return [
            root / name
            for name in raw.split("\0")
            if name and Path(name).suffix in SOURCE_SUFFIXES
        ]
    found: list[Path] = []
    for suffix in SOURCE_SUFFIXES:
        for path in root.rglob(f"*{suffix}"):
            relative = path.relative_to(root)
            if any(part in SKIP_DIRS for part in relative.parts):
                continue
            found.append(path)
    return sorted(found)


def analyse_document(path: Path, root: Path | None = None) -> tuple[list[Finding], int]:
    """Constats d'un document : (findings, nb de motifs verifies).

    Un front matter illisible qui annonce un listing est une **panne de
    l'instrument** (le verdict est inconnu), pas un listing vide. Un front
    matter illisible qui n'annonce rien est un fichier sans rapport : il est
    ignore.
    """
    source = _relative(path, root) if root is not None else str(path)
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return [Finding(source, "?", "", f"fichier-illisible:{exc}", instrument=True)], 0

    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return [], 0
    try:
        end = lines.index("---", 1)
    except ValueError:
        return [], 0
    front = "\n".join(lines[1:end])
    try:
        metadata = yaml.safe_load(front)
    except yaml.YAMLError as exc:
        if re.search(r"(?m)^\s*(?:listing|'listing'|\"listing\")\s*:", front):
            return (
                [
                    Finding(
                        source,
                        "?",
                        "",
                        f"YAML invalide : {exc}",
                        instrument=True,
                    )
                ],
                0,
            )
        return [], 0

    if not isinstance(metadata, dict) or "listing" not in metadata:
        return [], 0

    findings: list[Finding] = []
    checked = 0
    listings = metadata["listing"]
    if isinstance(listings, dict):
        listings = [listings]
    if not isinstance(listings, list):
        return (
            [Finding(source, "?", "", "listing non pris en charge", instrument=True)],
            0,
        )

    base = path.parent
    for item in listings:
        if not isinstance(item, dict):
            findings.append(
                Finding(source, "?", "", "entree listing non prise en charge")
            )
            continue
        name = str(item.get("id", "sans id"))
        if "contents" not in item:
            findings.append(
                Finding(source, name, "", "contents non pris en charge")
            )
            continue
        targets = collect_targets(item["contents"])
        if not targets:
            findings.append(
                Finding(source, name, "", "contents non pris en charge")
            )
            continue
        for target in targets:
            checked += 1
            # Fail-closed sur les negations : `!motif` n'est pas une exclusion
            # que l'instrument sait resoudre, elle est signalee.
            if target.value.startswith("!"):
                findings.append(
                    Finding(
                        source,
                        name,
                        target.value,
                        f"motif non pris en charge : {target.value!r}",
                    )
                )
                continue
            if resolve_target(base, target) == 0:
                findings.append(
                    Finding(
                        source,
                        name,
                        target.value,
                        f"aucun fichier pour {target.value!r}",
                    )
                )
    return findings, checked


def check_document(path: Path) -> list[str]:
    """Messages des constats d'un document (API historique de #25944).

    Les constats d'instrument y figurent aussi : un front matter illisible
    qui annonce un listing y est named, comme avant.
    """
    findings, _checked = analyse_document(Path(path))
    return [finding.message() for finding in findings]


def scan(root: Path) -> tuple[list[Finding], list[Finding], int]:
    """Parcourt l'arbre et mesure les motifs `contents:` non resolus.

    Retourne (listing vides, pannes de l'instrument, nb de motifs verifies).
    """
    broken: list[Finding] = []
    instrument: list[Finding] = []
    checked = 0
    for path in list_sources(root):
        findings, count = analyse_document(path, root)
        checked += count
        for finding in findings:
            if finding.instrument:
                instrument.append(finding)
            else:
                broken.append(finding)
    return broken, instrument, checked


def _relative(path: Path, root: Path | None) -> str:
    if root is None:
        return str(path).replace("\\", "/")
    try:
        return str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        return str(path).replace("\\", "/")


def build_report(
    root: Path,
    broken: list[Finding],
    instrument: list[Finding],
    checked: int,
) -> dict[str, Any]:
    """Rapport structure, partage entre la sortie texte et la sortie JSON."""
    return {
        "root": str(root),
        "checked": checked,
        "broken_count": len(broken),
        "instrument_errors": len(instrument),
        "broken": [item.to_dict() for item in broken],
        "instrument_error_details": [item.to_dict() for item in instrument],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Verifie que chaque motif `contents:` d'un listing Quarto "
            "resout au moins un fichier."
        )
    )
    default_root = Path(__file__).resolve().parents[1]
    parser.add_argument(
        "--root",
        type=Path,
        default=default_root,
        help=f"Racine du depot (defaut : {default_root})",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie structuree (JSON) au lieu du rapport texte",
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

    broken, instrument, checked = scan(root)
    report = build_report(root, broken, instrument, checked)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"listings verifies : {checked}")
        print(f"listings SANS correspondance sur disque : {len(broken)}")
        for item in broken:
            print(
                f"  {item.source} :: id={item.listing_id} :: motif={item.motif} :: 0 fichier"
            )
        if instrument:
            print(f"panne de l'instrument : {len(instrument)}")
            for item in instrument:
                print(f"  {item.source} :: {item.reason}")

    if instrument:
        return EXIT_INSTRUMENT
    if broken:
        return EXIT_BROKEN_LISTING
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
