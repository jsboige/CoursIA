#!/usr/bin/env python3
"""Garde des quadruplets d'heure de cycle ecrits a la main -- #22736.

Le gabarit d'heure de cycle prescrit par le skill `coordinate` (#14728) porte
quatre donnees : la date, l'heure UTC, l'heure locale, le decalage. Les quatre
etaient ecrites a la main. L'instance fondatrice : le gabarit annoncait
`2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)` alors que le 26/10/2026 est
posterieur a la fin de l'heure d'ete europeenne (25/10) -- Europe/Paris etait
a UTC+01:00 ce jour-la. L'arithmetique interne du quadruplet etait juste
(14:37 + 2 h = 16:37) ; c'est le couple (date, decalage) qui etait faux, et
rien dans le depot ne le verifiait.

Ce garde est le volet 2 de #22736 : il scanne les fichiers **normatifs**
(`.claude/skills/**`, `.claude/rules/**`, `docs/**`) et verifie, pour chaque
quadruplet trouve, DEUX relations -- jamais un compte :

1. **coherence interne** : l'heure locale annoncee est bien l'heure UTC
   plus le decalage annonce ;
2. **coherence calendaire** : le decalage annonce est bien le decalage en
   vigueur dans le fuseau de reference a CETTE date (donc en tenant compte de
   l'heure d'ete) -- c'est la relation que l'instance fondatrice violait.

Le fuseau de reference vaut `Europe/Paris` (le fuseau de la flotte) ; il
surcharge avec `--zone` ou la variable d'environnement
`CYCLE_TIME_REFERENCE_ZONE`, et une ligne peut designer son propre fuseau
avec le marqueur `cycle-time-zone: <IANA>`. Une ligne qui cite un quadruplet
a titre d'exemple (le recount d'un defaut, une citation) s'exempte avec le
marqueur `cycle-time-exempt: <motif>`.

Aucun compte n'est fige : le depot gagne et perd des quadruplets a chaque PR,
le garde verifie une RELATION. C'est le meme principe que l'organe de
l'integrite de la copie Argumentum
(`scripts/fallacy_detection/argumentum_taxonomy_integrity.py`).

Sorties : 0 = aucune contradiction · 1 = defaut · 2 = mesure impossible
(fuseau inconnu, donnees de fuseau absentes).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

try:
    from zoneinfo import ZoneInfo, ZoneInfoNotFoundError
except ImportError:  # pragma: no cover - Python < 3.9
    ZoneInfo = None  # type: ignore[assignment]
    ZoneInfoNotFoundError = Exception  # type: ignore[misc]

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_UNREACHABLE = 2

ZONE_REFERENCE_PAR_DEFAUT = "Europe/Paris"

# Arbres normatifs scannes : la prescription vit dans le harnais et la doc.
ARBRES_NORMATIFS = (".claude/skills", ".claude/rules", "docs")

MARQUEUR_EXEMPTION = "cycle-time-exempt:"
MARQUEUR_ZONE = "cycle-time-zone:"

# Un quadruplet : date + heure UTC + heure locale + decalage entre parentheses.
MOTIF_QUADRUPL = re.compile(
    r"(?P<date>\d{4}-\d{2}-\d{2})[ T](?P<utc>\d{1,2}:\d{2}(?::\d{2})?)\s*UTC"
    r"\s*(?:/|->|→|—|–|-)\s*"
    r"(?:(?P<ldate>\d{4}-\d{2}-\d{2})[ T])?"
    r"(?P<local>\d{1,2}:\d{2}(?::\d{2})?)\s*(?:heure\s+)?locale"
    r"\s*\(\s*UTC(?P<sign>[+-])(?P<oh>\d{1,2})(?::(?P<om>\d{2}))?\s*\)",
    re.IGNORECASE,
)


class MesureImpossible(RuntimeError):
    """L'instrument n'a pas pu rendre de verdict -- jamais confondu avec un vert."""


def _minutes_de_jour(heure: str) -> tuple[int, int]:
    """`14:37` / `14:37:16` -> (minutes, secondes)."""
    morceaux = heure.split(":")
    minutes = int(morceaux[0]) * 60 + int(morceaux[1])
    secondes = int(morceaux[2]) if len(morceaux) > 2 else 0
    return minutes, secondes


def _decalage_annonce(signe: str, heures: str, minutes: str | None) -> int:
    total = int(heures) * 60 + int(minutes or 0)
    return -total if signe == "-" else total


def verifier_quadruplet(
    quad, zone_reference: str
) -> list[dict]:
    """Verifie un quadruplet ; rend la liste des contradictions trouvees.

    Chaque contradiction porte une cle `relation` (`coherence-interne` ou
    `coherence-calendaire`) et les valeurs annoncees et attendues.
    """
    anomalies: list[dict] = []
    decalage = _decalage_annonce(quad["sign"], quad["oh"], quad.get("om"))
    minutes_utc, secondes_utc = _minutes_de_jour(quad["utc"])
    minutes_loc, secondes_loc = _minutes_de_jour(quad["local"])

    # Relation 1 -- coherence interne du quadruplet.
    attendues = (minutes_utc + decalage) % (24 * 60)
    if attendues != minutes_loc:
        anomalies.append(
            {
                "relation": "coherence-interne",
                "annonce": quad["local"],
                "attendu": _rendre_heure(attendues),
                "detail": (
                    f"l'heure locale annoncee ({quad['local']}) n'est pas "
                    f"l'heure UTC ({quad['utc']}) plus le decalage annonce "
                    f"({quad['sign']}{quad['oh']}:{quad.get('om') or '00'})"
                ),
            }
        )
    elif secondes_utc or secondes_loc:
        if (secondes_utc + decalage * 60) % 60 != secondes_loc:
            anomalies.append(
                {
                    "relation": "coherence-interne",
                    "annonce": quad["local"],
                    "attendu": _rendre_heure(attendues),
                    "detail": "les secondes annoncees ne correspondent pas au decalage",
                }
            )

    # Relation 2 -- coherence calendaire : le decalage annonce est-il celui
    # en vigueur dans le fuseau de reference a CETTE date ?
    zone = quad.get("zone") or zone_reference
    try:
        reference = ZoneInfo(zone)
    except (ZoneInfoNotFoundError, KeyError, ValueError) as exc:
        raise MesureImpossible(f"fuseau inconnu : {zone} ({exc})") from exc

    annee, mois, jour = (int(part) for part in quad["date"].split("-"))
    heure, minute = (int(part) for part in quad["utc"].split(":")[:2])
    instant = datetime(annee, mois, jour, heure, minute, tzinfo=timezone.utc)
    decalage_reel = instant.astimezone(reference).utcoffset()
    if decalage_reel is None:  # pragma: no cover - fuseau sans decalage
        raise MesureImpossible(f"fuseau sans decalage : {zone}")
    minutes_reels = int(decalage_reel.total_seconds()) // 60
    if minutes_reels != decalage:
        anomalies.append(
            {
                "relation": "coherence-calendaire",
                "annonce": f"UTC{quad['sign']}{quad['oh']}:{quad.get('om') or '00'}",
                "attendu": _rendre_decalage(minutes_reels),
                "detail": (
                    f"le decalage annonce ne correspond pas a l'heure en vigueur "
                    f"dans {zone} le {quad['date']} (changement d'heure d'ete "
                    f"pris en compte)"
                ),
            }
        )

    # La date locale, quand elle est ecrite, doit suivre le decalage.
    if quad.get("ldate"):
        attendu_date = (instant + timedelta(minutes=decalage)).date().isoformat()
        if attendu_date != quad["ldate"]:
            anomalies.append(
                {
                    "relation": "coherence-interne",
                    "annonce": quad["ldate"],
                    "attendu": attendu_date,
                    "detail": "la date locale annoncee ne suit pas le decalage annonce",
                }
            )

    return anomalies


def _rendre_heure(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"


def _rendre_decalage(minutes: int) -> str:
    signe = "-" if minutes < 0 else "+"
    minutes = abs(minutes)
    return f"UTC{signe}{minutes // 60:02d}:{minutes % 60:02d}"


def _fichiers_a_scanner(racine: Path, arbres: tuple[str, ...]):
    for arbre in arbres:
        base = racine / arbre
        if not base.exists():
            continue
        for chemin in sorted(base.rglob("*")):
            if not chemin.is_file():
                continue
            if ".git" in chemin.parts or "__pycache__" in chemin.parts:
                continue
            if chemin.suffix.lower() in {".png", ".jpg", ".jpeg", ".gif", ".pdf", ".ipynb"}:
                continue
            yield chemin


def scanner(racine: Path, zone_reference: str, arbres: tuple[str, ...] = ARBRES_NORMATIFS) -> dict:
    """Scanne les arbres normatifs et rend le rapport des contradictions."""
    findings: list[dict] = []
    exemptes: list[dict] = []
    quadruplets: list[dict] = []
    for chemin in _fichiers_a_scanner(racine, arbres):
        try:
            texte = chemin.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        for numero, ligne in enumerate(texte.splitlines(), start=1):
            if MARQUEUR_EXEMPTION in ligne:
                exemptes.append(
                    {"fichier": _relatif(chemin, racine), "ligne": numero}
                )
                continue
            zone_ligne = zone_reference
            if MARQUEUR_ZONE in ligne:
                zone_ligne = ligne.split(MARQUEUR_ZONE, 1)[1].strip().split()[0]
            for quad in MOTIF_QUADRUPL.finditer(ligne):
                donnees = quad.groupdict()
                donnees["zone"] = zone_ligne
                quadruplets.append(
                    {"fichier": _relatif(chemin, racine), "ligne": numero}
                )
                for anomalie in verifier_quadruplet(donnees, zone_reference):
                    findings.append(
                        {
                            "fichier": _relatif(chemin, racine),
                            "ligne": numero,
                            "quadruplet": ligne.strip(),
                            **anomalie,
                        }
                    )
    return {
        "verdict": "DEFECT" if findings else "CLEAN",
        "quadruplets": quadruplets,
        "anomalies": findings,
        "exemptes": exemptes,
    }


def _relatif(chemin: Path, racine: Path) -> str:
    try:
        return chemin.relative_to(racine).as_posix()
    except ValueError:  # pragma: no cover
        return chemin.as_posix()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Verifie les quadruplets d'heure de cycle des fichiers normatifs "
            "(coherence interne + coherence calendaire, heure d'ete comprise)."
        )
    )
    parser.add_argument("--root", default=".", help="Racine du depot.")
    parser.add_argument(
        "--zone",
        default=os.environ.get("CYCLE_TIME_REFERENCE_ZONE", ZONE_REFERENCE_PAR_DEFAUT),
        help=f"Fuseau de reference (defaut : {ZONE_REFERENCE_PAR_DEFAUT}).",
    )
    parser.add_argument("--json", action="store_true", help="Sortie structuree.")
    args = parser.parse_args(argv)

    racine = Path(args.root).resolve()
    if not racine.is_dir():
        print(f"UNKNOWN -- racine introuvable : {racine}", file=sys.stderr)
        return EXIT_UNREACHABLE
    if ZoneInfo is None:
        print("UNKNOWN -- zoneinfo indisponible (Python 3.9+ requis)", file=sys.stderr)
        return EXIT_UNREACHABLE

    try:
        rapport = scanner(racine, args.zone)
    except MesureImpossible as exc:
        if args.json:
            print(json.dumps({"verdict": "UNKNOWN", "raison": str(exc)}, ensure_ascii=False))
        else:
            print(f"UNKNOWN -- {exc}", file=sys.stderr)
        return EXIT_UNREACHABLE

    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
        return EXIT_OK if rapport["verdict"] == "CLEAN" else EXIT_DEFECT

    if rapport["anomalies"]:
        print(
            f"DEFECT -- {len(rapport['anomalies'])} contradiction(s) sur "
            f"{len(rapport['quadruplets'])} quadruplet(s) lu(s) "
            f"(fuseau de reference : {args.zone}) :"
        )
        for anomalie in rapport["anomalies"]:
            print(
                f"  {anomalie['fichier']}:{anomalie['ligne']}  "
                f"[{anomalie['relation']}] {anomalie['detail']}"
            )
            print(
                f"      annonce : {anomalie['annonce']} | "
                f"attendu : {anomalie['attendu']}"
            )
            print(f"      ligne   : {anomalie['quadruplet']}")
        return EXIT_DEFECT

    print(
        f"CLEAN -- {len(rapport['quadruplets'])} quadruplet(s) lu(s), "
        f"{len(rapport['anomalies'])} contradiction(s) "
        f"(fuseau de reference : {args.zone}) ; "
        f"{len(rapport['exemptes'])} ligne(s) exemptee(s)."
    )
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
