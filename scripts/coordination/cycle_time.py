#!/usr/bin/env python3
"""Emetteur de l'heure de cycle (UTC + locale + decalage) -- #22736.

Le gabarit d'heure de cycle prescrit par le skill `coordinate` (#14728) demande
de porter **trois** informations : la date, l'heure UTC, l'heure locale **et**
le decalage. Les trois etaient ecrits a la main -- deux heures calculees de
tete, un decalage recopie d'un autre jour. L'instance mesuree : le gabarit
annoncait `2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)`, alors que le
26/10/2026 est posterieur a la fin de l'heure d'ete europeenne (25/10) :
Europe/Paris etait a UTC+01:00 ce jour-la. Le couple (date, decalage) n'avait
ete vrai pour aucun fuseau europeen ce jour-la.

Ce module est le remede du volet 1 de #22736 : il **lit l'horloge** et rend
l'en-tete au format prescrit, decalage compris. Le decalage sort de la
bibliotheque (`datetime.astimezone().strftime("%z")`), il n'est pas memore :
il suit le fuseau de la machine -- heure d'ete comprise.

Usage :

    python scripts/coordination/cycle_time.py
    Heure de cycle : 2026-10-26 15:48:16 UTC / 16:48:16 locale (UTC+01:00)

    python scripts/coordination/cycle_time.py --zone Europe/Paris
    python scripts/coordination/cycle_time.py --json

`--zone` rend l'heure locale d'un fuseau nomme (stdlib `zoneinfo`), ce qui
rend la sortie independante du fuseau de la machine -- utile pour un runner
ou une machine de CI. `--json` rend la meme information sous forme machine.

Quand la date locale differe de la date UTC (le passage de minuit), la date
locale est ecrite explicitement : `... / 2026-10-27 00:48:16 locale (...)`.
Sans elle, `00:48:16 locale` se lirait `00:48:16` **du jour UTC** -- un
decalage d'un jour, c'est-a-dire une heure fausse d'un cran plus grave que
celle que cet emisseur existe pour empecher.

Le garde qui verifie les quadruplets ecrits ailleurs dans le depot est
`scripts/ci/check_cycle_time_examples.py` (volet 2 de #22736).
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone

try:  # Python 3.9+ : zoneinfo est dans la stdlib ; le paquet `tzdata` peut
    from zoneinfo import ZoneInfo  # noqa: F401
except ImportError:  # pragma: no cover - Python < 3.9
    ZoneInfo = None  # type: ignore[assignment]

PREFIXE = "Heure de cycle :"


def formater_decalage(decalage: str) -> str:
    """`'%z'` (`+0100`) -> `+01:00`, la forme prescrite par le gabarit."""
    if len(decalage) != 5 or decalage[0] not in "+-" or not decalage[1:].isdigit():
        raise ValueError(f"decalage illisible : {decalage!r}")
    return f"{decalage[:3]}:{decalage[3:]}"


def decalage_en_minutes(decalage: str) -> int:
    """`'+01:00'` -> 60. Utilise par le garde pour l'arithmetique horaire."""
    signe = -1 if decalage.startswith("-") else 1
    heures, _, minutes = decalage[1:].partition(":")
    return signe * (int(heures) * 60 + int(minutes or 0))


def rendre(moment: datetime | None = None, zone: str | None = None) -> str:
    """Rend l'en-tete d'heure de cycle au format prescrit.

    `moment` : instant de reference (par defaut : maintenant). `zone` : nom IANA
    du fuseau local a afficher (par defaut : le fuseau de la machine).
    """
    now = moment or datetime.now(timezone.utc)
    utc = now.astimezone(timezone.utc)
    if zone is None:
        local = now.astimezone()
    else:
        if ZoneInfo is None:  # pragma: no cover - Python < 3.9
            raise RuntimeError("zoneinfo indisponible : Python 3.9+ requis")
        local = now.astimezone(ZoneInfo(zone))

    decalage = formater_decalage(local.strftime("%z"))
    heure_utc = utc.strftime("%Y-%m-%d %H:%M:%S")
    heure_locale = local.strftime("%H:%M:%S")
    if local.date() != utc.date():
        # Le passage de minuit : sans la date locale, l'heure serait lue
        # comme celle du jour UTC.
        heure_locale = f"{local.strftime('%Y-%m-%d')} {heure_locale}"
    return f"{PREFIXE} {heure_utc} UTC / {heure_locale} locale (UTC{decalage})"


def rendre_json(moment: datetime | None = None, zone: str | None = None) -> dict:
    """La meme information, sous forme machine."""
    now = moment or datetime.now(timezone.utc)
    utc = now.astimezone(timezone.utc)
    if zone is None:
        local = now.astimezone()
    else:
        if ZoneInfo is None:  # pragma: no cover
            raise RuntimeError("zoneinfo indisponible : Python 3.9+ requis")
        local = now.astimezone(ZoneInfo(zone))
    return {
        "utc": utc.strftime("%Y-%m-%d %H:%M:%S"),
        "local": local.strftime("%Y-%m-%d %H:%M:%S"),
        "offset": formater_decalage(local.strftime("%z")),
        "header": rendre(now, zone),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emet l'heure de cycle au format prescrit (UTC + locale + decalage)."
    )
    parser.add_argument(
        "--zone",
        default=None,
        help="Fuseau IANA pour l'heure locale (defaut : le fuseau de la machine).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Rend l'information sous forme machine.",
    )
    args = parser.parse_args(argv)

    try:
        if args.json:
            print(json.dumps(rendre_json(zone=args.zone), ensure_ascii=False))
        else:
            print(rendre(zone=args.zone))
    except Exception as exc:  # noqa: BLE001 -- l'emetteur ne doit pas masquer l'erreur
        print(f"ERREUR -- {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
