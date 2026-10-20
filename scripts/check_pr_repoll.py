#!/usr/bin/env python3
"""Organe de garde anti re-sondage de PR (#16144, item 2).

Pourquoi cet organe existe
--------------------------
Le sondage repete de la meme PR par une meme session (relectures `gh pr view`
en boucle pendant une attente) est la consommation la plus silencieuse du
quota serveur : mesure ai-01 du 13/09, 9,2 refs/PR cote client, en salves de
3-9 relectures pendant les attentes (corrobore cote serveur : #15881 x30 refs
dans la journee). Le client CC >= 2.1.269 a retire les bornes generiques
(rumination, perimetre) -- l'organe les reintroduit au moment du geste, sur
le pattern de `check_unaddressed_nits.py` : un refus AVANT la lecture, pas
un audit apres.

Bornes (plan du 14/09, formes corrigees 10:53Z) :
  - B2'    : refus d'une relecture manuelle si `last_read` date de moins de
             `--min-age` minutes ET qu'aucun signal de changement d'etat
             n'est survenu depuis (Monitor arme, `--watch`, notification).
  - B2-bis : toute lecture manuelle est refusee tant qu'une surveillance
             (watch) est vivante -- le watcher notifie de lui-meme, la
             lecture manuelle est redondante par construction.

Usage
-----
    python scripts/check_pr_repoll.py check 20992                  # pre-lecture (gate)
    python scripts/check_pr_repoll.py check 20992 --min-age 20     # seuil B2' explicite
    python scripts/check_pr_repoll.py record 20992                 # post-lecture
    python scripts/check_pr_repoll.py record 20992 --watch         # arme la surveillance
    python scripts/check_pr_repoll.py record 20992 --watch-end     # clot la surveillance
    python scripts/check_pr_repoll.py record 20992 --signal monitor  # trace un signal

Registre : JSON `{<PR>: {"last_read": ..., "watch_armed_at": ...,
"watch_ended_at": ..., "signals": [{"at": ..., "kind": ...}]}}`, tenu par
l'organe -- le skill appelant n'ecrit jamais le JSON a la main. Emplacement :
`--ledger`, sinon `$PR_POLL_LEDGER`, sinon un emplacement stable hors tempdir (`%LOCALAPPDATA%\\CoursIA` sur Windows, `~/.local/share/CoursIA` sinon) — le tempdir est purgé par les règles de scratch de la flotte et vidait silencieusement le registre (review #21060).

Fail-open assume : registre absent ou corrompu -> `check` sort 0 + warning
stderr. L'organe garde des tokens ; il ne doit jamais bloquer la
coordination sur un sidecar casse. Un `record` sur registre corrompu
preserve la donnee (renommee `<ledger>.corrupt-<ts>`) avant de repartir
vieux : jamais de destruction sans preuve de preservation.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

DEFAULT_MIN_AGE_MIN = 30

# ---------------------------------------------------------------------------
# Horodatage : UTC explicite, jamais d'heure locale habillee d'un Z
# (lecon utc-vs-local : le suffixe Z sur une heure locale est proscrit).
# ---------------------------------------------------------------------------


def _now() -> datetime:
    return datetime.now(timezone.utc)


def _iso(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _parse_iso(ts: str) -> datetime:
    return datetime.fromisoformat(ts.replace("Z", "+00:00"))


# ---------------------------------------------------------------------------
# Registre : chargement fail-open, ecriture atomique.
# ---------------------------------------------------------------------------


def default_ledger_path() -> Path:
    env = os.environ.get("PR_POLL_LEDGER")
    if env:
        return Path(env)
    # Defaut stable hors tempdir (review #21060) : le tempdir est
    # purge par les regles de scratch de la flotte ; un registre qui
    # disparait avec lui rend le garde inoperant sans le dire.
    # Precedent d'emplacement : journal de la tache planifiee prune
    # (%LOCALAPPDATA%\CoursIA\prune_task\logs\).
    local = os.environ.get("LOCALAPPDATA")
    root = Path(local) if local else Path.home() / ".local" / "share"
    return root / "CoursIA" / "pr-poll-ledger.json"


def load_ledger(path: Path) -> tuple[dict[str, Any] | None, str | None]:
    """Charge le registre ; (None, warning) si absent ou corrompu (fail-open)."""
    if not path.exists():
        return None, None
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return None, f"registre illisible ({path}) : {exc} -- fail-open"
    if not isinstance(raw, dict):
        return None, f"registre non-object ({path}) -- fail-open"
    return raw, None


def save_ledger(path: Path, ledger: dict[str, Any]) -> str | None:
    """Ecrit le registre ; sur corrompu existant, le preserve avant remplacement."""
    warning: str | None = None
    if path.exists():
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            backup = path.with_name(f"{path.name}.corrupt-{_iso(_now())}")
            # Remplacement : caractere ':' interdit dans les noms Windows, sanatise.
            backup = path.with_name(backup.name.replace(":", ""))
            try:
                path.replace(backup)
                warning = f"registre corrompu preserve en {backup.name}, repart a vide"
            except OSError as exc:
                return f"impossible de preserver le registre corrompu ({exc}) -- rien ecrit"
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f"{path.name}.tmp")
    try:
        tmp.write_text(
            json.dumps(ledger, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        tmp.replace(path)
    except OSError as exc:
        return f"ecriture registre echouee ({path}) : {exc}"
    return warning


# ---------------------------------------------------------------------------
# Coeur pur : la decision B2'/B2-bis, testable sans I/O.
# ---------------------------------------------------------------------------


@dataclass
class Decision:
    """Verdict du gate `check` : refused=True -> exit 1 au moment du geste."""

    refused: bool
    reason: str = ""


def evaluate(entry: dict[str, Any] | None, now: datetime, min_age_min: int) -> Decision:
    """Applique B2-bis puis B2' sur une entree de registre.

    B2-bis en premier : une surveillance vivante refuse toute lecture
    manuelle, meme si `last_read` est ancien -- le watcher notifie de
    lui-meme (le refus ne depend pas de l'age).
    """
    if entry is None:
        return Decision(False, "aucune lecture enregistree -- premiere lecture libre")
    if entry.get("watch_armed_at") and not entry.get("watch_ended_at"):
        return Decision(
            True,
            f"surveillance vivante depuis {entry['watch_armed_at']} (B2-bis) : "
            "le watcher notifie de lui-meme, lecture manuelle refusee",
        )
    last_read = entry.get("last_read")
    if not last_read:
        return Decision(False, "pas de last_read -- lecture libre")
    read_at = _parse_iso(last_read)
    age_min = (now - read_at).total_seconds() / 60.0
    if age_min >= min_age_min:
        return Decision(False, f"derniere lecture il y a {age_min:.0f} min (>= {min_age_min} min)")
    signals = entry.get("signals") or []
    fresh = [s for s in signals if _parse_iso(s["at"]) >= read_at]
    if fresh:
        kinds = ", ".join(sorted({s["kind"] for s in fresh}))
        return Decision(False, f"signal(s) depuis la lecture ({kinds}) -- changement d'etat")
    return Decision(
        True,
        f"derniere lecture il y a {age_min:.0f} min (< {min_age_min} min) sans signal "
        "de changement d'etat (B2') : relecture refusee ; pour forcer, "
        "`record <PR> --signal <motif>` ou armer un watch",
    )


# ---------------------------------------------------------------------------
# CLI : record (post-lecture) / check (pre-lecture).
# ---------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Gate anti re-sondage de PR (#16144 item 2) : refuse la relecture "
        "d'une PR lue trop recemment sans changement d'etat.",
    )
    parser.add_argument(
        "--ledger",
        type=Path,
        default=None,
        help="chemin du registre (defaut : $PR_POLL_LEDGER, sinon un emplacement "
        "stable hors tempdir : %%LOCALAPPDATA%%\\CoursIA sur Windows, "
        "~/.local/share/CoursIA sinon)",
    )
    sub = parser.add_subparsers(dest="verb", required=True)

    p_rec = sub.add_parser("record", help="post-lecture : stamp last_read (+ effets)")
    p_rec.add_argument("pr", help="numero de PR (cle du registre)")
    flags = p_rec.add_mutually_exclusive_group()
    flags.add_argument(
        "--watch",
        action="store_true",
        help="arme la surveillance (watch_armed_at, efface watch_ended_at)",
    )
    flags.add_argument(
        "--watch-end",
        action="store_true",
        help="clot la surveillance (watch_ended_at)",
    )
    flags.add_argument(
        "--signal",
        metavar="KIND",
        help="trace un signal de changement d'etat (monitor, notification, ...)",
    )

    p_chk = sub.add_parser("check", help="pre-lecture : exit 1 si relecture refusee")
    p_chk.add_argument("pr", help="numero de PR (cle du registre)")
    p_chk.add_argument(
        "--min-age",
        type=int,
        default=DEFAULT_MIN_AGE_MIN,
        metavar="N",
        help=f"age minimal en minutes avant relecture libre (defaut {DEFAULT_MIN_AGE_MIN})",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    path = args.ledger if args.ledger is not None else default_ledger_path()
    now = _now()

    ledger, warning = load_ledger(path)
    if warning:
        print(f"WARNING: {warning}", file=sys.stderr)

    if args.verb == "check":
        entry = (ledger or {}).get(args.pr)
        decision = evaluate(entry, now, args.min_age)
        print(f"[pr-repoll] PR {args.pr} : {'REFUS -- ' if decision.refused else 'OK -- '}"
              f"{decision.reason}")
        return 1 if decision.refused else 0

    # record : registre absent -> repart vide ; corrompu -> preserve par save_ledger
    ledger = ledger or {}
    entry = ledger.setdefault(args.pr, {"signals": []})
    entry["signals"] = entry.get("signals") or []
    entry["last_read"] = _iso(now)
    if args.watch:
        entry["watch_armed_at"] = _iso(now)
        entry["watch_ended_at"] = None
        entry["signals"].append({"at": _iso(now), "kind": "watch"})
    if args.watch_end:
        entry["watch_ended_at"] = _iso(now)
        entry["signals"].append({"at": _iso(now), "kind": "watch-end"})
    if args.signal:
        entry["signals"].append({"at": _iso(now), "kind": args.signal})
    warn_save = save_ledger(path, ledger)
    if warn_save:
        print(f"WARNING: {warn_save}", file=sys.stderr)
    print(f"[pr-repoll] PR {args.pr} : last_read={entry['last_read']}"
          + (" +watch" if args.watch else "")
          + (" +watch-end" if args.watch_end else "")
          + (f" +signal:{args.signal}" if args.signal else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
