#!/usr/bin/env python3
"""Epinglage de la toolchain Lean par environnement (organe).

Probleme mesure (2026-11-10, poste ai-01) : le defaut elan de ce poste est
``leanprover/lean4:v4.11.0`` alors que le pin des lakes du depot est
``leanprover/lean4:v4.33.0``. Deux postes dont l'elan par defaut differe
jugent les memes rollouts sur des moteurs differents : le resultat n'est pas
reproductible inter-postes. Le repli historique ``v4.27.0`` n'etait installe
nulle part et declenchait un telechargement elan a chaque rollout.

Cet organe detient la source de verite du pin :

* ``lean_toolchain_inventory.json`` — la **declaration** : le tag que
  chaque poste epingle, plus le pin de flotte ;
* la **resolution**, d'ordre explicite, avec la provenance dans le retour :
  ``ELAN_TOOLCHAIN`` (lu tel quel aux espaces de bord pres) >
  ``lean-toolchain`` du projet > declaration de l'hote > pin de flotte >
  defaut elan mesure (**non epingle**, mesure paresseuse : elle n'a lieu
  qu'au palier 5) > repli alerte ;
* le **controle de derive** : compare le pin effectif, la declaration et le
  defaut elan mesure.

Usage CLI ::

    python scripts/lean/lean_toolchain.py --resolve
    python scripts/lean/lean_toolchain.py --check
    python scripts/lean/lean_toolchain.py --check --json

Sorties de ``--resolve`` : ``<tag> <provenance>``, ou la provenance est
``env`` / ``projet`` / ``declaration`` / ``declaration_flotte`` /
``default_resolu`` / ``fallback_averti``.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import socket
import subprocess
import sys
from pathlib import Path
from typing import Callable

__all__ = [
    "INVENTORY_FILENAME",
    "LAST_RESORT_TOOLCHAIN",
    "check_drift",
    "current_host",
    "declared_pin",
    "fleet_pin",
    "installed_toolchain",
    "inventory_path",
    "load_inventory",
    "repo_root",
    "resolve_pin",
    "toolchain_from_version",
]

LOGGER = logging.getLogger(__name__)

#: Fichier de declaration, lu par le code (jamais un commentaire).
INVENTORY_FILENAME = "lean_toolchain_inventory.json"

#: Dernier recours, avertissement explicite. Tag PRESENT dans le parc mesure
#: (2026-11-10) ; le repli historique ``v4.27.0`` n'etait installe sur aucun
#: poste mesure et forcait un telechargement elan a chaque rollout.
LAST_RESORT_TOOLCHAIN = "leanprover/lean4:v4.33.0"

_VERSION_RE = re.compile(r"version (\d+\.\d+\.\d+)")

#: Sentinelle : distingue « non fourni » de « mesure : aucune toolchain ».
_UNSET = object()


def repo_root() -> Path:
    """Racine du depot (``scripts/lean/`` -> racine)."""
    return Path(__file__).resolve().parents[2]


def inventory_path(root: Path | None = None) -> Path:
    """Chemin du fichier de declaration."""
    return (root if root is not None else repo_root()) / "scripts" / "lean" / INVENTORY_FILENAME


def load_inventory(root: Path | None = None) -> dict:
    """Charge la declaration ; ``{}`` si absente ou illisible.

    Jamais d'exception : une declaration manquante degrade la resolution vers
    le defaut elan mesure (non eingle), elle n'interrompt pas un rollout.
    """
    path = inventory_path(root)
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        LOGGER.warning(
            "Declaration de toolchain absente (%s) : resolution repliee sur le "
            "defaut elan mesure, non reproductible entre postes.", path)
        return {}
    except OSError as exc:
        LOGGER.warning("Declaration de toolchain illisible (%s) : %s", path, exc)
        return {}
    except UnicodeDecodeError as exc:
        LOGGER.warning("Declaration de toolchain illisible (%s) : %s", path, exc)
        return {}
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        LOGGER.warning("Declaration de toolchain mal formee (%s) : %s", path, exc)
        return {}
    if not isinstance(data, dict):
        LOGGER.warning("Declaration de toolchain mal formee (%s) : objet attendu.", path)
        return {}
    return data


def fleet_pin(inventory: dict | None = None) -> str | None:
    """Tag declare pour toute la flotte, ou ``None``."""
    inv = load_inventory() if inventory is None else inventory
    value = inv.get("fleet_pin")
    if isinstance(value, str) and value.strip():
        return value.strip()
    return None


def declared_pin(inventory: dict | None, host: str) -> str | None:
    """Tag declare pour un hote, ou ``None`` s'il n'en declare pas.

    La cle d'hote est le nom d'hote en minuscules ; une declaration portant
    une cle differente n'est pas un pin pour cet hote (on ne devine pas).

    Une entree **mal formee** (pas un objet, ou un ``toolchain`` qui n'est
    pas une chaine) est signalee puis ignoree : le pin manque, et le
    silence ferait croire a une declaration absente.
    """
    inv = load_inventory() if inventory is None else inventory
    environments = inv.get("environments")
    if not isinstance(environments, dict):
        return None
    key = host.strip().lower()
    if key not in environments:
        return None
    entry = environments[key]
    if not isinstance(entry, dict):
        LOGGER.warning(
            "Declaration de toolchain mal formee pour l'hote %s : objet "
            "attendu, pin ignore.", key)
        return None
    value = entry.get("toolchain")
    if value is None:
        return None
    if not isinstance(value, str):
        LOGGER.warning(
            "Declaration de toolchain mal formee pour l'hote %s : chaine "
            "attendue pour 'toolchain', pin ignore.", key)
        return None
    return value.strip() or None


def current_host() -> str:
    """Nom d'hote en minuscules (cle de declaration)."""
    try:
        return socket.gethostname().strip().lower()
    except OSError:
        return ""


def _elan_bin_dir() -> str:
    """Repertoire des binaires elan.

    elan respecte ``ELAN_HOME`` : on l'honore aussi, sinon la mesure
    chercherait le proxy dans le home de l'utilisateur la ou l'elan
    n'installe rien (et le proxy echouerait au lieu de repondre).
    """
    elan_home = os.environ.get("ELAN_HOME")
    base = Path(elan_home) if elan_home else Path.home() / ".elan"
    return str(base / "bin")


def toolchain_from_version(output: str) -> str | None:
    """Reconstruit le tag elan depuis la sortie de ``lean --version``.

    Fonction pure : la reconstruction se teste sans declencher de processus.
    Une sortie qui ne nomme pas une version rend ``None`` (aucune mesure,
    pas un tag invente).
    """
    match = _VERSION_RE.search(output)
    if match:
        return f"leanprover/lean4:v{match.group(1)}"
    return None


def installed_toolchain() -> str | None:
    """Tag de la toolchain **reellement** en usage, ou ``None`` si inmesurable.

    Mesure : ``lean --version`` dans le PATH (elan prioritaire). Le tag est
    RECONSTITUE depuis la version rapportee — c'est le defaut elan de
    l'hote, donc un moteur NON FIGE : il ne vaut pas un pin reproductible.
    """
    bin_dir = _elan_bin_dir()
    try:
        proc = subprocess.run(
            ["lean", "--version"], capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=30,
            env={**os.environ,
                 "PATH": bin_dir + os.pathsep + os.environ.get("PATH", "")},
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return toolchain_from_version(proc.stdout + proc.stderr)


class _Measured:
    """Mesure **paresseuse** et unique du defaut elan.

    Une mesure lance un ``lean --version`` par le proxy elan : sur un poste
    ou le defaut n'est pas installe, elle peut declencher un
    telechargement (30 s au plus). Elle n'est donc interrogee qu'au moment
    ou elle est necessaire — le palier 5 de la resolution — et une seule
    fois, meme quand plusieurs appels partagent la meme mesure.
    """

    def __init__(self, value: str | None | object = _UNSET,
                 loader: Callable[[], str | None] | None = None) -> None:
        self._value = value
        self._loader = loader or installed_toolchain

    def get(self) -> str | None:
        """Valeur mesuree ; la mesure n'a lieu qu'a ce premier appel."""
        if self._value is _UNSET:
            self._value = self._loader()
        return self._value  # type: ignore[return-value]


def _measurement(
    installed: str | None | object,
    loader: Callable[[], str | None] | None = None,
) -> _Measured:
    """Enveloppe la mesure du defaut elan (valeur injectee ou paresseuse)."""
    if isinstance(installed, _Measured):
        return installed
    return _Measured(installed, loader)


def resolve_pin(
    project_dir: str | os.PathLike | None = None,
    *,
    env: dict | None = None,
    inventory: dict | None = None,
    host: str | None = None,
    installed: str | None | object = _UNSET,
    loader: Callable[[], str | None] | None = None,
) -> tuple[str, str]:
    """Resout le pin de toolchain et rend ``(tag, provenance)``.

    Ordre (explicite, chaque palier testable isolement) :

    1. ``ELAN_TOOLCHAIN`` — lu **tel quel aux espaces de bord pres**
       (``.strip()``), jamais reconstruit ;
    2. ``lean-toolchain`` du projet fourni ;
    3. declaration de l'hote (le tag que CE poste declare epingler) ;
    4. pin de flotte (declaration commune) ;
    5. defaut elan mesure — **non eingle**, propre a chaque poste ;
    6. repli alerte (constante presente dans le parc).

    Le palier 2 ne s'applique qu'a un projet FOURNI : le squelette gere
    (``~/.cache/rlvr-lean``) ecrit son propre pin, le relire comme un pin
    de projet masquerait la provenance reelle.

    La mesure du defaut elan est **paresseuse** : elle n'a lieu qu'au
    palier 5. Aucun ``lean --version`` n'est lance quand un palier plus
    haut tranche — sur un poste ou le defaut elan n'est pas installe, la
    mesure peut declencher un telechargement que le rollout n'a pas
    besoin. ``loader`` permet d'injecter la mesure (tests) ; ``installed``
    injecte une valeur deja mesuree.
    """
    environment = os.environ if env is None else env
    inv = load_inventory() if inventory is None else inventory
    hostname = current_host() if host is None else host
    measurement = _measurement(installed, loader)

    environment_pin = (environment.get("ELAN_TOOLCHAIN") or "").strip()
    if environment_pin:
        return environment_pin, "env"

    if project_dir is not None:
        try:
            project_pin = (
                Path(project_dir) / "lean-toolchain"
            ).read_text(encoding="utf-8").strip()
        except (OSError, UnicodeDecodeError):
            project_pin = ""
        if project_pin:
            return project_pin, "projet"

    declared = declared_pin(inv, hostname)
    if declared:
        return declared, "declaration"

    fleet = fleet_pin(inv)
    if fleet:
        return fleet, "declaration_flotte"

    measured = measurement.get()
    if measured:
        return measured, "default_resolu"

    LOGGER.warning(
        "RLVR Lean: aucun pin env/projet, aucune declaration, défaut elan "
        "inmesurable ; repli explicite vers %s (un téléchargement elan peut "
        "être requis).", LAST_RESORT_TOOLCHAIN)
    return LAST_RESORT_TOOLCHAIN, "fallback_averti"


def check_drift(
    *,
    env: dict | None = None,
    inventory: dict | None = None,
    host: str | None = None,
    project_dir: str | os.PathLike | None = None,
    installed: str | None | object = _UNSET,
    loader: Callable[[], str | None] | None = None,
) -> dict:
    """Compare pin effectif, declaration et defaut elan mesure.

    Rendue :

    * ``effective`` / ``provenance`` — le pin que les rollouts utilisent ;
    * ``declared`` — la declaration de l'hote ;
    * ``elan_default`` — le defaut elan mesure sur CE poste ;
    * ``drift`` — vrai si le pin effectif n'est pas reproductible entre
      postes (aucune declaration : chaque poste suivrait son propre
      defaut elan) ;
    * ``fleet_drift`` — les environnements dont la declaration diverge du
      pin de flotte.

    La mesure du defaut elan est **partagee** avec la resolution : une
    seule mesure, quel que soit le nombre de paliers traverses. Le
    controle de derive est un diagnostic : il mesure toujours le defaut
    elan du poste, c'est son objet.
    """
    inv = load_inventory() if inventory is None else inventory
    hostname = current_host() if host is None else host
    measurement = _measurement(installed, loader)
    effective, provenance = resolve_pin(
        project_dir,
        env=env,
        inventory=inv,
        host=hostname,
        installed=measurement,
    )
    measured = measurement.get()
    declared = declared_pin(inv, hostname)
    fleet = fleet_pin(inv)
    environments = inv.get("environments") if isinstance(inv, dict) else None
    fleet_drift: list[dict] = []
    if isinstance(environments, dict) and fleet:
        for name, entry in sorted(environments.items()):
            if not isinstance(entry, dict):
                continue
            tag = entry.get("toolchain")
            if isinstance(tag, str) and tag.strip() and tag.strip() != fleet:
                fleet_drift.append({"host": name, "toolchain": tag.strip()})
    return {
        "host": hostname,
        "effective": effective,
        "provenance": provenance,
        "declared": declared,
        "elan_default": measured,
        "fleet_pin": fleet,
        "drift": provenance in ("default_resolu", "fallback_averti"),
        "local_default_drift": bool(
            measured and provenance != "default_resolu" and effective != measured),
        "fleet_drift": fleet_drift,
    }


def _format_report(report: dict) -> str:
    """Rendu lisible du controle de derive."""
    lines = [
        "Toolchain Lean — controle de derive",
        f"  hote              : {report['host'] or '<inconnu>'}",
        f"  pin effectif      : {report['effective']}  (provenance: {report['provenance']})",
        f"  declaration hote  : {report['declared'] or '<aucune>'}",
        f"  defaut elan mesure: {report['elan_default'] or '<inmesurable>'}",
        f"  pin de flotte     : {report['fleet_pin'] or '<aucun>'}",
    ]
    if report["drift"]:
        lines.append(
            "  VERDICT           : DERIVE — aucun pin declare pour ce poste ; "
            "chaque poste suivrait son propre defaut elan.")
    else:
        lines.append("  VERDICT           : OK — pin effectif reproductible entre postes.")
    if report["local_default_drift"]:
        lines.append(
            "  note              : le defaut elan de ce poste differe de sa "
            "declaration ; le pin effectif reste la declaration.")
    for entry in report["fleet_drift"]:
        lines.append(
            f"  derive flotte      : {entry['host']} declare {entry['toolchain']} "
            f"(pin de flotte : {report['fleet_pin']}).")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI : ``--resolve`` (defaut) et ``--check``."""
    parser = argparse.ArgumentParser(
        description="Epinglage de la toolchain Lean par environnement.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--resolve", action="store_true",
                       help="affiche le pin effectif et sa provenance (defaut)")
    group.add_argument("--check", action="store_true",
                       help="controle de derive (exit 1 si le pin n'est pas reproductible)")
    parser.add_argument("--project-dir", default=None,
                        help="projet lake dont le lean-toolchain est lu")
    parser.add_argument("--json", action="store_true",
                        help="sortie structuree")
    parser.add_argument("--verbose", action="store_true",
                        help="journal de l'organe")
    args = parser.parse_args(argv)

    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format="%(levelname)s %(name)s: %(message)s",
    )

    if args.check:
        report = check_drift(project_dir=args.project_dir)
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
        else:
            print(_format_report(report))
        return 1 if report["drift"] else 0

    tag, provenance = resolve_pin(args.project_dir)
    if args.json:
        print(json.dumps({"toolchain": tag, "provenance": provenance},
                         ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(f"{tag} {provenance}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
