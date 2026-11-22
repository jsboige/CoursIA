#!/usr/bin/env python3
"""Les criteres d'acceptation de #25082, mesures sur le SERVICE EFFECTIF.

Pourquoi ce module existe
-------------------------
#25082 (bandit par famille + priorite de consolidation) porte quatre criteres
d'acceptation. Le deuxieme demande : « au moins 15 % des 50 tirages en
``consolidation`` ou ``delivered``, et ``family`` resolue sur au moins 80 % des
tirages ».

Ce critere a ete mesure sur une VOIE qui n'est plus le service :

- le **rejeu** (``pick_idle_grain.py --belt-replay-input``) rejoue le
  classement du 07/11 : c'est un **diagnostic** (#26926), pas le service ;
- le **service effectif** n'a jamais ete mesure : le releve persistant n'a
  pas de section de service remplie, et le journal des tirages ne porte que
  des tirages de la voie diagnostic (octobre) ;
- la classe ``delivered`` n'est **pas servie** par le service effectif : les
  regles ``LIVREE`` et ``LABEL candidate-delivered`` l'ecartent AVANT le
  tirage (seules les issues de consolidation y sont exemptes) : la part
  ``delivered`` est donc **nulle par construction**.

Ce module comble le manque : il **journalise** les tirages reellement servis
et **mesure** les deux criteres sur le service effectif. Il n'invente ni le
journal ni son verrou -- il reutilise ``coordination.tirage_journal``.

Deux garde-fous, mesures :

- **un magasin dedie** (``%LOCALAPPDATA%/CoursIA/tapis_service/journal.jsonl``) :
  la mesure du service lit son propre magasin, distinct des ``belt`` ;
- **une lecture reelle** : un tirage issu d'une lecture INJECTEE n'est pas un
  tirage servi et ne s'ecrit pas -- sinon la mesure compte des grains jamais servis.

Ecriture consultative : une panne de telemetry ne doit pas casser le service
(le tirage reste servi) ; elle se dit sur stderr. La mesure, elle, est
fail-CLOSED : sans echantillon elle rend ``AUCUNE MESURE``, jamais 0 % ; sous
l'echantillon plein (50 tirages) elle rend ``MESURE PARTIELLE``.

Usage : ``--stat [--json]`` pour mesurer le magasin, ``--draw <tirage.json>``
pour journaliser un tirage capture.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import uuid
from collections.abc import Iterable
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, tirage_journal

MODE = "tapis_rapide"
"""Mode des enregistrements du journal : le service effectif, pas le diagnostic."""

URN = "live"
CRITERE_PART_PRIORITAIRE = 0.15
CRITERE_PART_FAMILLE = 0.80
ECHANTILLON_PLEIN = 50
"""Le critere parle de « 50 tirages » : sous ce nombre, le verdict est partiel."""

NOTE_DELIVERED = (
    "la classe delivered est ecartee avant service par les regles LIVREE et LABEL "
    "candidate-delivered (seules les issues de consolidation y sont exemptes) : "
    "sur le service effectif la part delivered est nulle par construction, "
    "le critere se lit 'consolidation'"
)


def _etat_base() -> Path:
    """Le state dir machine, comme les autres organes de coordination."""
    local = os.environ.get("LOCALAPPDATA")
    if local:
        return Path(local) / "CoursIA"
    xdg = os.environ.get("XDG_STATE_HOME")
    if xdg:
        return Path(xdg) / "coursia"
    return Path.home() / ".local" / "state" / "coursia"


def default_store() -> Path:
    """Le magasin dedie aux tirages du service effectif."""
    return _etat_base() / "tapis_service" / "journal.jsonl"


def journaliser(
    grains: list[dict],
    lane: str,
    *,
    ts: str | None = None,
    path: Path | str | None = None,
    draw_id: str | None = None,
) -> int:
    """Enregistre les grains servis par un tirage du service effectif.

    Un enregistrement par grain servi ; les grains d'un meme tirage partagent
    un ``draw_id`` et une horodatage. Le verrou et le magasin sont ceux de
    ``coordination.tirage_journal`` : rien n'est reimplemente ici.
    """
    if not grains:
        return 0
    nombres = [int(g["numero"]) for g in grains]
    draw_id = draw_id or uuid.uuid4().hex[:12]
    ts = ts or datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
    journal = tirage_journal.Journal(path or default_store())
    ecrits = 0
    for g in grains:
        record = tirage_journal.TirageRecord.new(
            lane=lane,
            candidates=nombres,
            retained=int(g["numero"]),
            urn=URN,
            mode=MODE,
            draw_id=draw_id,
            ts=ts,
            extras={"famille": g.get("famille"), "consolidation": bool(g.get("consolidation")),
                    "rang": g.get("rang"), "conteneur": bool(g.get("conteneur"))},
        )
        journal.log(record)
        ecrits += 1
    return ecrits


def journaliser_service(r: dict, lane: str, replay: bool = False,
                       run: object = None, path: Path | str | None = None) -> dict:
    """Journalise le tirage rendu par le service, sans jamais casser le service.

    Trois refus, tous motives : un rejeu (``--lecture``) n'est pas un tirage
    servi ; une lecture injectee (les tests appellent ``main()`` avec une
    lecture factice) n'est pas non plus un tirage servi ; et une panne de
    telemetry se dit sur stderr sans interrompre le tirage -- fail-OPEN, comme
    le parcage Origami dans le meme organe.
    """
    if replay:
        return {"enregistres": 0, "motif": "rejeu hors ligne : pas un tirage servi"}
    if run is not None and run is not gh_bulk.run_defaut:
        return {"enregistres": 0, "motif": "lecture injectee : pas un tirage servi"}
    try:
        ecrits = journaliser(grains_de_tirage(r), lane, path=path)
    except Exception as exc:  # noqa: BLE001 - une telemetry muette = une mesure absente
        print(f"[WARN] journal du service indisponible : {exc}", file=sys.stderr)
        return {"enregistres": 0, "erreur": str(exc)}
    return {"enregistres": ecrits}


def _tirages(servies: list[tirage_journal.TirageRecord]) -> list[list[tirage_journal.TirageRecord]]:
    """Les enregistrements regroupes par tirage (le `draw_id`).

    Le journal ecrit un enregistrement par grain servi ; l'unite du critere
    de #25082 est le tirage (« 50 tirages »), pas le grain.
    """
    groupes: dict[str, list[tirage_journal.TirageRecord]] = {}
    for r in servies:
        # Un enregistrement sans `draw_id` n'est attribuable a aucun tirage :
        # il compte pour lui.
        cle = r.draw_id or f"__sans_draw_id__:{len(groupes)}"
        groupes.setdefault(cle, []).append(r)
    return list(groupes.values())


def mesurer(records: Iterable[tirage_journal.TirageRecord]) -> dict:
    """Mesure les deux criteres de #25082 sur les tirages du service effectif.

    Seuls les enregistrements du service effectif (``mode == MODE``) comptent :
    ceux de la voie diagnostic mesurent une autre chose.

    L'unite est le **tirage** : il est de consolidation si un de ses grains
    l'est, et sa famille est resolue si tous ses grains l'ont.
    """
    servies = [r for r in records if r.mode == MODE]
    tirages = _tirages(servies)
    n = len(tirages)
    if n == 0:
        return {
            "tirages": 0,
            "grains": 0,
            "part_consolidation": None,
            "part_famille": None,
            "criteres": {
                "prioritaire": _critere(None, CRITERE_PART_PRIORITAIRE, "AUCUNE MESURE"),
                "famille": _critere(None, CRITERE_PART_FAMILLE, "AUCUNE MESURE"),
            },
            "note_delivered": NOTE_DELIVERED,
        }
    conso = sum(1 for t in tirages
                if any((r.extras or {}).get("consolidation") for r in t))
    famille = sum(1 for t in tirages
                  if all((r.extras or {}).get("famille") is not None for r in t))
    part_c = conso / n
    part_f = famille / n
    return {
        "tirages": n,
        "grains": len(servies),
        "part_consolidation": part_c,
        "part_famille": part_f,
        "criteres": {
            "prioritaire": _critere(part_c, CRITERE_PART_PRIORITAIRE, None),
            "famille": _critere(part_f, CRITERE_PART_FAMILLE, None),
        },
        "note_delivered": NOTE_DELIVERED,
    }


def _critere(mesure: float | None, seuil: float, force: str | None) -> dict:
    """Le verdict d'un critere : TENU, NON TENU, MESURE PARTIELLE ou AUCUNE MESURE.

    L'echantillon plein conditionne le verdict : sous 50 tirages, la mesure
    est partielle et ne conclut pas.
    """
    if force:
        return {"seuil": seuil, "mesure": mesure, "statut": force}
    if mesure is None:
        return {"seuil": seuil, "mesure": None, "statut": "AUCUNE MESURE"}
    if mesure >= seuil:
        return {"seuil": seuil, "mesure": mesure, "statut": "TENU"}
    return {"seuil": seuil, "mesure": mesure, "statut": "NON TENU"}


def _statut_partiel(mesure: dict) -> dict:
    """Marque la mesure comme partielle quand l'echantillon est trop court."""
    n = mesure["tirages"]
    if 0 < n < ECHANTILLON_PLEIN:
        for crit in mesure["criteres"].values():
            if crit["statut"] in ("TENU", "NON TENU"):
                crit["statut"] = "MESURE PARTIELLE"
                crit["echantillon"] = n
                crit["echantillon_plein"] = ECHANTILLON_PLEIN
    return mesure


def grains_de_tirage(draw: dict) -> list[dict]:
    """Les grains servis d'un tirage du service effectif (JSON du tirage)."""
    return list(draw.get("grains") or [])


def _texte(m: dict) -> str:
    def part(v: float | None) -> str:
        return "n/a" if v is None else f"{v * 100:.1f} %"
    lignes = [
        "Acceptance 2 de #25082, mesuree sur le service effectif",
        f"tirages servis (magasin dedie, mode {MODE}) : {m['tirages']}",
        f"grains servis : {m['grains']}",
        ("part consolidation : " + part(m['part_consolidation'])
         + f" (seuil {CRITERE_PART_PRIORITAIRE * 100:.0f} % -> {m['criteres']['prioritaire']['statut']})"),
        ("part famille resolue : " + part(m['part_famille'])
         + f" (seuil {CRITERE_PART_FAMILLE * 100:.0f} % -> {m['criteres']['famille']['statut']})"),
        f"note : {m['note_delivered']}",
    ]
    if 0 < m["tirages"] < ECHANTILLON_PLEIN:
        lignes.append(
            f"echantillon partiel ({m['tirages']} < {ECHANTILLON_PLEIN} tirages) : "
            "aucun verdict, la mesure est indicative")
    return "\n".join(lignes)


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Criteres de #25082 mesures sur le service effectif.")
    p.add_argument("--stat", action="store_true", help="mesurer le magasin du service")
    p.add_argument("--draw", default=None, help="journaliser un tirage capture (JSON)")
    p.add_argument("--lane", default=None, help="lane du tirage capture")
    p.add_argument("--journal", default=None, help="chemin du magasin (sinon le magasin machine)")
    p.add_argument("--json", action="store_true")
    return p


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    chemin = Path(args.journal) if args.journal else default_store()
    if args.draw:
        draw = json.loads(Path(args.draw).read_text(encoding="utf-8"))
        grains = grains_de_tirage(draw)
        lane = args.lane or draw.get("lane") or "?"
        ecrits = journaliser(grains, lane, path=chemin)
        mesures = _statut_partiel(mesurer(tirage_journal.read_journal(chemin)))
        if args.json:
            print(json.dumps({"enregistres": ecrits, "mesure": mesures},
                             ensure_ascii=False, indent=1))
        else:
            print(f"{ecrits} grain(s) enregistre(s) pour la lane {lane}.")
            print(_texte(mesures))
        return 0
    if not args.stat:
        _parser().print_help()
        return 2
    mesures = _statut_partiel(mesurer(tirage_journal.read_journal(chemin)))
    if args.json:
        print(json.dumps(mesures, ensure_ascii=False, indent=1))
    else:
        print(_texte(mesures))
    return 0


if __name__ == "__main__":
    sys.exit(main())
