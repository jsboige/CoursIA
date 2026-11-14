"""Le parcage Origami, dans le tapis rapide (#26523, parite de #24373).

Le tapis rapide decide sur la seule lecture groupee de `gh_bulk` : il ne lance
aucun processus. Le parcage Origami, lui, a besoin de l'etat des PLIS d'un
EPIC Origami -- ses sous-issues (y compris **fermees**) et les declarations de
depliage de son fil. Ces deux lectures ne sont pas dans `gh_bulk`.

Ce module fait le pont, sans lecture par issue :

* la **sonde de livraison** -- un pli est livre quand un commit de fusion le
  cite -- est fondee sur les citations de `gh_bulk` : **zero appel reseau** ;
* la **lecture des plis** passe par `origami_parking.measure`, dont le
  resultat est mis en cache **par la machine** (30 min, comme l'organe) :
  dans la demi-heure, le second tirage ne repaye rien.

C'est donc le seul point du tapis rapide qui sorte de la lecture groupee. Il
le dit, et il le borne : deux appels groupes, au plus une fois toutes les
30 min et par machine.

**Trois etats, jamais melanges.**

* `measured: true` : la mesure est faite ; les EPICs dont le pli suivant
  n'est pas deplie sont **parques** (ecart `ORIGAMI` dans le tapis) ;
* `measured: false` + `reason` : la mesure est impossible ; **rien n'est
  parque** et la cause est nommee -- jamais une liste vide, qui se lirait
  « rien a parquer » ;
* `measured: true`, `epics: 0` : le pool ne porte aucun EPIC Origami ; la
  mesure est faite, et vide.

Le parcage est **fail-OPEN** comme celui du tapis lourd (#24373) : une mesure
absente ne supprime jamais un grain. Ce qui change, c'est que la mesure est
faite -- l'absence de mesure se voit au lieu de passer inapercue.
"""
from __future__ import annotations

from typing import Any

from coordination import gh_bulk


class MesureImpossible(RuntimeError):
    """La mesure Origami n'a pas pu etre faite : la cause est nommee."""


def _stamps(lecture: gh_bulk.Lecture) -> dict[int, str]:
    """Le dernier commit de fusion qui cite chaque issue : la sonde de livraison."""
    out: dict[int, str] = {}
    for num, commits in (lecture.citations or {}).items():
        dates = [c.get("date") for c in commits or [] if c.get("date")]
        if dates:
            out[int(num)] = max(dates)
    return out


def _pool(lecture: gh_bulk.Lecture) -> list[dict]:
    """Le pool des issues ouvertes, vu par `origami_parking.measure`."""
    stamps = _stamps(lecture)
    return [{"number": int(it["number"]), "title": it.get("title") or "",
             "body": it.get("body") or "", "state": "OPEN",
             "labels": list(it.get("labels") or []),
             "last_delivery_stamp": stamps.get(int(it["number"]))}
            for it in lecture.issues]


def _verdicts(lecture: gh_bulk.Lecture, op: Any, *, cache: bool,
              reseau: bool) -> list[dict]:
    """Les verdicts de parcage : le cache machine s'il couvre le pool, sinon
    une mesure fraiche.

    Le cache est celui de l'organe (`%LOCALAPPDATA%/CoursIA/origami_parking`) :
    il est partage par la machine et par les lanes. Il expire en 30 min, la
    cadence du tapis -- un depliage fait dans la demi-heure est vu au cycle
    suivant.
    """
    pool = _pool(lecture)
    epics = op.origami_epic_numbers(pool)
    if not epics:
        return []
    if cache:
        cached = op.load_cache()
        if cached is not None:
            verdicts = cached.get("verdicts") or []
            couverts = {int(v["epic"]) for v in verdicts if v.get("epic") is not None}
            if set(epics) <= couverts:
                return verdicts
    if not reseau:
        raise MesureImpossible("rejeu hors ligne : la mesure Origami n'est pas disponible")
    stamps = _stamps(lecture)
    verdicts = op.measure(pool, delivered_probe=lambda n: bool(stamps.get(int(n))))
    try:
        op.save_cache(verdicts)
    except OSError:
        pass  # un cache non ecrit ne change pas la mesure
    return verdicts


def _etat(verdicts: list[dict]) -> tuple[dict[int, str], dict]:
    """(parques, etat) -- la forme que `belt_queues.py board` lit deja."""
    parques = {int(v["epic"]): v.get("reason") or ""
               for v in verdicts if v.get("parked")}
    etat = {"active": True, "measured": True, "epics": len(verdicts),
            "parked": sorted(parques),
            "details": [{"epic": int(v["epic"]), "parked": bool(v.get("parked")),
                         "reason": v.get("reason"), "next_pli": v.get("next_pli"),
                         "title": v.get("title")} for v in verdicts],
            "reason": "mesure faite"}
    return parques, etat


def _echec(cause: str, *, actif: bool = True) -> tuple[dict[int, str], dict]:
    """Une mesure impossible : rien n'est parque, et la cause est nommee.

    `actif` distingue les deux causes : le module absent (`False` -- la
    protection n'est pas installee, le tirage continue) et la lecture en
    echec (`True` -- la protection est installee mais n'a pas repondu).
    """
    return {}, {"active": actif, "measured": False, "parked": [], "reason": cause}


def mesurer(lecture: gh_bulk.Lecture, *, op: Any = None, cache: bool = True,
            reseau: bool = True) -> tuple[dict[int, str], dict]:
    """Les EPICs Origami a parquer, et l'etat de la mesure.

    `op` est le module `origami_parking` : les tests en passent un faux, et
    n'atteignent donc jamais le reseau.
    """
    if op is None:
        try:
            from coordination import origami_parking as op
        except ImportError as exc:  # pragma: no cover - le module est dans le depot
            return _echec(f"module indisponible ({exc})", actif=False)
    try:
        epics = op.origami_epic_numbers(_pool(lecture))
        if not epics:
            return {}, {"active": True, "measured": True, "epics": 0, "parked": [],
                        "details": [], "reason": "aucun EPIC Origami dans le pool"}
        verdicts = _verdicts(lecture, op, cache=cache, reseau=reseau)
    except MesureImpossible as exc:
        return _echec(str(exc))
    except Exception as exc:  # noqa: BLE001 - un garde ne doit pas casser le tirage
        return _echec(f"mesure en echec ({type(exc).__name__}: {exc})")
    if not any(v.get("measured") for v in verdicts):
        # Aucun pli connu : la mesure n'a pas abouti (fail-OPEN, rien n'est parque).
        return _echec("aucun pli materialise connu -- mesure absente")
    return _etat(verdicts)
