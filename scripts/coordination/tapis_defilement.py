#!/usr/bin/env python3
"""Le DEFILEMENT par lane sur toutes les issues ouvertes, et l'ORDRE mesure.

Mandat du mainteneur (22/11, #28114) : le picker doit tirer une file **sans
fin** pour chaque lane, et, si tout le reste echoue, defiler **chronologiquement
toutes les issues ouvertes**. Le coordinateur (26/11) demande la
**demonstration**, sur le pool REEL :

- l'ordre « consolidation -> jamais visitée -> anciennete », mesure **hors
  exclusions dures** ;
- le defilement reel qui couvre **toutes** les ouvertes, en moins de 60 s (I6).

Ce module ne REIMPLEMENTE aucun organe : il les **mesure**.

- l'ordre : `tapis_equilibre.niveau` (le bonus consolidation + age, pose en
  dixiemes et borne a 0,9) et l'equite du 16/11 (0 visite avant 1 visite) ;
- le defilement : `tapis_repli.replir`, le repli chronologique **reel**, joue
  sur le cache local reel, avec son curseur persistant.

Les exclusions dures sont **retirees** de la mesure : une issue livree, gelee,
couverte, en pause ou reclamee par une autre lane n'a pas a etre servie par le
defilement -- elle est comptee et nommee.

Ce que la mesure d'ordre ne pretend pas : l'ordre servi n'est pas un ordre
TOTAL. Le tapis fait tourner la tete de file par lane et entrelace les
familles dans un niveau (`tapis_equilibre.ordre`), donc deux issues de meme
niveau peuvent se succeder dans un ordre qui n'est ni par creation, ni par
numero. La mesure porte donc sur les **deux invariants verifiables** du
mandat -- l'equite (0 visite avant 1 visite) et la consolidation (posee en
premier dans le bonus) -- et sur les **comptes** des trois classes, pas sur une
clef totale qu'aucun organe ne produit.

L'ancre de la lane est **neutralisee** pendant la mesure : elle porte les
grains que la lane a servis sans les decider, donc l'etat de la lane, pas le
pool. Sans cette neutralisation, la mesure dependrait de l'historique de la
lane au lieu de porter sur le POOL.

Usage : tapis_defilement.py [--json] [--dashboard-line] [--lane <machine:workspace>]
    [--grains 8] [--jours 45] [--cache-s 3600] [--lecture <dossier>] [--max-s 60]
    (sorties : 0 l'ordre est respecte et le defilement est complet sous la
     borne ; 1 ordre rompu, defilement incomplet, ou hors borne ; 2 lecture
     incomplete sans secours, jamais un faux 0)

Un POOL VIDE (lecture complete, zero issue) est un etat **defini** : la
mesure est complete et le rapport le nomme (`pool_vide`), plutot que de lever
l'echec de lecture que le repli porte sur un cache vide.

Doc : docs/reference/tapis-rapide.md.
"""
from __future__ import annotations

import argparse
import json
import sys
import tempfile
import time
from contextlib import contextmanager
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import (
    gh_bulk,
    gh_cache_fichier,
    tapis_age,
    tapis_ancre,
    tapis_avantages,
    tapis_equilibre,
    tapis_labels,
    tapis_rapide,
    tapis_repli,
)

#: La borne du contrat (I6) : un tirage de lane rend en moins de 60 s.
BORNE_S = 60
#: Le nombre de tours de repli au-dela duquel le defilement est declare
#: incomplet : au-dela, ce n'est plus un defilement, c'est une boucle.
TOURS_MAX = 400


# --- l'ordre mesure -------------------------------------------------------------

def pool_servable(etats: list[tapis_rapide.Etat]) -> list[tapis_rapide.Etat]:
    """Le pool de la mesure : les issues sans ecart (exclusions dures retirees).

    Un ecart (`LIVREE`, `MERGEE`, `COUVERTE`, `GEL`, `PAUSE`, `LABEL`,
    `RECLAMEE`...) est une **exclusion dure** : l'issue n'a pas a etre servie
    par le defilement. Elle est comptee dans `exclusions`, pas servie.
    """
    return [e for e in etats if e.ecart is None]


def _positions(file_: list[tapis_rapide.Etat]) -> dict[int, int]:
    """La position de chaque issue servie, dans l'ordre du tour."""
    return {int(e.numero): i for i, e in enumerate(file_)}


def _est_conso(e: tapis_rapide.Etat, conso: set[int]) -> bool:
    """Une issue de consolidation : label, ou famille dont la racine l'est.

    La regle est celle de `tapis_avantages.est_consolidation` -- l'organe de
    la consolidation, pas une copie.
    """
    return tapis_avantages.est_consolidation(
        bool(getattr(e, "consolidation", False)),
        int(getattr(e, "famille", 0) or 0), conso)


def ordre(etats: list[tapis_rapide.Etat], lane: str, maintenant: datetime,
          grains: int = 8) -> dict:
    """L'ordre mesure sur le pool servable, et les temoins de sa rupture.

    La mesure porte sur l'ordre **effectivement servi** (la tete du tour
    rendue par `tapis_rapide.ordonner`), pas sur un pool re-trié : un pool
    re-trié prouverait la fonction de tri, pas l'organe.

    Deux invariants sont verifiables, et deux seulement :

    - l'**equite** du 16/11 : aucune issue deja visitée ne passe devant une
      issue jamais visitée (temoins : les positions fautives) ;
    - la **consolidation** (I7) : posee en premier dans le bonus, elle ne se
      fait pas distancer par les non-consolidations de la meme classe de
      visite (temoins : les paires fautives).

    Le rapport nomme aussi les trois classes du mandat -- consolidation,
    jamais visitée, deja visitée -- et les exclusions dures retirees.
    """
    servables = pool_servable(etats)
    conso = tapis_equilibre.familles_consolidation(etats)
    classes = {
        "pool": len(servables),
        "consolidation": sum(1 for e in servables if _est_conso(e, conso)),
        "jamais_visitee": sum(1 for e in servables
                              if int(getattr(e, "visites", 0) or 0) == 0),
        "deja_visitee": sum(1 for e in servables
                            if int(getattr(e, "visites", 0) or 0) > 0),
    }
    exclusions = sorted(e.numero for e in etats if e.ecart is not None)
    # Le PERIMETRE MARATHON est nomme, pas retire : les marathons de parite
    # (#26070, #26510) sont a niveau infini -- hors equilibrage, servis par le
    # harnais sk-agent. Ils restent dans le defilement (ils ne sortent pas du
    # pool) ; le rapport dit simplement qu'ils ne disputent pas l'equilibre.
    marathons = sorted(e.numero for e in etats if tapis_equilibre.est_marathon(e))
    # Les CLAIMS de la lane sont servis EN TETE par construction ("vos claims
    # en tete") : un claim deja visite precede donc, par design, une issue
    # jamais visitee, et le controle d'equite peut le nommer comme temoin.
    # Le rapport les NOME (le rapport se lit) ; l'invariant n'est pas change
    # -- c'est un arbitrage du coordinateur, pas un correctif silencieux.
    claims = sorted(e.numero for e in etats if getattr(e, "mon_claim", False))
    file_ = tapis_rapide.ordonner(etats, lane, maintenant, grains)
    pos = _positions(file_)

    # --- l'equite : 0 visite avant 1 visite --------------------------------
    jamais = [i for i, e in enumerate(file_) if int(getattr(e, "visites", 0) or 0) == 0]
    deja = [i for i, e in enumerate(file_) if int(getattr(e, "visites", 0) or 0) > 0]
    temoins_equite = sorted(int(file_[j].numero) for j in deja
                            if jamais and j < max(jamais))
    equite_ok = not temoins_equite

    # --- la consolidation : elle ne se fait pas distancer -------------------
    # I7 : dans une meme classe de visite, la consolidation est posee EN
    # PREMIER dans le bonus (mandat du 18/11) : son bonus est donc le plus
    # eleve, et elle doit preceder les non-consolidations de sa classe.
    # Une non-consolidation servie DEVANT elle, alors que le bonus de la
    # consolidation est le superieur, la fait distancer : le temoin est cette
    # non-consolidation, et le bonus superieur attendu est celui de la
    # consolidation -- pas celui du temoin.
    temoins_conso: list[int] = []
    for i, e in enumerate(file_):
        if not _est_conso(e, conso):
            continue
        dix, _ = tapis_equilibre.bonus(e, conso, maintenant)
        for j, f in enumerate(file_):
            if _est_conso(f, conso):
                continue
            if int(getattr(e, "visites", 0) or 0) != int(getattr(f, "visites", 0) or 0):
                continue  # pas la meme classe de visite : l'equite tranche
            if j >= i:
                continue  # la consolidation est deja devant : rien a signaler
            dix_f, _ = tapis_equilibre.bonus(f, conso, maintenant)
            if dix > dix_f:
                temoins_conso.append(int(f.numero))
    conso_ok = not temoins_conso

    return {
        "lane": lane,
        "classes": classes,
        "exclusions_dures": len(exclusions),
        "exclusions_numeros": exclusions,
        "marathon": {"hors_equilibrage": marathons, "nombre": len(marathons)},
        "claims_en_tete": {"numeros": claims, "nombre": len(claims)},
        "file": [int(e.numero) for e in file_],
        "equite": {"ok": equite_ok, "temoins": temoins_equite,
                   "jamais_servies": len(jamais), "deja_servies": len(deja)},
        "consolidation": {"ok": conso_ok, "temoins": sorted(set(temoins_conso)),
                          "rang_moyen": _rang_moyen(file_, conso)},
        "rompu": not (equite_ok and conso_ok),
        "positions": pos,
    }


def _rang_moyen(file_: list[tapis_rapide.Etat], conso: set[int]) -> dict:
    """Le rang moyen des consolidations et des autres dans la file servie.

    Le rang moyen ne dit pas « la consolidation passe devant » : il dit ou
    elle se tient, en moyenne, dans la file servie. Un ecart notable entre
    les deux rangs est un **signal**, pas une violation : la rotation de tete
    par lane et l'entrelacement des familles les deplacent.
    """
    if not file_:
        return {"consolidation": None, "autres": None}
    conso_pos = [i for i, e in enumerate(file_) if _est_conso(e, conso)]
    autres_pos = [i for i, e in enumerate(file_) if not _est_conso(e, conso)]
    def moy(xs: list[int]) -> float | None:
        return round(sum(xs) / len(xs), 2) if xs else None

    return {"consolidation": moy(conso_pos), "autres": moy(autres_pos)}


# --- le defilement reel ---------------------------------------------------------

@contextmanager
def _ancre_neutralisee():
    """L'ancre de la lane neutralisee : la mesure porte sur le POOL.

    L'ancre porte les grains que la lane a servis **sans les decider** : c'est
    l'etat de la lane, pas une exclusion du pool. Neutralisee, elle rend la
    mesure reproductible d'une lane a l'autre.
    """
    original = tapis_ancre.lire
    tapis_ancre.lire = lambda lane: {}  # type: ignore[assignment]
    try:
        yield
    finally:
        tapis_ancre.lire = original  # type: ignore[assignment]


@contextmanager
def _cache_dans(dossier: Path):
    """Le cache local **dans** le dossier de la mesure (curseur compris).

    Le repli lit son cache (`gh_bulk.dossier_cache_defaut`) et ecrit son
    curseur a cote. Sans cette redirection, la mesure consommerait le curseur
    REEL de la lane : ce serait un vol de position, pas une mesure.
    """
    original = gh_bulk.dossier_cache_defaut
    gh_bulk.dossier_cache_defaut = lambda: dossier  # type: ignore[assignment]
    try:
        yield
    finally:
        gh_bulk.dossier_cache_defaut = original  # type: ignore[assignment]


def _exclues_par_labels(lecture: gh_bulk.Lecture) -> set[int]:
    """Les issues ecartees par une exclusion dure de la voie legere.

    La meme regle que `tapis_universel.etats_leger` : le label de pause
    ecarte, l'urne (`candidate-delivered`) **non** -- l'urne a deux portes, et
    la voie legere n'est pas la sienne.
    """
    exclues: set[int] = set()
    for i in lecture.issues:
        labs = [str(l) for l in (i.get("labels") or [])]
        autres = [l for l in labs
                  if l.strip().lower() != tapis_labels.LABEL_LIVRE]
        if tapis_labels.ecart_label(autres):
            exclues.add(int(i["number"]))
    return exclues


def ouvertes_pool(lecture: gh_bulk.Lecture) -> set[int]:
    """Les numeros de toutes les issues ouvertes de la lecture."""
    return {int(i["number"]) for i in lecture.issues}


def defilement(lecture: gh_bulk.Lecture, lane: str, maintenant: datetime,
               grains: int = 8, jours: int = 45, dossier: Path | None = None,
               borne_s: int = BORNE_S) -> dict:
    """Le repli chronologique **reel**, joue jusqu'a la couverture du pool.

    Le repli (`tapis_repli.replir`) sert le pool dans l'ordre de creation, par
    blocs, avec un curseur persiste : des tours successifs couvrent le pool
    entier. La mesure compte les tours, la couverture et le temps.

    La couverture attendue est celle du pool **servable** : les issues ecartees
    par une exclusion dure (label de pause) ne sont pas comptees comme
    manquantes -- elles sont nommees.

    Le POOL VIDE est un etat **defini** : la lecture est complete (elle a
    rendu zero issue), il n'y a donc rien a defiler. Le repli, lui, ne peut pas
    servir un cache vide -- il leverait `LectureIncomplete` sur une lecture
    reussie. C'est un **zero vrai** : une mesure sur un pool vide, jamais un
    defilement absent (jamais un faux 0).
    """
    dossier = dossier or Path(tempfile.gettempdir()) / "tapis-defilement"
    dossier.mkdir(parents=True, exist_ok=True)
    gh_cache_fichier.ecrire(dossier / f"lecture-{jours}j.json", lecture)
    ouvertes = ouvertes_pool(lecture)
    if not ouvertes:
        return {
            "lane": lane,
            "ouvertes": 0,
            "exclues": [],
            "attendues": 0,
            "servies": 0,
            "manquantes": [],
            "manquantes_detail": _detail_manquantes(lecture, [], maintenant),
            "tours": 0,
            "blocs_annonces": 0,
            "slots": 0,
            "reprises": 0,
            "secondes": 0.0,
            "borne_s": borne_s,
            "sous_la_borne": True,
            "complet": True,
            "bloc": None,
            "avance": 0,
            "pool_vide": True,
        }
    servies: set[int] = set()
    tours = 0
    slots = 0
    reprises = 0
    debut = time.monotonic()
    rapport: dict = {}
    blocs = 0
    with _ancre_neutralisee(), _cache_dans(dossier):
        while tours < TOURS_MAX:
            tours += 1
            rapport, code = tapis_repli.replir(lane, grains, maintenant, jours,
                                               f"defilement-{tours}", dossier)
            if code != 0:
                break
            blocs = int(rapport.get("repli", {}).get("blocs") or 0) or blocs
            nums = {int(g["numero"]) for g in rapport.get("grains") or []}
            slots += len(nums)
            reprises += len(nums & servies)
            servies |= nums
            # Un tour qui n'apporte rien NEUTRE n'est pas une couverture close :
            # le repli sert des reprises, donc un tour peut ne rendre que des
            # deja servis. La mesure court donc le CYCLE complet (le nombre de
            # blocs annonce par le repli) et s'arrete plus tot si le pool est
            # couvert.
            if len(servies) >= len(ouvertes_pool(lecture)):
                break
            if blocs and tours >= blocs:
                break  # un cycle complet : le pool n'est pas couvert, c'est dit
    secondes = time.monotonic() - debut
    exclues = _exclues_par_labels(lecture)
    attendues = ouvertes - exclues
    manquantes = sorted(attendues - servies)
    return {
        "lane": lane,
        "ouvertes": len(ouvertes),
        "exclues": sorted(exclues),
        "attendues": len(attendues),
        "servies": len(servies),
        "manquantes": manquantes,
        "manquantes_detail": _detail_manquantes(lecture, manquantes, maintenant),
        "tours": tours,
        "blocs_annonces": blocs,
        "slots": slots,
        "reprises": reprises,
        "secondes": round(secondes, 3),
        "borne_s": borne_s,
        "sous_la_borne": secondes <= borne_s,
        "complet": not manquantes,
        "bloc": rapport.get("repli", {}).get("blocs"),
        "avance": rapport.get("repli", {}).get("avance"),
    }


def _detail_manquantes(lecture: gh_bulk.Lecture, manquantes: list[int],
                       maintenant: datetime) -> dict:
    """Pourquoi ces issues n'ont pas ete servies : leur age, leur nature.

    Le repli passe a la rotation l'ordre **par age** (`tapis_age.tour`), donc
    la bande des issues fraiches (`SEUIL_FRAICHES_H`) part en FIN de file. Les
    issues manquantes sont donc classees ici par age : la mesure dit si le
    defilement manque les issues fraiches, ou les anciennes.

    Les **conteneurs** (une EPIC, une umbrella) sont nommes a part : ils
    partagent le tour avec les grains (le quota des conteneurs prend des
    slots sur ceux des grains), donc ils sont une cause possible du meme
    defaut -- et la mesure doit les distinguer des autres.
    """
    ages: dict[int, float] = {}
    conteneurs: list[int] = []
    for i in lecture.issues:
        n = int(i["number"])
        if n not in manquantes:
            continue
        d = tapis_age._dt(i.get("created_at") or "")
        ages[n] = (maintenant - d).total_seconds() / 3600.0 if d else -1.0
        if tapis_rapide._conteneur_de(i.get("title") or "", i.get("labels") or []):
            conteneurs.append(n)
    frais = sorted(n for n, h in ages.items() if 0 <= h < tapis_age.SEUIL_FRAICHES_H)
    return {"frais": frais, "frais_nombre": len(frais),
            "conteneurs": sorted(conteneurs), "conteneurs_nombre": len(conteneurs),
            "anciennes": sorted(n for n in ages if n not in set(frais)),
            "echantillon": {str(n): round(h, 1) for n, h in
                            sorted(ages.items())[:12]}}


# --- la ligne de rapport --------------------------------------------------------

def ligne_dashboard(r: dict, code: int) -> str:
    """Une ligne (200 caracteres au plus) : le verdict d'abord."""
    o, d = r["ordre"], r["defilement"]
    ordre_txt = "ordre rompu" if o["rompu"] else "ordre respecte"
    defil_txt = ("defilement complet" if d["complet"]
                 else f"defilement incomplet ({len(d['manquantes'])} non couvertes)")
    tete = (f"Defilement #28114 : {d['ouvertes']} ouvertes, {d['servies']} servies "
            f"en {d['tours']} tour(s) ; {d['secondes']} s (borne {d['borne_s']} s)")
    ligne = f"{tete} ; {defil_txt} ; {ordre_txt} ; rc {code}"
    return ligne if len(ligne) <= 200 else ligne[:197] + "..."


def _texte(r: dict, source: str) -> str:
    """Le rapport en texte court, derive du rapport structure."""
    o, d = r["ordre"], r["defilement"]
    c = o["classes"]
    lignes = [
        f"Defilement et ordre du tapis (#28114) -- {r['maintenant']} -- source : {source}",
        (f"Ordre : pool servable {c['pool']} (exclusions dures {o['exclusions_dures']} "
         f"retirees) ; {c['consolidation']} consolidation(s), "
         f"{c['jamais_visitee']} jamais visitee(s), {c['deja_visitee']} deja visitee(s)."),
        f"  file servie : {o['file']}",
        (f"  marathons (hors equilibrage, harnais sk-agent) : "
         f"{o['marathon']['nombre']} {o['marathon']['hors_equilibrage']}"),
        (f"  claims de la lane (servis en tete par construction) : "
         f"{o['claims_en_tete']['nombre']} {o['claims_en_tete']['numeros']}"),
        (f"  equite (0 visite avant 1 visite) : "
         f"{'OK' if o['equite']['ok'] else 'ROMPUE -- ' + str(o['equite']['temoins'])}"),
        (f"  consolidation : "
         f"{'OK' if o['consolidation']['ok'] else 'ROMPUE -- ' + str(o['consolidation']['temoins'])}"
         f" ; rangs moyens {o['consolidation']['rang_moyen']}"),
        (f"Defilement : {d['ouvertes']} ouvertes, {d['attendues']} attendues "
         f"(exclues {len(d['exclues'])}), {d['servies']} servies en {d['tours']} tour(s) ; "
         f"{d['secondes']} s pour une borne de {d['borne_s']} s."),
        f"  manquantes : {d['manquantes']}",
    ]
    return "\n".join(lignes)


def verdict(r: dict) -> int:
    """Le code de sortie : 0 si tout tient, 1 sinon.

    Trois conditions, une par invariant mesure : l'ordre (equite et
    consolidation), la **couverture** du pool par le defilement, et la borne
    de temps (I6). Un defilement incomplet est un code 1 : le contrat I2
    veut TOUTES les issues ouvertes.
    """
    if r["ordre"]["rompu"]:
        return 1
    if not r["defilement"]["complet"] or not r["defilement"]["sous_la_borne"]:
        return 1
    return 0


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Defilement par lane sur toutes les issues ouvertes (#28114).")
    p.add_argument("--json", action="store_true")
    p.add_argument("--dashboard-line", action="store_true",
                   help="une seule ligne (200 caracteres au plus) pour le dashboard")
    p.add_argument("--lane", default="myia-ai-01:CoursIA-2",
                   help="machine:workspace")
    p.add_argument("--grains", type=int, default=8, help="taille du tour")
    p.add_argument("--jours", type=int, default=45, help="fenetre du cache")
    p.add_argument("--cache-s", type=int, default=3600,
                   help="0 desactive le cache (lecture reseau)")
    p.add_argument("--lecture", default=None, help="rejouer un dossier deja lu")
    p.add_argument("--max-s", type=int, default=BORNE_S, help="borne de temps (I6)")
    return p


def _lu_a(lecture: gh_bulk.Lecture) -> datetime | None:
    """L'instant de la lecture, pour un rejeu : memes ages, meme fenetre."""
    texte = str(lecture.lu_a)
    if texte.endswith("Z"):
        texte = texte[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(texte)
    except ValueError:
        return None


def main(argv: list[str] | None = None, run: gh_bulk.Run = gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    args = _parser().parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    try:
        if args.lecture:
            lecture = gh_bulk.charger_depuis(args.lecture, depot, args.jours, run)
        else:
            lecture = gh_bulk.lire_tout(depot, args.cache_s, run, args.jours)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        print("Defilement NON MESURE -- jamais un faux 0.", file=sys.stderr)
        return 2
    maintenant = maintenant or (args.lecture and _lu_a(lecture)) or datetime.now(UTC)
    etats = tapis_rapide.etats(lecture, args.lane, maintenant, args.jours)
    r = {
        "maintenant": maintenant.isoformat(),
        "lane": args.lane,
        "ordre": ordre(etats, args.lane, maintenant, args.grains),
        "lecture": {"lu_a": lecture.lu_a, "issues": len(lecture.issues),
                    "prs": len(lecture.prs), "depuis_cache": lecture.depuis_cache},
    }
    with tempfile.TemporaryDirectory(prefix="tapis-defilement-") as dossier:
        try:
            r["defilement"] = defilement(lecture, args.lane, maintenant, args.grains,
                                        args.jours, Path(dossier), args.max_s)
        except gh_bulk.LectureIncomplete as exc:
            # Le repli n'a pas pu lire son cache (`tapis_repli.replir` leve) :
            # l'echec de lecture reste l'echec de lecture, avec le meme
            # contrat que la lecture initiale -- rc 2, jamais une traceback.
            print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
                  file=sys.stderr)
            print("Defilement NON MESURE -- jamais un faux 0.", file=sys.stderr)
            return 2
    code = verdict(r)
    if args.json:
        out = json.dumps(r, ensure_ascii=False, indent=1)
    elif args.dashboard_line:
        out = ligne_dashboard(r, code)
    else:
        source = f"dossier {args.lecture}" if args.lecture else "cache et reseau du tapis"
        out = _texte(r, source)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return code


if __name__ == "__main__":
    sys.exit(main())
