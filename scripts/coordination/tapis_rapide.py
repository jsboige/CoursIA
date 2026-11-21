#!/usr/bin/env python3
"""Tapis rapide : voie legere du tirage des grains (#22983).

Le tapis PROPOSE, il ne fait pas autorite : avant d'editer, la lane relance
`check_lane_claim.py N --lane L` (`--paths` sur un conteneur, #26926). Tout est decide en fonctions pures sur la lecture
groupee de `gh_bulk`, seul module qui parle au reseau -- sauf le parcage
Origami (#26523), qui lit l'etat des plis d'un EPIC via le cache machine de
`origami_parking` (deux appels groupes, au plus une fois toutes les 30 min).
Doc : docs/reference/tapis-rapide.md.

Usage : tapis_rapide.py --lane <machine:workspace> [--grains 8] [--json] [--jours 45]
    [--cache-s 300] [--graine S] [--lecture <dossier>] [--allow-stale]
    (sorties : 0 tirage, y compris sur la lecture de secours du cache de moins
     de 12 h ; 3 lecture incomplete sans secours ; 4 main perime ou organe
     divergent. Aucune sortie ne renvoie au tapis lourd (#26926). Une mesure
     Origami en echec ne bloque pas le tirage -- fail-OPEN)
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import (frozen_campaigns, gh_bulk, gh_recherche, tapis_dernier_grain,
                         tapis_equilibre, tapis_origami, tapis_sature, tapis_service)
from coordination.tapis_marqueurs import (
    _FENCE_RE, _INFO_LIVRE_RE, _MARQUEUR_RE, VISITE, Evt, _age, _dt, _iso, _rouverte,
    claims_ouverts, evenements, lane_de_pr)
from coordination.tapis_hors_flotte import ecart_hors_flotte
from coordination.tapis_service import texte  # sortie texte, aussi lue par les tests

# Part au plus des conteneurs (EPIC, parapluie) dans la liste : la lane recoit des grains,
# pas des Epics ou chercher sa tranche ; ils completent la liste s'il manque des grains,
# toujours APRES les grains, avec leur procedure --paths (#26926).
PART_CONTENEURS = 0.25
CLAIM_VIVANT_H = 48  # au-dela, un claim est tenu pour abandonne (meme borne que l'organe)
# Plafond EPIC (#22500) : meme fenetre que l'organe check_lane_claim.py epic_visit_cap.
PLAFOND_EPIC_J = 7
# Une issue rendue par [RELEASED] n'est pas resservie pendant ce delai : la lane suivante
# re-mesurait la meme barriere (38 cycles sans grain servable, po-2023, 13/11).
RELACHE_J = 3
PROFONDEUR_FAMILLE = 5
LABEL_LIVRE = "candidate-delivered"
LABEL_CONSOLIDATION = "consolidation"
LABELS_CONTENEUR = frozenset({"epic", "umbrella"})
# Login partage : la lane habilitee a degeler se lit dans le marqueur, pas dans l'auteur.
LANES_DEGEL = frozenset({"myia-ai-01:CoursIA", "myia-po-2025:CoursIA-2"})
# Main a sorti les textes de service dans tapis_service (#26926) : REPLI et VERIF
# n'ont plus d'usage ici, seul le code d'ecart HORSFLOTTE reste a cabler.
# EPAISSE et SATURE sont les deux barrieres de FOND d'un CONTENEUR (#26973) :
# le fil declare l'epuisement, ou tous les enfants sont fermes.
CODES = ("HORSFLOTTE", "LABEL", "GEL", "EPAISSE", "LIVREE", "MERGEE", "COUVERTE",
         "RELACHEE", "PLAFOND", "ORIGAMI", "RECLAMEE", "SATURE")

_CITE_RE = re.compile(r"#(\d+)\b")
_PART_OF_RE = re.compile(r"\bpart\s+of\s*:?\s*#(\d+)\b", re.IGNORECASE)
_TITRE_EPIC_RE = re.compile(r"^\s*\[\s*epic\b[^\]]{0,40}?#(\d+)", re.IGNORECASE)
_TITRE_CROCHET_RE = re.compile(r"^\s*\[#(\d+)\b")
_TITRE_KIND_RE = re.compile(r"^\s*[\w.\- ]+?\s*\([^)]*?,\s*#(\d+)[^)]*\)\s*:")


@dataclass
class Etat:
    """L'etat d'une issue ouverte pour une lane : servable si `ecart` est None."""

    numero: int
    titre: str
    labels: list[str]
    cree_le: str
    parent: int | None
    famille: int
    conteneur: bool
    consolidation: bool
    derniere_visite: str | None = None
    visites: int = 0  # seances du tour (FENETRE_J jours), l'unite de l'equilibrage
    visites_total: int = 0  # seances sur toute la lecture
    ecart: str | None = None
    motif: str = ""
    notes: list[str] = field(default_factory=list)
    mon_claim: bool = False
    occupes: list[tuple[str, str]] = field(default_factory=list)  # (lane, paths) bornes
    #: L'etat de grain (raccord du classement, c3274) : `grain`,
    #: `passage_seul`, `jamais_servie` ou `non_measurable`. `None` = inconnu
    #: (la voie legere ne lit pas le fil : elle ne peut pas le dire).
    etat_grain: str | None = None


def parent_de(it: dict) -> int | None:
    """`Part of #N` du body, sinon un titre `[EPIC #N]`, `[Epic ... #N]`, `[#N`
    ou `type(zone,#N):` -- les formes que lit deja l'ancienne voie."""
    titre = it.get("title") or ""
    for m in (_PART_OF_RE.search(it.get("body") or ""), _TITRE_EPIC_RE.match(titre),
              _TITRE_CROCHET_RE.match(titre), _TITRE_KIND_RE.match(titre)):
        if m and int(m.group(1)) != it.get("number"):
            return int(m.group(1))
    return None


def _conteneur_propre(it: dict) -> bool:
    """Label EPIC/umbrella, ou titre `[EPIC...` qui ne nomme pas de parent
    (un `[EPIC #N] Phase 2` est une tranche)."""
    if any(lab.strip().lower() in LABELS_CONTENEUR for lab in it.get("labels") or []):
        return True
    titre = it.get("title") or ""
    return titre.lstrip(" [").upper().startswith("EPIC") and not _TITRE_EPIC_RE.match(titre)


def _ancetres(n: int, parents: dict[int, int | None]) -> tuple[list[int], int]:
    """Les parents en remontant (5 niveaux au plus) et la racine de famille.
    Une boucle rend la plus petite issue du cycle, la meme pour tous."""
    chaine, vus, cur = [], {n}, parents.get(n)
    while cur is not None and len(chaine) < PROFONDEUR_FAMILLE:
        if cur in vus:
            return chaine, min([n, *chaine])
        chaine.append(cur)
        vus.add(cur)
        cur = parents.get(cur)
    return chaine, (chaine[-1] if chaine else n)


def _gel(n: int, body: str, evts: list[Evt], ancetres: list[int]) -> str | None:
    """Regles de `frozen_campaigns.py` : parapluie gele en dur, ligne du body, fil."""
    for num in (n, *ancetres):
        if veto := frozen_campaigns.FROZEN_UMBRELLAS.get(str(num)):
            return f"parapluie #{num} gele par le veto user #{veto}"
    marques = _MARQUEUR_RE.finditer(_FENCE_RE.sub("", body))
    if any(m.group(1).upper() == "FROZEN" for m in marques):
        return "ligne [FROZEN] dans le body (degel : retirer la ligne)"
    gele = False
    for e in evts:
        if e.marque == "FROZEN":
            gele = True
        elif e.marque == "UNFROZEN" and e.lane in LANES_DEGEL:
            gele = False
    return "en-tete [FROZEN] du fil (degel : [UNFROZEN] d'une lane habilitee)" if gele else None


def _livree(it: dict, e: Etat, evts: list[Evt]) -> str | None:
    dernier = (it.get("comments") or [])[-1:]
    if dernier and _INFO_LIVRE_RE.search(_FENCE_RE.sub("", dernier[0].get("body") or "")):
        return "dernier commentaire [INFO] candidate-delivered"
    if e.conteneur or e.consolidation:
        return None  # un [DELIVERED] y livre une tranche, pas l'issue
    livres = [ev for ev in evts if ev.marque == "DELIVERED"]
    if livres and livres[-1].paths is None and not _rouverte(evts, livres[-1].quand):
        ev = livres[-1]
        return f"[DELIVERED] sans paths: de {ev.lane or '?'} le {_iso(ev.quand)[:10]}"
    return None


def _mergee(n: int, evts: list[Evt], citations: dict, limite: datetime) -> str | None:
    """Seul un commit qui FERME l'issue compte (`gh_bulk`) ; une simple citation
    reste une visite."""
    dates = [(d, c["sha"]) for c in citations.get(n, []) if c.get("ferme", True)
             and (d := _dt(c.get("date"))) and d >= limite]
    if not dates:
        return None
    quand, sha = max(dates)
    return None if _rouverte(evts, quand) else f"livraison probable, commit {sha[:7]}"


def _couverte(n: int, lane: str, prs_par_issue: dict[int, list[dict]]) -> str | None:
    prs = prs_par_issue.get(n) or []
    miennes = [pr["number"] for pr in prs if lane_de_pr(pr) == lane]
    if miennes:
        return f"votre PR #{miennes[0]} la cite : portez-la au merge"
    return f"PR ouverte #{prs[0]['number']} la cite" if prs else None


def _plafond(e: Etat, evts: list[Evt], naissances: list[tuple[int, str | None]],
             lane: str, maintenant: datetime) -> str | None:
    """Plafond hebdo des conteneurs hors consolidation (#22500 point 3) : le
    tapis ne sert pas un EPIC que le gate L898 refuserait. Une visite = un
    marqueur d'une AUTRE lane (#25443) ou la creation d'une fille ouverte."""
    if not e.conteneur or e.consolidation:
        return None
    limite = maintenant - timedelta(days=PLAFOND_EPIC_J)
    visites = [(ev.quand, f"visite de {ev.lane}") for ev in evts if ev.marque in VISITE
               and ev.lane and ev.lane != lane and ev.quand > limite]
    visites += [(d, f"sous-issue #{n} creee") for n, cree in naissances
                if (d := _dt(cree)) and d > limite]
    if not visites:
        return None
    quand, quoi = max(visites)
    age = round((maintenant - quand).total_seconds() / 86400, 1)
    return f"plafond EPIC (#22500) : {quoi} il y a {age} j (< {PLAFOND_EPIC_J} j)"


def _relachee(evts: list[Evt], maintenant: datetime) -> str | None:
    """Le dernier marqueur du fil est un [RELEASED] de moins de RELACHE_J jours,
    quelle que soit la lane : son motif (barriere, siege) vaut encore."""
    if not evts or evts[-1].marque != "RELEASED":
        return None
    ev = evts[-1]
    age = round((maintenant - ev.quand).total_seconds() / 86400, 1)
    if age >= RELACHE_J:
        return None
    return f"rendue par {ev.lane or '?'} il y a {age} j (< {RELACHE_J} j) : lire son motif"


def _reclamee(e: Etat, evts: list[Evt], lane: str, maintenant: datetime) -> None:
    """Claims vivants (< 48 h) : le mien remonte, celui d'une autre lane ecarte
    -- sauf sur un conteneur, ou seul un claim sans `paths:` ecarte."""
    for autre, ev in sorted(claims_ouverts(evts).items()):
        if maintenant - ev.quand > timedelta(hours=CLAIM_VIVANT_H):
            continue
        if autre == lane:
            e.mon_claim = True
            e.notes.insert(0, "votre claim")
        elif e.conteneur and ev.paths is not None:
            e.occupes.append((autre, ev.paths))  # servis en entier (#26926)
            e.notes.append(f"claim borne de {autre}")
        elif e.ecart is None:
            e.ecart, e.motif = "RECLAMEE", f"claim de {autre} du {_iso(ev.quand)[:16]}Z"


def _decider(e: Etat, it: dict, evts: list[Evt], ancetres: list[int], ctx: dict) -> None:
    """Le premier ecart qui s'applique gagne ; chacun est decide localement."""
    regles = [
        ("HORSFLOTTE", lambda: ecart_hors_flotte(it.get("body") or "")),
        ("LABEL", lambda: "label candidate-delivered : urne de cloture (coordinateur, adjoint)"
         if any(lab.strip().lower() == LABEL_LIVRE for lab in e.labels) else None),
        ("GEL", lambda: _gel(e.numero, it.get("body") or "", evts, ancetres)),
        ("EPAISSE", lambda: tapis_sature.epuise(e, it.get("comments") or [])),
        ("LIVREE", lambda: _livree(it, e, evts)),
        ("MERGEE", lambda: None if e.conteneur or e.consolidation else _mergee(
            e.numero, evts, ctx["citations"], ctx["limite"])),
        ("COUVERTE", lambda: None if e.conteneur else _couverte(
            e.numero, ctx["lane"], ctx["prs_par_issue"])),
        ("RELACHEE", lambda: _relachee(evts, ctx["maintenant"])),
        ("PLAFOND", lambda: _plafond(e, evts, ctx["filles"].get(e.numero, []),
                                     ctx["lane"], ctx["maintenant"])),
    ]
    for code, regle in regles:
        if motif := regle():
            e.ecart, e.motif = code, motif
            return
    _reclamee(e, evts, ctx["lane"], ctx["maintenant"])


def _prs_par_issue(prs: list[dict]) -> dict[int, list[dict]]:
    index: dict[int, list[dict]] = {}
    for pr in prs:
        texte = f"{pr.get('title') or ''}\n{pr.get('body') or ''}"
        for num in {int(x) for x in _CITE_RE.findall(texte)}:
            index.setdefault(num, []).append(pr)
    return index


def _contexte(lecture: gh_bulk.Lecture, lane: str, maintenant: datetime,
              jours: int = 45):
    """Issues ouvertes, parents, naissances et contexte de decision -- partages
    par `etats` et la re-decision sur fil complet (#27179)."""
    ouvertes = {it["number"]: it for it in lecture.issues}
    parents = {n: parent_de(it) for n, it in ouvertes.items()}
    # Naissances des filles ouvertes par conteneur : une visite du parent (#22500).
    filles: dict[int, list[tuple[int, str | None]]] = {}
    for n, p in parents.items():
        if p is not None:
            filles.setdefault(p, []).append((n, ouvertes[n].get("created_at")))
    ctx = {"lane": lane, "maintenant": maintenant, "citations": lecture.citations,
           "limite": maintenant - timedelta(days=jours), "filles": filles,
           "prs_par_issue": _prs_par_issue(lecture.prs)}
    return ouvertes, parents, filles, ctx


def etats(lecture: gh_bulk.Lecture, lane: str, maintenant: datetime,
          jours: int = 45) -> list[Etat]:
    """Un `Etat` par issue ouverte, decide sur la seule lecture."""
    ouvertes, parents, filles, ctx = _contexte(lecture, lane, maintenant, jours)
    nommes = {p for p in parents.values() if p is not None}
    resultat = []
    depuis = maintenant - timedelta(days=tapis_equilibre.FENETRE_J)
    for n, it in ouvertes.items():
        ancetres, famille = _ancetres(n, parents)
        labels = list(it.get("labels") or [])
        e = Etat(n, it.get("title") or "", labels, it.get("created_at") or "", parents[n],
                 famille, n in nommes or _conteneur_propre(it),
                 any(lab.strip().lower() == LABEL_CONSOLIDATION for lab in labels))
        evts = evenements(it.get("comments") or [])
        lus, total = len(it.get("comments") or []), it.get("comments_total") or 0
        # Raccord du classement (c3274) : une prise en charge nominative est
        # une visite, une citation Git n'en est pas une. L'etat de grain
        # distingue l'absence ETABLIE de l'absence NON MESURABLE (fil
        # partiel) : sans cette distinction, une issue dont le fil n'a pas
        # ete lu en entier se lit comme une issue jamais servie.
        e.etat_grain = tapis_dernier_grain.depuis_evenements(
            evts, lecture.citations.get(n, []), numero=n,
            fil_complet=(total <= lus), depuis=depuis).etat
        e.derniere_visite, e.visites_total, e.visites = tapis_dernier_grain.compter_grains(
            evts, depuis)
        _decider(e, it, evts, ancetres, ctx)
        if e.ecart is None and total > lus:
            e.notes.append(f"fil partiel ({lus}/{total} commentaires lus)")
        resultat.append(e)
    return resultat


def _parquer(tous: list[Etat], parcs: dict[int, str]) -> None:
    """Les EPICs Origami dont le pli suivant n'est pas deplie sortent du tirage.

    Le parcage est applique **apres** les autres ecarts : celui qui gagne
    reste le plus informatif pour la lane (un EPIC deja livre le reste livre).
    """
    for e in tous:
        if e.numero in parcs and e.ecart is None:
            e.ecart, e.motif = "ORIGAMI", parcs[e.numero]


def graine_defaut(lane: str, maintenant: datetime) -> str:
    """Meme lane, meme tranche de 4 h : meme liste ; deux lanes : deux listes."""
    m = maintenant.astimezone(UTC)
    return f"{lane}|{m:%Y-%m-%d}|{m.hour // 4}"


def _servable(e: Etat) -> bool:
    """Une issue que le tapis peut servir.

    Le #27059 elargit cette notion aux ecarts de recul (COUVERTE, RELACHEE,
    MERGEE), servis apres les autres : quand sa definition est presente, on la
    suit ; sinon on garde celle d'avant (aucun ecart dur). Sans cette
    compatibilite, le filtre de `ordonner` ecarterait du tour des issues que
    le tirage du #27059 entend servir.
    """
    f = globals().get("servable")
    return f(e) if f is not None else e.ecart is None


def ordonner(etats_: list[Etat], lane: str, maintenant: datetime, grains: int,
             graine: str | None = None) -> list[Etat]:
    """Vos claims en tete, puis l'equilibrage des visites (`tapis_equilibre`) :
    le niveau le moins visite d'abord, la plus ancienne issue d'abord.

    Invariant de couverture (#27590, dispatch `c0013-tapis-coverage-20`) : une
    issue **jamais visitée** ne cède jamais sa place a une issue deja visitée.
    Mesure du 21/11 sur le pool reel : 20 issues worker a 0 visite, dont 14
    conteneurs hors du tour de 8 -- deux issues deja visitees prenaient leurs
    places (le quota de conteneurs ecartait les conteneurs jamais visites, et
    le tri final plaçait les grains d'abord, #26926). Le mandat du 16/11
    (« toute issue visitée au moins une fois avant qu'une autre le soit deux
    fois ») etait donc structurellement violable. Les conteneurs jamais
    visités que le quota ecarte passent desormais en second temps, quand la
    place ne peut pas etre prise par une issue deja visitée. Le quota et
    l'ordre final (les grains d'abord) restent inchangés.
    """
    graine = graine or graine_defaut(lane, maintenant)
    servables = [e for e in etats_ if _servable(e)]
    file = sorted((e for e in servables if e.mon_claim), key=lambda e: (e.cree_le, e.numero))
    pris = {e.numero for e in file}
    # Un marathon est hors equilibrage (harnais sk-agent) : il ne dispute pas la
    # place d'une issue du pool, et il ne bloque pas non plus une issue deja
    # visitee -- sinon un marathon jamais visite passerait devant le grain
    # equilibre du tour.
    jamais = {e.numero for e in servables
              if e.visites == 0 and not tapis_equilibre.est_marathon(e)}
    tour = tapis_equilibre.ordre(etats_, [e for e in servables if not e.mon_claim],
                                 graine, maintenant)
    quota = max(1, int(grains * PART_CONTENEURS))
    reportes: list[Etat] = []
    for e in tour:  # un conteneur ne passe que dans son quota
        if len(file) >= grains:
            break
        if e.visites > 0 and (jamais - pris):
            # Une issue deja visitée ne prend pas la place d'une jamais visitée.
            continue
        if e.conteneur and quota <= 0:
            reportes.append(e)  # jamais visitée : elle passe en second temps
            continue
        quota -= e.conteneur
        file.append(e)
        pris.add(e.numero)
    for e in reportes:  # second temps : les conteneurs jamais visités
        if len(file) >= grains:
            break
        file.append(e)
        pris.add(e.numero)
    file += [e for e in tour if e.numero not in pris][:max(grains - len(file), 0)]
    # Vos claims, puis les grains, puis les conteneurs (#26926) : un conteneur
    # demande une lecture et un --paths, il ne passe jamais devant un grain.
    return sorted(file[:max(grains, 0)], key=lambda e: (not e.mon_claim, e.conteneur))


def rapport(lecture: gh_bulk.Lecture, etats_: list[Etat], file: list[Etat], lane: str,
            maintenant: datetime, graine: str) -> dict:
    """Les donnees du tirage, une seule fois : la sortie texte en derive."""
    conso, prs_par = tapis_equilibre.familles_consolidation(etats_), _prs_par_issue(lecture.prs)
    vos = sorted((pr for pr in lecture.prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    ecartees: dict[str, list[dict]] = {code: [] for code in CODES}
    for e in etats_:
        if e.ecart:
            ecartees[e.ecart].append({"numero": e.numero, "motif": e.motif})
    return {
        "lane": lane, "graine": graine, "maintenant": _iso(maintenant),
        "lecture": {"issues": len(etats_), "servables": sum(e.ecart is None for e in etats_),
                    "familles": len({e.famille for e in etats_ if e.ecart is None}), "lu_a": lecture.lu_a, "appels": lecture.appels,
                    "secondes": lecture.secondes, "depuis_cache": lecture.depuis_cache,
                    "fetch_note": lecture.fetch_note,
                    "origin_main_le": lecture.origin_main_le,
                    "origin_main_age_h": _age(maintenant, lecture.origin_main_le, 3600)},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)} for pr in vos],
        "grains": [tapis_service.grain_servi(
            i, e, lane, tapis_equilibre.raisons(e, conso, maintenant), prs_par) for i, e in enumerate(file, 1)],
        "ecartees": ecartees,
        # Les items ETEINTS (barrieres de fond) sont nommes pour l'urne de
        # cloture : ecarte en silence, un item eteint ne revient jamais et
        # personne ne le ferme (#26973).
        "eteints": tapis_sature.eteints(ecartees),
    }


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Tapis rapide : tirage leger des grains (#22983).")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8)
    p.add_argument("--json", action="store_true")
    p.add_argument("--jours", type=int, default=45, help="fenetre des commits cites")
    p.add_argument("--cache-s", type=int, default=300, help="0 desactive le cache")
    p.add_argument("--graine", default=None)
    p.add_argument("--lecture", default=None, help="rejouer un dossier deja lu")
    p.add_argument("--allow-stale", action="store_true",
                   help="outre-passer la garde de fraicheur (main local en retard "
                        "ou module du tirage divergent d'origin/main)")
    return p


def _ecarts_de_fond(tous: list, file: list, args, lecture, run, maintenant,
                    graine: str, lire_fils) -> tuple[list, dict | None]:
    """Les deux ecarteurs de FOND, dans l'ordre qui les rend cumulatifs.

    1. la **re-decision** (#27179) : un grain servi au fil tronque se re-decide
       sur son fil complet ; hors ligne ou cache, la fenetre reste la fenetre ;
    2. l'**ecart de saturation** (#26973) : les conteneurs dont tous les
       enfants sont fermes sortent de la file, et le tirage est refait pour
       les remplacer par un grain reel. La mesure porte sur les seuls
       conteneurs de la file, et elle est fail-OPEN : une panne n'ecarte rien.
       Un rejeu `--lecture` est hors ligne : rien n'est mesure, rien n'est
       ecarte.

    **ORDRE** : la re-decision passe AVANT la saturation. Les deux marquent le
    meme objet (`e.ecart`) et la saturation est la seule des deux a ne JAMAIS
    effacer une marque etrangere : la re-decision, elle, RECALCULE `e.ecart`
    depuis le fil complet -- appliquee apres, elle pourrait rendre servable un
    conteneur qui vient d'etre mesure sature. Dans cet ordre les deux
    exclusions subsistent : `ordonner` ne garde que les items dont
    `e.ecart is None`.
    """
    reverif = None
    if not args.lecture and not lecture.depuis_cache:
        from coordination import tapis_reverif
        file, reverif = tapis_reverif.passer(
            tous, file, args.grains, args.lane, maintenant, args.jours, graine,
            lecture, lire_fils)
    if not args.lecture:
        file = tapis_sature.ecarter_satures(
            tous, file,
            lambda n: gh_recherche.chercher_enfants(run, gh_bulk.DEPOT_GH, n),
            lambda: ordonner(tous, args.lane, maintenant, args.grains, graine))
    return file, reverif


def main(argv: list[str] | None = None, run: gh_bulk.Run = gh_bulk.run_defaut,
         maintenant: datetime | None = None, lire_fils: object = None) -> int:
    args = _parser().parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    # Garde de fraicheur (mandat 14/11) : le tirage se REFUSE (sortie 4, sans
    # repli picker) sur un main local en retard ou un organe du tirage divergent
    # d'origin/main ; un rejeu --lecture est hors ligne, pas de garde.
    fraicheur = None
    if not args.lecture:
        from coordination import main_freshness
        fraicheur = main_freshness.garder_et_dire(depot, allow_stale=args.allow_stale)
        if fraicheur["refuse"]:
            return 4  # pas le repli picker : il fait rejouer le meme incident
    try:
        if args.lecture:
            lecture = gh_bulk.charger_depuis(args.lecture, depot, args.jours, run)
        else:
            lecture = gh_bulk.lire_tout(depot, args.cache_s, run, args.jours)
    except gh_bulk.LectureIncomplete as exc:
        # Secours (#26926) : la derniere lecture COMPLETE du cache (< 12 h), jamais
        # le tapis lourd (240 s, grains non verifies). Un rejeu n'a pas de secours.
        secours = None if args.lecture or args.cache_s <= 0 else \
            tapis_service.lecture_de_secours(args.jours, exc)
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        if secours is None:
            print(tapis_service.SANS_SECOURS, file=sys.stderr)
            return 3
        lecture = secours
        print(f"Tirage sur la lecture de secours du {lecture.lu_a}.", file=sys.stderr)
    # Un rejeu se tire a l'instant de sa lecture : memes ages de claims, meme graine.
    maintenant = maintenant or (args.lecture and _dt(lecture.lu_a)) or datetime.now(UTC)
    # Parcage Origami (#24373) : un EPIC au pli non deplie n'est pas servi ;
    # une mesure en panne ne bloque pas le tirage, elle se dit (fail-OPEN, #26528).
    parcs, origami = tapis_origami.mesurer(lecture, reseau=not args.lecture)
    if not origami.get("measured") and origami.get("active") and not args.lecture:
        tapis_origami.dire_panne(origami)
    tous = etats(lecture, args.lane, maintenant, args.jours)
    _parquer(tous, parcs)
    graine = args.graine or graine_defaut(args.lane, maintenant)
    file = ordonner(tous, args.lane, maintenant, args.grains, graine)
    file, reverif = _ecarts_de_fond(tous, file, args, lecture, run, maintenant,
                                     graine, lire_fils)
    r = rapport(lecture, tous, file, args.lane, maintenant, graine)
    r["origami_parking"] = origami
    if reverif is not None:
        r["reverif_fils"] = reverif
    if fraicheur is not None:
        r["fraicheur"] = fraicheur  # le depassement --allow-stale se LIT dans le JSON
    source = f"dossier {args.lecture}" if args.lecture else "GitHub + origin/main local"
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else texte(r, source)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
