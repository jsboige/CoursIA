#!/usr/bin/env python3
"""Tapis rapide : voie legere du tirage des grains (#22983).

Le tapis PROPOSE, il ne fait pas autorite : avant d'editer, la lane relance
`check_lane_claim.py N --lane L`. Tout est decide en fonctions pures sur la lecture
groupee de `gh_bulk`, seul module qui parle au reseau. Doc : docs/reference/tapis-rapide.md.

Usage : tapis_rapide.py --lane <machine:workspace> [--grains 8] [--json] [--jours 45]
    [--cache-s 300] [--graine S] [--lecture <dossier>]   (sortie 0, ou 3 : lecture incomplete)
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import sys
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import frozen_campaigns, gh_bulk
from coordination.tapis_marqueurs import (
    _FENCE_RE, _INFO_LIVRE_RE, _MARQUEUR_RE, VISITE, Evt, _dt, _iso, _rouverte,
    claims_ouverts, evenements, lane_de_pr)

# Poids des familles, une ligne a changer pour regler la priorite. Ils restent
# legers : aucune famille n'est privee de service.
PRIO_CONSOLIDATION = 1.5
PRIO_VIEIL_EPIC = 1.5
AGE_VIEIL_EPIC_J = 60
# Part au plus des conteneurs (EPIC, parapluie) dans la liste : la lane recoit des grains,
# pas des Epics ou chercher sa tranche ; ils completent la liste s'il manque des grains.
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
CODES = ("LABEL", "GEL", "LIVREE", "MERGEE", "COUVERTE", "RELACHEE", "PLAFOND", "RECLAMEE")
REPLI = "python scripts/pick_idle_grain.py --belt --lane {lane}"
VERIF = "python scripts/check_lane_claim.py {n} --lane {lane}"

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
    ecart: str | None = None
    motif: str = ""
    notes: list[str] = field(default_factory=list)
    mon_claim: bool = False


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
            e.notes.append(f"claim borne de {autre} : {ev.paths[:60]}")
        elif e.ecart is None:
            e.ecart, e.motif = "RECLAMEE", f"claim de {autre} du {_iso(ev.quand)[:16]}Z"


def _decider(e: Etat, it: dict, evts: list[Evt], ancetres: list[int], ctx: dict) -> None:
    """Le premier ecart qui s'applique gagne ; chacun est decide localement."""
    regles = [
        ("LABEL", lambda: "label candidate-delivered : urne de cloture (coordinateur, adjoint)"
         if any(lab.strip().lower() == LABEL_LIVRE for lab in e.labels) else None),
        ("GEL", lambda: _gel(e.numero, it.get("body") or "", evts, ancetres)),
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


def etats(lecture: gh_bulk.Lecture, lane: str, maintenant: datetime,
          jours: int = 45) -> list[Etat]:
    """Un `Etat` par issue ouverte, decide sur la seule lecture."""
    ouvertes = {it["number"]: it for it in lecture.issues}
    parents = {n: parent_de(it) for n, it in ouvertes.items()}
    nommes = {p for p in parents.values() if p is not None}
    # Naissances des filles ouvertes par conteneur : une visite du parent (#22500).
    filles: dict[int, list[tuple[int, str | None]]] = {}
    for n, p in parents.items():
        if p is not None:
            filles.setdefault(p, []).append((n, ouvertes[n].get("created_at")))
    ctx = {"lane": lane, "maintenant": maintenant, "citations": lecture.citations,
           "limite": maintenant - timedelta(days=jours), "filles": filles,
           "prs_par_issue": _prs_par_issue(lecture.prs)}
    resultat = []
    for n, it in ouvertes.items():
        ancetres, famille = _ancetres(n, parents)
        labels = list(it.get("labels") or [])
        e = Etat(n, it.get("title") or "", labels, it.get("created_at") or "", parents[n],
                 famille, n in nommes or _conteneur_propre(it),
                 any(lab.strip().lower() == LABEL_CONSOLIDATION for lab in labels))
        evts = evenements(it.get("comments") or [])
        visites = [ev.quand for ev in evts if ev.marque in VISITE]
        visites += [d for c in lecture.citations.get(n, []) if (d := _dt(c.get("date")))]
        e.derniere_visite = _iso(max(visites)) if visites else None
        _decider(e, it, evts, ancetres, ctx)
        lus, total = len(it.get("comments") or []), it.get("comments_total") or 0
        if e.ecart is None and total > lus:
            e.notes.append(f"fil partiel ({lus}/{total} commentaires lus)")
        resultat.append(e)
    return resultat


def graine_defaut(lane: str, maintenant: datetime) -> str:
    """Meme lane, meme tranche de 4 h : meme liste ; deux lanes : deux listes."""
    m = maintenant.astimezone(UTC)
    return f"{lane}|{m:%Y-%m-%d}|{m.hour // 4}"


def poids_familles(etats_: list[Etat], maintenant: datetime) -> dict[int, tuple[float, list[str]]]:
    """Poids et raisons de priorite de chaque famille servable."""
    par_num = {e.numero: e for e in etats_}
    groupes: dict[int, list[Etat]] = {}
    for e in etats_:
        if e.ecart is None:
            groupes.setdefault(e.famille, []).append(e)
    res: dict[int, tuple[float, list[str]]] = {}
    for fam, membres in groupes.items():
        racine, poids, raisons = par_num.get(fam), 1.0, []
        if any(e.consolidation for e in membres) or (racine and racine.consolidation):
            poids, raisons = poids * PRIO_CONSOLIDATION, ["consolidation"]
        cree = _dt(racine.cree_le) if racine else None
        if racine and racine.conteneur and cree and \
                maintenant - cree > timedelta(days=AGE_VIEIL_EPIC_J):
            poids, raisons = poids * PRIO_VIEIL_EPIC, [*raisons, f"vieil EPIC #{fam}"]
        res[fam] = (poids, raisons)
    return res


def _cle_famille(graine: str, famille: int, poids: float) -> float:
    """Tirage pondere sans remise : `u ** (1 / poids)`, la plus grande d'abord."""
    h = hashlib.sha256(f"{graine}|{famille}".encode()).digest()
    return random.Random(int.from_bytes(h[:8], "big")).random() ** (1.0 / poids)


def _cle_membre(e: Etat) -> tuple:
    """Votre claim, puis jamais visitee (la plus ancienne), puis la moins
    recemment visitee ; a egalite, le grain borne avant son conteneur."""
    jamais = e.derniere_visite is None
    return (not e.mon_claim, not jamais, e.cree_le if jamais else e.derniere_visite,
            e.conteneur, e.numero)


def ordonner(etats_: list[Etat], lane: str, maintenant: datetime, grains: int,
             graine: str | None = None) -> list[Etat]:
    """Vos claims en tete, puis les familles servies a tour de role."""
    graine = graine or graine_defaut(lane, maintenant)
    poids = poids_familles(etats_, maintenant)
    servables = sorted((e for e in etats_ if e.ecart is None), key=_cle_membre)
    file = [e for e in servables if e.mon_claim]
    groupes: dict[int, list[Etat]] = {}
    for e in servables:
        if not e.mon_claim:
            groupes.setdefault(e.famille, []).append(e)
    ordre = sorted(groupes, key=lambda f: (-_cle_famille(graine, f, poids[f][0]), f))
    tour, rang = [], 0
    while any(rang < len(groupes[f]) for f in ordre):
        tour.extend(groupes[f][rang] for f in ordre if rang < len(groupes[f]))
        rang += 1
    quota, pris = max(1, int(grains * PART_CONTENEURS)), set()
    for e in tour:  # un conteneur ne passe que dans son quota
        if len(file) < grains and (not e.conteneur or quota > 0):
            quota -= e.conteneur
            file.append(e)
            pris.add(e.numero)
    file += [e for e in tour if e.numero not in pris][:max(grains - len(file), 0)]
    return file[:max(grains, 0)]


def _age(maintenant: datetime, quand: str | None, unite_s: int) -> float | None:
    d = _dt(quand)
    return round((maintenant - d).total_seconds() / unite_s, 1) if d else None


def rapport(lecture: gh_bulk.Lecture, etats_: list[Etat], file: list[Etat], lane: str,
            maintenant: datetime, graine: str) -> dict:
    """Les donnees du tirage, une seule fois : la sortie texte en derive."""
    poids = poids_familles(etats_, maintenant)
    vos = sorted((pr for pr in lecture.prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    ecartees: dict[str, list[dict]] = {code: [] for code in CODES}
    for e in etats_:
        if e.ecart:
            ecartees[e.ecart].append({"numero": e.numero, "motif": e.motif})
    return {
        "lane": lane, "graine": graine, "maintenant": _iso(maintenant),
        "lecture": {"issues": len(etats_), "servables": sum(e.ecart is None for e in etats_),
                    "familles": len(poids), "lu_a": lecture.lu_a, "appels": lecture.appels,
                    "secondes": lecture.secondes, "depuis_cache": lecture.depuis_cache,
                    "fetch_note": lecture.fetch_note,
                    "origin_main_le": lecture.origin_main_le,
                    "origin_main_age_h": _age(maintenant, lecture.origin_main_le, 3600)},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)} for pr in vos],
        "grains": [{"rang": i, "numero": e.numero, "titre": e.titre, "famille": e.famille,
                    "parent": e.parent, "conteneur": e.conteneur, "notes": e.notes,
                    "consolidation": e.consolidation, "derniere_visite": e.derniere_visite,
                    "priorite": poids.get(e.famille, (1.0, []))[1],
                    "avant_d_editer": VERIF.format(n=e.numero, lane=lane)}
                   for i, e in enumerate(file, 1)],
        "ecartees": ecartees,
    }


def _court(texte: str, n: int) -> str:
    return texte if len(texte) <= n else texte[:n - 3] + "..."


def texte(r: dict, source: str) -> str:
    """Sortie courte, en francais, derivee du rapport."""
    lu, age_h = r["lecture"], r["lecture"]["origin_main_age_h"]
    age = "inconnu" if age_h is None else (
        f"il y a {age_h} h" if age_h >= 0 else f"{-age_h} h apres la lecture rejouee")
    fetch = f" ; {lu['fetch_note']}" if lu.get("fetch_note") else ""
    lignes = [f"Tapis rapide -- lane {r['lane']} -- {r['maintenant']} -- source : {source}"]
    lignes.append(f"{lu['issues']} issues ouvertes, {lu['servables']} servables en "
                  f"{lu['familles']} familles ; lecture {lu['secondes']} s, {lu['appels']} "
                  f"appels, cache {'oui' if lu['depuis_cache'] else 'non'} ; origin/main "
                  f"local : dernier commit {age}{fetch}")
    lignes.append(f"\nVos PRs ouvertes ({len(r['vos_prs'])}) -- portez d'abord au merge "
                  "celles de plus de 24 h :")
    lignes += [f"  #{p['numero']}  {p['age_j']} j  {_court(p['titre'], 90)}"
               for p in r["vos_prs"]]
    lignes.append(f"\nGrains ({len(r['grains'])}) :")
    if not r["grains"]:
        lignes.append("  Pool vide : aucune issue servable pour cette lane apres les ecarts.")
    for g in r["grains"]:
        notes = f" | notes : {' ; '.join(g['notes'])}" if g["notes"] else ""
        lignes.append(f"{g['rang']:2d}. #{g['numero']} {_court(g['titre'], 100)}\n"
                      f"    famille #{g['famille']} | priorite : "
                      f"{', '.join(g['priorite']) or 'neutre'} | derniere visite : "
                      f"{(g['derniere_visite'] or 'jamais')[:10]}{notes}\n"
                      f"    avant d'editer : {g['avant_d_editer']}")
    comptes = ", ".join(f"{code} {len(v)}" for code, v in r["ecartees"].items())
    total = sum(len(v) for v in r["ecartees"].values())
    lignes.append(f"\nEcartees sans sonde : {comptes} (total {total})")
    return "\n".join(lignes)


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Tapis rapide : tirage leger des grains (#22983).")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8)
    p.add_argument("--json", action="store_true")
    p.add_argument("--jours", type=int, default=45, help="fenetre des commits cites")
    p.add_argument("--cache-s", type=int, default=300, help="0 desactive le cache")
    p.add_argument("--graine", default=None)
    p.add_argument("--lecture", default=None, help="rejouer un dossier deja lu")
    return p


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
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}\n"
              f"Rien n'est servi. Repli : {REPLI.format(lane=args.lane)}", file=sys.stderr)
        return 3
    # Un rejeu se tire a l'instant de sa lecture : memes ages de claims, meme graine.
    maintenant = maintenant or (args.lecture and _dt(lecture.lu_a)) or datetime.now(UTC)
    tous = etats(lecture, args.lane, maintenant, args.jours)
    graine = args.graine or graine_defaut(args.lane, maintenant)
    file = ordonner(tous, args.lane, maintenant, args.grains, graine)
    r = rapport(lecture, tous, file, args.lane, maintenant, graine)
    source = f"dossier {args.lecture}" if args.lecture else "GitHub + origin/main local"
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else texte(r, source)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
