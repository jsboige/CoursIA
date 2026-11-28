#!/usr/bin/env python3
"""La fenetre SERVIE de la voie leger : cap de livraisons, qualification, rapport.

Ce module est **extrait** de `coordination.tapis_leger` pour tenir le plafond de
lignes de ce module (meme geste que l'extraction de `tapis_leger_texte`) : la fin
du tirage -- le cap de livraisons, la **qualification de la fenetre** et le
rapport -- y vit desormais.

**La qualification precede le service** (dispatch `c0030` du coordinateur,
24/11) : la lane ne recoit que des grains **CONFIRMES** sur leur FIL COMPLET.
Mesure du 24/11 sur la fenetre reelle d'une lane (24 candidats) : la
qualification ecarte **16 des 24** (RELACHE, RECLAMEE, GEL, LIVREE, PLAFOND,
EPAISSE) et n'en confirme que **8** -- la file rendue sans elle etait servie a
deux tiers de grains que la qualification refusait ensuite. Un refus porte son
code et son motif ; un grain **non qualifie** n'est PAS servi (fail-CLOSED :
une decision qui n'a pas pu etre prise refuse le grain).

**Une file confirmee VIDE n'est pas un service** (revue du 24/11) : quand la
qualification ne confirme aucun grain — le mur atteint avant tout verdict, ou
une fenetre entierement refusee — le **repli chronologique** prend le relais,
comme le fait le cap de livraisons. Les grains **non qualifies** restent
DECLARES dans le rapport ; aucun n'est servi en silence.

**La lecture du cap est resserree sur la machine de la lane** (#28884) : le
cap compte les livraisons de la lane dans les PR fusionnees sur 7 jours, et
la recherche GitHub ne lui rend que les corps qui citent sa machine -- le
filtre Python du cap reste seul juge. Mesure du 27/11 : 931 PR et 4,4 Mo lus
en 9,5 s pour en retenir 3 de la lane.
"""
from __future__ import annotations

import sys
import time
from datetime import datetime
from pathlib import Path

from coordination import (gh_bulk, gh_prs_cache, tapis_cap_livraisons,
                          tapis_leger_rapport, tapis_repli)
from coordination import tapis_qualification as tq

#: Le mur PROPRE de la qualification : il borne la LECTURE DES FILS quand
#: l'appelant ne donne aucune echeance (appel direct). Au point d'entree, la
#: qualification partage la part du tirage (I6 de #28114) -- lecture du pool,
#: cap, qualification et repli -- et le temps du repli y est reserve.
MUR_QUALIFICATION_S = 60

#: Le TEMPS DU REPLI est RESERVE (reserve du coordinateur, I6 de #28114,
#: 25/11) : le repli chronologique lit le cache local et publie le rapport --
#: il doit avoir la place meme quand la qualification a consomme le budget.
#: La qualification s'arrete donc a `echeance - RESERVE_REPLI_S`.
RESERVE_REPLI_S = 5

#: La part minimale laissee a la QUALIFICATION par le cap de livraisons : le
#: cap est fail-OPEN (une mesure perdue n'ecarte rien), la qualification est
#: fail-CLOSED (un grain non qualifie n'est pas servi) -- le premier ne prend
#: donc pas la part du second (#28884).
RESERVE_QUALIFICATION_S = 10


def qualifier(file: list, lane: str, maintenant: datetime, jours: int,
              prs: list[dict], run,
              echeance: float | None = None) -> tuple[list, dict, Exception | None]:
    """Qualifie la fenetre servie sur le FIL COMPLET de chaque grain.

    Rend `(file_confirmee, qualif, erreur)`. L'erreur n'est pas un verdict :
    elle rend la main au repli chronologique -- une qualification en panne ne
    sert **jamais** une file non qualifiee.

    `echeance` est celle du **point d'entree** (monotone, I6 de #28114) : la
    qualification ne repart pas d'une horloge neuve, elle partage le budget
    de la commande, et le temps du REPLI y est reserve. Sans echeance (appel
    direct), le mur propre de la qualification s'applique.
    """
    debut = time.monotonic()
    nums = [e.numero for e in file]
    # L'ECHEANCE est celle du point d'entree, MOINS le temps du repli : un
    # etage qui a consomme sa part voit l'etage suivant etre COUPE plutot
    # qu'attendu (fail-CLOSED : une decision non prise ne sert rien).
    fin = (echeance - RESERVE_REPLI_S if echeance is not None
           else debut + MUR_QUALIFICATION_S)
    try:
        servis, ecartees, illisibles, arrete, appels, chrono = tq.qualifier(
            nums, lane, maintenant, jours, prs, run,
            fin, debut=debut)
    except Exception as exc:  # noqa: BLE001 - une qualification en panne ne sert rien
        return file, {}, exc
    confirmes = {e.numero for e in servis}
    qualif = {
        "candidats": len(nums), "servis": len(confirmes),
        "ecartees": [{"numero": n, "code": v.get("code"), "motif": v.get("motif")}
                     for n, v in sorted(ecartees.items())],
        "illisibles": list(illisibles),
        "non_qualifies": [n for n in nums
                          if n not in confirmes and n not in ecartees],
        "appels": appels, "secondes": chrono.get("secondes"),
        "premier_servable_s": chrono.get("premier_servable_s"),
        "budget_epuise": bool(arrete),
    }
    return [e for e in file if e.numero in confirmes], qualif, None


#: Le RAPPORT est canonique dans `tapis_leger_rapport` (extraction du 22/11,
#: #28090 + #27223) : c'est la que vit l'**occupation** de l'urne. Cette PR
#: y ajoute la **qualification de la fenetre servie** (#28114) -- l'alias garde
#: un seul objet pour les deux voies d'appel (`tapis_leger._rapport`, ici).
rapport = tapis_leger_rapport.rapport


def lanceur_cap_resserre(run_commande, lane: str):
    """Le lanceur de la commande, la lecture du cap resserree sur la machine de la lane.

    Le cap ne compte que les livraisons de la LANE : la recherche GitHub rend
    plus petit le corpus qu'il lit, en ne demandant que les corps qui citent
    sa machine. Le meme ensemble de PR de la lane, en 2,2 a 2,7 s au lieu de
    9,5 s sur les trois tranches (27/11, #28884) : le cout etait celui du
    volume de corps lus, pas celui du nombre d'appels.

    Une PR comptee par le cap porte le nom de la machine dans son tag
    `Grain:`. Si la recherche derivait, le cap sous-compterait -- dans le
    sens fail-OPEN : il ecarterait moins, jamais un grain a tort.

    Sans lanceur (`None` : le cap lit par `subprocess`) ou sans `--search`
    dans l'argv, le lanceur passe tel quel.
    """
    if run_commande is None:
        return None
    machine = lane.split(":", 1)[0]

    def lancer(argv, timeout):
        argv = list(argv)
        if "--search" in argv:
            pos = argv.index("--search") + 1
            argv[pos] = f'{argv[pos]} "{machine}" in:body'
        return run_commande(argv, timeout)

    return lancer


def passer_et_replir(file: list, ordre: list, lane: str, maintenant: datetime,
                     prs_ouvertes: list[dict] | None, run=None,
                     repli=None, pool_ouvert: bool = False,
                     echeance: float | None = None, run_commande=None):
    """Le cap, puis -- s'il a VIDE la file -- le repli qui rend la main.

    Le cap de livraisons est la derniere etape de la selection : quand il
    ecarte tous les items, la file sort VIDE et la lane ne recoit RIEN --
    l'invariant I1 ("une file sans fin") est rompu par les filtres eux-memes.
    La voie chronologique prend alors le relais : le cache local rend une
    file, servie par date de creation.

    `repli` : l'appelable de repli, **injecte** (le module du repli importe
    celui-ci : l'injection evite l'import circulaire). `pool_ouvert` : le
    pool porte-t-il des candidats ? Sans candidat, il n'y a rien a servir.

    `run` : le FETTEUR du cap, au contrat `(since, until) -> list[dict]`.
    `None` : le cap lit le reseau par son propre organe, avec le `run` de la
    commande (`run_commande`) comme lanceur, resserre sur la machine de la
    lane (`lanceur_cap_resserre`), sous l'`echeance` partagee.

    Rend `(file, temoins, mesure, rendu)` : `rendu` est le `(rapport, code)`
    du repli quand il a rendu la main, `None` sinon.

    Le module `tapis_cap_livraisons` porte le CAP ; la glue cap-puis-repli
    vit ici, avec la fenetre servie -- meme geste que l'extraction du
    RAPPORT (`tapis_leger_rapport`) : le plafond de lignes du module du cap
    ne bouge pas.
    """
    file, temoins, mesure = tapis_cap_livraisons.passer(
        file, ordre, lane, maintenant, prs_ouvertes, run=run,
        echeance=echeance, run_commande=lanceur_cap_resserre(run_commande, lane))
    if file or not pool_ouvert or repli is None:
        return file, temoins, mesure, None
    try:
        return file, temoins, mesure, repli()
    except gh_bulk.LectureIncomplete:
        return file, temoins, mesure, None  # pas de cache local : file vide


def servir(classe: dict, file: list, fenetre: dict, origami: dict, lane: str,
           grains: int, maintenant: datetime, jours: int, graine: str,
           depot: Path, run, phases: dict, secondes: float,
           budget_s: float,
           echeance: float | None = None) -> tuple[dict, int]:
    """Le cap de livraisons, la qualification, puis le rapport de la fenetre.

    Trois temps dans l'ordre : le CAP ecarte les livraisons d'EPIC trop
    recentes (fail-OPEN), la QUALIFICATION confirme chaque grain sur son fil
    complet, et le RAPPORT publie les refus -- une exclusion n'est jamais
    silencieuse.
    """
    # Le tirage **publie** la liste de PRs qu'il vient de payer : la
    # qualification, qui vient apres et sur le meme contenu, la relit dans le
    # cache partage au lieu de payer la meme pagination une seconde fois
    # (#29027). Le tirage garde sa lecture fraiche -- il n'est jamais servi
    # une liste plus ancienne que celle qu'il lit lui-meme.
    gh_prs_cache.publier_prs(classe["prs"])
    # Le CAP lit le reseau par son PROPRE organe : son contrat de fetteur
    # (`(since, until) -> list[dict]`) n'est pas celui de la commande
    # (`(argv, timeout) -> str`) ; l'adaptation se fait dans le module du cap,
    # au point de contact, en passant par l'argument du fetteur.
    # Le cap cede le budget restant a la qualification et au repli ; si la
    # lecture du pool l'a deja consomme, cette reserve ne peut etre garantie.
    fin_cap = (echeance - RESERVE_REPLI_S - RESERVE_QUALIFICATION_S
               if echeance is not None else None)
    file, temoins_cap, cap_mesure, rendu = passer_et_replir(
        file, classe["grains"] + classe["conteneurs"], lane, maintenant,
        classe["prs"], run=None, run_commande=run, echeance=fin_cap,
        pool_ouvert=bool(classe["grains"]),
        repli=lambda: tapis_repli.replir(lane, grains, maintenant, jours, graine,
                                         depot, echeance=echeance))
    if rendu is not None:
        return rendu
    file, qualif, erreur = qualifier(file, lane, maintenant, jours,
                                     classe["prs"], run, echeance=echeance)
    if erreur is not None:
        print(f"Qualification en echec ({erreur}) : repli chronologique.",
              file=sys.stderr)
        try:
            return tapis_repli.replir(lane, grains, maintenant, jours, graine, depot)
        except gh_bulk.LectureIncomplete as exc:
            raise gh_bulk.LectureIncomplete(exc.lecture, exc.page,
                                            f"qualification : {erreur} ; repli : {exc.cause}") from exc
    if not file:
        # Une file CONFIRMEE VIDE n'est pas un service : la lane s'eteint
        # (mandat #28114, « file sans fin par lane »). Deux causes, un meme
        # geste : le mur atteint avant tout verdict, ou une fenetre
        # entierement refusee (mesure du 24/11 : 16 des 24 candidats refuses,
        # pour une marge de 3 -- elle est mince). Le repli chronologique prend
        # le relais, comme le fait le cap de livraisons ; les grains NON
        # QUALIFIES restent DECLARES dans le rapport, jamais servis en
        # silence (fail-CLOSED).
        try:
            r, code = tapis_repli.replir(lane, grains, maintenant, jours, graine,
                                         depot, echeance=echeance)
        except gh_bulk.LectureIncomplete as exc:
            cause = ("budget de qualification epuise" if qualif.get("budget_epuise")
                     else "aucun grain confirme par la qualification")
            raise gh_bulk.LectureIncomplete(exc.lecture, exc.page,
                                            f"{cause} ; repli : {exc.cause}") from exc
        q = dict(r.get("qualification") or {})
        q.update(qualif or {})
        q["repli"] = ("file confirmee vide : repli chronologique")
        r["qualification"] = q
        return r, code
    r = rapport(lane, graine, maintenant, classe["metas"],
                phases["selection_s"], secondes, budget_s, classe["etats"],
                file, classe["prs"], origami, phases, fenetre,
                occupation=classe.get("occupation"), qualif=qualif)
    r["cap_livraisons"] = {"mesure": cap_mesure, "ecartes": temoins_cap,
                           "fenetre_j": tapis_cap_livraisons.FENETRE_J}
    return r, 0


def texte_fenetre(fen: dict) -> list[str]:
    """Les lignes de la fenetre : selection par age, blocs, non-visites."""
    lignes = []
    if fen.get("ordre") == "age":
        seuil = (fen.get("age") or {}).get("seuil_h", 72)
        lignes.append(f"Selection par AGE (mandat du 22/11) : les issues "
                      f"anciennes d'abord ; une issue de moins de {seuil} h "
                      f"va en fin de file ; "
                      f"{(fen.get('age') or {}).get('exclus', 0)} issue(s) "
                      f"deja servie(s) en attente de verdict, laisses de cote.")
    if fen.get("blocs", 1) > 1:
        lignes.append(f"Fenetre : bloc {fen['bloc']}/{fen['blocs']} du pool classe "
                      f"(taille {fen['taille']}) -- la fenetre avance d'un bloc par "
                      f"tranche de 4 h : le pool entier est couvert en "
                      f"{fen['blocs']} tranches.")
    non_visites = fen.get("non_visites") or []
    if non_visites:
        apercu = ", ".join(f"#{n}" for n in non_visites[:12])
        suite = " ..." if len(non_visites) > 12 else ""
        lignes.append(f"Fenetre : {len(non_visites)} numero(s) du pool non visite(s) "
                      f"a cette tranche -- delai max de requalification "
                      f"{fen.get('delai_max_h')} h : {apercu}{suite}.")
    elif fen.get("delai_max_h"):
        lignes.append(f"Fenetre : pool entier visite -- delai max de "
                      f"requalification {fen.get('delai_max_h')} h.")
    return lignes


def texte_qualification(q: dict) -> list[str]:
    """Les lignes de la qualification : mesure, refus (code + motif), non qualifies."""
    lignes = [f"\nQualification : {q['organe']} -- {q['quand']} ; {q['ecarts']}."]
    if q.get("candidats") is not None:
        lignes.append(f"Qualification de la fenetre servie : {q['candidats']} candidat(s) "
                      f"-> {q['servis']} confirme(s) sur le fil complet "
                      f"({q.get('appels')} appel(s), {q.get('secondes')} s"
                      + (", budget epuise" if q.get("budget_epuise") else "") + ").")
    for e in q.get("ecartees") or []:
        lignes.append(f"  #{e['numero']}  ecarte -- {e['code']} : {e['motif']}")
    if q.get("non_qualifies"):
        apercu = ", ".join(f"#{n}" for n in q["non_qualifies"][:12])
        suite = " ..." if len(q["non_qualifies"]) > 12 else ""
        lignes.append(f"  {len(q['non_qualifies'])} grain(s) non qualifies (mur) : "
                      f"{apercu}{suite} -- ils reviendront au tour suivant.")
    if q.get("repli"):
        lignes.append(f"  {q['repli']} -- la file confirmee etait vide ; "
                      f"la file servie vient du repli chronologique.")
    return lignes
