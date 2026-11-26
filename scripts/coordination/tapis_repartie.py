#!/usr/bin/env python3
"""La livraison REPARTIE : plusieurs PR livrent chacune une tranche (#24461).

Defaut mesure (25/11, #24461) : quand une issue est livree par PLUSIEURS PR,
chacune bornee par sa clause `paths:`, la preuve par le diff ne confronte que
le DERNIER `[DELIVERED]` a l'attribution de l'issue. Ce marqueur ne porte
qu'une tranche : l'ecart LIVREE est leve, et l'issue attestee livree repart
dans la rotation (3 grains sur 24 servis avec une attestation vivante).

**L'agregat n'ecarte rien par lui-meme.** Il n'intervient que sur un ecart
LIVREE que la regle legere a DEJA pose (dernier commentaire : une
attestation de livraison vivante, ou une livraison epic-wide), et APRES la
voie unique : si son dernier marqueur couvre l'attribution (`tapis_diff`),
rien n'est reecrit. Sinon l'UNION des livraisons prouvees, chacune par le
diff de sa PR, est confrontee a l'attribution. L'agregat peut TENIR un ecart
que la voie unique leverait, jamais en lever un qu'elle garde : un grain sans
attestation, livre par une seule PR, ou dont un claim global est mele a des
claims bornes, garde la lecture de la voie unique.

**Ce que la preuve etablit.** Comme la voie unique, elle etablit qu'un
PERIMETRE est couvre : chaque chemin que l'issue attribue a ete livre par une
PR integree. Les criteres d'acceptation de l'issue ne se lisent pas dans un
diff : c'est l'attestation de la lane qui les affirme, le diff qui la
contredit ou la laisse.

Quatre garde-fous, tous fail-CLOSED :

1. **Fil complet seulement.** L'ecart LIVREE se decide sur un fil prouve
   complet : la fenetre quand `tapis_fenetre.suffit` la dit entiere, sinon le
   fil relu par `tapis_fil_complet.confirmer`. Une fenetre partielle peut
   cacher une attribution plus large (un claim plus ancien qu'elle) : sur
   LIVREE elle ne sonde rien et ne decide rien, la voie unique comprise.
2. **Perimetre declare d'abord.** L'union des perimetres declares doit
   couvrir l'attribution AVANT toute lecture de PR par l'agregat :
   attribution inconnue, globale, melee d'un claim sans clause `paths:`, ou
   en glob -- il ne sonde rien (la voie unique a deja lu la sienne).
3. **Une revocation desarme ce qui la precede.** Seules comptent les
   livraisons posterieures a la derniere retractation (`[NOT-DELIVERED]`,
   `[INFO] candidate-delivered-revoked`).
4. **Borne de sondes.** Les `LIVRAISONS_MAX` PR les plus recentes sont lues,
   de la plus recente a la plus ancienne, arret des que l'attribution est
   couverte ; la borne est dite quand elle arrete la lecture.
"""
from __future__ import annotations

import functools
import sys
from dataclasses import replace
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import delivery_grammar
from coordination import tapis_diff, tapis_fenetre
from coordination.tapis_diff import COUVRE, TRANCHE, perimetre, pr_designee, verdict
from coordination.tapis_marqueurs import OUVRE, _JAMAIS, _dt, evenements
from coordination.tapis_perimetre import attribution, couvert_par

#: Les PR les plus recentes lues au plus, par issue.
LIVRAISONS_MAX = 4


def _ligne(livre) -> str:
    """Le marqueur de livraison reconstruit, comme `tapis_diff` le lit."""
    return f"[{livre.marque}] {livre.reste}"


def _nums(livres: list) -> str:
    return ", ".join(f"PR #{pr_designee(_ligne(l))}" for l in livres)


def _fusion(nouveau, ancien) -> str:
    """Le marqueur d'une PR livree deux fois : l'union de ses deux clauses,
    sous forme canonique (une clause ecrite `PATHS :`, ou precedee d'une prose
    contenant `paths:`, n'offre pas de point de coupe fiable)."""
    per = perimetre(_ligne(ancien))
    per += [p for p in perimetre(_ligne(nouveau)) if p not in per]
    return f"PR #{pr_designee(_ligne(nouveau))} -- paths: {', '.join(per)}"


def revocation(comments: list[dict]) -> datetime:
    """L'instant de la derniere retractation du fil (jamais s'il n'y en a pas)."""
    instants = [_dt(c.get("created_at")) for c in comments
                if delivery_grammar.DELIVERED_MARKER_REVOKED_RE.search(
                    delivery_grammar.strip_code(c.get("body") or ""))]
    return max((d for d in instants if d), default=_JAMAIS)


def verifiables(comments: list[dict]) -> list:
    """Les livraisons VERIFIABLES, une par PR, de la plus recente a la plus ancienne.

    Verifiable : elle designe une PR, declare un perimetre (`[DELIVERED] ...
    PR #N -- paths: ...`), et aucune retractation ne l'a desarmee. Une PR
    livree plusieurs fois (une clause `paths:` etendue) compte pour une.
    """
    uniques: dict = {}
    borne = revocation(comments)
    for e in evenements(comments):
        ligne = _ligne(e)
        if (e.marque != "DELIVERED" or e.quand <= borne
                or not (pr_designee(ligne) and perimetre(ligne))):
            continue
        pr = pr_designee(ligne)
        uniques[pr] = e if pr not in uniques else replace(e, reste=_fusion(e, uniques[pr]))
    return sorted(uniques.values(), key=lambda e: e.quand, reverse=True)


def attribution_du_fil(comments: list[dict]) -> list[str] | None:
    """L'attribution de l'issue -- `[]` des qu'un claim est GLOBAL : sans
    clause `paths:`, un marqueur attribue l'issue entiere, seul ou mele aux
    claims bornes d'autres lanes, et un diff de chemins ne le prouve pas."""
    evts = evenements(comments)
    derniers = {e.lane: e for e in evts if e.marque in OUVRE and e.lane}
    nus = [e for e in derniers.values() if not perimetre(f"[{e.marque}] {e.reste}")]
    return [] if nus else attribution(evts)


def agreger(livres: list, attr: list[str] | None, preuve) -> tuple[str, str]:
    """(verdict, detail) de l'UNION des livraisons, chacune prouvee par le diff de sa PR.

    Meme standard que la voie unique : une livraison est prouvee si le diff de
    sa PR, integree, couvre chaque entree explicite qu'elle DECLARE, et la
    clause declaree doit couvrir l'attribution, pas seulement le diff.
    """
    if attr is None:
        return TRANCHE, "attribution inconnue (l'issue ne porte aucun marqueur d'attribution)"
    if not attr:
        return TRANCHE, "attribution globale, ou melee d'un claim sans clause `paths:`"
    lus = livres[:LIVRAISONS_MAX]
    declares = [p for livre in lus for p in perimetre(_ligne(livre))]
    manques = [a for a in attr if not couvert_par(a, declares)]
    prouvees: list = []
    for livre in lus if not manques else []:
        per = perimetre(_ligne(livre))
        etat, _ = verdict(_ligne(livre), preuve(pr_designee(_ligne(livre))), per)
        if etat != COUVRE:
            continue
        prouvees.append(livre)
        couverts = [p for l in prouvees for p in perimetre(_ligne(l))]
        if all(couvert_par(a, couverts) for a in attr):
            return COUVRE, (f"{len(prouvees)} livraisons ({_nums(prouvees)}) : leurs diffs "
                            f"couvrent le perimetre ({len(attr)})")
    if manques:
        detail = (f"{len(lus)} livraisons ({_nums(lus)}) : perimetre declare plus etroit que "
                  f"l'issue -- manque {', '.join(manques)}")
    else:
        detail = (f"{len(lus)} livraisons ({_nums(lus)}) : {len(prouvees)} prouvee(s) par "
                  f"leur diff ({_nums(prouvees) or 'aucune'}), le perimetre n'est pas couvert")
    non_lues = len(livres) - len(lus)
    if non_lues:
        detail += f" ; {non_lues} plus ancienne(s) non lue(s) (borne {LIVRAISONS_MAX})"
    return TRANCHE, detail


def decider(e, livres: list, comments: list[dict], preuve) -> str | None:
    """L'ecart LIVREE d'une livraison repartie : il tient, ou il est leve."""
    etat, detail = agreger(livres, attribution_du_fil(comments), preuve)
    if etat == COUVRE:
        e.motif = detail
        return "LIVREE"
    e.ecart, e.motif = None, ""
    e.notes.append(f"livraison repartie : {detail} -- l'issue reste dans la rotation")
    return None


def _unique_couvre(comments: list[dict], preuve) -> bool:
    """Ce que la voie unique conclurait sur ce fil : COUVRE, sans rien ecrire."""
    evts = evenements(comments)
    livres = [e for e in evts if e.marque == "DELIVERED"]
    ligne = _ligne(livres[-1]) if livres else ""
    num = pr_designee(ligne)
    if not perimetre(ligne) or not num:
        return False
    return verdict(ligne, preuve(num), attribution(evts))[0] == COUVRE


def a_agreger(comments: list[dict], preuve) -> list:
    """Les livraisons a reunir : vides quand la voie unique suffit deja."""
    livres = verifiables(comments)
    return livres if len(livres) > 1 and not _unique_couvre(comments, preuve) else []


def sur_fenetre(etats: list, lec, preuve) -> tuple[list, list]:
    """(rendus, differees) : ce que la fenetre laisse a la voie unique, et ce
    qu'elle reporte au fil complet.

    L'ecart LIVREE se decide sur un fil PROUVE complet (`tapis_fenetre.suffit`),
    par `sur_fil_complet`. Sur une fenetre PARTIELLE il ne tient que d'un fil
    tronque -- une attribution plus large peut etre cachee plus haut : il est
    differe, ni sonde ni decide. Les autres ecarts suivent la voie unique.
    """
    issues = {it["number"]: it for it in lec.issues}
    rendus, differees = [], []
    for e in etats:
        it = issues.get(e.numero) or {}
        if e.ecart != "LIVREE":
            rendus.append(e)
        elif not tapis_fenetre.suffit(it):
            differees.append(e)
        else:
            e.ecart = sur_fil_complet(e, it.get("comments") or [], e.ecart, preuve)
    return rendus, differees


def sur_fil_complet(e, comments: list[dict], code: str | None, preuve) -> str | None:
    """Decide sur un fil PROUVE complet : la voie unique, l'union si elle ne suffit pas."""
    if code != "LIVREE":
        return tapis_diff.decider(e, comments, code, preuve)
    preuve = functools.lru_cache(preuve)  # chaque PR lue une fois par decision
    livres = a_agreger(comments, preuve)
    if livres:
        return decider(e, livres, comments, preuve)
    return tapis_diff.decider(e, comments, code, preuve)
