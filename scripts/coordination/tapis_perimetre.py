#!/usr/bin/env python3
"""Le PERIMETRE d'une livraison : ce qu'un glob certifie, et ce qu'il ne
certifie pas (revue du coordinateur, 19/11, DM
`night-27242-glob-is-not-whole-scope`).

Trois notions, separees :

1. la **VISITE** -- un marqueur de fil existe. C'est un fait de marqueur,
   sans preuve ni reseau (`coordination.tapis_marqueurs`) ;
2. l'**ATTRIBUTION** -- le perimetre que l'ISSUE porte, declare par ses
   marqueurs d'attribution (`[CLAIMED]`, `[CLAIMED-AMEND]`) ;
3. la **LIVRAISON COMPLETE** -- le diff couvre un perimetre **explicite**,
   et ce perimetre couvre l'attribution.

**Un glob ne certifie jamais la completude.** `scripts/tests/**` ne dit pas
combien de fichiers il attend : une seule modification sous ce glob ne
prouve donc pas que le perimetre est couvert. Une entree **explicite** est
couverte si le diff contient ce fichier ; une entree **en glob** est au
mieux **partielle** (au moins un fichier du diff est sous le glob), au pire
**manquante**.

**Une livraison complete mais plus etroite que l'issue ne livre pas
l'issue** : quand l'issue porte une attribution, le perimetre livre doit la
couvrir ; sinon la preuve reste une preuve de tranche.

Aucune lecture n'est reecrite : la clause `paths:` et le matcher de chemins
sont ceux de `scripts/check_lane_claim.py`, l'organe qui fait autorite sur
les claims.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_lane_claim
from coordination.tapis_marqueurs import OUVRE

#: Les caracteres qui font d'un perimetre un **glob** plutot qu'un chemin.
GLOBS = ("*", "?", "[")


def est_glob(entree: str) -> bool:
    """Vrai si l'entree de perimetre est un glob (elle ne dit pas combien
    de fichiers elle attend)."""
    return any(c in entree for c in GLOBS)


def couverture(diff: list[str], paths: list[str]) -> tuple[list[str], list[str], list[str]]:
    """(couverts, partiels, manquants) sur les entrees d'un perimetre.

    - une entree **explicite** presente dans le diff est **couverte** ;
    - une entree **en glob** touchee par au moins un fichier du diff est
      **partielle** : elle ne certifie jamais la completude ;
    - une entree que le diff n'atteint pas est **manquante**.
    """
    couverts, partiels, manquants = [], [], []
    for p in paths:
        touche = any(check_lane_claim._full_path_matches(f, p) for f in diff)
        if est_glob(p):
            (partiels if touche else manquants).append(p)
        else:
            (couverts if touche else manquants).append(p)
    return couverts, partiels, manquants


def attribution(evts) -> list[str] | None:
    """Le perimetre **attribue** de l'issue : les clauses `paths:` des
    marqueurs d'attribution (`[CLAIMED]`, `[CLAIMED-AMEND]`), la derniere
    par lane (un amend remplace le perimetre precedent).

    Trois etats, qui ne se confondent pas : `None` (aucun marqueur --
    perimetre **inconnu**), `[]` (marqueur sans `paths:` -- perimetre
    **global**, l'issue entiere), une liste non vide (perimetre
    **explicite**, que la livraison doit couvrir).
    """
    par_lane: dict[str, object] = {}
    for e in evts:
        if e.marque in OUVRE and e.lane:
            par_lane[e.lane] = e
    if not par_lane:
        return None
    per: list[str] = []
    for e in par_lane.values():
        clause = check_lane_claim._extract_paths_clause(f"[{e.marque}] {e.reste}") or []
        for p in clause:
            if p not in per:
                per.append(p)
    return per


def couvert_par(entree: str, tranche: list[str]) -> bool:
    """L'entree d'attribution est-elle couverte par le perimetre livre ?

    Une entree explicite est couverte par une tranche qui la nomme, ou par
    un glob de la tranche qui la contient. Une entree **en glob** n'est
    jamais tenue pour couverte : elle ne peut pas etre verifiee etroite
    (fail-CLOSED).
    """
    if est_glob(entree):
        return False
    for t in tranche:
        if est_glob(t):
            if check_lane_claim._full_path_matches(entree, t):
                return True
        elif t == entree:
            return True
    return False
