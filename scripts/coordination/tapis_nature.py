#!/usr/bin/env python3
"""La NATURE d'un grain : worker, harnais, parapluie.

Decidee sur les **metadonnees seules** (titre + labels) : la voie legere ne
lit ni corps ni fil, et le tapis doit decider de la tete du tirage sur ce
qu'il a deja lu. Aucune lecture reseau de plus, aucun cout de temps ajoute.

Trois classes :

- **parapluie** : la graine d'une FAMILLE. Elle ne se sert pas elle-meme --
  une lane y prend un SOUS-GRAIN. Deux cas :

  1. le conteneur **declare** : label `epic`/`umbrella`, titre `[EPIC...]` ;
  2. la **racine de famille** d'une consolidation : l'issue porte le label
     `consolidation` ET un AUTRE titre declare son numero comme racine
     (`[ICT #20298] G4 -- ...`, `Fix(tooling,#16231): ...`). La voie legere
     ne lit pas les corps, donc elle ne voit pas `Part of #N` : elle lit les
     TITRES, qui portent la meme declaration.

  Effet mesure (24/11, pool de 489 issues ouvertes, lecture reelle) : les
  **huit** premiers grains du tirage d'une lane worker etaient **huit**
  issues de consolidation. La priorite de consolidation etait une priorite
  TOTALE : elle passait devant la bande d'age ET devant la regle « jamais
  visitee », donc la tete du tirage etait une famille, pas des grains. Apres
  la correction, la tete du tirage worker est une suite de **sous-grains**
  (#27170, #28195, #28305, #28306 -- des enfants de #17417 et #20298), et
  les racines de famille passent dans le slot des conteneurs.

  La priorite de consolidation, elle, reste : un sous-grain de famille
  (une feuille) la garde, et l'invariant I7 (« la consolidation passe devant
  l'anciennete ») tient toujours -- une issue de consolidation **seule** dans
  le pool n'a personne qui la declare racine : c'est une feuille.

- **harnais** : le travail de COORDINATION ou de HARNAIS. Ce n'est pas un
  grain de worker : les labels `harnais` et `coordination` l'ecartent de la
  tete d'une lane **worker**. Les lanes qui **gerent** l'urne (coordinateur,
  adjoint, secretaire) le gardent : pour elles, c'est une information, pas
  une exclusion.

- **worker** : le reste.
"""
from __future__ import annotations

import re

#: Les labels qui ecarte un grain de harnais pour une lane worker.
LABELS_HARNAIS = ("harnais", "coordination")

#: La marque du grain de harnais, et le code d'ecart qui la dit a la
#: qualification (comme `OCCUPEE`).
MARQUE_HARNAIS = "harnais"
CODE_HARNAIS = "HARNAIS"

#: Le label d'une racine de famille (une consolidation de famille).
LABEL_CONSOLIDATION = "consolidation"

#: Les labels d'un conteneur declare.
LABELS_CONTENEUR = frozenset({"epic", "umbrella"})

#: Un crochet de TETE qui porte un numero : le parent declare par le titre.
_BRACKET_RE = re.compile(r"^\s*\[[^\]]*?#(\d+)[^\]]*\]")

#: Un crochet de TETE `[EPIC #N] ...` : le crochet porte l'EPIC ET son numero.
_EPIC_RE = re.compile(r"^\s*\[\s*epic\b[^\]]{0,40}?#(\d+)", re.IGNORECASE)

#: Un numero cite entre parentheses : la forme du SCOPE (`Fix(tooling,#N)`).
_PAREN_RE = re.compile(r"\(([^)]*?#(\d+)[^)]*)\)")


def parent_de_titre(titre: str, numero: int | None = None) -> int | None:
    """Le parent de famille declare par le TITRE, ou None.

    Seul un crochet de TETE compte : `[ICT #20298] G4`, `[#20250 phase 3]`,
    `[EPIC #18605 - Pli 3]`. Un crochet sans numero (`[GameTheory]`) ne
    declare rien ; un numero qui est l'issue elle-meme ne declare rien non
    plus.

    La forme entre parentheses (`Fix(tooling,#16231)`) ne declare PAS le
    parent : elle porte le scope du travail, qui designe souvent une autre
    issue (`(paire avec G1 #26864)`).
    """
    m = _BRACKET_RE.match(titre or "")
    if not m:
        return None
    n = int(m.group(1))
    return None if (numero is not None and n == numero) else n


def racines_declarees(metas: list[dict]) -> set[int]:
    """Les numeros qu'un AUTRE titre declare comme RACINE de famille.

    Une passe sur les titres de toutes les issues ouvertes -- la voie legere
    les a deja lus. Deux formes :

    - le crochet de tete (`[ICT #20298] G4`) ;
    - la parenthese du scope (`Fix(tooling,#16231): ...`).

    Le numero d'une issue ne se declare pas **elle-meme** : c'est le seul
    cas ecarte. Une racine qui est elle-meme dans le pool reste une racine --
    c'est justement elle que les sous-grains nomment.
    """
    racines: set[int] = set()
    for it in metas:
        n = int(it["number"])
        titre = it.get("title") or ""
        if m := _BRACKET_RE.match(titre):
            if int(m.group(1)) != n:
                racines.add(int(m.group(1)))
        for mm in _PAREN_RE.finditer(titre):
            p = int(mm.group(2))
            if p != n:
                racines.add(p)
    return racines


def est_conteneur_declare(titre: str, labels: list[str]) -> bool:
    """Le conteneur DECLARE : label `epic`/`umbrella`, ou titre `[EPIC...]`.

    Meme regle que `tapis_rapide._conteneur_de` -- la VOIE LEGERE ne peut
    pas la redire, elle la reprend (une regle dupliquee derive).
    """
    poses = {lab.strip().lower() for lab in labels}
    if poses & LABELS_CONTENEUR:
        return True
    t = (titre or "").lstrip(" [")
    return t.upper().startswith("EPIC") and not _EPIC_RE.match(titre or "")


def est_parapluie(titre: str, labels: list[str], numero: int | None = None,
                  racines: set[int] | None = None) -> bool:
    """La graine est-elle un PARAPLUIE (une racine de famille) ?

    Deux cas :

    1. le conteneur **declare** (label `epic`/`umbrella`, titre `[EPIC...]`) ;
    2. la **racine d'une consolidation** : le label `consolidation` et un
       autre titre declare son numero -- la famille se sert par ses
       sous-grains.

    Le cas 2 demande les RACINES DECLAREES (une passe sur les titres) : sans
    elles, toute consolidation serait une racine, et une consolidation seule
    dans le pool -- une FEUILLE -- perdrait sa priorite (invariant I7).
    """
    if est_conteneur_declare(titre, labels):
        return True
    poses = {lab.strip().lower() for lab in labels}
    return (LABEL_CONSOLIDATION in poses and numero is not None
            and numero in (racines or set()))


def est_harnais(labels: list[str]) -> bool:
    """Le grain est-il de HARNAIS ou de COORDINATION ?

    Les labels `harnais` et `coordination` : la donnee, posee par une main,
    visible dans GitHub. Une lane worker rend la main ; les lanes qui
    gerent l'urne le gardent.
    """
    poses = {lab.strip().lower() for lab in labels}
    return any(lab in poses for lab in LABELS_HARNAIS)


def marques_harnais(metas: list[dict]) -> dict[int, str]:
    """Les issues de **HARNAIS ou de COORDINATION** : `{numero: "harnais"}`.

    Ce ne sont pas des grains de worker : le travail de coordination et le
    travail de harnais appartiennent aux lanes qui **gerent** l'urne. Pour
    elles, la marque est une information (le `resume`) ; pour une lane
    worker, c'est une exclusion (le grain n'est pas servi).
    """
    marques: dict[int, str] = {}
    for it in metas:
        if est_harnais([str(l) for l in (it.get("labels") or [])]):
            marques[int(it["number"])] = MARQUE_HARNAIS
    return marques


def motif_harnais() -> str:
    """Le motif lisible de la marque de harnais."""
    return ("label harnais/coordination : grain de harnais ou de "
            "coordination -- ce n'est pas un grain de worker ; les lanes "
            "qui gerent l'urne le gardent")


def code_de(marque: str) -> str:
    """Le code d'ecart d'une marque d'occupation."""
    return CODE_HARNAIS if marque == MARQUE_HARNAIS else "OCCUPEE"
