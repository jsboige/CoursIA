#!/usr/bin/env python3
"""L'OCCUPATION d'un grain : l'urne de cloture, la PR qui le tient, et le
grain de harnais.

Trois classes, trois marques, une seule decision :

- **`urne`** -- l'issue porte le label `candidate-delivered` : elle est
  RESERVEE au coordinateur et a l'adjoint (#15069). Une lane worker la
  verifie sur l'artefact et rend la main ; elle ne la sert pas comme un
  grain neuf.
- **`occupee:#PR`** -- une PR **ouverte d'une autre lane** cite l'issue : le
  travail est en cours ailleurs. La servir a une autre lane creerait la
  collision L898 (deux lanes sur les memes fichiers).
- **`harnais`** -- l'issue porte le label `harnais` ou `coordination` : c'est
  du travail de harnais ou de coordination, pas un grain de worker
  (dispatch `c0035b`).

Les trois se decident sur des **metadonnees seules** -- les labels de la
lecture de selection et la liste des PRs ouvertes, que le tirage lit deja.
Aucun appel reseau supplementaire, aucun cout de temps ajoute.

Le meme module sert les **deux portes** : la rotation (le tirage, qui
propose) et la requalification (la prise en charge, qui engage). Les deux
rendent le meme verdict sur la meme question -- sinon la lane paie un cycle
pour decouvrir que l'organe de claim refuse le grain qu'on lui a servi.

**Une exclusion n'est jamais silencieuse** : le motif est rendu, avec le
numero de la PR qui occupe. L'issue n'est pas fermee -- elle reste dans le
pool ; seule sa place dans la tete change. Le rendu est **plafonne**
(`RENDU_MAX`) : au-dela, le compte est rendu, la liste complete reste dans
la sortie JSON. Le rendu lui-meme vit dans `tapis_occupation_rapport`
(extraction du 24/11).

Les lanes qui **gerent** l'urne (coordinateur, adjoint, secretaire) ne
perdent aucun grain : elles recoivent une section **courte** (`resume`),
qui dit ce qui est a l'urne, ce qui est occupe et ce qui est du harnais.
"""
from __future__ import annotations

import re

from coordination import tapis_nature, tapis_occupation_rapport

#: Le label d'urne : il route l'issue vers la cloture, il ne la livre pas.
LABEL_URNE = "candidate-delivered"

#: Les trois lanes qui **gerent** l'urne et l'occupation : le coordinateur
#: (`myia-ai-01:CoursIA`), l'adjoint (`myia-po-2025:CoursIA-2`) et le
#: secretaire (`myia-po-2028:CoursIA-3`), qui **ferme** l'urne (Q167 b).
#: Pour elles, les trois classes sont une information, pas une exclusion :
#: elles arbitrent, elles ne perdent pas une opportunite de travail.
LANES_PRIVILEGIEES = frozenset({"myia-ai-01:CoursIA", "myia-po-2025:CoursIA-2",
                                "myia-po-2028:CoursIA-3"})

#: Le code d'ecart de l'occupation (la qualification) : il rejoint les codes
#: des neuf regles, qui sont tous des exclusions.
CODE_OCCUPEE = "OCCUPEE"

#: Le rendu des exclusions est plafonne (le rendu lui-meme vit dans
#: `tapis_occupation_rapport`, extraction du 24/11).
RENDU_MAX = tapis_occupation_rapport.RENDU_MAX

#: La note d'urne : le label route l'issue, il ne prouve pas la livraison.
NOTE_URNE = ("label candidate-delivered : urne de cloture (coordinateur, adjoint, "
             "secretaire) -- signal, pas preuve : verifie l'artefact, puis rends "
             "la main")

#: Une reference **qui compte** : la forme sure de cloture de `git-workflow.md`
#: (le mot de cloture precede immediatement le numero) -- ou le numero porte
#: par le tag `Grain:`, qui nomme le grain servi.
_CLOSE_RE = re.compile(r"(?i)\b(?:closes|fixes|resolves)\s+#(\d+)\b")
_GRAIN_RE = re.compile(r"(?im)^[ \t>*]*Grain:.*$")
_CITE_RE = re.compile(r"#(\d+)\b")
_LANE_RE = re.compile(r"\blane\s+([A-Za-z0-9._-]+:[A-Za-z0-9._-]+)")

#: Le rendu des exclusions et la section courte vivent dans le module
#: extrait ; les alias gardent les appelants intacts.
rendre_exclus = tapis_occupation_rapport.rendre_exclus
resume = tapis_occupation_rapport.resume


def privilege(lane: str) -> bool:
    """La lane gerante l'urne et l'occupation (coordinateur, adjoint)."""
    return (lane or "") in LANES_PRIVILEGIEES


def lane_de_pr(pr: dict) -> str | None:
    """La lane d'une PR : la premiere mention `lane <m:w>` de son corps.

    Le login est partage (`jsboige` pour toutes les lanes) : l'auteur ne dit
    rien, seul le tag `lane` le fait. Une PR sans tag n'est attribuable a
    personne -- elle est donc traitee comme celle d'une autre lane.
    """
    for texte in (pr.get("body") or "", pr.get("title") or ""):
        if m := _LANE_RE.search(texte):
            return m.group(1).rstrip(".")
    return None


def refs_legitimes(texte: str) -> set[int]:
    """Les numeros d'issue qu'une PR **tient** reellement.

    Seules deux formes comptent :

    - la forme sure de `git-workflow.md` — le mot de cloture precede
      immediatement le numero (`Closes #N`, `Fixes #N`, `Resolves #N`) ;
    - le numero porte par le tag `Grain:` de la premiere ligne, qui nomme le
      grain que la PR sert.

    Les references **structurelles** ne comptent pas : `Part of #N`,
    `Refs #N` et `See #N` designent un parent, un contexte ou une issue
    partagee. Les compter marquait l'umbrella `OCCUPEE` pour toute la
    flotte (mesure du 22/11, sur le corps de #28096 : `Part of #24823`).

    Le numero du tag `Grain:` est aujourd'hui le numero de la PR
    **precedente** (`prev:`) : PR et issues partagent un compteur, donc il
    ne designe jamais une issue ouverte -- aucun grain du pool n'en
    souffre. La regle reste explicite pour le jour ou le tag portera le
    numero du grain servi.
    """
    refs = {int(m.group(1)) for m in _CLOSE_RE.finditer(texte)}
    for ligne in _GRAIN_RE.findall(texte):
        refs |= {int(x) for x in _CITE_RE.findall(ligne)}
    return refs


def prs_par_issue(prs: list[dict]) -> dict[int, list[dict]]:
    """Les PRs ouvertes, indexees par le numero d'issue qu'elles tiennent."""
    index: dict[int, list[dict]] = {}
    for pr in prs:
        texte = f"{pr.get('title') or ''}\n{pr.get('body') or ''}"
        for num in refs_legitimes(texte):
            index.setdefault(num, []).append(pr)
    return index


def marques_pr(prs_ou_index, lane: str) -> dict[int, str]:
    """Les issues **occupees** par une PR ouverte d'une autre lane.

    `{numero: "occupee:#28054"}`. La PR de la lane elle-meme n'occupe pas :
    c'est elle qui doit porter sa propre issue au merge (P0).
    """
    index = (prs_ou_index if isinstance(prs_ou_index, dict)
             else prs_par_issue(prs_ou_index))
    marques: dict[int, str] = {}
    for num, prs in index.items():
        autres = [pr for pr in prs if lane_de_pr(pr) != lane]
        if not autres:
            continue
        pr = sorted(autres, key=lambda p: p.get("number") or 0)[0]
        marques[num] = f"occupee:#{pr.get('number')}"
    return marques


def marques_urne(metas: list[dict]) -> dict[int, str]:
    """Les issues **a l'urne** : le label `candidate-delivered`."""
    marques: dict[int, str] = {}
    for it in metas:
        labs = [str(l) for l in (it.get("labels") or [])]
        if any(l.strip().lower() == LABEL_URNE for l in labs):
            marques[int(it["number"])] = "urne"
    return marques


def marques_harnais(metas: list[dict]) -> dict[int, str]:
    """Les issues de **HARNAIS ou de COORDINATION** : `{numero: "harnais"}`."""
    return tapis_nature.marques_harnais(metas)


def marques(metas: list[dict], prs: list[dict], lane: str) -> dict[int, str]:
    """Les trois classes, sur les metadonnees seules.

    L'urne l'emporte : c'est la classe la plus dure (une issue livree, dont
    la cloture appartient au coordinateur).
    """
    m = marques_pr(prs, lane)
    m.update(marques_urne(metas))
    m.update(marques_harnais(metas))
    return m


def marques_issues(issues: dict[int, dict], prs_par_issue_: dict[int, list[dict]],
                   lane: str) -> dict[int, str]:
    """Les memes marques, sur les issues **lues** (la qualification)."""
    metas = [{"number": n, "labels": list(it.get("labels") or [])}
             for n, it in issues.items()]
    m = marques_pr(prs_par_issue_, lane)
    m.update(marques_urne(metas))
    return m


def retirer(grains: list, conteneurs: list, occupation: dict[int, str],
            lane: str) -> tuple[list, list, list[dict]]:
    """Retire du tirage les issues occupees ou a l'urne.

    Rend `(grains, conteneurs, exclus)`. Les exclus sont **affiches** (numero
    + marque + motif) : une exclusion silencieuse serait un grain perdu. Une
    lane privilegiee ne perd rien : elle voit les marques sans perdre la tete.
    """
    if privilege(lane) or not occupation:
        return grains, conteneurs, []
    exclus: list[dict] = []

    def _filtre(items: list) -> list:
        restes = []
        for e in items:
            marque = occupation.get(e.numero)
            if marque is None:
                restes.append(e)
            else:
                exclus.append({"numero": e.numero, "marque": marque,
                               "motif": motif(marque)})
        return restes

    return _filtre(grains), _filtre(conteneurs), exclus


def retirer_harnais(grains: list, conteneurs: list, metas: list[dict],
                    lane: str) -> tuple[list, list]:
    """Retire les grains de **HARNAIS** pour une lane worker.

    Le repli sert le MEME pool que la voie legere : il ecarte donc les
    memes grains. Fail-OPEN : si l'exclusion vide le pool, le pool reste
    -- un tirage qui ne sert rien ne sert a rien (I1).
    """
    if not metas:
        return grains, conteneurs
    g2, c2, _exclus = retirer(grains, conteneurs,
                              tapis_nature.marques_harnais(metas), lane)
    return (g2, c2) if g2 or not grains else (grains, conteneurs)


def motif(marque: str) -> str:
    """Le motif lisible d'une marque d'occupation."""
    if marque == "urne":
        return ("label candidate-delivered : urne de cloture reservee au "
                "coordinateur, a l'adjoint et au secretaire (#15069) -- la lane "
                "worker rend la main")
    if marque == tapis_nature.MARQUE_HARNAIS:
        return tapis_nature.motif_harnais()
    if marque.startswith("occupee:#"):
        return (f"PR ouverte {marque.split(':', 1)[1]} d'une autre lane la "
                "cite : l'issue est occupee (collision L898 evitee)")
    return marque


def urne_en_note(issues: dict[int, dict], lane: str = "") -> dict[int, str]:
    """Retire le label d'urne du chemin de la decision ; rend sa note.

    Le label ne prouve pas la livraison : il ne doit donc pas ecarter le grain
    dans la requalification. Il reste dit -- en note, sur le grain servi.

    **Sauf pour une lane worker** : l'urne est reservee au coordinateur et a
    l'adjoint (#15069) ; le label reste alors sur le chemin de la decision --
    l'ecart `LABEL` des neuf regles retire le grain, avec son motif.
    """
    if lane and not privilege(lane):
        return {}
    notes: dict[int, str] = {}
    for n, it in issues.items():
        labs = [str(l) for l in (it.get("labels") or [])]
        reste = [l for l in labs if l.strip().lower() != LABEL_URNE]
        if len(reste) != len(labs):
            it["labels"] = reste
            notes[n] = NOTE_URNE
    return notes


def exclure(etats: list, occupation: dict[int, str], lane: str) -> list:
    """Porte la meme decision a la requalification (la prise en charge).

    Un grain occupe porte un **ecart** : il n'est pas servi. L'urne, elle,
    passe par l'ecart `LABEL` des neuf regles -- le label n'est pas retire
    du chemin de la decision pour une lane worker (cf. `tapis_preuves`).

    La note qui explique l'exclusion reste affichee : l'exclusion n'est
    jamais silencieuse.
    """
    if privilege(lane) or not occupation:
        return etats
    for e in etats:
        marque = occupation.get(e.numero)
        if marque is None or marque == "urne" or e.ecart is not None:
            continue
        e.ecart = tapis_nature.code_de(marque)
        e.motif = motif(marque)
        e.notes.append(e.motif)
    return etats
