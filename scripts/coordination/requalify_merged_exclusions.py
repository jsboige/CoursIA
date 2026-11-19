#!/usr/bin/env python3
"""Requalification des exclusions MERGEE du tapis -- banc de replay (#27242).

Le tapis ecarte une issue ouverte lorsque la surface ``PR MERGEE`` la cite :
l'issue est alors lue comme livree, et le pool ne la rend plus. Cette surface
est **aveugle au fil** : une issue dont la PR ne livre qu'une TRANCHE garde un
critere restant, et l'ecart la retire du pool alors qu'elle est alive -- c'est
le probleme mesure de la famine du tapis (37 issues sur 87 ecartees « MERGEE »
etaient vivantes).

Ce module refait la qualification **sur le fil complet** et rend cinq
verdicts, distincts :

  ``livre``       une PR MERGEE porte la **cloture** de l'issue : la livraison
                  est complete, l'ecart MERGEE est **legitime** ;
  ``a_clore``     les PRs MERGEE n'ont livre qu'une **TRANCHE** (marqueur
                  partiel) et rien ne reste dans le fil : le travail est fait,
                  la **cloture administrative** reste a faire (coordinateur) ;
  ``requalifiee`` l'issue est **vivante** : soit une PR en vol la cite, soit
                  le fil annonce apres le merge qu'un critere reste, soit
                  aucune PR MERGEE ne la livre (mention contextuelle) ;
  ``servable``    requalifiee ET le fil nomme une **action** executable : une
                  lane peut la prendre maintenant ;
  ``refusee``     l'ecart est legitime pour une raison **structurelle** :
                  EPIC, conteneur, ou claim vivant d'une autre lane.

Deux compteurs, donc : **requalifiees** (les issues dont l'ecart MERGEE etait
faux et qui redeviennent des grains de production) et **servables** (actionnable
maintenant). Le second est strictement inclus dans le premier. Les ``a_clore``
sont comptees a part : l'action qui reste est une cloture, pas une production.

La semantique de livraison (cloture vs tranche) **n'est pas reecrite** : elle
est appelee sur l'organe deja present (`candidate_delivered.closing_marker` /
`delivery_marker`), tout comme la detection des PRs citees
(`timeline_facts` + `_with_pr_bodies`).

Trois garde-fous, tous mesures :

1. **Un commentaire seul ne suffit jamais.** La preuve d'un reste doit etre
   **posterieure au merge** de la PR MERGEE qui cite l'issue : une phrase de
   travail restant ecrite *avant* le merge decrit la tranche, pas un residu.
   Le corps de l'issue n'est **pas** une preuve non plus : ses cases a cocher
   restent vides apres une livraison (mesure : #27213 livre par #27226, corps
   `- [ ]` x3 a 10 h apres la livraison).
2. **Une issue n'est servable que si une action est nommee** : la preuve doit
   porter un marqueur d'action ET une cible concrete (`#N`, un script). Une
   issue qui dit « reste du travail » sans dire lequel n'est pas servable.
3. **Une PR en vol exclut la servabilite** (pas la vie) : une autre lane
   travaille deja dessus.

Le banc rejoue un **corpus fige** (`--frozen`) : meme corpus, memes verdicts,
reproductible, et chaque refus porte son motif. C'est la suite independante
du merge demandee par le coordinateur (#27242) -- sans toucher au branchement
de production.

Usage :
    python scripts/coordination/requalify_merged_exclusions.py \
        --frozen scripts/tests/fixtures/requalification/corpus.json --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

#: `scripts/` dans le chemin : l'organe de la semantique de livraison
#: (`candidate_delivered`) vit a la racine de `scripts/`, pas dans le
#: paquet `coordination`.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

#: La grammaire des marqueurs du harnais -- **appelee**, pas reecrite
#: (revue du 19/11 : la copie locale derivait de la vraie).
from coordination import tapis_marqueurs  # noqa: E402

DEPO = "jsboige/CoursIA"

#: Un reste annonce. Le mot seul ne suffit pas : il est **conjonctionne** a un
#: mot de contexte (le mot seul sort partout, y compris dans un bilan).
REQUI = re.compile(
    r"\b(reste|restent|restant|restera|non couvert|pas encore|tranche suivante|"
    r"en attente|a faire|a refaire|non fait|non realise)\b", re.IGNORECASE)
#: Le contexte : un reste **de quoi**. Sans lui, la phrase est un constat.
CONTEXTE = re.compile(
    r"(crit[eè]re|criteres?|tranche|travail|livraison|lecture|fil\b|tapis|"
    r"qualification|mesure|organe|script|corpus|bascule|plan\b|transition)", re.IGNORECASE)
#: Une action nommee.
ACTION = re.compile(
    r"\b(bascule|basculer|tranche|livrer|livre|creer|créer|ouvrir|rejouer|"
    r"brancher|cabler|câbler|mesurer|relever|corriger|completer|compléter|"
    r"refaire|passer|qualifier|qualification|servir)\b", re.IGNORECASE)
#: Une cible concrete : un numero ou un script.
CIBLE = re.compile(r"(#\d+)|([\w./-]{3,}\.py\b)|(scripts/)")

#: Les marqueurs de claim du harnais : **une seule grammaire**, celle de
#: `coordination.tapis_marqueurs` (appelee, jamais reecrite). La version
#: locale du module ne connaissait que `(DELIVERED|RELEASED)` comme levee et
#: ignorait la decoration toleree par `check_lane_claim.py` : un claim leve
#: par `[CANCELLED]`, `[ABANDONED]` ou `[DONE]` y restait compte **vivant**,
#: et l'issue partait en `refusee` a tort (revue du 19/11).
CLAIM = tapis_marqueurs.OUVRE
LEVE = tapis_marqueurs.FERME


def phrases(texte: str) -> list[str]:
    """Decoupe un texte en phrases porteuses de sens."""
    parts = re.split(r"(?<=[.!?])\s+|\n+|\s*;\s+", texte or "")
    return [p.strip() for p in parts if p and p.strip()]


def _iso(texte: str) -> datetime:
    return datetime.fromisoformat((texte or "").replace("Z", "+00:00"))


def preuves_reste_fenetre(texte: str) -> list[tuple[str, list[str]]]:
    """Les phrases qui annoncent un reste, avec leur **fenetre +- 1 phrase**.

    Conjonction obligatoire : un marqueur de reste **et** un mot de contexte.
    La fenetre accompagne la phrase parce que la cible concrete peut etre
    ecrite dans la phrase voisine : sur #27223 l'action nommee et la cible
    (`#27225`) sont dans deux phrases distinctes du meme etat mesure.
    """
    ps = phrases(texte)
    return [(p, ps[max(0, i - 1): i + 2]) for i, p in enumerate(ps)
            if REQUI.search(p) and CONTEXTE.search(p)]


def preuves_reste(texte: str) -> list[str]:
    """Les phrases qui annoncent un reste, dans l'ordre du texte."""
    return [p for p, _ in preuves_reste_fenetre(texte)]


def preuve_reste(texte: str) -> str | None:
    """La premiere phrase qui annonce un reste, ou ``None``."""
    trouves = preuves_reste(texte)
    return trouves[0] if trouves else None


def preuve_action(phrase: str, voisins: list[str] | None = None) -> str | None:
    """Une action nommee ET une cible concrete **dans la phrase +- voisine**.

    Revue du 19/11 (NanoClaw sur #27297) : la cible pouvait venir de
    N'IMPORTE OU dans le **corps** de l'issue -- une phrase d'action sans
    cible suffisait des que le corps contenait un `#N` ou `scripts/` dans
    une phrase sans rapport, et l'issue partait en `servable` a tort.

    La cible est desormais **dans la phrase qui porte l'action, ou dans sa
    voisine immediate** (`voisins`) : l'action et la cible sont parfois
    ecrites dans deux phrases distinctes d'un meme etat mesure (temoin
    #27223). Le mot d'action, lui, reste dans la phrase : une phrase voisine
    qui nomme une action ne rend pas la phrase actionnable.
    """
    if not ACTION.search(phrase):
        return None
    if CIBLE.search(phrase):
        return phrase
    for v in voisins or []:
        if CIBLE.search(v):
            return phrase
    return None


def claim_vivant(apres_merge: list[dict]) -> str | None:
    """La lane d'un claim **vivant** (pose, jamais leve) apres le merge.

    La grammaire est celle du harnais (`coordination.tapis_marqueurs`) :
    un claim ferme par `[RELEASED]`, `[DELIVERED]`, `[CANCELLED]`,
    `[ABANDONED]` ou `[DONE]` n'est plus vivant, et la decoration toleree
    par `check_lane_claim.py` (puces, gras, indentation) est acceptee. La
    copie locale du module ne connaissait que `(DELIVERED|RELEASED)` : un
    claim leve par `[CANCELLED]` y restait compte vivant -> `refusee`
    fausse (revue du 19/11).
    """
    vivant: str | None = None
    for e in tapis_marqueurs.evenements(apres_merge):
        if e.marque == "OVERRIDE":
            vivant = None
        elif e.marque in CLAIM:
            vivant = e.lane or "lane inconnue"
        elif e.marque in LEVE:
            if vivant is None or e.lane is None or e.lane == vivant:
                vivant = None
    return vivant


def _marqueurs() -> tuple:
    """Les deux predicats de livraison de l'organe deja present.

    ``candidate_delivered`` sait dire si une PR MERGEE **clot** une issue
    (`Closes`/`Fixes`/`Resolves`) ou si elle n'en livre qu'une **tranche**
    (`See`/`Part of`/`Refs`). Cette semantique n'est **pas reproduite** ici :
    elle estappelee (predicats purs, aucun appel reseau).
    """
    from candidate_delivered import closing_marker, delivery_marker  # noqa: E402
    return closing_marker, delivery_marker


def classer(cas: dict) -> dict:
    """Verdict d'un cas (issue + PR MERGEE + fil complet). Pure.

    **Precedence assumee** (revue du 19/11, point « a trancher ») : une
    phrase de reste **posterieure** au merge prime le marqueur de
    **cloture**. Consequence : ``livre`` n'est atteignable que si aucune
    phrase de reste ne subsiste dans le fil apres le merge -- le fil recent
    parle plus fort que la PR MERGEE. Le choix est **documente**, pas subi.
    """
    numero = cas.get("number")
    titre = cas.get("title") or ""
    labels = [str(l).upper() for l in (cas.get("labels") or [])]

    # 1 -- refus structurels.
    if "EPIC" in titre.upper() or "EPIC" in labels:
        return _v(numero, "refusee", "EPIC : une racine reste ouverte par construction")
    if re.search(r"\[Audit #\d+\]", titre):
        return _v(numero, "refusee", "conteneur : une PR ne livre qu'une partition")

    merged = list(cas.get("merged_refs") or [])
    if not merged:
        return _v(numero, "hors_perimetre", "aucune PR MERGEE ne cite l'issue")
    merge = max(merged, key=lambda r: r.get("merged_at") or "")
    merge_at = merge.get("merged_at") or ""
    apres = [c for c in (cas.get("comments") or [])
             if (c.get("created_at") or "") > merge_at]

    # 2 -- claim vivant d'une autre lane : l'ecart est structurel.
    lane = claim_vivant(apres)
    if lane:
        return _v(numero, "refusee", "claim vivant de la lane {}".format(lane))

    # 3 -- la livraison de la PR MERGEE : **cloture** ou simple **tranche** ?
    # C'est la semantique de `candidate_delivered`, appelee et non reecrite.
    closing_marker, delivery_marker = _marqueurs()
    cloture = [r for r in merged if closing_marker(r.get("body") or "", numero)]
    tranche = [r for r in merged if delivery_marker(r.get("body") or "", numero)]

    # 4 -- le fil annonce-t-il un reste APRES le merge ?
    # Une phrase qui annonce un reste ET une action est preferee : la preuve
    # retenue doit etre celle qui **nome le travail restant** (mesure : le
    # fil de #27223 porte d'abord « critere de cloture NON couvert » -- un
    # constat -- puis « restent dues la bascule du tapis par defaut ... » --
    # l'action ; c'est la seconde qui rend l'issue servable). Chaque phrase
    # est accompagnee de sa fenetre +- 1 phrase : la cible peut legitimement
    # se trouver dans la phrase voisine (revue du 19/11).
    candidats: list[tuple[str, list[str]]] = []
    for c in apres:
        candidats.extend(preuves_reste_fenetre(c.get("body") or ""))
    reste = None
    fenetre = None
    for p, v in candidats:
        if preuve_action(p, v):
            reste, fenetre = p, v
            break
    if reste is None and candidats:
        reste, fenetre = candidats[0]
    action = preuve_action(reste, fenetre) if reste else None

    # 5 -- PR en vol citant l'issue : vivante, mais pas servable.
    en_vol = [p for p in (cas.get("prs_ouverts") or [])]
    if en_vol:
        motif = "PR en vol citant l'issue : {}".format(
            ", ".join("#{}".format(p) for p in en_vol[:3]))
        return _v(numero, "requalifiee", motif, reste)
    if reste:
        if action:
            return _v(numero, "servable", "reste nomme et action concrete", reste)
        return _v(numero, "requalifiee", "reste annonce sans action concrete", reste)
    if cloture:
        return _v(numero, "livre", "une PR MERGEE porte la cloture de l'issue", reste)
    if tranche:
        return _v(numero, "a_clore",
                  "les PRs MERGEE n'ont livre qu'une TRANCHE (marqueur partiel) et "
                  "rien ne reste dans le fil : la cloture administrative reste a faire",
                  reste)
    return _v(numero, "requalifiee",
              "aucune PR MERGEE ne livre l'issue (mention contextuelle) : l'ecart "
              "MERGEE etait faux", reste)


def _v(numero, verdict: str, motif: str, preuve: str | None = None) -> dict:
    return {"issue": numero, "verdict": verdict, "motif": motif, "preuve": preuve}


def rejouer(cas: list[dict]) -> dict:
    """Rejoue un corpus. Rendu : compteurs, refus, duree, cas."""
    t0 = time.monotonic()
    verdicts = [classer(c) for c in cas]
    duree = time.monotonic() - t0
    compteurs: dict[str, int] = {}
    for v in verdicts:
        compteurs[v["verdict"]] = compteurs.get(v["verdict"], 0) + 1
    refus: dict[str, int] = {}
    for v in verdicts:
        refus[v["motif"]] = refus.get(v["motif"], 0) + 1
    # Deux compteurs demandes : les issues **requalifiees** (l'ecart MERGEE
    # etait faux : elles redeviennent des grains de production) et celles
    # **reellement servables** (une lane peut les prendre maintenant).
    # Les `a_clore` sont comptees a part : l'ecart MERGEE y etait faux aussi,
    # mais l'action qui reste est une **cloture administrative** -- le
    # travail de production est fait (coordinateur / adjoint).
    requalifiees = compteurs.get("requalifiee", 0) + compteurs.get("servable", 0)
    return {
        "corpus": len(cas),
        "compteurs": compteurs,
        "requalifiees": requalifiees,
        "servables": compteurs.get("servable", 0),
        "a_clore": compteurs.get("a_clore", 0),
        "ecart_mergee_faux": requalifiees + compteurs.get("a_clore", 0),
        "duree_s": round(duree, 3),
        "refus": refus,
        "cas": verdicts,
    }


def corpus_live(numeros: list[int]) -> list[dict]:
    """Construit un cas depuis GitHub (lecture seule) : issue + fil + PRs.

    Les PRs sont vues par les **organes deja presents** : la timeline et les
    corps de PR par `candidate_delivered` (`timeline_facts` +
    `_with_pr_bodies`), l'issue et ses commentaires par `gh_snapshot`
    (`fetch_issue`, `fetch_issue_comments`). Aucun second lecteur.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from candidate_delivered import (  # noqa: E402
        LABEL_DEFAULT, _with_pr_bodies, timeline_facts)
    from coordination import gh_snapshot  # noqa: E402

    cache: dict[int, tuple[str, str]] = {}
    cas = []
    for n in numeros:
        it = gh_snapshot.fetch_issue(DEPO, n) or {}
        cmts = gh_snapshot.fetch_issue_comments(DEPO, n) or []
        refs, _ = timeline_facts(DEPO, n, LABEL_DEFAULT)
        refs = _with_pr_bodies(DEPO, refs, cache)
        merged, ouverts = [], []
        for r in refs:
            if not r.get("is_pr"):
                continue
            corps = {"pr": r.get("pr_number"), "merged_at": r.get("merged_at"),
                     "body": r.get("body") or "", "title": r.get("title") or ""}
            if r.get("merged_at"):
                merged.append(corps)
            elif r.get("state") == "open":
                ouverts.append(r.get("pr_number"))
        cas.append({
            "number": n,
            "title": it.get("title") or "",
            "labels": [l.get("name") for l in (it.get("labels") or [])],
            "body": it.get("body") or "",
            "merged_refs": merged,
            "prs_ouverts": sorted(set(ouverts)),
            "comments": [{"created_at": c.get("createdAt") or c.get("created_at") or "",
                          "author": (c.get("author") or {}).get("login")
                          or (c.get("user") or {}).get("login") or "",
                          "body": c.get("body") or ""} for c in cmts],
        })
    return cas


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--frozen", help="corpus fige (JSON) a rejouer")
    ap.add_argument("--live", nargs="*", type=int, default=None,
                    help="numeros d'issues a relire en direct")
    ap.add_argument("--sortie", help="ecrire le corpus live dans ce fichier")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)

    if args.live:
        cas = corpus_live(args.live)
        if args.sortie:
            Path(args.sortie).write_text(
                json.dumps(cas, ensure_ascii=False, indent=1), encoding="utf-8")
    elif args.frozen:
        cas = json.loads(Path(args.frozen).read_text(encoding="utf-8"))
    else:
        ap.error("--frozen FICHIER ou --live N... ")

    rapport = rejouer(cas)
    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
    else:
        for v in rapport["cas"]:
            print("#{:<7} {:<12} {}".format(v["issue"], v["verdict"], v["motif"]))
            if v.get("preuve"):
                print("          preuve : {}".format(v["preuve"][:160]))
        print("compteurs: {} (requalifiees={}, servables={}, {} s)".format(
            rapport["compteurs"], rapport["requalifiees"], rapport["servables"],
            rapport["duree_s"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
