#!/usr/bin/env python3
"""Requalification des exclusions MERGEE du tapis -- banc de replay (#27242).

Le tapis ecarte une issue ouverte lorsque la surface ``PR MERGEE`` la cite :
l'issue est alors lue comme livree, et le pool ne la rend plus. Cette surface
est **aveugle au fil** : une issue dont la PR ne livre qu'une TRANCHE garde un
critere restant, et l'ecart la retire du pool alors qu'elle est alive -- c'est
le probleme mesure de la famine du tapis (37 issues sur 87 ecartees « MERGEE »
etaient vivantes).

Ce module refait la qualification **sur le fil complet** et rend quatre
verdicts, distincts :

  ``livre``       rien ne reste apres le merge et aucune PR en vol : l'ecart
                  MERGEE est **legitime** -- l'issue reste hors du pool ;
  ``requalifiee`` l'issue est **vivante** : soit une PR en vol la cite, soit
                  le fil annonce apres le merge qu'un critere reste. L'ecart
                  MERGEE etait donc faux : elle redevient servable par le tapis ;
  ``servable``    requalifiee ET le fil nomme une **action** executable : une
                  lane peut la prendre maintenant ;
  ``refusee``     l'ecart est legitime pour une raison **structurelle** :
                  EPIC, conteneur, ou claim vivant d'une autre lane.

Deux compteurs, donc : **requalifiees** (vivantes) et **servables** (actionnable
maintenant). Le second est strictement inclus dans le premier.

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
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

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

#: Les marqueurs de claim du harnais.
CLAIM = re.compile(r"\[CLAIMED(?:-AMEND)?\]")
LEVE = re.compile(r"\[(DELIVERED|RELEASED)\]")
LANE = re.compile(r"lane\s+([\w:.-]+)")


def phrases(texte: str) -> list[str]:
    """Decoupe un texte en phrases porteuses de sens."""
    parts = re.split(r"(?<=[.!?])\s+|\n+|\s*;\s+", texte or "")
    return [p.strip() for p in parts if p and p.strip()]


def _iso(texte: str) -> datetime:
    return datetime.fromisoformat((texte or "").replace("Z", "+00:00"))


def preuves_reste(texte: str) -> list[str]:
    """Les phrases qui annoncent un reste, dans l'ordre du texte.

    Conjonction obligatoire : un marqueur de reste **et** un mot de contexte.
    """
    return [p for p in phrases(texte) if REQUI.search(p) and CONTEXTE.search(p)]


def preuve_reste(texte: str) -> str | None:
    """La premiere phrase qui annonce un reste, ou ``None``."""
    trouves = preuves_reste(texte)
    return trouves[0] if trouves else None


def preuve_action(phrase: str, corps: str) -> str | None:
    """Une action nommee ET une cible concrete, ou ``None``."""
    if not ACTION.search(phrase):
        return None
    if CIBLE.search(phrase) or CIBLE.search(corps or ""):
        return phrase
    return None


def claim_vivant(cas: dict, apres_merge: list[dict]) -> str | None:
    """La lane d'un claim **vivant** (pose, jamais leve) apres le merge."""
    vivant: str | None = None
    for c in apres_merge:
        corps = c.get("body") or ""
        if LEVE.search(corps):
            vivant = None
        elif CLAIM.search(corps):
            m = LANE.search(corps)
            vivant = m.group(1) if m else "lane inconnue"
    return vivant


def classer(cas: dict) -> dict:
    """Verdict d'un cas (issue + PR MERGEE + fil complet). Pure."""
    numero = cas.get("number")
    titre = cas.get("title") or ""
    labels = [str(l).upper() for l in (cas.get("labels") or [])]
    corps = cas.get("body") or ""

    # 1 -- refus structurels.
    if "EPIC" in titre.upper() or "EPIC" in labels:
        return _v(numero, "refusee", "EPIC : une racine reste ouverte par construction")
    if re.search(r"\[Audit #\d+\]", titre):
        return _v(numero, "refusee", "conteneur : une PR ne livre qu'une partition")

    merge = max([m for m in (cas.get("merged_refs") or [])], key=lambda r: r.get("merged_at") or "",
                default=None)
    if not merge:
        return _v(numero, "hors_perimetre", "aucune PR MERGEE ne cite l'issue")
    merge_at = merge.get("merged_at") or ""
    apres = [c for c in (cas.get("comments") or [])
             if (c.get("created_at") or "") > merge_at]

    # 2 -- claim vivant d'une autre lane : l'ecart est structurel.
    lane = claim_vivant(cas, apres)
    if lane:
        return _v(numero, "refusee", "claim vivant de la lane {}".format(lane))

    # 3 -- le fil annonce-t-il un reste APRES le merge ?
    # Une phrase qui annonce un reste ET une action est preferee : la preuve
    # retenue doit etre celle qui **nomme le travail restant** (mesure : le
    # fil de #27223 porte d'abord « critere de cloture NON couvert » -- un
    # constat -- puis « restent dues la bascule du tapis par defaut ... » --
    # l'action ; c'est la seconde qui rend l'issue servable).
    candidats: list[str] = []
    for c in apres:
        candidats.extend(preuves_reste(c.get("body") or ""))
    reste = next((p for p in candidats if preuve_action(p, corps)), None)
    if reste is None and candidats:
        reste = candidats[0]
    action = preuve_action(reste, corps) if reste else None

    # 4 -- PR en vol citant l'issue : vivante, mais pas servable.
    en_vol = [p for p in (cas.get("prs_ouverts") or [])]
    if en_vol:
        motif = "PR en vol citant l'issue : {}".format(
            ", ".join("#{}".format(p) for p in en_vol[:3]))
        return _v(numero, "requalifiee", motif, reste)
    if reste:
        if action:
            return _v(numero, "servable", "reste nomme et action concrete", reste)
        return _v(numero, "requalifiee", "reste annonce sans action concrete", reste)
    return _v(numero, "livre", "rien ne reste apres le merge du {}".format(
        merge_at), None)


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
    return {
        "corpus": len(cas),
        "compteurs": compteurs,
        "requalifiees": compteurs.get("requalifiee", 0) + compteurs.get("servable", 0),
        "servables": compteurs.get("servable", 0),
        "duree_s": round(duree, 3),
        "refus": refus,
        "cas": verdicts,
    }


def _api(chemin: str):
    out = subprocess.run(["gh", "api", "repos/{}{}".format(DEPO, chemin)],
                         capture_output=True, text=True, encoding="utf-8")
    if out.returncode:
        raise RuntimeError("gh api {}: {}".format(chemin, (out.stderr or "")[:160]))
    return json.loads(out.stdout)


def corpus_live(numeros: list[int]) -> list[dict]:
    """Construit un cas depuis GitHub (lecture seule) : issue + fil + PRs."""
    cas = []
    for n in numeros:
        it = _api("/issues/{}".format(n))
        cmts = _api("/issues/{}/comments?per_page=100".format(n))
        tl = _api("/issues/{}/timeline?per_page=100".format(n))
        merged, ouverts = [], []
        for ev in tl:
            if ev.get("event") != "cross-referenced":
                continue
            src = (ev.get("source", {}).get("issue", {}) or {})
            pr = src.get("pull_request") or {}
            m = pr.get("merged_at") or pr.get("mergedAt")
            if m:
                merged.append({"pr": src.get("number"), "merged_at": m})
            elif pr:
                ouverts.append(src.get("number"))
        cas.append({
            "number": n,
            "title": it.get("title") or "",
            "labels": [l.get("name") for l in (it.get("labels") or [])],
            "body": it.get("body") or "",
            "merged_refs": merged,
            "prs_ouverts": sorted(set(ouverts)),
            "comments": [{"created_at": c.get("created_at"),
                          "author": (c.get("user") or {}).get("login"),
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
