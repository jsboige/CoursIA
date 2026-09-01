#!/usr/bin/env python3
"""Un EPIC qui alimente une serie declare-t-il sa regle d'arret et son pendant
de consolidation ?

Le dernier chantier ouvert de #13420, dans les mots du user (2026-08-28) :

    « si un Epic alimente une serie comme MGS, il faut qu'il soit capable de
    creer autant des issues de renumerotations et consolidations de Notebooks
    [...] que d'issues qui rajoutent un nouveau numero. Mais la aussi c'est en
    partie la redaction des Epic »

Le picker sait deja MESURER la parite d'une zone (`series_saturation.zone_balance`)
et REFUSER un grain d'expansion dans une zone sans remede (`pick_idle_grain.
admissibility`). Ce qui manquait : la parite n'etait une contrainte qu'au
TIRAGE. Un EPIC pouvait continuer d'engendrer de l'expansion pure, et le refus
n'arrivait qu'a la consommation -- une fois les issues ecrites, c'est-a-dire
trop tard pour la seule personne qui pouvait les ecrire autrement.

Cet organe deplace la question a la SOURCE : l'EPIC lui-meme.

DEUX JAMBES, DE FORCE TRES INEGALE -- et c'est delibere.

  Jambe A (MESURE, forte) : parite des filles par polarite. On compte les
    issues qui declarent servir cet EPIC, on les classe par `polarity()`, et un
    EPIC a >= EXPANSION_MIN filles d'expansion pour ZERO fille de consolidation
    est en defaut. C'est un fait verifiable, pas une lecture de prose.

  Jambe B (REDACTION, faible, ADVISORY) : l'EPIC declare-t-il une regle
    d'arret ? Cette jambe repose sur un jeu de motifs, et un jeu de motifs
    ecrit a la main SOUS-COMPTE en silence (lecon inscrite dans
    anti-regression.md : un motif se valide par ses faux negatifs, pas par ses
    hits). Elle ne peut donc pas bloquer -- elle SIGNALE. Ses motifs sont
    couverts par des controles positifs dans scripts/tests/test_epic_charter.py :
    chaque forme acceptee y est ecrite, et le test echoue si l'une cesse
    d'etre reconnue.

La jambe A est ce sur quoi on peut agir ; la jambe B est ce qui rappelle au
redacteur ce qu'il s'apprete a oublier.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from series_saturation import (  # noqa: E402
    CONSOLIDATION,
    EXPANSION,
    family_from_text,
    fetch_series_visits,
    parent_issue,
    polarity,
)

REPO = "jsboige/CoursIA"

# Nombre de filles d'expansion a partir duquel l'absence totale de
# consolidation devient un defaut. Trois, et non deux : deux instances peuvent
# etre une paire legitime (un jumeau FR/EN, un twin Infer/PyMC) ; a trois on
# est dans une serie, et une serie sans pendant de consolidation est
# exactement le motif MGS que #13420 a ouvert.
EXPANSION_MIN = 3

# Jambe B. Formes sous lesquelles une regle d'arret s'ecrit reellement en
# francais dans ce depot. Chacune est couverte par un controle positif dans
# les tests : si une forme cesse d'etre reconnue, le test rougit -- c'est la
# seule protection contre le sous-comptage silencieux d'un jeu de motifs.
# Les deux apostrophes sont acceptees. Mesure du 2026-08-29 : 2 des 52
# EPICs ouverts ecrivent deja leur corps avec l'apostrophe typographique.
# Aucune regle d'arret n'etait ratee ce jour-la -- mais la forme est vivante
# dans le corpus, et un motif absent ne leve pas d'erreur : il rend un
# chiffre plus petit et plus propre.
_STOP_RE = re.compile(
    r"r[eeè]gle\s+d[e'’]\s*arr[eeê]t"
    r"|crit[eeè]re\s+d[e'’]\s*arr[eeê]t"
    r"|condition\s+d[e'’]\s*arr[eeê]t"
    r"|r[eeè]gle\s+de\s+sortie"
    r"|crit[eeè]re\s+de\s+sortie"
    r"|stopping\s+rule"
    r"|exit\s+criteri(?:on|a)"
    r"|quand\s+s[e'’]\s*arr[eeê]te"
    r"|cet\s+epic\s+s[e'’]\s*arr[eeê]te"
    r"|arr[eeê]t\s*:"
    r"|borne\s*:"
    r"|plafond\s*:",
    re.I,
)

# Jambe B, second volet : l'EPIC annonce-t-il son pendant de consolidation ?
_CONSO_PLEDGE_RE = re.compile(
    r"consolidation"
    r"|renum[eeé]rotation"
    r"|renum[eeé]roter"
    r"|fusion(?:ner)?\s+(?:les?\s+)?notebooks"
    r"|regroup(?:er|ement)"
    r"|sous-s[eeé]rie",
    re.I,
)

_EPIC_TITLE_RE = re.compile(r"^\s*\[?\s*epic\s*\]?\s*[:\-]?", re.I)


def _gh_json(args):
    out = subprocess.run(["gh", *args], capture_output=True, text=True,
                         encoding="utf-8", errors="replace")
    if out.returncode != 0:
        raise RuntimeError((out.stderr or "").strip()[:300])
    return json.loads(out.stdout or "null")


def _labels(issue):
    raw = issue.get("labels") or []
    return [x.get("name", x) if isinstance(x, dict) else x for x in raw]


def is_epic(issue) -> bool:
    """Un EPIC se declare par son titre ou par une etiquette."""
    labels = {str(x).lower() for x in _labels(issue)}
    if labels & {"epic", "umbrella", "ombrelle"}:
        return True
    return bool(_EPIC_TITLE_RE.match(issue.get("title") or ""))


def fetch_issues(limit: int = 2500, state: str = "all"):
    """Le recensement porte sur TOUS les etats, et ce n'est pas un detail.

    Compter les seules filles OUVERTES mesure la file d'attente restante, pas
    ce que l'EPIC a ENGENDRE -- or c'est l'engendrement que le mandat
    interroge. Les issues d'expansion de #13420 ont ete consommees et fermees
    en 2,3 jours de mediane : c'est precisement la plainte. Mesure du
    2026-08-29 : #12373 (MGS) compte **6** filles ouvertes et **14** tous
    etats confondus. Un organe qui n'aurait vu que les 6 aurait rendu un
    verdict rassurant sur l'EPIC meme qui a motive #13420.
    """
    return _gh_json([
        "issue", "list", "-R", REPO, "--state", state, "--limit", str(limit),
        "--json", "number,title,body,labels,createdAt,updatedAt,state",
    ])


def children_of(epic_number: int, pool):
    """Issues qui DECLARENT servir cet EPIC, tous etats confondus.

    On reutilise `parent_issue` -- la meme extraction d'ascendance que le
    picker. Un second extracteur divergerait, et c'est precisement le defaut
    que #13435 a corrige ailleurs.
    """
    return [it for it in pool
            if parent_issue(it.get("body") or "") == epic_number]


def audit_epic(epic, pool, families=(), expansion_min: int = EXPANSION_MIN):
    kids = children_of(epic["number"], pool)
    by_pol = {EXPANSION: [], CONSOLIDATION: [], "neutral": []}
    for k in kids:
        pol = polarity(k.get("title") or "", k.get("body") or "")
        by_pol.setdefault(pol, []).append(k["number"])
    open_kids = sum(1 for k in kids if (k.get("state") or "").upper() == "OPEN")

    body = epic.get("body") or ""
    text = (epic.get("title") or "") + "\n" + body
    zone = family_from_text(text, families) if families else None

    exp = by_pol[EXPANSION]
    con = by_pol[CONSOLIDATION]
    feeds_series = len(exp) >= 1

    defects = []
    # Aucune fille DECLAREE : l'organe n'a rien mesure. Un EPIC peut tres bien
    # engendrer des issues qui ne declarent pas leur ascendance -- `parent_issue`
    # exige une forme explicite ("Enfant de #N", "EPIC #N"). Rendre `OK` dans ce
    # cas ferait passer une absence de mesure pour une absence de defaut, et
    # c'est le vert le plus dangereux qu'un garde puisse produire.
    if not kids:
        return {
            "number": epic["number"],
            "title": (epic.get("title") or "")[:90],
            "zone": zone,
            "children": 0,
            "open_children": 0,
            "expansion": [],
            "consolidation": [],
            "neutral": [],
            "feeds_series": False,
            "measured": False,
            "defects": [],
            "verdict": "NON-MESURE",
        }

    # Jambe A -- mesure.
    if len(exp) >= expansion_min and not con:
        defects.append("PARITE-ABSENTE")
    # Jambe B -- redaction. Ne se pose QUE sur un EPIC qui alimente
    # effectivement une serie : exiger une regle d'arret d'un EPIC qui
    # n'engendre rien serait du bruit.
    # Deux surfaces et non `body` seul : une regle d'arret ecrite UNIQUEMENT dans
    # le titre ("EPIC X -- s'arrete a 12 notebooks") passerait inapercue si on
    # ne lisait que le corps. La jambe etant advisory, la consequence serait un
    # signal manque et jamais un faux gate -- ce qui est precisement la raison
    # de corriger : un faux negatif ne se plaint pas, il rend un chiffre plus
    # propre. Concern 2 de la review NanoClaw sur #13539.
    #
    # `_CONSO_PLEDGE_RE` reste volontairement sur le corps seul : un engagement
    # de consolidation est une clause, pas un intitule -- l'elargir au titre
    # ajouterait de la surface sans forme attestee derriere.
    _title = epic.get("title") or ""
    if feeds_series and not (_STOP_RE.search(body) or _STOP_RE.search(_title)):
        defects.append("ARRET-NON-DECLARE")
    if len(exp) >= expansion_min and not _CONSO_PLEDGE_RE.search(body):
        defects.append("PENDANT-NON-DECLARE")

    return {
        "number": epic["number"],
        "title": (epic.get("title") or "")[:90],
        "zone": zone,
        "children": len(kids),
        "open_children": open_kids,
        "expansion": sorted(exp),
        "consolidation": sorted(con),
        "neutral": sorted(by_pol["neutral"]),
        "feeds_series": feeds_series,
        "measured": True,
        "defects": defects,
        "verdict": "OK" if not defects else "/".join(defects),
    }


def _render(rows, zone_err):
    if zone_err:
        print("(zones NON MESUREES : {} -- la colonne zone reste vide. Les "
              "jambes A et B restent valides : elles ne dependent pas des "
              "zones.)".format(zone_err))
        print()
    bad = [r for r in rows if r["defects"]]
    unmeasured = [r for r in rows if not r.get("measured")]
    print("EPICs ouverts : {}   mesures : {}   en defaut : {}   "
          "non mesures : {}".format(len(rows), len(rows) - len(unmeasured),
                                    len(bad), len(unmeasured)))
    print("  (NON-MESURE = aucune fille ne DECLARE cette ascendance. Ce n'est "
          "pas un satisfecit :")
    print("   l'organe n'a rien pu compter. Pour rendre un EPIC mesurable, ses "
          "filles doivent")
    print("   porter 'Enfant de #N' ou 'EPIC #N' dans leur corps.)")
    print()
    if not rows:
        print("Aucun EPIC ouvert trouve.")
        return
    for r in sorted(rows, key=lambda d: (not d["defects"], not d.get("measured"),
                                         -len(d["expansion"]))):
        flag = "DEF " if r["defects"] else ("OK  " if r.get("measured") else "--  ")
        print("{}#{:<6d} {}".format(flag, r["number"], r["title"]))
        if not r.get("measured"):
            print("       NON-MESURE : aucune fille declaree")
            print()
            continue
        line = ("       filles {:>2d} ({} ouvertes)  |  expansion {:>2d}  "
                "consolidation {:>2d}  neutre {:>2d}").format(
            r["children"], r.get("open_children", 0), len(r["expansion"]),
            len(r["consolidation"]), len(r["neutral"]))
        if r["zone"]:
            line += "  |  zone {}".format(r["zone"])
        print(line)
        if r["defects"]:
            print("       -> {}".format(r["verdict"]))
            if "PARITE-ABSENTE" in r["defects"]:
                shown = ", ".join("#" + str(n) for n in r["expansion"][:6])
                more = ", ..." if len(r["expansion"]) > 6 else ""
                print("          {} filles d'expansion ({}{}) et AUCUNE de "
                      "consolidation.".format(len(r["expansion"]), shown, more))
                print("          Remede : ouvrir dans cet EPIC un grain de "
                      "consolidation (renumerotation, fusion, mise en "
                      "sous-serie) avant la prochaine issue d'expansion.")
            if "ARRET-NON-DECLARE" in r["defects"]:
                print("          Le corps ne declare aucune regle d'arret. "
                      "Ecrire a quelle condition cet EPIC cesse d'engendrer "
                      "des filles (ADVISORY : jeu de motifs, peut sous-compter).")
            if "PENDANT-NON-DECLARE" in r["defects"]:
                print("          Le corps n'annonce aucun pendant de "
                      "consolidation (ADVISORY, meme reserve).")
        print()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("epic", nargs="?", type=int, default=None,
                    help="numero d'un EPIC ; sans argument, tous les EPICs "
                         "ouverts sont examines")
    ap.add_argument("--audit", action="store_true",
                    help="examiner tous les EPICs ouverts (defaut sans argument)")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--limit", type=int, default=2500,
                    help="plafond de la requete de recensement (defaut 2500 ; "
                         "`gh issue list` plafonne a 30 en SILENCE sans lui)")
    ap.add_argument("--expansion-min", type=int, default=EXPANSION_MIN,
                    help="seuil de la jambe A (defaut {})".format(EXPANSION_MIN))
    args = ap.parse_args()

    try:
        census = fetch_issues(args.limit)
    except RuntimeError as exc:
        print("recensement illisible : {}".format(exc), file=sys.stderr)
        return 2

    # Le plafond doit etre CONSTATE, pas espere : une troncature silencieuse
    # ferait disparaitre des filles et rendrait des paritees faussement saines.
    if len(census) >= args.limit:
        print("ATTENTION : le recensement a rendu exactement --limit ({}) "
              "issues -- il est probablement TRONQUE, et des filles peuvent "
              "manquer. Relancer avec --limit plus haut avant de croire une "
              "parite saine.".format(args.limit), file=sys.stderr)

    zones, _i2f, zone_err = fetch_series_visits()
    families = tuple(zones.keys())

    open_pool = [x for x in census if (x.get("state") or "").upper() == "OPEN"]

    if args.epic is not None:
        hit = next((x for x in census if x["number"] == args.epic), None)
        if hit is None:
            print("#{} : absente du recensement (au-dela de --limit {}).".format(
                args.epic, args.limit))
            return 2
        rows = [audit_epic(hit, census, families, args.expansion_min)]
    else:
        rows = [audit_epic(e, census, families, args.expansion_min)
                for e in open_pool if is_epic(e)]

    if args.json:
        print(json.dumps({
            "epics": rows,
            "expansion_min": args.expansion_min,
            "zones_measured": zone_err is None,
            "zones_error": zone_err,
            "defective": [r["number"] for r in rows if r["defects"]],
        }, indent=2, ensure_ascii=False))
    else:
        _render(rows, zone_err)

    # Jambe A seule decide du code de sortie : la jambe B est advisory, et un
    # jeu de motifs qui sous-compte ne doit jamais faire rougir un gate.
    hard = [r for r in rows if "PARITE-ABSENTE" in r["defects"]]
    return 1 if hard else 0


if __name__ == "__main__":
    sys.exit(main())
