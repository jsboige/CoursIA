#!/usr/bin/env python3
"""Saturation par ZONE D'ATTERRISSAGE -- l'axe que le picker n'avait pas.

Contexte (#13420, mandat user 2026-08-28, cinquieme rappel sur la monoculture).

Le picker `pick_idle_grain.py` amortit deja l'affluence de flotte, mais son
compteur est indexe par **issue** (`fetch_visits`). C'est precisement ce que la
monoculture du 2026-08-22..28 a defait : l'EPIC #12373 a ete decoupe en NEUF
issues filles (une par paire d'algorithmes), donc chaque fille n'a recu que 1
ou 2 PRs et n'a subi AUCUN amortissement -- pendant que la flotte deposait sept
notebooks `MGS-2x-<Algo>-vs-Mealpy` dans le MEME repertoire.

Le compteur par issue **recompense donc le partitionnement fin** : plus une
veine est decoupee, plus elle est invisible. La zone d'atterrissage ferme ce
trapdoor parce qu'elle n'est pas partitionnable -- on peut eclater un EPIC en
cent issues, on ne peut pas eclater un repertoire.

Mesure fondatrice du 2026-08-28 (fenetre 14 j, 400 PRs mergees) :

    13 neufs / 22 PRs   MyIA.AI.Notebooks/ML/DataScienceWithAgents
     7 neufs /  9 PRs   MyIA.AI.Notebooks/GenAI/Texte
     5 neufs / 16 PRs   MyIA.AI.Notebooks/Search/Part4-Metaheuristics

Aucune de ces trois zones n'etait visible d'aucun garde. La premiere n'avait
ete nommee par personne.

Usage
-----
    python scripts/series_saturation.py --json
    python scripts/series_saturation.py --days 7
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import sys

REPO = "jsboige/CoursIA"

# Fenetre. Le compteur par issue du picker tourne sur 1 jour -- correct pour
# une lane qui pilonne une issue, aveugle a un rollout qui avance d'un
# notebook par jour pendant une semaine. La monoculture MGS a couru du 22 au
# 28 aout : chaque jour, pris seul, avait l'air calme.
DEFAULT_WINDOW_DAYS = 14

# Amortissement plus mordant que celui par issue : une zone qui a deja recu
# quatre notebooks neufs dans la quinzaine n'a pas besoin du cinquieme.
SERIES_SCALE_DEFAULT = 2.0

# Un notebook AJOUTE, pas modifie. Seuil bas volontairement : un notebook
# pedagogique reel fait des milliers de lignes, un fichier de config non.
NEW_NB_MIN_ADDITIONS = 200

_PARENT_RE = re.compile(
    r"(?:enfant\s+de|fille\s+de|sous-t\w+\s+de|part\s+of"
    r"|paire\s+\d+\s*/\s*\d+\s+de)[^#\n]{0,40}#(\d{4,6})\b",
    re.I,
)
_EPIC_PARENT_RE = re.compile(r"(?:EPIC|Epic|epic|ombrelle)\s*#(\d{4,6})\b")

_REF_RE = re.compile(r"#(\d{4,6})\b")
_PREV_RE = re.compile(r"prev:\s*[^\n]*?#(\d{4,6})\b")
# Declaration de travail uniquement (#13435) : le vocabulaire qui DIT servir
# l'issue. Les renvois de contexte (voir, cf, bare "EPIC #N") sont exclus --
# mesure fenetre 14 j du 2026-08-29 : 19 rattachements sur 459 (4,1 %, 18
# PRs) venaient d'un renvoi seul et amortissaient une zone que la PR ne
# touchait pas. Les formes structurelles restent couvertes via `_PARENT_RE`.
_DECL_RE = re.compile(
    r"(?:closes|fixes|resolves|see|refs?|part of)"
    r"\s*:?\s*#(\d{4,6})\b",
    re.I,
)


def parent_issue(body: str) -> int | None:
    """L'ombrelle qu'une issue DECLARE servir, ou None.

    Les neuf filles de #12373 l'annoncent noir sur blanc -- "Enfant de l'Epic
    #12373", "Paire 9/9 de l'EPIC #12373". Le rattachement etait DEJA ecrit ;
    aucun garde ne le lisait.

    C'est cette reprise qui permet a une fille NEUVE d'heriter du poids de la
    zone que sa fratrie sature. Sans elle, l'amortissement ne mord que sur les
    issues DEJA travaillees -- c'est-a-dire jamais sur la prochaine instance,
    qui est exactement la seule qu'il faudrait freiner. (Verifie firsthand le
    2026-08-28 : sans ascendance, #13394 et #13268 ressortaient a `zone=None`,
    poids intact -- le correctif ne corrigeait pas son propre cas.)
    """
    if not body:
        return None
    m = _PARENT_RE.search(body) or _EPIC_PARENT_RE.search(body)
    return int(m.group(1)) if m else None


def cited_issues(pr: dict) -> set[int]:
    """Issues qu'une PR DECLARE servir : refs du titre + clauses de rattachement.

    La clause `prev:` du tag `Grain:` est masquee -- elle documente le grain
    PRECEDENT de la lane (adjacence G-VAR-3), jamais le sujet de la PR.

    Declaration != renvoi de contexte (#13435). Seuls rattaches :
    (a) le vocabulaire de declaration (`closes|fixes|resolves|see|refs|part
    of`), (b) les formes structurelles (`Enfant de l'Epic #N`, `Paire 3/9 de
    l'EPIC #N` -- `_PARENT_RE`), (c) les refs du titre. Un `voir #N` ou un
    bare `EPIC #N` en prose raconte le contexte historique sans declarer
    travailler la zone : sur la fenetre 14 j du 2026-08-29 (400 PRs mergees),
    19 rattachements sur 459 venaient d'un renvoi seul -- chacun amortissait
    le poids d'une issue neutre et gonflait l'expansion apparente d'une zone
    deja saturee.
    """
    body = _PREV_RE.sub("prev: <adjacence>", pr.get("body") or "")
    found = {int(m.group(1)) for m in _DECL_RE.finditer(body)}
    found |= {int(m.group(1)) for m in _PARENT_RE.finditer(body)}
    found |= {int(m.group(1)) for m in _REF_RE.finditer(pr.get("title") or "")}
    return found - {pr.get("number")}


def family_of(path: str) -> str:
    """Zone d'atterrissage d'un chemin : la serie, pas le fichier.

    Trois niveaux sous `MyIA.AI.Notebooks/`, deux ailleurs. C'est la
    granularite a laquelle un lecteur percoit "encore un de plus" :
    `Search/Part4-Metaheuristics` -- ni `Search` (toute la serie deviendrait
    une seule veine, et le signal se noierait), ni le fichier (jamais deux fois
    le meme, donc jamais de saturation visible).
    """
    parts = path.split("/")
    if len(parts) >= 3 and parts[0] == "MyIA.AI.Notebooks":
        return "/".join(parts[:3])
    return "/".join(parts[:2]) if len(parts) >= 2 else path


def fetch_merged(days: int, now: dt.datetime | None = None) -> tuple[list[dict], str | None]:
    """PRs mergees sur la fenetre, avec leurs fichiers.

    Le filtre de date est **serveur** (`--search "merged:>=..."`). `gh pr list
    --state merged --limit N` trie par date de CREATION : couper a N puis
    filtrer sur `mergedAt` cote client laisse tomber toute PR creee avant la
    coupe mais mergee dans la fenetre (mesure du 2026-08-23 : 101 pechees
    contre 181 reelles, 44 % de la population absente). Cle de tri != cle de
    filtre est un faux silencieux.
    """
    now = now or dt.datetime.now(dt.timezone.utc)
    stamp = (now - dt.timedelta(days=days)).strftime("%Y-%m-%dT%H:%M:%S+00:00")
    try:
        raw = subprocess.run(
            [
                "gh", "pr", "list", "--repo", REPO, "--state", "merged",
                "--limit", "400", "--search", "merged:>=" + stamp,
                "--json", "number,title,body,files,mergedAt",
            ],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True, timeout=300,
        ).stdout
        return json.loads(raw), None
    except (subprocess.CalledProcessError, json.JSONDecodeError,
            subprocess.TimeoutExpired, OSError) as exc:
        return [], "{}: {}".format(type(exc).__name__, exc)


def saturation(prs: list[dict]) -> tuple[dict[str, dict], dict[int, str]]:
    """Zones saturees + carte issue -> zone, deduites des PRs mergees.

    ``zones[f]`` porte ``{"prs", "new_notebooks", "numbers"}``. La carte
    issue -> zone vient des PRs elles-memes : une PR qui cite #N et depose dans
    F rattache #N a F. C'est ce qui permet d'amortir une issue au poids de la
    zone que sa fratrie sature sans dependre d'une ascendance declarative.
    """
    zones: dict[str, dict] = {}
    issue_to_family: dict[int, str] = {}
    for pr in prs:
        fams: set[str] = set()
        new_here: dict[str, int] = {}
        for f in pr.get("files") or []:
            path = f.get("path", "")
            if not path:
                continue
            fam = family_of(path)
            fams.add(fam)
            if (path.endswith(".ipynb")
                    and (f.get("deletions") or 0) == 0
                    and (f.get("additions") or 0) >= NEW_NB_MIN_ADDITIONS):
                new_here[fam] = new_here.get(fam, 0) + 1
        for fam in fams:
            z = zones.setdefault(fam, {"prs": 0, "new_notebooks": 0, "numbers": []})
            z["prs"] += 1
            z["new_notebooks"] += new_here.get(fam, 0)
            z["numbers"].append(pr.get("number"))
        if fams:
            dominant = max(fams, key=lambda f: (new_here.get(f, 0), f))
            for key in cited_issues(pr):
                issue_to_family.setdefault(key, dominant)
    return zones, issue_to_family


def fetch_series_visits(
    days: int = DEFAULT_WINDOW_DAYS,
) -> tuple[dict[str, dict], dict[int, str], str | None]:
    """``(zones, issue_to_family, erreur)``.

    En cas d'echec les deux structures sont vides ET l'erreur est non nulle :
    l'appelant doit dire que la saturation n'a pas ete MESUREE, jamais laisser
    un zero d'absence de mesure se lire comme un zero de saturation.
    """
    prs, err = fetch_merged(days)
    if err:
        return {}, {}, err
    zones, i2f = saturation(prs)
    return zones, i2f, None


# --- Polarite d'un grain : EXPANSION vs CONSOLIDATION ---------------------
# Mandat user 2026-08-28 : "si un Epic alimente une serie comme MGS, il faut
# qu'il soit capable de creer autant d'issues de renumerotations et
# consolidations de Notebooks -- transformant par exemple des numeros eleves
# en lettres de numeros existants, ou consolidant plusieurs lettres en un
# petit nombre d'autres -- que d'issues qui rajoutent un nouveau numero."
#
# C'est ce qui manquait a l'amortissement de zone pris seul : mesure du
# 2026-08-28, la saturation de `Search/Part4-Metaheuristics` faisait tomber a
# 0.36x **aussi** #12607, le tracker de consolidation -- c'est-a-dire le seul
# grain que la zone saturee reclamait. Une zone saturee n'a pas besoin d'une
# instance de plus : elle a besoin d'etre consolidee. La MEME mesure doit donc
# pousser dans les deux sens, sans quoi le frein ecrase le remede avec le mal.
_CONSOLIDATION_RE = re.compile(
    r"consolid|fusion|regroup|renum|synth[eè]se|d[eé]doublon|d[eé]duplic"
    r"|factoris|archiv|absorb|unifi|rassembl|en un seul|sous-s[eé]rie",
    re.I,
)
_EXPANSION_RE = re.compile(
    r"nouveau notebook|nouvelle instance|ajouter un notebook|paire \d+\s*/\s*\d+"
    r"|\bajout\b|\bcr[eé]er\b|\bnew notebook\b",
    re.I,
)

EXPANSION = "expansion"
CONSOLIDATION = "consolidation"
NEUTRAL = "neutral"


def polarity(title: str, body: str = "") -> str:
    """EXPANSION (ajoute une instance) / CONSOLIDATION (en retire) / NEUTRAL.

    Le titre pese plus que le corps : un grain d'expansion mentionne souvent la
    consolidation future en prose ("la synthese suivra"), et l'inverse est
    rare. On tranche donc sur le titre d'abord, le corps ne servant qu'a
    departager un titre muet.
    """
    t = title or ""
    if _CONSOLIDATION_RE.search(t):
        return CONSOLIDATION
    if _EXPANSION_RE.search(t):
        return EXPANSION
    b = body or ""
    if _CONSOLIDATION_RE.search(b):
        return CONSOLIDATION
    if _EXPANSION_RE.search(b):
        return EXPANSION
    return NEUTRAL


def zone_balance(zones: dict, issue_to_family: dict, pool: list) -> dict:
    """Par zone : combien de grains OUVERTS ajoutent, combien consolident.

    C'est la mesure que la redaction des EPICs doit satisfaire (parite
    demandee par le user). Une zone saturee dont le vivier ouvert ne contient
    que de l'expansion est un EPIC mal redige : il genere de l'accumulation et
    aucun remede.
    """
    out: dict[str, dict] = {}
    for it in pool:
        fam = issue_to_family.get(it.get("number"))
        if fam is None and it.get("parent"):
            fam = issue_to_family.get(it["parent"])
        if not fam:
            continue
        pol = polarity(it.get("title", ""), it.get("body", "") or "")
        slot = out.setdefault(
            fam, {EXPANSION: 0, CONSOLIDATION: 0, NEUTRAL: 0, "new_notebooks": 0})
        slot[pol] += 1
        slot["new_notebooks"] = (zones.get(fam) or {}).get("new_notebooks", 0)
    return out


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--days", type=int, default=DEFAULT_WINDOW_DAYS)
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    zones, i2f, err = fetch_series_visits(args.days)
    if err:
        payload = {"error": err, "measured": False}
        print(json.dumps(payload, ensure_ascii=False, indent=2) if args.json
              else "saturation NON MESUREE : " + err)
        return 1

    ranked = sorted(zones.items(),
                    key=lambda kv: (-kv[1]["new_notebooks"], -kv[1]["prs"]))
    if args.json:
        print(json.dumps(
            {"measured": True, "window_days": args.days,
             "zones": [{"family": f, **z} for f, z in ranked[:args.top]],
             "issues_mapped": len(i2f)},
            ensure_ascii=False, indent=2))
        return 0

    print("zones d'atterrissage -- fenetre {} j".format(args.days))
    for fam, z in ranked[:args.top]:
        print("  {:3d} notebooks neufs / {:3d} PRs   {}".format(
            z["new_notebooks"], z["prs"], fam))
    print("\n{} issues rattachees a une zone".format(len(i2f)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
