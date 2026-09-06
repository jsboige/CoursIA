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
from typing import Any

from gh_payload_cache import PayloadCache, cache_key

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


# Un motif nu `EPIC #N` ne vaut declaration qu'en TETE de corps : une
# ascendance se pose d'emblee ("## Contexte / Sous-grain de l'EPIC #1454"),
# un renvoi de comparaison se glisse au fil du texte. Mesure 2026-08-29 sur
# les 201 issues ouvertes : couper a 3 lignes garde les declarations reelles
# (#13436 "Sous-grain", #12915 "Tranche T5", #12607 "Fils techniques") et
# retire les 14 renvois mi-corps ; 1 ligne perdait les declarations, 5
# n'apportait rien de plus.
_EPIC_PARENT_HEAD_LINES = 3


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

    Declaration != renvoi de contexte (#13435, etendu ici par #13507) : le
    motif nu `EPIC #N` ne rattache plus au fil du texte. Mesure 2026-08-29 sur
    les 201 issues ouvertes : 39 parents declares, 14 changent -- tous des
    renvois mi-corps, dont #13504 qui rendait parent=12373 sur la foi de
    "dont l'EPIC #12373 porte la consolidation". Les formes structurelles
    (`_PARENT_RE`, n'importe ou) et les declarations nues en tete de corps
    restent rattachees.
    """
    if not body:
        return None
    m = _PARENT_RE.search(body)
    if m:
        return int(m.group(1))
    head = "\n".join(body.splitlines()[:_EPIC_PARENT_HEAD_LINES])
    m = _EPIC_PARENT_RE.search(head)
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


def fetch_merged(
    days: int,
    now: dt.datetime | None = None,
    *,
    cache: PayloadCache | None = None,
    cache_mode: str = "off",
    cache_status: dict[str, dict[str, Any]] | None = None,
    cache_ttl_seconds: float = 60 * 60,
) -> tuple[list[dict], str | None]:
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
    command = [
        "gh", "pr", "list", "--repo", REPO, "--state", "merged",
        "--limit", "400", "--search", "merged:>=" + stamp,
        "--json", "number,title,body,files,mergedAt",
    ]
    identity = [
        "gh", "pr", "list", "--repo", REPO, "--state", "merged",
        "--limit", "400", "--window-days", str(days),
        "--json", "number,title,body,files,mergedAt",
    ]

    def fetch_raw() -> list[dict]:
        raw = subprocess.run(
            command,
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True, timeout=300,
        ).stdout
        return json.loads(raw)

    try:
        cache_err = None
        cache_read_status = None
        if cache is None:
            prs = fetch_raw()
        else:
            result = cache.get_or_fetch(
                cache_key(REPO, "series", identity),
                cache_ttl_seconds,
                fetch_raw,
                mode=cache_mode,
            )
            prs = result.payload
            cache_read_status = result.status
            if cache_status is not None:
                cache_status["series"] = result.as_dict()
            if result.status == "stale":
                cache_err = "cache stale apres echec du refresh: {}".format(
                    result.error or "erreur inconnue"
                )
        if cache_read_status in {"hit", "stale"}:
            prs = [
                pr for pr in prs
                if pr.get("mergedAt")
                and dt.datetime.fromisoformat(
                    pr["mergedAt"].replace("Z", "+00:00")
                ) >= now - dt.timedelta(days=days)
            ]
        return prs, cache_err
    except (subprocess.CalledProcessError, json.JSONDecodeError,
            subprocess.TimeoutExpired, OSError) as exc:
        return [], "{}: {}".format(type(exc).__name__, exc)


_CAMEL_RE = re.compile(r"[a-z][A-Z]")


def _is_distinctive(seg: str) -> bool:
    """Le dernier segment d une zone peut-il se chercher SEUL sans faux positif ?

    Chercher `Texte` seul matcherait toute prose francaise -- c est le faux
    positif que la recherche a deux segments evite, et il faut le garder. Mais
    le refus etait total, et il coutait le cas inverse : `DataScienceWithAgents`
    n est pas un mot, c est un identifiant. Mesure du 2026-08-29 : l EPIC
    #13504, ouvert precisement pour declarer cette zone, ne s y rattachait pas
    -- son titre dit `consolidation(DataScienceWithAgents)` sans le prefixe
    `ML/`, et personne n ecrit le chemin complet dans un titre.

    Un segment se cherche seul s il est assez long ET porte une marque qui le
    sort du lexique : une bosse CamelCase, un chiffre, un tiret ou un underscore. `Texte`,
    `Audio`, `Video`, `Search` echouent aux deux conditions ; `ML-Training-
    Pipeline`, `Part4-Metaheuristics`, `DataScienceWithAgents` les passent.
    """
    s = seg or ""
    if len(s) < 10:
        return False
    return (bool(_CAMEL_RE.search(s)) or any(c.isdigit() for c in s)
            or "-" in s or "_" in s)


def _is_series(fam: str) -> bool:
    """Une zone est-elle une serie de notebooks ?

    Le prefixe suffit et se lit : `MyIA.AI.Notebooks/<domaine>/<serie>`. Tout
    le reste -- `scripts/`, `.github/`, `docs/` -- est de l outillage, jamais
    une zone d atterrissage pedagogique.
    """
    return (fam or "").replace(chr(92), "/").startswith("MyIA.AI.Notebooks/")


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
        nb_here: dict[str, int] = {}
        for f in pr.get("files") or []:
            path = f.get("path", "")
            if not path:
                continue
            fam = family_of(path)
            fams.add(fam)
            if path.endswith(".ipynb"):
                nb_here[fam] = nb_here.get(fam, 0) + 1
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
            # Une zone est une SERIE de notebooks, pas n importe quel chemin.
            # Le classement ne regardait que les notebooks NEUFS, puis l ordre
            # alphabetique : une PR d outillage pur rattachait donc l issue
            # qu elle cite a `scripts/<fichier>.py`. Mesure du 2026-08-29 :
            # `i2f[12373]` -- l EPIC MGS, une serie de notebooks -- valait
            # `scripts/series_saturation.py`, parce que mes propres PRs de
            # picker citent #12373 en prose et ne touchent que des scripts.
            # Toute fille de cet EPIC heritait de la zone d un script.
            dominant = max(
                fams,
                key=lambda f: (new_here.get(f, 0), nb_here.get(f, 0), f))
            touches_nb = nb_here.get(dominant, 0) > 0
            for key in cited_issues(pr):
                prev = issue_to_family.get(key)
                if prev is None:
                    issue_to_family[key] = dominant
                elif touches_nb and not _is_series(prev):
                    # Premier-arrive gagnait sans condition. On autorise UNE
                    # promotion : un rattachement a une serie remplace un
                    # rattachement a un chemin qui n en est pas une.
                    issue_to_family[key] = dominant
    return zones, issue_to_family


def fetch_series_visits(
    days: int = DEFAULT_WINDOW_DAYS,
    *,
    cache: PayloadCache | None = None,
    cache_mode: str = "off",
    cache_status: dict[str, dict[str, Any]] | None = None,
    cache_ttl_seconds: float = 60 * 60,
) -> tuple[dict[str, dict], dict[int, str], str | None]:
    """``(zones, issue_to_family, erreur)``.

    En cas d'echec les deux structures sont vides ET l'erreur est non nulle :
    l'appelant doit dire que la saturation n'a pas ete MESUREE, jamais laisser
    un zero d'absence de mesure se lire comme un zero de saturation.
    """
    prs, err = fetch_merged(
        days,
        cache=cache,
        cache_mode=cache_mode,
        cache_status=cache_status,
        cache_ttl_seconds=cache_ttl_seconds,
    )
    if err and not prs:
        return {}, {}, err
    zones, i2f = saturation(prs)
    return zones, i2f, err


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
    r"|\[\s*[^\]]+?\s+\d+\s*/\s*\d+\s*\]"
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



def family_from_text(text: str, families) -> str | None:
    """Zone NOMMEE explicitement dans le texte d'une issue.

    `issue_to_family` est construit par archeologie de PRs mergees : une issue
    n'y entre que si une PR l'a deja citee. Une issue FRAICHE -- typiquement le
    grain de consolidation qu'une zone saturee reclame -- n'y est donc jamais,
    et la zone reste `SANS REMEDE` alors que son remede vient d'etre ouvert.
    Un garde dont le remede est invisible ne peut pas etre satisfait : mesure
    du 2026-08-29, #13467 (renumerotation GenAI/Texte, polarite `consolidation`
    correctement detectee, parent #5081 correctement extrait) ne remontait a
    aucune zone -- la zone serait restee fermee a l'expansion pour toujours.

    On resout donc aussi par le TEXTE. Le motif est le chemin de famille
    lui-meme (`MyIA.AI.Notebooks/GenAI/Texte`) ou ses deux derniers segments
    (`GenAI/Texte`) -- assez specifique pour ne pas confondre la serie avec le
    mot courant qui lui sert de feuille : `Texte` seul matcherait toute prose
    francaise, et c'est le faux positif que ce garde doit eviter.
    """
    low = (text or "").replace(chr(92), "/").lower()
    if not low:
        return None
    # La FREQUENCE avant la longueur. "La plus longue chaine gagne" traite un
    # renvoi incident comme le sujet : mesure du 2026-08-29, l'EPIC #13504
    # (qui nomme deux fois `ML/DataScienceWithAgents` et cite UNE fois
    # `Search/Part4-Metaheuristics` dans un tableau de comparaison) se
    # resolvait en Part4-Metaheuristics -- 45 caracteres contre 44. La zone
    # que l'EPIC venait declarer restait `(aucun EPIC declare)`, c'est-a-dire
    # que l'organe repondait le contraire de ce qui venait d'etre ecrit.
    # Ce qu'une issue REPETE est son sujet ; ce qu'elle cite une fois est un
    # renvoi. La longueur reste en second : elle departage `GenAI/Texte` de
    # `Texte` quand les deux apparaissent autant.
    best = None
    for fam in families:
        raw_segs = fam.replace(chr(92), "/").split("/")
        segs = [s.lower() for s in raw_segs]
        cands = ["/".join(segs)]
        if len(segs) >= 2:
            cands.append("/".join(segs[-2:]))
        if _is_distinctive(raw_segs[-1]):
            cands.append(segs[-1])
        hits, span = 0, 0
        for c in cands:
            n = low.count(c)
            if n:
                hits = max(hits, n)
                span = max(span, len(c))
        if hits:
            key = (hits, span)
            if best is None or key > best[0]:
                best = (key, fam)
    return best[1] if best else None



def enrich_parent_families(pool, issue_to_family: dict, zones: dict) -> dict:
    """Rend la zone d'un EPIC a ses ENFANTS, pas aux PRs qui le citent.

    `saturation()` lie une issue a la zone dominante de la premiere PR
    mergee qui la cite (`setdefault`). Pour un GRAIN c'est factuel. Pour un
    EPIC c'est un piege : un EPIC est un tracker, cite par tout ce qui
    l'outille, et la premiere PR d'outillage le fige sur un chemin de script
    qui ne portera jamais de notebook. Mesure du 2026-08-29 : #12373 (EPIC
    MGS, 9 paires de notebooks) etait fige sur `scripts/series_saturation.py`,
    zone a 0 notebook -- si bien que sa fille #13268, sans PR citante propre,
    heritait d'un frein NUL (x1.00) la ou sa soeur #13394 prenait x0.33 dans
    la meme zone saturee. Deux grains d'expansion du meme EPIC, deux poids
    incomparables, selon qu'une PR les avait deja touches ou non.

    Le vote des enfants est la source factuelle qui manquait : la zone d'un
    EPIC est celle ou ses grains ATTERRISSENT. Il ne remplace jamais une
    attribution deja informative -- il ne comble que l'absente et la muette.
    """
    votes: dict[int, dict[str, int]] = {}
    for it in pool or ():
        parent = it.get("parent")
        if not parent:
            continue
        fam = (issue_to_family or {}).get(it.get("number"))
        if fam and (zones.get(fam) or {}).get("new_notebooks", 0) > 0:
            tally = votes.setdefault(parent, {})
            tally[fam] = tally.get(fam, 0) + 1
    out = dict(issue_to_family or {})
    for parent, tally in votes.items():
        cur = out.get(parent)
        if cur is None or (zones.get(cur) or {}).get("new_notebooks", 0) == 0:
            out[parent] = max(tally, key=lambda f: (tally[f], f))
    return out


def _informative(fams, zones) -> bool:
    """Une zone informe le frein si elle a MESURE des notebooks neufs.

    Sans `zones` on ne sait rien : on ne degrade pas le comportement
    existant (toute reponse est alors tenue pour informative).

    Une liste VIDE, elle, n'informe jamais -- et c'est le cas qui compte le
    plus, car c'est celui d'un grain frais sans PR citante ni parent resolu.
    `any()` sur une liste vide rend deja False ; sans ce garde, le raccourci
    `zones is None` repondait True et faisait sauter le repli par le texte
    pour tous les appelants a trois arguments (mesure du 2026-08-29 :
    `test_titre_prime_sur_le_corps` et ses deux soeurs rendaient None).
    """
    if not fams:
        return False
    if zones is None:
        return True
    return any((zones.get(f) or {}).get("new_notebooks", 0) > 0 for f in fams)


def resolve_family(item: dict, issue_to_family: dict, families=(),
                   zones: dict | None = None) -> str | None:
    """Zone d'un grain : par PR citante, sinon par son EPIC parent, sinon par
    le texte. Les trois sources vont de la plus factuelle (une PR a reellement
    touche ce chemin) a la plus declarative (l'issue dit son sujet).

    Une source qui repond une zone SANS accumulation de notebooks mesuree
    n'informe pas un frein qui compte des notebooks : la cascade continue au
    lieu de s'arreter dessus (`zones` fourni). Mesure du 2026-08-29 :
    #13268 (paire 8/9 de l'EPIC #12373, MGS) n'avait pas de PR citante, sa
    source parente rendait `scripts/series_saturation.py` -- l'EPIC est un
    tracker, la premiere PR d'outillage qui le cite le lie a un chemin de
    script par `setdefault` + departage alphabetique -- et ce chemin, qui ne
    peut par construction porter aucun notebook, ANNULAIT le frein : x1.00 la
    ou sa soeur #13394 prenait x0.33 dans la meme zone saturee. C'est le trou
    par lequel passe exactement l'emballement decrit par le user (les grains
    qui arrivent frais chaque jour n'ont pas encore de PR citante).

    Le garde-fou ne peut pas inventer de frein : il ne retient une source
    ulterieure que si elle porte des notebooks MESURES ; si aucune n'en porte,
    la premiere reponse non nulle est rendue, comme avant.
    """
    cands = []
    fam = (issue_to_family or {}).get(item.get("number"))
    if fam is not None:
        cands.append(fam)
    if item.get("parent"):
        fam = (issue_to_family or {}).get(item["parent"])
        if fam is not None:
            cands.append(fam)
    fam = cands[0] if cands else None
    if families and not _informative(cands, zones):
        # TITRE d abord, corps ensuite -- meme principe que polarity().
        # Le corps CITE beaucoup (regles, conventions, precedents) ; le
        # titre DIT le sujet. Chercher dans un blob unique laisse la plus
        # longue citation gagner : mesure du 2026-08-29, #13467 (titre
        # "GenAI/Texte : renumerotation...") se resolvait en `.claude/rules`
        # parce que son corps citait `.claude/rules/catalog-pr-hygiene.md`
        # et que cette chaine est plus longue que `genai/texte`. La zone
        # reelle restait alors SANS REMEDE, remede en main.
        txt = family_from_text(item.get("title") or "", families)
        if txt is None:
            txt = family_from_text(item.get("body") or "", families)
        if txt is not None and (not cands or _informative([txt], zones)):
            return txt
    return fam


def zone_balance(zones: dict, issue_to_family: dict, pool: list) -> dict:
    """Par zone : combien de grains OUVERTS ajoutent, combien consolident.

    C'est la mesure que la redaction des EPICs doit satisfaire (parite
    demandee par le user). Une zone saturee dont le vivier ouvert ne contient
    que de l'expansion est un EPIC mal redige : il genere de l'accumulation et
    aucun remede.
    """
    out: dict[str, dict] = {}
    families = tuple(zones or ())
    for it in pool:
        fam = resolve_family(it, issue_to_family, families, zones)
        if not fam:
            continue
        pol = polarity(it.get("title", ""), it.get("body", "") or "")
        slot = out.setdefault(
            fam, {EXPANSION: 0, CONSOLIDATION: 0, NEUTRAL: 0,
                  "new_notebooks": 0, "neutral_issues": []})
        slot[pol] += 1
        if pol == NEUTRAL and it.get("number"):
            # #13466 (review NanoClaw, concern 1) : le veto "SANS REMEDE"
            # herite de la recall du lexique de polarite. Un grain de
            # consolidation dont le titre echappe au lexique tombe en
            # NEUTRAL -- le remede existe alors, mais il est INVISIBLE, et
            # le refus devient un faux positif SILENCIEUX. On retient donc
            # les numeros pour que le refus puisse les citer : le lecteur
            # voit ou le faux positif se cacherait, au lieu de devoir
            # deviner que le lexique a pu manquer quelque chose.
            slot["neutral_issues"].append(it["number"])
        slot["new_notebooks"] = (zones.get(fam) or {}).get("new_notebooks", 0)
    return out


# --- Emballement d'une zone : la MAGNITUDE, que la polarite ne voit pas ------
# Mandat user 2026-08-28 : "il ne devrait pas y avoir d'emballement".
#
# `zone_verdict` ne lit que la POLARITE du vivier ouvert : une zone dont les
# grains ouverts consolident plus qu'ils n'ajoutent rend OK, quel que soit le
# nombre de notebooks DEJA tombes. Mesure du 2026-08-29 :
# `ML/DataScienceWithAgents` a recu 11 notebooks neufs en 14 jours (21 ajouts
# bruts au sens git) pour 3 grains de consolidation ouverts, et l'organe
# repondait OK -- sur la zone la plus saturee du depot, celle-la meme que le
# user a nommee. Trois remedes ouverts ne repondent pas a onze arrivees : la
# parite demandee porte sur les issues, le RYTHME est une seconde dimension.
#
# Le critere s'enonce, il ne se regle pas : une zone s'emballe si elle a recu
# au moins RUNAWAY_MIN_LANDED notebooks sur la fenetre ET qu'il lui manque un
# grain de consolidation ouvert par tranche de RUNAWAY_RATIO arrivees. Le
# plancher absolu evite de qualifier d'emballement trois notebooks sans
# remede (c'est petit, pas emballe) ; le ratio evite de sanctionner une zone
# volumineuse dont la consolidation est deja engagee -- mesure du meme jour :
# `Search/Part4-Metaheuristics` (6 arrivees, 3 consolidations) ne s'emballe
# PAS, sa consolidation est en cours, et c'est la zone que le user avait
# signalee en premier.
RUNAWAY_MIN_LANDED = 6
RUNAWAY_RATIO = 3

RUNAWAY = "EMBALLEMENT"
BALANCED = "OK"
IMBALANCED = "DESEQUILIBRE"
NO_REMEDY = "SANS REMEDE"


def zone_verdict(slot: dict) -> str:
    """Verdict de POLARITE d'une zone -- inchange, il gouverne le tirage.

    Extrait du picker pour que les deux lisent la meme source (sinon ils
    re-divergeraient). `SANS REMEDE` a un effet de bord -- il retient des
    grains hors tirage -- donc son predicat n'est pas touche ici.
    """
    exp = slot.get(EXPANSION, 0)
    con = slot.get(CONSOLIDATION, 0)
    if exp == 0 and con == 0:
        return NO_REMEDY
    if con >= exp:
        return BALANCED
    return IMBALANCED


def is_runaway(slot: dict) -> bool:
    """La zone recoit-elle plus vite qu'elle ne consolide ?

    Dimension ORTHOGONALE a `zone_verdict` : une zone peut etre OK en
    polarite et emballee en rythme -- c'est meme le cas exact qui a motive
    cette mesure. On ne remplace donc pas le verdict, on l'accompagne.
    """
    landed = slot.get("new_notebooks", 0)
    con = slot.get(CONSOLIDATION, 0)
    return landed >= RUNAWAY_MIN_LANDED and landed >= RUNAWAY_RATIO * max(1, con)


def zone_umbrellas(issue_to_family: dict, pool: list, families=()) -> dict:
    """Par zone : quels EPICs parents alimentent ses grains ouverts.

    Le mandat demande qu'un EPIC qui alimente une serie sache produire de la
    consolidation autant que de l'expansion. Encore faut-il savoir OU l'ecrire
    -- un verdict qui ne nomme pas l'EPIC responsable laisse le lecteur le
    chercher. Une zone chaude SANS parent declare est le cas le plus grave et
    non le plus propre : personne n'y est comptable de la contrepartie.

    Deux sources : (1) les parents DECLARES par les grains du pool ; (2) les
    EPICs racines (label/titre EPIC, file de tranches) ATTESTES dans une zone
    par les PRs mergees qui les citent (`issue_to_family`). Sans la seconde,
    un tracker racine sans fille ouverte -- #13934, dont les tranches vivent
    dans des PRs mergees, pas dans des issues -- rendait la zone qu'il
    alimente "SANS REMEDE (aucun EPIC declare)".

    L'attestation est la porte d'entree de la source (2) : une issue qui ne
    fait que MENTIONNER la zone (body de diagnostic, renvoi de contexte) n'est
    pas un comptable, meme si son texte porte les marqueurs de tracker. La
    source (2) ne nomme que des trackers RACINES (`parent is None`) : une
    fille d'EPIC dont le titre porte "tranches" est deja comptee sous son
    parent par la source (1), la nommer aussi en propre la compterait en
    double a la fois comme elle-meme et comme sa racine.
    """
    out: dict[str, dict[int, int]] = {}
    for it in pool:
        fam = resolve_family(it, issue_to_family, families)
        parent = it.get("parent")
        if not fam or not parent:
            continue
        out.setdefault(fam, {})
        out[fam][parent] = out[fam].get(parent, 0) + 1
    for it in pool:
        if not is_area_umbrella(it):
            continue
        if it.get("parent") is not None:
            continue
        fam = (issue_to_family or {}).get(it.get("number"))
        if not fam:
            continue
        out.setdefault(fam, {})
        out[fam][it["number"]] = out[fam].get(it["number"], 0) + 1
    return out


# Une issue qui TRACK une zone est nommable comme "alimente par" d'une zone
# chaude : EPIC par label/titre (meme logique que le pool du picker), ou file
# de tranches (#13934, "queue de tranches"). Les tranches vivent dans des PRs
# mergees, pas dans des issues ouvertes -- un tel tracker racine n'a donc
# jamais de parent declare dans le pool, et seule l'attestation par les PRs
# citees (`issue_to_family`) le rend visible.
_TRACKER_TRANCHES_RE = re.compile(r"tranches?", re.I)


def is_area_umbrella(item: dict) -> bool:
    """L'issue PEUT-ELLE etre nommee comme comptable d'une zone chaude ?

    Distingue de la classification du pool (`klass` = umbrella) : celle-la
    decide du triage du tirage (un grain utilisable), celle-ci ne nomme qu'un
    comptable pour l'affichage de la parite. Les deux predicats peuvent
    diverger sans creer de double lecteur de source.
    """
    title = item.get("title") or ""
    labels = {str(x).lower() for x in item.get("labels", []) or []}
    if "epic" in labels or title.upper().lstrip("[").startswith("EPIC"):
        return True
    head = "\n".join((item.get("body") or "").splitlines()[:_EPIC_PARENT_HEAD_LINES])
    return bool(_TRACKER_TRANCHES_RE.search(title)) or bool(
        _TRACKER_TRANCHES_RE.search(head))


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
