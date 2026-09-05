#!/usr/bin/env python3
"""Tirage aleatoire pondere d'une poignee de grains dans le pool d'issues ouvertes.

Pourquoi cet organe existe
--------------------------
`gh issue list` plafonne a 30 resultats par defaut, tries par recence. Avec un
pool de 140 issues dont 89 creees dans les 7 derniers jours, un worker qui
scanne le pool ne voit **rien de plus vieux que ~6 jours** -- il repioche
mecaniquement dans ce que le coordinateur vient de creer, ce qui referme la
boucle de monoculture que `.claude/rules/variation-protocol.md` cherche a
ouvrir. Le picker defait la troncature courante par construction (`--limit
2000`, une seule requete, plafond surveille) et rend la selection *aleatoire ponderee* au lieu de
*recente-d'abord*.

Il **ne decide pas** du grain. Il tire une poignee de candidats et laisse a
l'agent le choix final selon les criteres de variete de sa lane (G-VAR-1/2/3).
Il decide en revanche de ce qui est **admissible** -- voir ci-dessous.

Classer ne suffisait pas : le garde d'admission (mandat user 2026-08-28)
------------------------------------------------------------------------
Mesure du 2026-08-29. Le tirage place deja **62 % de sa masse au-dela de 7
jours** et sous-pondere les issues du jour a **0.39x** : son classement n'est
pas le defaut. Pourtant, sur les 112 issues travaillees en 48 h, **70 avaient
moins de 24 h** (63 %), la ou le tirage n'en voulait que 3.9 %. L'ecart de
**16x** ne s'explique pas par le bruit : le travail n'arrivait pas par le
tirage. Il arrivait par le **steering** du coordinateur et par l'auto-pick --
deux chemins qu'aucune ponderation ne touche. Un poids se fait battre par la
population et par le steer ; seul un **refus** s'applique quel que soit le
chemin de selection.

D'ou deux causes d'inadmissibilite, verifiables par `--admissible <issue>` et
appliquees aussi au tirage :

- **dwell** -- une issue de moins de `--dwell-hours` (24 h) n'est pas encore
  consommable. C'est la reponse directe a "les issues auraient du attendre au
  lieu d'etre immediatement prises en charge" : un audit qui ouvre quinze
  issues le matin ne doit pas mobiliser la flotte l'apres-midi. Les etiquettes
  d'urgence (`urgent`, `security`, `regression`, `hotfix`...) court-circuitent
  le delai -- le garde vise l'emballement, pas les correctifs.
- **zone sans remede** -- un grain d'EXPANSION dans une zone qui a recu >= 3
  notebooks neufs sur la fenetre **et dont le vivier ouvert ne contient aucun
  grain de consolidation** est refuse. C'est "il ne faut pas se taper le
  produit cartesien MGS x PythonNet x Mealpy" rendu mecanique.

Le second veto porte sur `con == 0`, **pas** sur la parite stricte
`con >= exp`, bien que le mandat dise "autant ... que" : la parite se mesure
sur le vivier OUVERT, et *consommer* un grain de consolidation le ferme -- donc
le retire du vivier et degrade le ratio. Un veto sur la parite punirait la zone
precisement quand elle vient de faire ce qu'on lui demandait. La parite reste
**mesuree et affichee** (verdict `DESEQUILIBRE` / `SANS REMEDE`) parce qu'elle
vise la **redaction des EPICs** : c'est au coordinateur d'y repondre en ouvrant
des grains de consolidation, pas au worker d'y buter.

Regime : voie normale, pas filet de secours (mandat user 2026-08-20)
--------------------------------------------------------------------
Ce tirage est le **premier geste de chaque cycle**, pas le recours d'une lane
en panne de grain. Un steering nomme par le coordinateur reste possible -- il
devient l'**exception**, et doit lui-meme etre equilibre entre familles et
genres. La raison est mecanique : tant que la selection par defaut restait
"ce que je vois", elle restait "ce qui est recent", et les sujets conduits a
leur terme etaient toujours ceux du moment.

Trois urnes, parce que le pool n'est pas homogene
-------------------------------------------------
- **grains**    : issues unitaires, directement executables.
- **umbrella**  : EPIC / conteneurs. Le tirage rend l'EPIC ; l'agent pioche ou
                  cree un sous-grain dedans. C'est la que vit le DEEP/CONTENU
                  ancien -- une urne unique ne le montrerait jamais.
- **delivered** : issues portant `candidate-delivered` (livrees par une PR
                  mergee mais jamais fermees). Les offrir a chaque tirage est
                  ce qui fait *refluer* le compte sans batch-close aveugle :
                  l'agent verifie firsthand (G.9) puis ferme avec preuve, ou
                  retire le label en disant pourquoi.

Reprendre ses PRs AVANT de piocher (mandats user 2026-08-22 et 2026-08-24)
--------------------------------------------------------------------------
Le picker **assigne la reparation** (sortie 0, un grain rendu) tant que la
lane porte une PR a reprendre, ouverte depuis plus de 24 h. La reparation
n'appartient qu'a sa lane : le coordinateur ne peut ni rebaser, ni corriger,
ni repondre a sa place -- une lane qui pioche du neuf en laissant sa PR
derriere elle fabrique un residu que personne d'autre ne peut resorber.

Ce chemin a longtemps rendu **"REFUS DE TIRAGE" + sortie 2, aucun candidat**.
Le fond etait juste -- la liste, les causes, les gestes -- mais la forme
disait *l'outil n'a rien pour toi*, et une lane pouvait s'arreter en croyant
la sortie sanctionnee. Une lane a forte cadence accumule les PRs plus vite,
declenche `count`/`nits` plus tot, et recevait donc ce refus a **chaque**
cycle : le boost causait le drain (incident lanes 2, 2026-08-30). Le travail
rendu ici EST le grain du cycle. Aucune sortie de cet outil n'autorise une
lane a ne rien produire tant que du rouge lui appartient ou que
`gh issue list` renvoie > 0.

Quatre causes, dont la derniere est arrivee en dernier et couvre le plus :

1. **check requis en echec** -- lu sur le champ GraphQL `isRequired`, ce que la
   protection de branche exige vraiment, et non "au moins un check rouge", qui
   rougissait 52 PRs sur 55 le 2026-08-22 en comptant les advisories ;
2. **conflit avec main** ;
3. **CHANGES_REQUESTED non leve** ;
4. **point de review non leve** (mandat 2026-08-24 : "ne plus produire tant
   qu'il leur reste des points a traiter dans leurs vieilles PRs, ca doit leur
   etre propose en premier lieu"). Les trois premieres causes sont
   structurellement aveugles aux trois surfaces ou vit la substance des reviews
   sur ce depot : nits du user en issue comments (aucune entree dans
   `reviews[]`), reserves d'Hermes en prefixe de body sous `state: COMMENTED`,
   threads inline dans `reviewThreads`. Une PR peut etre verte, sans conflit,
   sans CHANGES_REQUESTED -- et rester non mergeable. Cette cause est donc
   **placee en tete** de la liste : c'est la seule qu'un `update-branch` ne
   reparera jamais.

La 4e cause n'est pas redetectee ici : elle **delegue** a
`check_unaddressed_nits.analyse`, l'organe du merge-gate B.0. Un jeu de motifs
ecrit une seconde fois sous-compterait en silence, et surtout : si les deux
gardes divergeaient, une lane pourrait etre autorisee a produire du neuf sur
une PR que le merge-gate refusera. Voir `red_backlog` et
`unaddressed_review_points`.

Usage
-----
    python scripts/pick_idle_grain.py --lane myia-po-2026:CoursIA
    python scripts/pick_idle_grain.py --lane myia-po-2023:CoursIA-2 --prev-genre guard
    python scripts/pick_idle_grain.py --lane <l> --reroll 1        # nouveau tirage
    python scripts/pick_idle_grain.py --lane <l> --no-check-claims # sans verif claims
    python scripts/pick_idle_grain.py --lane <l> --json            # sortie machine
    python scripts/pick_idle_grain.py --lane <l> --ignore-red      # rouge non reparable
                                                                   # par cette lane, ECRIT sur la PR

Le tirage est **deterministe par (lane, heure UTC, reroll)** : deux lanes
tirent des candidats differents a la meme minute, et une meme lane qui relance
dans l'heure retrouve son tirage (idempotent, pas de thrash). `--reroll N`
decale la graine quand aucun candidat ne convient.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import pathlib
import random
import re
import subprocess
import sys
from typing import Any

REPO = "jsboige/CoursIA"

# Saturation par zone d atterrissage (#13420) : l axe partition-proof que
# le compteur par issue ne peut pas porter. Voir scripts/series_saturation.py
# pour le diagnostic complet (EPIC decoupe en 9 filles = 9 veines invisibles).
from series_saturation import (  # noqa: E402
    CONSOLIDATION,
    enrich_parent_families,
    EXPANSION,
    NEUTRAL,
    SERIES_SCALE_DEFAULT,
    cited_issues,
    fetch_series_visits,
    zone_balance,
    zone_umbrellas,
    zone_verdict,
    is_runaway,
    parent_issue,
    polarity,
    resolve_family,
)

# Lecteur PARTAGE du tag `Grain:` (#9485). C'est la SEULE ancre qui rattache
# une PR a une lane : mesure du 2026-08-22 sur les 55 PRs ouvertes -- 50 sont
# poussees sous le compte `jsboige`, l'auteur GitHub ne porte donc aucune
# information de lane. Reutiliser l'extracteur plutot qu'en ecrire un
# troisieme : deux lecteurs divergents avaient deja rendu 38 % d'une journee
# de merges invisibles au cap G-VAR-2.
from grain_tag import parse_grain_tag  # noqa: E402
from gh_payload_cache import PayloadCache, cache_key  # noqa: E402

# Normalisation CANONIQUE du genre (#10020). Reutilisee, jamais
# reimplementee : `notebook-genai-python` et `research-notebook-python`
# se replient tous deux sur `notebook-python` (du CONTENU), et les lire
# bruts les compterait META -- une lane qui vient de livrer un notebook
# serait accusee de secheresse. Mesure du 2026-08-31 : la canonicalisation
# resout 8 des 11 genres hors-enumeration du corpus, dont 2 CONTENU.
from variation_light_cap import canonicalize_genre  # noqa: E402

# Enumeration CLOSE de variation-protocol.md, partitionnee CONTENU / META.
CONTENU = {
    "lean", "qc", "training", "genai",
    "notebook-python", "notebook-dotnet", "notebook-lean", "slides",
    "research-code",
}
META = {"guard", "tooling", "ledger", "docs", "readme", "test", "refactor"}

# Inference de genre : (regex sur titre+labels, genre). Premiere qui matche.
# Volontairement grossier -- le genre infere est une *aide au tri*, pas un
# verdict : l'agent pose le vrai tag Grain: lui-meme.
GENRE_RULES: list[tuple[str, str]] = [
    # AVANT la regle `lean` generique : un notebook a kernel Lean est du
    # travail de NOTEBOOK (materiel pedagogique), pas du travail de lake.
    # L'ordre compte -- la regle generique ci-dessous matcherait "notebook
    # Lean" en premier et le genre notebook-lean serait inatteignable.
    # `[.]ipynb` == `\.ipynb` sans backslash a transporter.
    (r"(?=.*(?:notebook|[.]ipynb|companion))(?=.*lean)", "notebook-lean"),
    (r"\.lean\b|\blean[-_ ]|\blake\b|sorry|mathlib|grothendieck|knot|hashlife|tao\b", "lean"),
    (r"quantconnect|\bqc[-_ (]|backtest|quantbook|lean-cli|sharpe", "qc"),
    (r"training|post[- ]?training|\bppo\b|fine[- ]?tun|checkpoint|walk[- ]?forward", "training"),
    (r"genai|comfyui|diffusion|audiobook|\btts\b|whisper|acestep|voice|image gener", "genai"),
    (r"\.ipynb|notebook", "notebook-python"),
    (r"slidev|\bslides?\b|deck\b", "slides"),
    (r"c#|csharp|\.net|dotnet|roslyn|aspire|nuget|semantickernel", "notebook-dotnet"),
    (r"z3|solveur|solver|automat|opensp|tweety|pymc|infer\.net|prover", "research-code"),
    (r"workflow|\bci\b|gate\b|guard|gitleaks|check-|advisory", "guard"),
    (r"script|tooling|organe|cli\b|papermill|render_envs", "tooling"),
    (r"readme", "readme"),
    (r"\bdocs?\b|documentation|resync doc|cadrage", "docs"),
    (r"\btests?\b|pytest|vitest", "test"),
    (r"ledger|registre|inventaire|catalog", "ledger"),
    (r"refactor|consolidation|migration", "refactor"),
]

# Attribution PR -> issue, pour l'AFFLUENCE (combien de PRs de la flotte ont
# visite cette issue). Ce n'est PAS la meme grandeur que la "veine" du cap
# (`variation_light_cap.extract_vein_key`, #11343), et la difference est
# deliberee -- ne pas "unifier" les deux sans relire ceci :
#
#   * Le cap demande "a quelle ombrelle UNIQUE cette PR appartient-elle ?",
#     pour compter des tranches par lane. Il lui faut UNE cle, donc le premier
#     `#N` du corps, et une sur-attribution y serait une fausse accusation.
#   * L'affluence demande "combien d'attention cette issue a-t-elle recue ?".
#     Il lui faut du RAPPEL : rater une citation fait lire une ombrelle chaude
#     comme froide, donc la sur-pondere -- l'inverse exact du but.
#
# Mesure du 2026-08-23 sur 10 issues (verite = `gh pr list --search "N
# in:title,body"` restreint a la fenetre) : le premier-`#N` rappelle 59 %, le
# schema d'attribution 76 %. Cas d'ecole : #12591 s'intitule `fix(notebooks,#11947)`
# et porte `See #11947`, mais son premier `#N` de corps est #11949 (la tranche
# soeur) -- la veine y est juste pour le cap, et fausse pour l'affluence.
#
# `cited_issues` vit dans series_saturation.py (source unique depuis #13435 :
# declaration de travail vs renvoi de contexte -- un `voir #N` en prose
# n'amortit plus l'issue citee dans le compteur de visites).


NOW = dt.datetime.now(dt.timezone.utc)


def infer_genre(title: str, labels: list[str]) -> str:
    hay = (title + " " + " ".join(labels)).lower()
    for pattern, genre in GENRE_RULES:
        if re.search(pattern, hay):
            return genre
    return "docs"


def authoritative_genre(body: str) -> str | None:
    """#13972 : extraire le genre que l'auteur de l'issue a DEClare dans le body.

    Un tag `Grain: TIER/GENRE -- lane ...` dans le body est **autoritatif** :
    c'est le genre que l'auteur a lui-meme pose, et il prime sur
    `infer_genre(title, labels)` qui n'infere que du titre (et donc peut
    declarer `notebook-python` un titre mentionnant `notebook_tools/`).

    Renvoie le genre CANONIQUE (via `canonicalize_genre`), ou None si le
    body n'a pas de tag `Grain:` lisible. Le retour None signifie «
    l'auteur n'a rien declare, inferer du titre est acceptable ».
    """
    tag = parse_grain_tag(body)
    if not tag or not tag.get("genre"):
        return None
    return canonicalize_genre(tag["genre"])


def age_days(created: str) -> int:
    created_dt = dt.datetime.fromisoformat(created.replace("Z", "+00:00"))
    return max(0, (NOW - created_dt).days)


# Plafond de recuperation du pool. Ce n'est PAS un reglage de confort : quand
# il sature, `gh issue list` rend les N plus RECENTES (mesure du 2026-08-30 :
# les 12 premieres rendues etaient les 12 dernieres creees), donc la
# troncature ampute exactement la traine -- la population que la ponderation
# age + delaissement existe pour atteindre. Un plafond atteint inverse
# l'instrument au lieu de le borner, et le fait sans rien dire.
#
# Mesure du 2026-08-30 : 213 ouvertes, et ce que l'ancien plafond de 300
# aurait fait tomber en premier etait #1028 (mandat audiobook), #1203, #1206,
# #1210, #1453, #1454 -- six EPICs de mai, tous vivants.
POOL_FETCH_LIMIT = 2000
POOL_CACHE_TTL_SECONDS = 10 * 60
VISITS_CACHE_TTL_SECONDS = 15 * 60
SERIES_CACHE_TTL_SECONDS = 60 * 60


def _cached_payload(
    name: str,
    identity: list[str],
    fetch: Any,
    *,
    cache: PayloadCache | None,
    cache_mode: str,
    ttl_seconds: float,
    cache_status: dict[str, dict[str, Any]] | None,
) -> Any:
    """Fetch raw JSON, optionally recording an observable cache decision."""
    if cache is None:
        return fetch()
    result = cache.get_or_fetch(
        cache_key(REPO, name, identity),
        ttl_seconds,
        fetch,
        mode=cache_mode,
    )
    if cache_status is not None:
        cache_status[name] = result.as_dict()
    return result.payload


def fetch_pool(
    *,
    cache: PayloadCache | None = None,
    cache_mode: str = "off",
    cache_status: dict[str, dict[str, Any]] | None = None,
) -> list[dict]:
    """Une seule requete, limite haute -- c'est ce qui defait la troncature.

    Le plafond est haut ET surveille : aucun plafond ne se choisit une fois
    pour toutes, et celui-ci se fait franchir en silence par construction.
    """
    command = [
        "gh", "issue", "list", "--repo", REPO, "--state", "open",
        "--limit", str(POOL_FETCH_LIMIT),
        "--json", "number,title,labels,body,createdAt,updatedAt",
    ]

    def fetch_raw() -> list[dict]:
        out = subprocess.run(
            command,
            capture_output=True, text=True, encoding="utf-8", check=True,
        ).stdout
        return json.loads(out)

    raw = _cached_payload(
        "pool",
        command,
        fetch_raw,
        cache=cache,
        cache_mode=cache_mode,
        ttl_seconds=POOL_CACHE_TTL_SECONDS,
        cache_status=cache_status,
    )
    if len(raw) >= POOL_FETCH_LIMIT:
        # Signature de la troncature : on a recu exactement ce qu'on a demande.
        # Le tirage reste possible et se poursuit -- bloquer la lane serait pire
        # que la biaiser (R4 : jamais sanctionner l'idle). Mais il est desormais
        # biaise VERS LE RECENT, et le dire est la seule chose qui empeche de
        # lire son resultat comme une couverture du pool.
        print(
            f"[POOL TRONQUE] {len(raw)} issues rendues pour un plafond de "
            f"{POOL_FETCH_LIMIT} : le pool est probablement plus grand. "
            "gh rend les plus RECENTES, donc la traine -- vieux EPICs, sujets "
            "delaisses -- est absente de ce tirage. Le resultat ci-dessous est "
            "biaise vers le recent : relever POOL_FETCH_LIMIT avant de s'en "
            "servir pour conclure quoi que ce soit sur la couverture.",
            file=sys.stderr,
        )
    pool = []
    for it in raw:
        labels = [lb["name"] for lb in it.get("labels", [])]
        title = it["title"]
        is_umbrella = "EPIC" in labels or title.upper().lstrip("[").startswith("EPIC")
        body = it.get("body") or ""
        # #13972 : le genre que l'AUTEUR de l'issue a declare dans le body
        # (`Grain: TIER/GENRE -- lane ...`) prime sur l'inference du titre.
        # Mesure du 2026-09-01 (lane ai-01) : `infer_genre` declarait
        # `notebook-python` pour des issues `[consolidation] notebook_tools/`
        # dont le body dit noir sur blanc `Grain: MED/docs` -- le META etait
        # servi sous restriction CONTENU.
        declared_genre = authoritative_genre(body)
        pool.append({
            "number": it["number"],
            "title": title,
            "labels": labels,
            "created_at": it["createdAt"],
            "age": age_days(it["createdAt"]),
            "idle": age_days(it["updatedAt"]),
            "updated_at": it["updatedAt"],
            "genre": declared_genre if declared_genre else infer_genre(title, labels),
            "body": body,
            "parent": parent_issue(body),
            "polarity": polarity(title, body),
            "klass": (
                "delivered" if "candidate-delivered" in labels
                else "umbrella" if is_umbrella
                else "grain"
            ),
        })
    return pool


# Fenetre d'affluence : la MEME que celle du cap de veine (`vein_cap`, par
# lane et par jour). Le cap est aveugle a la flotte -- il ne voit qu'une lane a
# la fois -- alors que la concentration observee vient surtout de plusieurs
# lanes restant CHACUNE sous son cap. Mesure du 2026-08-23 sur 308 PRs mergees
# en 3 jours : #11601 a recu 22 PRs reparties sur 8 cellules (lane x jour), et
# 6 de ces 8 cellules etaient DANS les clous. Aucun garde ne pouvait le voir.
VISITS_WINDOW_DAYS = 1
# Echelle de l'amortissement. Diviseur = 1 + log2(1 + vus / VISITS_SCALE) :
# 0 vu -> intact, 4 vus -> poids /2, 10 vus -> /2.6, 22 vus -> /3.1. Doux a 1
# vu (/1.3 : une PR du jour sur un sujet est du travail normal, pas une veine),
# mordant en tete de distribution -- qui est exactement la ou le desequilibre
# se trouve.
VISITS_SCALE = 4.0


def fetch_visits(
    days: int = VISITS_WINDOW_DAYS,
    *,
    cache: PayloadCache | None = None,
    cache_mode: str = "off",
    cache_status: dict[str, dict[str, Any]] | None = None,
) -> tuple[dict[int, int], str | None]:
    """Combien de PRs mergees par LA FLOTTE citent chaque issue sur la fenetre.

    Rend ``(compteur, erreur)``. En cas d'echec, le compteur est vide **et**
    l'erreur est non nulle : l'appelant doit dire que l'affluence n'a pas ete
    mesuree plutot que de laisser un zero d'absence de mesure se lire comme un
    zero d'affluence.

    Le filtre de date est **serveur** (`--search "merged:>=..."`), et ce n'est
    pas un detail de style. ``gh pr list --state merged --limit N`` trie par
    date de **creation** decroissante : couper a N puis filtrer sur ``mergedAt``
    cote client laisse tomber toute PR creee avant la coupe mais mergee dans la
    fenetre. Mesure du 2026-08-23 sur la meme fenetre de 24 h : 101 PRs pechees
    ainsi contre 181 reelles -- **44 % de la population absente**, et 3 des
    "ratages d'attribution" que je poursuivais n'etaient que des PRs jamais
    pechees. Cle de tri != cle de filtre est un faux silencieux.
    """
    cutoff = NOW - dt.timedelta(days=days)
    stamp = cutoff.strftime("%Y-%m-%dT%H:%M:%S+00:00")
    command = [
        "gh", "pr", "list", "--repo", REPO, "--state", "merged",
        "--limit", "400", "--search", f"merged:>={stamp}",
        "--json", "number,title,body,mergedAt",
    ]
    identity = [
        "gh", "pr", "list", "--repo", REPO, "--state", "merged",
        "--limit", "400", "--window-days", str(days),
        "--json", "number,title,body,mergedAt",
    ]

    def fetch_raw() -> list[dict]:
        raw = subprocess.run(
            command,
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True, timeout=60,
        ).stdout
        return json.loads(raw)

    try:
        prs = _cached_payload(
            "visits",
            identity,
            fetch_raw,
            cache=cache,
            cache_mode=cache_mode,
            ttl_seconds=VISITS_CACHE_TTL_SECONDS,
            cache_status=cache_status,
        )
    except (subprocess.CalledProcessError, json.JSONDecodeError,
            subprocess.TimeoutExpired, OSError) as exc:
        return {}, f"{type(exc).__name__}: {exc}"

    cache_entry = (cache_status or {}).get("visits") or {}
    cache_err = None
    if cache_entry.get("status") == "stale":
        cache_err = "cache stale apres echec du refresh: " + str(
            cache_entry.get("error") or "erreur inconnue"
        )

    if cache_entry.get("status") in {"hit", "stale"}:
        prs = [
            pr for pr in prs
            if pr.get("mergedAt")
            and dt.datetime.fromisoformat(
                pr["mergedAt"].replace("Z", "+00:00")
            ) >= cutoff
        ]
    counts: dict[int, int] = {}
    for pr in prs:
        for key in cited_issues(pr):
            counts[key] = counts.get(key, 0) + 1
    return counts, cache_err



# --- Admission : le tirage CLASSE, ce garde ADMET -------------------------
# Mesure du 2026-08-29 qui fonde ce garde. Le tirage place deja 62 % de sa
# masse au-dela de 7 jours et sous-pondere les issues du jour a 0.39x -- son
# classement n'est PAS le defaut. Mais sur 112 issues travaillees en 48 h,
# 70 avaient moins de 24 h (63 %), la ou le tirage n'en voulait que 3.9 % :
# un ecart de 16x, que le bruit d'echantillonnage n'explique pas. Le travail
# n'arrive donc pas par le tirage -- il arrive par le steering et l'auto-pick,
# deux chemins qu'aucune ponderation ne touche.
#
# D'ou la forme : un GARDE, pas un poids. Un poids se fait battre par la
# population et par le steer ; un refus s'applique quel que soit le chemin de
# selection. C'est ce que "revois completement l'organe de pick" demandait --
# pas de mieux classer, mais de cesser d'etre un simple conseil de classement.
DWELL_HOURS_DEFAULT = 24.0
URN_NAMES = {"grain", "umbrella", "delivered"}


def _csv_values(groups: list[str] | None) -> list[str]:
    """Flatten repeatable comma-separated CLI values, ignoring empty fields."""
    return [
        value.strip()
        for group in groups or []
        for value in group.split(",")
        if value.strip()
    ]


def filter_candidates(
    items: list[dict],
    *,
    exclude_issues: set[int] | None = None,
    required_labels: set[str] | None = None,
    excluded_labels: set[str] | None = None,
    min_age_days: int | None = None,
    max_age_days: int | None = None,
    min_idle_days: int | None = None,
    max_idle_days: int | None = None,
    urns: set[str] | None = None,
) -> tuple[list[dict], dict[str, Any]]:
    """Apply factual local filters and return an exact exclusion funnel."""
    exclude_issues = exclude_issues or set()
    required_labels = {label.casefold() for label in required_labels or set()}
    excluded_labels = {label.casefold() for label in excluded_labels or set()}
    urns = urns or set(URN_NAMES)
    checks = [
        ("exclude_issue", lambda item, labels: item["number"] in exclude_issues),
        ("require_label", lambda item, labels: not required_labels.issubset(labels)),
        ("exclude_label", lambda item, labels: bool(excluded_labels & labels)),
        ("min_age_days", lambda item, labels: min_age_days is not None
         and item["age"] < min_age_days),
        ("max_age_days", lambda item, labels: max_age_days is not None
         and item["age"] > max_age_days),
        ("min_idle_days", lambda item, labels: min_idle_days is not None
         and item["idle"] < min_idle_days),
        ("max_idle_days", lambda item, labels: max_idle_days is not None
         and item["idle"] > max_idle_days),
        ("urns", lambda item, labels: item["klass"] not in urns),
    ]
    excluded = {name: 0 for name, _ in checks}
    examples: dict[str, list[int]] = {name: [] for name, _ in checks}
    kept = []
    for item in items:
        labels = {str(label).casefold() for label in item.get("labels", [])}
        for name, rejects in checks:
            if rejects(item, labels):
                excluded[name] += 1
                if len(examples[name]) < 5:
                    examples[name].append(item["number"])
                break
        else:
            kept.append(item)
    excluded = {name: count for name, count in excluded.items() if count}
    examples = {name: values for name, values in examples.items() if values}
    return kept, {
        "initial": len(items),
        "final": len(kept),
        "excluded_total": len(items) - len(kept),
        "excluded": excluded,
        "examples": examples,
        "by_urn": {
            name: sum(1 for item in kept if item["klass"] == name)
            for name in sorted(URN_NAMES)
        },
    }

# Une issue portant l'une de ces etiquettes se consomme sans delai : le
# dwell existe pour empecher l'emballement d'audit, pas pour retarder un
# correctif de securite ou une regression qui casse main.
#
# Les synonymes FR sont la par PROSPECTIVE, pas par constat : mesure du
# 2026-08-29, `gh label list` ne rend qu'UNE etiquette de cette famille sur
# le depot (`security`) -- aucune etiquette FR d'urgence n'existe
# aujourd'hui. Le concern (review NanoClaw sur #13466) porte donc sur le
# jour ou quelqu'un en creera une : sur un depot dont les issues sont
# redigees en francais, `urgence` ou `securite` est la forme qu'on ecrira
# spontanement, et le bypass echouerait alors en SILENCE -- une issue
# vraiment urgente retenue 24 h par un garde cense l'exempter. Le cout de
# la prevention est une ligne ; celui de la detection serait un incident.
URGENT_LABELS = {"urgent", "blocker", "security", "regression", "p0",
                 "critical", "hotfix",
                 # variantes FR (accentuees et nues : les etiquettes
                 # GitHub acceptent les deux graphies)
                 "urgence", "bloquant", "securite", "sécurité",
                 "regression-fr", "régression", "critique"}

# Une zone qui a recu ce nombre de notebooks NEUFS sur la fenetre est saturee.
ZONE_SATURATION_MIN = 3


def _hours_old(created: str) -> float:
    born = dt.datetime.fromisoformat(created.replace("Z", "+00:00"))
    return max(0.0, (NOW - born).total_seconds() / 3600.0)


def admissibility(item: dict, balance: dict | None,
                  issue_to_family: dict[int, str] | None,
                  dwell_hours: float = DWELL_HOURS_DEFAULT) -> str | None:
    """None = admissible. Sinon la CAUSE du refus, redigee pour etre citee.

    Deux causes, et une seule est un veto dur sur la parite -- voir plus bas
    pourquoi la parite stricte n'en est pas un.
    """
    labels_lc = {str(x).lower() for x in item.get("labels", [])}
    if not (labels_lc & URGENT_LABELS):
        h = _hours_old(item.get("created_at") or NOW.isoformat())
        if h < dwell_hours:
            return ("DWELL : creee il y a {:.0f} h, seuil {:.0f} h. "
                    "Une issue d'audit ouverte ce matin n'a pas encore ete "
                    "confrontee au reste du pool -- c'est ce delai qui "
                    "distingue depiler d'emballer.".format(h, dwell_hours))

    fam = resolve_family(item, issue_to_family or {},
                         tuple((balance or {}).keys()), balance)
    if fam and item.get("polarity") == EXPANSION:
        z = (balance or {}).get(fam) or {}
        nb = z.get("new_notebooks", 0)
        con = z.get(CONSOLIDATION, 0)
        if nb >= ZONE_SATURATION_MIN and con == 0:
            msg = ("ZONE SANS REMEDE : {} a recu {} notebooks neufs sur la "
                   "fenetre et le vivier ouvert ne contient AUCUN grain de "
                   "consolidation. Ce grain en ajoute un de plus. Ouvrir ou "
                   "prendre un grain de consolidation de cette zone d'abord."
                   .format(fam, nb))
            # Ou le faux positif se cacherait, s'il y en a un : "aucun grain
            # de consolidation" est une lecture du LEXIQUE de polarite, pas
            # une lecture des intentions. Un grain NEUTRAL de la meme zone
            # peut etre une consolidation que le lexique a manquee -- on les
            # nomme pour que le refus soit refutable sur pieces, au lieu
            # d'etre a croire sur parole.
            neutres = (z.get("neutral_issues") or [])[:5]
            if neutres:
                msg += (" A verifier avant d'y croire : {} grain(s) NEUTRAL "
                        "ouvert(s) dans cette zone ({}) -- si l'un d'eux est "
                        "une consolidation que le lexique a manquee, le "
                        "remede existe et ce refus est un faux positif."
                        .format(z.get(NEUTRAL, 0),
                                ", ".join("#" + str(n) for n in neutres)))
            return msg
    return None


# Pourquoi le veto porte sur `con == 0` et non sur la parite stricte
# `con >= exp`, alors que le mandat user dit bien "autant ... que" :
# la parite stricte se mesure sur le vivier OUVERT, et consommer un grain de
# consolidation le FERME -- donc le retire du vivier et degrade le ratio.
# Un veto sur `con >= exp` punirait donc la zone precisement quand elle vient
# de faire ce qu'on lui demandait. Le veto porte sur le cas non ambigu (aucun
# remede n'existe) ; la parite graduelle reste MESUREE et affichee
# (verdict DESEQUILIBRE), parce qu'elle vise la redaction des EPICs -- c'est
# au coordinateur d'y repondre en ouvrant des grains, pas au worker d'y buter.

def weight(item: dict, prev_genre: str | None,
           visits: dict[int, int] | None = None,
           series: dict[str, dict] | None = None,
           issue_to_family: dict[int, str] | None = None) -> float:
    """Trois facteurs, tous doux, tous explicables en une ligne.

    Trop de ponderation reproduirait une monoculture avec des etapes en plus :
    on se limite a ce que les gates du variation-protocol demandent deja.
    """
    # Anciennete : sert "faire refluer doucement" -- la traine est la ou le
    # compte s'accumule. 6 mois pesent ~4x une issue de la semaine.
    w = 1.0 + math.log2(1.0 + item["age"] / 7.0)
    # Delaissement : jours depuis la DERNIERE activite, distinct de l'age de
    # creation (mesure du 2026-08-20 sur les 140 ouvertes : pearson r = 0.334,
    # donc pas redondant). 91/140 avaient bouge dans les 24 h -- le bruit du
    # moment ; les 12 plus inactives comptaient 9 EPICs. C'est cette population
    # que le tirage doit atteindre : un EPIC intouche depuis 53 j pese ~2.4x un
    # sujet du jour, assez pour remonter, trop peu pour devenir la seule veine.
    w *= 1.0 + math.log2(1.0 + item["idle"] / 14.0)
    # G-VAR-3 au tirage plutot qu'en HOLD a posteriori.
    if prev_genre and item["genre"] == prev_genre:
        w *= 0.25
    # G-VAR-1 : le plancher exige DEEP/MED **et** CONTENU.
    if item["genre"] in CONTENU:
        w *= 2.0
    # Affluence de FLOTTE : combien de PRs mergees citent deja cette issue sur
    # la fenetre, toutes lanes confondues. C'est le facteur qui manquait --
    # l'anciennete et le delaissement remontent le fond du pool, mais rien ne
    # redescendait la tete. Un sujet qui a deja recu dix grains aujourd'hui n'a
    # pas besoin du onzieme ; un sujet a zero visite garde son poids intact.
    seen = (visits or {}).get(item["number"], 0)
    if seen:
        w /= 1.0 + math.log2(1.0 + seen / VISITS_SCALE)
    item["visits"] = seen
    # Saturation de ZONE : le facteur que le compteur par issue ne peut pas
    # porter, parce qu il est defait par le partitionnement. Une fille NEUVE
    # (age 0, idle 0, aucune visite) herite ici du poids de la zone que sa
    # FRATRIE sature -- le cas exact des 9 paires de #12373. La remontee par
    # `parent` est indispensable : sans elle l amortissement ne mord que sur
    # les issues DEJA travaillees, donc jamais sur la prochaine instance.
    fam = resolve_family(item, issue_to_family or {}, tuple(series or ()),
                         series)
    nb_new = 0
    if fam:
        nb_new = ((series or {}).get(fam) or {}).get("new_notebooks", 0)
    if nb_new:
        # La saturation pousse dans les DEUX sens. Une zone qui vient de
        # recevoir cinq notebooks n'a pas besoin du sixieme -- elle a besoin
        # d'etre consolidee. Amortir sans ce miroir ecrasait le remede avec
        # le mal : mesure du 2026-08-28, #12607 (le tracker de consolidation
        # de la zone saturee) tombait a 0.36x comme les paires qu'il devait
        # solder.
        factor = 1.0 + math.log2(1.0 + nb_new / SERIES_SCALE_DEFAULT)
        if item.get("polarity") == CONSOLIDATION:
            w *= factor
        elif item.get("polarity") == EXPANSION:
            w /= factor
        else:
            w /= 1.0 + (factor - 1.0) / 2.0
    item["family"] = fam
    item["family_new_notebooks"] = nb_new
    return w


def draw(items: list[dict], n: int, rng: random.Random, prev_genre: str | None,
         visits: dict[int, int] | None = None,
         series: dict[str, dict] | None = None,
         issue_to_family: dict[int, str] | None = None) -> list[dict]:
    """Tirage pondere sans remise (Efraimidis-Spirakis : cle = u^(1/w))."""
    if not items:
        return []
    keyed = []
    for it in items:
        w = weight(it, prev_genre, visits, series, issue_to_family)
        u = rng.random() or 1e-12
        keyed.append((u ** (1.0 / w), w, it))
    keyed.sort(key=lambda t: t[0], reverse=True)
    picked = []
    for _, w, it in keyed[:n]:
        it = dict(it)
        it.pop("body", None)
        it["weight"] = round(w, 2)
        it.setdefault("visits", 0)
        it.setdefault("family", None)
        it.setdefault("family_new_notebooks", 0)
        it.setdefault("polarity", "neutral")
        picked.append(it)
    return picked


def _summarize_claim(out: str, returncode: int) -> str:
    """Reduit la sortie de ``check_lane_claim.py`` a un verdict d'une ligne.

    La sortie melange une phrase humaine (uniquement quand c'est bloque) puis
    un objet JSON. Prendre la premiere ligne telle quelle affichait ``{`` des
    que le grain etait libre -- soit exactement le cas ou le tirage a besoin
    d'un verdict lisible. On lit donc le JSON, qui porte les deux cas.
    """
    brace = out.find("{")
    if brace != -1:
        # ``raw_decode`` et pas ``loads`` : la sortie porte une phrase humaine
        # APRES l'objet (``CLEAR: no other lane claims #N.``), et ``loads``
        # echoue sur ce suffixe -- c'est ce qui laissait passer un ``{``.
        try:
            data, _ = json.JSONDecoder().raw_decode(out[brace:])
        except json.JSONDecodeError:
            data = None
        if isinstance(data, dict):
            blocking = data.get("blocking_lanes") or []
            if blocking:
                return "BLOQUE par " + ", ".join(blocking)
            if data.get("my_active_claim"):
                return "deja claim par cette lane"
            stale = data.get("stale_claims") or []
            if stale:
                return f"libre (claim perime : {', '.join(map(str, stale))})"
            return "libre"
    first = out.strip().splitlines()
    if first:
        return first[0][:60]
    return f"exit={returncode}"


def _utf8_child_env() -> dict:
    """Environnement pour un enfant **Python** dont on lit le stdout en UTF-8.

    ``encoding="utf-8"`` cote parent ne dit que comment le parent DECODE ; il
    ne dit rien de ce que l'enfant ENCODE. Un `python` enfant dont stdout est
    un tube choisit ``locale.getpreferredencoding()`` -- cp1252 sur un Windows
    francais. Le parent recoit alors du cp1252 et le decode en UTF-8 : tout
    caractere non-ASCII leve ``UnicodeDecodeError`` et tue le thread lecteur.

    Mesure (Windows FR) : un enfant imprimant un tiret cadratin rend l'octet
    isole 0x97 (cp1252) sans cette variable -- invalide en UTF-8, c'est
    exactement l'octet sur lequel le picker plantait -- et la sequence
    0xE2 0x80 0x94 avec. ``check_lane_claim.py`` rend precisement des verdicts
    en francais accentue ("claim perime", "deja claim par cette lane").

    ``PYTHONIOENCODING`` est la seule variable qui traverse la frontiere de
    process : elle instruit l'ENFANT, la ou le hook pre-commit du depot
    ("refuse NEW text=True without encoding=") ne peut regarder que le parent.
    """
    return {**os.environ, "PYTHONIOENCODING": "utf-8"}


def check_claims(numbers: list[int], lane: str) -> dict[int, str]:
    """Verif claims sur les seuls candidats tires (N appels, pas 140).

    ``--lane`` est **requis** par ``check_lane_claim.py`` : sans lui, l'appel
    sort en erreur d'usage et chaque candidat affichait ``usage: ...`` a la
    place de son verdict -- un check qui ne peut pas rougir, donc pas un check.
    """
    verdicts = {}
    for n in numbers:
        try:
            r = subprocess.run(
                [sys.executable, "scripts/check_lane_claim.py",
                 "--lane", lane, str(n)],
                capture_output=True, text=True, encoding="utf-8", timeout=60,
                env=_utf8_child_env(),
            )
            verdicts[n] = _summarize_claim(r.stdout or r.stderr or "",
                                           r.returncode)
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            verdicts[n] = f"(check indisponible: {type(exc).__name__})"
    return verdicts


def draw_unclaimed(by_class, args, rng, visits, series, issue_to_family):
    """Tire, puis REMPLACE tout candidat qu une autre lane tient deja.

    Deux raisons de remplacer plutot que d annoter :

    1. Un candidat annote << BLOQUE par X >> reste un candidat. La lane le
       lit, juge que son scope differe, et ecrit quand meme -- c est le
       profil exact des quatre collisions mesurees. Le retirer de la liste
       ne se discute pas ; un avertissement, si.
    2. Retirer sans remplacer transformerait le garde en source d idle, ce
       que la regle 4 de coordinator-discipline interdit. On retire ET on
       retire un candidat de plus dans la meme urne.

    Le cout est borne : N appels sur les tires (une poignee), jamais sur le
    pool. C est pourquoi le check pouvait etre par defaut sans etre lent --
    il etait opt-in par prudence de cout, sur une depense qui n existait pas.
    """
    urnes = (("grain", args.grains, args.prev_genre),
             ("umbrella", args.umbrellas, args.prev_genre),
             ("delivered", args.delivered, None))
    picks, claims, conflicts = [], {}, []
    for cls, want, prev in urnes:
        pool = list(by_class[cls])
        got = []
        # Borne dure : au pire on epuise l urne. Pas de while nu.
        for _ in range(len(pool) + 1):
            if len(got) >= want or not pool:
                break
            cand = draw(pool, want - len(got), rng, prev, visits,
                        series, issue_to_family)
            if not cand:
                break
            nums = [c["number"] for c in cand]
            verdicts = (check_claims(nums, args.lane)
                        if args.check_claims and args.lane else {})
            claims.update(verdicts)
            drawn = {c["number"] for c in cand}
            pool = [it for it in pool
                    if it["number"] not in drawn]
            for c in cand:
                v = verdicts.get(c["number"], "")
                if v.startswith("BLOQUE par"):
                    conflicts.append((c, "CLAIM : " + v + (
                        ". Une autre lane tient ce grain -- ecrire dessus "
                        "produirait la collision, pas le livrable. Candidat "
                        "remplace dans la meme urne.")))
                else:
                    got.append(c)
        picks.extend(got)
    return picks, claims, conflicts


def recent_delivery(picks: list[dict]) -> dict[int, str]:
    """Annote les candidats tires qu'une autre PR couvre deja -- ouverte ou mergee.

    #12174 : le label ``candidate-delivered`` est pose par un workflow
    ``schedule:`` quotidien, dans une flotte qui merge plusieurs PRs par heure
    -- au tirage de 16:47Z, #12014 etait classee ``grain`` alors que #12077
    (mergee 16:19Z) avait deja livre 3 de ses 4 items. Le body d'une issue est
    date de sa redaction et un claim ne dit rien d'une livraison : la
    recherche de PRs est la troisieme surface de grounding, et ce geste doit
    vivre dans l'outil qui propose le grain, pas dans la discipline de qui le
    lit. Une requete par candidat tire, jamais un balayage du pool.

    #12504 (rapporte par myia-po-2023:CoursIA, 2026-08-24) : ne regarder que
    les PRs **mergees** laissait un angle mort plus couteux que celui qu'on
    fermait. Une issue couverte par une PR encore **OUVERTE** ne porte aucune
    trace de livraison -- ni label, ni body a jour, ni fusion a trouver -- et
    ressort donc en tete d'urne comme un grain frais. Le tirage a place #12504
    en tete (p=2.0) alors que #12519 la couvrait depuis des heures ; la lane
    qui l'a prise a pose un claim **void**. Les deux etats se lisent dans la
    **meme** requete (``--state all``), l'invariant "une requete par candidat"
    est donc preserve.

    Priorite du signal : une PR ouverte l'emporte sur une fusion recente. Une
    fusion dit "c'est peut-etre deja fait" ; une PR ouverte dit "quelqu'un y
    est en ce moment, ton claim sera void". Une PR **fermee sans fusion** ne
    dit rien et est ignoree explicitement.

    L'annotation **n'ecarte pas** le candidat (parite avec la doctrine
    ``candidate-delivered`` : signale, ne ferme pas) : elle change ce qu'on
    en dit, pas s'il est pris. Le verrou cross-lane reste
    ``check_lane_claim.py``, que le tirage interroge desormais par defaut.
    """
    notes: dict[int, str] = {}
    for p in picks:
        n = p["number"]
        try:
            out = subprocess.run(
                ["gh", "pr", "list", "--repo", REPO, "--state", "all",
                 "--limit", "20", "--search", f"{n} in:title,body",
                 "--json", "number,state,isDraft,mergedAt"],
                capture_output=True, text=True, encoding="utf-8", check=True,
                timeout=30,
            ).stdout
            prs = json.loads(out)
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            notes[n] = f"(recherche PR indisponible: {type(exc).__name__})"
            continue
        if not prs:
            continue

        # Une PR fermee-sans-fusion n'atteste de rien : on l'ecarte ici plutot
        # que de la laisser peser dans les deux partitions ci-dessous.
        opened = [pr for pr in prs if pr.get("state") == "OPEN"]
        merged = [pr for pr in prs if pr.get("state") == "MERGED"]

        if opened:
            first = min(opened, key=lambda pr: pr["number"])
            others = [pr["number"] for pr in opened if pr["number"] != first["number"]]
            extra = f" (+{len(others)} autre(s) : " + ", ".join(
                f"#{x}" for x in others) + ")" if others else ""
            draft = " [draft]" if first.get("isDraft") else ""
            notes[n] = (f"TRAVAIL EN COURS : PR #{first['number']}{draft} OUVERTE "
                        f"couvre cette issue{extra} "
                        f"-> claim probablement VOID ; lire "
                        f"`gh pr view {first['number']}` AVANT de claimer")
            continue

        if not merged:
            continue
        latest = max(merged, key=lambda pr: pr.get("mergedAt") or "")
        when = latest.get("mergedAt") or ""
        # Fusion plus recente que la derniere activite de l'issue = le corps
        # visible est potentiellement perime par rapport au reel. Une fusion
        # ANTERIEURE a updatedAt est deja digeree par le body (ou les
        # commentaires) : pas d'annotation, sinon le signal noie.
        if when and when > p.get("updated_at", ""):
            extra = f" (+{len(merged) - 1} autres)" if len(merged) > 1 else ""
            notes[n] = (f"LIVRAISON RECENTE : #{latest['number']} mergee {when}{extra} "
                        f"(issue non mise a jour depuis {p.get('updated_at', '?')}) "
                        f"-> confronter le body au reel AVANT de dispatcher")
    return notes


# --- garde "reparer son rouge d'abord" (mandat user 2026-08-22) ------------
#
# Pourquoi ce garde vit DANS le picker et pas dans une consigne
# -------------------------------------------------------------
# Le residu de PRs anciennes ne vient pas d'un debit de merge insuffisant
# (65 PRs mergees le 2026-08-22, 100 la veille) : il vient de ce qu'une lane
# qui se reveille pioche un grain NEUF au lieu de reparer le rouge qu'elle a
# laisse. La reparation d'une PR rouge appartient a sa lane -- le coordinateur
# ne peut ni rebaser ni corriger a sa place -- donc tant que la lane ne
# revient pas dessus, la PR reste ouverte indefiniment pendant que les PRs du
# jour, elles, mergent. Une consigne de plus ne changerait rien : le picker
# est le point de passage de la selection, c'est donc lui qui doit refuser.
#
# Ce qui compte comme "rouge" -- et ce qui n'en est PAS
# -----------------------------------------------------
# Mesure du 2026-08-22 sur les 55 PRs ouvertes : la definition naive
# "au moins un check en echec" rougissait **52 PRs sur 55**, un garde qui
# refuse tout a tout le monde et se fait contourner le jour meme. La cause
# est que la flotte fait tourner des checks ADVISORY (`... advisory`,
# `fast-lane (ombre)`, `Degraded-mode confessions`) dont l'echec n'empeche
# aucun merge. Le discriminant retenu n'est pas un motif de nom -- fragile,
# et il faudrait le maintenir a chaque nouvel advisory -- mais le champ
# GraphQL `isRequired(pullRequestNumber:)`, qui dit ce que la protection de
# branche exige VRAIMENT. Avec lui : 47 PRs bloquees au lieu de 52, les 4
# ecartees ne l'etant QUE sur des advisories. Si la protection change, le
# garde suit sans edition.
#
# Trois causes bloquantes, toutes reparables par la lane :
#   1. un check REQUIS en echec        -> corriger la substance, ou relancer
#   2. `mergeable: CONFLICTING`        -> rebaser
#   3. un CHANGES_REQUESTED non leve   -> repondre / corriger
#
# L'horloge est l'AGE DE LA PR (`createdAt`), pas la date du dernier echec :
# un timestamp de check se remet a zero a chaque push, ce qui rendrait le
# garde evitable par un commit vide. L'age d'ouverture ne se falsifie pas, et
# il vise exactement la population que le user a pointee -- "les vieilles de
# plus de 12 h" qui trainent pendant que les neuves passent.

RED_HOURS_DEFAULT = 24

# ...mais l'age seul laisse passer l'essentiel. Mesure du 2026-08-23 sur les 58
# PRs bloquees de la flotte : **51 sur 58 avaient moins de 24 h**, donc etaient
# INVISIBLES a ce garde. Une lane pouvait porter 8 rouges et tirer un grain neuf
# sans que rien ne rougisse (verifie sur myia-po-2024:CoursIA-2, 8 rouges, garde
# n'en voyant qu'1). Le compte est donc le second declencheur, independant de
# l'age : au-dela de RED_COUNT_DEFAULT rouges simultanes, la lane repare avant
# de produire. Seuil choisi sur la distribution mesuree (8,8,7,6,5,5,5,2,1,1,1) :
# a 3, toutes les lanes lourdes sont prises, les legeres tirent encore.
# Mandat user 2026-08-23 : "s'il y a des dizaines de rouge, les agents ne
# devraient pas produire de nouveaux grains mais etre en train de les traiter".
RED_COUNT_DEFAULT = 3

# CANCELLED / SKIPPED / NEUTRAL sont volontairement absents : un run annule
# par `concurrency` n'est pas un echec, et le confondre avec un rouge est le
# faux positif qui rend un garde de cascade inutilisable.
CHECK_FAILED = {"FAILURE", "TIMED_OUT", "ACTION_REQUIRED", "STARTUP_FAILURE", "ERROR"}

# #13420 : un check "en vol" est celui dont la file peut encore bouger. C'est
# lui qui date la saturation -- pas la PR qui le porte. La chaine vide couvre
# le CheckRun reel, dont `conclusion` est `null` tant qu'il n'a pas conclu.
CHECK_IN_FLIGHT = {"PENDING", "QUEUED", "IN_PROGRESS", "WAITING", "EXPECTED", ""}

# #14537 : les agregateurs portent un nom IDENTIQUE quel que soit l'organe
# enfant qui tombe -- corroborer sur leur nom ne prouve jamais une cause
# commune ("plusieurs PRs echouent cet agregat" != "plusieurs PRs echouent
# pour la meme cause"). Le nom "Always-on guards" embarque en plus un compte
# d'organes qui derive ("-- 12 organes, 1 checkout"), donc meme l'identite
# nominale n'est pas stable. Le match est donc un PREFIXE pour lui, un nom
# exact pour "PR gate".
AGGREGATOR_CHECK_PREFIXES = ("Always-on guards",)
AGGREGATOR_CHECK_NAMES = {"PR gate"}

# Banniere finale de l'agregateur always-on-guards.yml : l'organe en echec
# vit dans l'ANNOTATION du check-run, pas dans son nom.
_ORGAN_BANNER_RE = re.compile(r"Organes bloquants en echec\s*:\s*([a-z_ ]+?)\s*(?:\(|$)")

_PR_STATE_FRAGMENT = """
  p%(n)d: pullRequest(number:%(n)d) {
    number mergeable
    reviews(last:40) { nodes { state submittedAt author { login } } }
    commits(last:1) { nodes { commit { statusCheckRollup {
      state   # #12830 : SUCCESS/FAILURE/PENDING/NEUTRAL au niveau rollup, pour le 3e etat file-saturation
      contexts(first:100) { nodes {
      ... on CheckRun      { name databaseId conclusion completedAt startedAt isRequired(pullRequestNumber:%(n)d) }
      ... on StatusContext { context state       createdAt              isRequired(pullRequestNumber:%(n)d) }
    } } } } } }
  }
"""


def _hours_since(iso: str) -> float:
    return (NOW - dt.datetime.fromisoformat(iso.replace("Z", "+00:00"))).total_seconds() / 3600.0


def fetch_open_prs() -> list[dict]:
    """Toutes les PRs ouvertes, avec le corps (pour y lire le tag de lane)."""
    out = subprocess.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "open", "--limit", "300",
         "--json", "number,title,body,createdAt,isDraft,author,headRefName"],
        capture_output=True, text=True, encoding="utf-8", check=True, timeout=120,
    ).stdout
    return json.loads(out)


def fetch_pr_states(numbers: list[int]) -> dict[int, dict]:
    """Etat de merge + checks (avec `isRequired`) + reviews, par lots de 8.

    Une seule requete par lot : le garde n'interroge que les PRs DE LA LANE
    (typiquement 2 a 11), jamais les 55 ouvertes.
    """
    states: dict[int, dict] = {}
    for i in range(0, len(numbers), 8):
        chunk = numbers[i:i + 8]
        query = ('query { repository(owner:"jsboige", name:"CoursIA") {'
                 + "".join(_PR_STATE_FRAGMENT % {"n": n} for n in chunk) + "} }")
        try:
            raw = subprocess.run(
                ["gh", "api", "graphql", "-f", "query=" + query],
                capture_output=True, text=True, encoding="utf-8", check=True, timeout=90,
            ).stdout
            repo = json.loads(raw)["data"]["repository"]
        except Exception:  # noqa: BLE001 - diagnostic best-effort
            continue
        for value in repo.values():
            if value:
                states[value["number"]] = value
    return states


def _ctx_stamp(ctx: dict) -> str:
    """Horodatage comparable d'un contexte. Chaine vide si le run n'a rien rendu."""
    return ctx.get("completedAt") or ctx.get("createdAt") or ctx.get("startedAt") or ""


def drop_superseded(contexts: list[dict]) -> list[dict]:
    """Retire les echecs PERIMES : un rouge anterieur au dernier vert du meme nom.

    Le discriminant est TEMPOREL, jamais nominal, et les deux erreurs symetriques
    sont documentees : dedupliquer par nom seul masque un rouge vivant emis par un
    workflow jumeau (#11894), ne pas dedupliquer du tout en fabrique de faux
    (#12054, 9 rouges pour 0 reel). La regle qui tranche les deux : un echec
    ANTERIEUR au dernier non-echec du meme nom est de l'histoire ; un echec
    CONTEMPORAIN ou posterieur est un jumeau vivant, on le garde.

    Mesure du 2026-08-22 sur #11916 : `Require genre diversity vs prev:` porte un
    FAILURE du 20/08 et un SUCCESS du 22/08 sur le meme head. Sans ce filtre le
    garde renvoyait la lane reparer un check deja vert.
    """
    newest_ok: dict[str, str] = {}
    for ctx in contexts:
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        if verdict in CHECK_FAILED:
            continue
        name = ctx.get("name") or ctx.get("context") or "?"
        stamp = _ctx_stamp(ctx)
        if stamp > newest_ok.get(name, ""):
            newest_ok[name] = stamp
    kept = []
    for ctx in contexts:
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        name = ctx.get("name") or ctx.get("context") or "?"
        if verdict in CHECK_FAILED and _ctx_stamp(ctx) < newest_ok.get(name, ""):
            continue  # rouge anterieur au dernier vert du meme nom : perime
        kept.append(ctx)
    return kept


def is_aggregator_check(name: str) -> bool:
    """Ce nom de check couvre-t-il plusieurs organes distincts (#14537) ?"""
    return (name in AGGREGATOR_CHECK_NAMES
            or name.startswith(AGGREGATOR_CHECK_PREFIXES))


def fetch_check_organs(check_run_id: int) -> list[str]:
    """Organes nommes par la banniere d'annotation de l'agregateur.

    L'agregateur termine par ``::error::Organes bloquants en echec : <organe
    organe...>`` -- c'est la seule surface qui nomme l'organe reellement tombe,
    le nom du check-run ne le porte pas. Best-effort et fail-closed : une
    annotation illisible rend [], et l'appelant exclut alors le check de la
    corroboration au lieu de le laisser corroborer par son nom.
    """
    try:
        raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/check-runs/{check_run_id}/annotations"],
            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60,
        ).stdout
        annotations = json.loads(raw)
    except Exception:  # noqa: BLE001 - reseau/parse : fail-closed, jamais un crash de picker
        return []
    organs: list[str] = []
    for ann in annotations or []:
        match = _ORGAN_BANNER_RE.search(ann.get("message") or "")
        if not match:
            continue
        for organ in match.group(1).split():
            if organ not in organs:
                organs.append(organ)
    return organs


def failed_check_keys(ctx: dict, organ_cache: dict) -> list[str]:
    """Cles de CAUSE d'un check rouge, pas de son nom de job (#14537, #14567).

    Check direct (``Scripts Tests (CPU)``) : le nom EST la cause, on le rend
    tel quel -- c'est le cas fondateur #13545 et il reste corroborable par nom.
    Agregateur (``Always-on guards``, ``PR gate``) : la cause est l'ORGANE nomme
    par l'annotation du check-run ; sans organe lisible (pas d'id, annotation
    illisible), la cle est VIDE -- fail-closed, un agregateur ne peut pas
    corroborer sur la seule foi de son nom.
    """
    name = ctx.get("name") or ctx.get("context") or "?"
    if not is_aggregator_check(name):
        return [name]
    run_id = ctx.get("databaseId")
    if run_id is None:
        return []
    if run_id not in organ_cache:
        organ_cache[run_id] = fetch_check_organs(run_id)
    return [f"{name} :: {organ}" for organ in organ_cache[run_id]]


def _failed_contexts(state: dict | None) -> list[dict]:
    """Contexts rouges vivants d'un etat GraphQL (rollup, dedup temporel)."""
    if not state:
        return []
    commits = state.get("commits", {}).get("nodes") or []
    rollup = (commits[0]["commit"].get("statusCheckRollup") if commits else None) or {}
    return [ctx for ctx in drop_superseded(
        (rollup.get("contexts", {}) or {}).get("nodes") or [])
        if (ctx.get("conclusion") or ctx.get("state") or "").upper() in CHECK_FAILED]


def impute_base_reds(states_by_number: dict[int, dict],
                     lane_by_number: dict[int, str | None],
                     organ_cache: dict | None = None,
                     unresolved_out: list[tuple[str, int]] | None = None,
                     ) -> dict[str, list[int]]:
    """Checks rouges de meme CAUSE chez >=2 LANES distinctes : imputes a la base (#13545, #14537).

    Le predicat que le garde n'avait pas : « ce rouge existe-t-il aussi sur la
    base ? ». Un check qui echoue pour la meme cause sur des lanes sans rapport
    ne peut pas etre un defaut de chacune -- elles partagent la base (mesure
    2026-08-29 : `Scripts Tests (CPU)` rouge sur 11 PRs / 4 lanes pour un seul
    test casse sur main).

    Les deux cles du predicat ont ete refaites (#14537, mesure 2026-09-03) :
    l'unite de corroboration est le TAG DE LANE du grain tag, pas
    ``author.login`` -- c'est l'identite de poussee partagee des cinq lanes
    (52 PRs sur 59 sous ``jsboige``), donc l'ancien predicat ne croisait jamais
    le cas nominal et ne tenait qu'a l'accident du compte de poussee ; et la
    cle de regroupement est la CAUSE -- l'organe nomme par l'annotation pour un
    agregateur, le nom pour un check direct -- pas le nom du job, identique
    quel que soit l'organe enfant tombe.

    Fail-closed aux deux bouts : une PR sans tag de lane lisible reste HORS
    corroboration (elle n'irait grossir aucun seau), et un agregateur sans
    organe lisible non plus -- il est signale dans ``unresolved_out`` pour que
    la sortie dise qu'elle n'a pas pu trancher, et le rouge reste a la lane,
    seul cote qui peut le reparer (#14567).

    Renvoie {cle de cause: [numeros de PRs corroborantes]} (numerotes uniques).
    """
    if organ_cache is None:
        organ_cache = {}
    failures: dict[str, dict[str, list[int]]] = {}
    for number, state in states_by_number.items():
        lane = lane_by_number.get(number)
        if not lane:
            continue  # sans tag lisible : hors corroboration (fail-closed)
        for ctx in _failed_contexts(state):
            keys = failed_check_keys(ctx, organ_cache)
            if not keys:
                if unresolved_out is not None:
                    unresolved_out.append(
                        (ctx.get("name") or ctx.get("context") or "?", number))
                continue
            for key in keys:
                failures.setdefault(key, {}).setdefault(lane, []).append(number)
    return {key: sorted({n for nums in lanes.values() for n in nums})
            for key, lanes in failures.items()
            if len(lanes) >= 2}


def _has_failed_check(state: dict | None) -> bool:
    if not state:
        return False
    commits = state.get("commits", {}).get("nodes") or []
    rollup = (commits[0]["commit"].get("statusCheckRollup") if commits else None) or {}
    contexts = drop_superseded((rollup.get("contexts", {}) or {}).get("nodes") or [])
    return any((c.get("conclusion") or c.get("state") or "").upper() in CHECK_FAILED
               for c in contexts)


def blocking_causes(state: dict, *, age_hours: float | None = None,
                    saturation_hours: float | None = None,
                    inherited: set[str] | None = None,
                    resolved_keys_by_name: dict[str, set[str]] | None = None
                    ) -> list[str]:
    """Causes qui empechent VRAIMENT le merge, formulees en geste de reparation.

    `mergeStateStatus: BLOCKED` n'est deliberement PAS une cause : il vaut
    aussi pour "en attente de review", que la lane ne peut pas lever -- c'est
    au coordinateur de merger. Verifie firsthand sur #12108 le 2026-08-22 :
    BLOCKED, MERGEABLE, zero check en echec. L'accuser aurait renvoye la lane
    reparer une PR qui n'a rien a reparer.

    `file_saturation` (issue #12830, mandant c.508-L2 + ai-01 c.1331p69) : le
    3ᵉ etat distinct de `mergeStateStatus: BLOCKED` est `BLOCKED + MERGEABLE
    + statusCheckRollup.state=PENDING > saturation_hours`. La lane pioche sur
    un pool virtuellement vide parce que ce 3ᵉ etat n'etait pas declencheur
    (mesure ai-01 du 2026-08-26T04:52Z : 1000 runs en file, 14 concurrents,
    attente observee 4 h 25 -- c'est le regime nominal, plus un cas limite).
    Le critere exige qu'AUCUN check n'ait demarre (PENDING/QUEUED partout)
    sur une PR MERGEABLE : c'est exactement la file qui n'a pas bouge, pas
    un rouge substance. La cause est formulee comme geste = commentaire
    + `--ignore-red` ou `rerun/updater-branch` selon le cas -- la lane peut
    poser un acte (commenter) mais ne peut pas derainer la file seule.

    Le critere reste PASSIF si `age_hours` ou `saturation_hours` ne sont pas
    fournis (defaut=None), ce qui preserve la signature utilisee par les 12
    tests existants (cf `_state(...)` qui ne porte pas `age_hours`).
    """
    causes: list[str] = []
    advisory: list[str] = []
    commits = state.get("commits", {}).get("nodes") or []
    rollup = (commits[0]["commit"].get("statusCheckRollup") if commits else None) or {}
    contexts = drop_superseded((rollup.get("contexts", {}) or {}).get("nodes") or [])
    for ctx in contexts:
        name = ctx.get("name") or ctx.get("context") or "?"
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        if verdict not in CHECK_FAILED:
            continue
        if inherited:
            # #13545/#14537 : rouge impute a la base (cause commune corroboree
            # chez >=2 lanes distinctes) -- pas reparable par cette lane. Pour
            # un agregateur, l'appartenance se teste sur ses CAUSES resolues
            # (organes), pas sur son nom identique quel que soit l'organe tombe.
            # Un aggregateur partiellement herite (un organe a la base, un autre
            # a la lane) reste une cause : la lane doit encore reparer le sien.
            keys = (resolved_keys_by_name or {}).get(name) or {name}
            if keys <= inherited:
                continue
        if ctx.get("isRequired"):
            cause = f"check requis en echec : {name}"
            if cause not in causes:
                causes.append(cause)
        elif name not in advisory:
            advisory.append(name)
    if state.get("mergeable") == "CONFLICTING":
        causes.append("conflits avec main -> rebaser")
    latest: dict[str, dict] = {}
    for review in (state.get("reviews", {}) or {}).get("nodes") or []:
        if review["state"] in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            latest[review["author"]["login"]] = review
    for login, review in latest.items():
        if review["state"] == "CHANGES_REQUESTED":
            causes.append(f"CHANGES_REQUESTED non leve ({login})")
    # 3ᵉ declencheur `file_saturation` (cf issue #12830) : aucun check n'a
    # demarre (PENDING/QUEUED partout), pas de conflit, pas de CHANGES_REQUESTED
    # non leve, et la PR est ouverte depuis plus de `saturation_hours`.
    # On ne l'ajoute que si rien d'autre n'a deja ete trouve : un rouge
    # substance prime sur la file-saturation (la lane reparera la substance,
    # la file draine naturellement).
    if (age_hours is not None and saturation_hours is not None
            and age_hours >= saturation_hours
            and state.get("mergeable") == "MERGEABLE"
            and not causes
            and contexts):
        statuses = {(c.get("conclusion") or c.get("state") or "").upper() for c in contexts}
        if statuses <= {"PENDING", "QUEUED", ""}:
            causes.append(
                f"file_saturation : {len(contexts)} check(s) tous pending depuis > "
                f"{int(saturation_hours)}h (faux-rouge non-reparable par la lane -- "
                f"commenter la PR + --ignore-red ou rerun/updater-branch si gel CI)"
            )
    if causes and advisory:
        # #13545 : l'advisory n'est pas une seconde panne independante --
        # c'est la CAUSE probable du requis rouge au-dessus (PR gate est un
        # agregateur : il est rouge PARCE QUE Scripts Tests l'est). Dire le
        # lien plutot que deux lignes qui se contredisent (« requis en
        # echec » vs « non bloquant ») sur le meme rouge.
        causes.append("(diagnostic, non bloquant : " + ", ".join(advisory[:3])
                      + " -- cause probable du requis ci-dessus, reparer UNE cause)")
    return causes


def _is_adjacency_red(body: str) -> bool:
    """Verdict LIGHT-genre adjacency pour le corps d'une PR rouge (#13967).

    Pont entre l'organe `scripts/ci/variation_adjacency_guard.py` (verdict
    G-VAR-3, fail-CLOSED sur `genre == prev_genre` dans la liste LIGHT) et
    le picker : la branche d'affichage specialisee `print_red_assignment`
    se declenche SI ET SEULEMENT SI tous les rouges sont detenus par cette
    cause. Enveloppe tolérante : si l'organe est indisponible (import,
    panne), on rend False -- les trois conseils generiques restent le
    fallback sur, jamais un crash de picker.
    """
    try:
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / "ci"))
        import variation_adjacency_guard as vag  # noqa: PLC0415 - import tardif volontaire
    except Exception:  # noqa: BLE001 - le picker ne doit jamais casser sur l'organe
        return False
    try:
        verdict = vag.check(body)
    except Exception:  # noqa: BLE001 - idem : organe optionnel, picker robuste
        return False
    # L'organe est fail-CLOSED : blocking=True <=> LIGHT adjacency reelle
    # (cf docstring `check`). On conserve `adjacent` pour les diagnostics
    # futurs (DEEP/MED adjacency = advisory, hors branche specialised).
    return bool(verdict.get("blocking"))


def _newest_start_hours(stamps) -> float | None:
    """Age, en heures, du demarrage le PLUS RECENT parmi `stamps` (ISO-8601).

    None si aucun horodatage n'est lisible -- l'appelant retombe alors sur
    l'age de la PR. On prend le plus RECENT et non le plus ancien : la
    question posee est "la file a-t-elle bouge recemment ?", a laquelle un
    seul check parti il y a 5 min repond oui, meme si dix autres attendent
    depuis la veille.
    """
    best = None
    for s in stamps:
        if not s:
            continue
        try:
            when = dt.datetime.fromisoformat(str(s).replace("Z", "+00:00"))
        except ValueError:
            continue
        hours = (dt.datetime.now(dt.timezone.utc) - when).total_seconds() / 3600.0
        if best is None or hours < best:
            best = hours
    return best


def file_saturation_cause(state: dict, age_hours: float, threshold_hours: float) -> str | None:
    """#12830 : detecte le 3e etat -- PR non-mergeable non par rouge substance,
    non par attente-coordinateur (BLOCKED+MERGEABLE+zero-fail, cf #12108),
    mais par **saturation file** : tous les checks requis PENDING depuis
    longtemps sans qu'aucun n'ait demarre. Cause = "faux-rouge" : la lane ne
    peut pas la reparer (c'est l'infra CI), geste = commenter la PR (cause)
    + --ignore-red ou re-run via api, pas un push muet qui ne leve rien.

    Critere (tous requis) :
      1. mergeable=MERGEABLE (pas de conflit git)
      2. statusCheckRollup.state EXPLICITEMENT "PENDING" (pas None : les
         fixtures de test sans rollup.state ne sont pas des saturations
         file, juste des PRs sans rollup tracke)
      3. >=1 check requis existe (sans ca, c'est juste un PR sans CI)
      4. Aucun check requis en FAIL (sinon c'est un rouge substance classique)
      5. le check requis PENDING le PLUS RECEMMENT DEMARRE l'a ete il y a
         >= saturation_hours (defaut 24 h, configurable --saturation-hours)

    Le critere 5 date les **checks**, pas la PR (#13420). Une PR ouverte
    depuis 121 h dont la CI vient de re-declencher il y a 25 min n'est pas
    saturee : sa file avance. Datee sur l'age de la PR -- ce que faisait ce
    detecteur -- elle etait annoncee "PENDING depuis >24h, cause infra", et
    le geste prescrit (`--ignore-red` ou re-run) etait exactement le mauvais :
    re-run RE-EMPILE dans la file que le message dit saturee, et --ignore-red
    pousse la lane devant un garde qui allait repondre. Mesure du 2026-08-29 :
    #12757 (ouverte 121 h) et #12850 (109 h) etaient annoncees saturees alors
    que leurs checks avaient demarre a 11:39:44Z, soit 25 min plus tot.

    Quand aucun horodatage n'est lisible, on retombe sur l'age de la PR
    (comportement historique) : un champ absent ne doit pas eteindre le
    detecteur, seulement le priver de sa precision.

    Retourne la cause formulee, ou None.
    """
    if age_hours < threshold_hours:
        return None
    if state.get("mergeable") != "MERGEABLE":
        return None  # conflit git = rouge classique, pas file-saturation
    commits = state.get("commits", {}).get("nodes") or []
    rollup = (commits[0]["commit"].get("statusCheckRollup") if commits else None) or {}
    rollup_state = (rollup.get("state") or "").upper()
    # Distinction explicite : "champ absent" (None, fixtures legacy) ne doit
    # PAS etre lu comme PENDING, sinon les tests historiques et les fixtures
    # in-memory cassent. PENDING reel = la chaine "PENDING" du rollup GitHub.
    if rollup_state != "PENDING":
        return None
    required_checks = []
    stamps = []
    for ctx in drop_superseded((rollup.get("contexts", {}) or {}).get("nodes") or []):
        if ctx.get("isRequired"):
            verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
            if verdict in CHECK_FAILED:
                # Rouge substance detecte, blocking_causes le prendra ; on ne
                # double pas la cause.
                return None
            required_checks.append(ctx.get("name") or ctx.get("context") or "?")
            if verdict in CHECK_IN_FLIGHT:
                # Check encore en vol : c'est SON demarrage qui date la file.
                stamps.append(ctx.get("startedAt") or ctx.get("createdAt"))
    if not required_checks:
        # Aucun check requis : pas un "faux-rouge CI sature", juste pas de CI.
        return None
    newest = _newest_start_hours(stamps)
    if newest is not None and newest < threshold_hours:
        # La file AVANCE : un check requis a demarre recemment. Le bon geste
        # est d'attendre, pas de re-run (qui re-empile) ni d'--ignore-red.
        return None
    n = len(required_checks)
    return (f"file-saturation : {n} check(s) requis en PENDING depuis "
            f">{threshold_hours:.0f}h (cause infra, pas substance ; "
            f"geste = commenter la PR + --ignore-red ou re-run)")


def unaddressed_review_points(numbers: list[int]) -> dict[int, int]:
    """Points de review non leves, par PR. Delegue a l'organe du merge-gate B.0.

    Mandat user 2026-08-24 : une lane ne produit plus tant qu'il lui reste des
    points a traiter sur ses vieilles PRs, et ces points lui sont proposes EN
    PREMIER a chaque cycle.

    Pourquoi deleguer plutot que redetecter : les trois surfaces qui portent la
    substance des reviews sur ce depot (nits du user en issue comments, reserves
    d'Hermes en prefixe de body sous `state: COMMENTED`, threads inline dans
    `reviewThreads`) sont invisibles a `reviews[].state`. Un jeu de motifs
    ecrit ici sous-compterait en silence -- et un detecteur qui sous-compte rend
    un chiffre plus petit et plus propre, sans jamais lever d'erreur. Le meme
    organe sert donc le pre-merge et le pre-tirage : s'ils divergeaient, une
    lane pourrait etre autorisee a tirer sur une PR que le merge-gate refuse.

    Panne d'import ou de reseau : dictionnaire vide plutot qu'une exception. Le
    garde ne doit jamais empecher un tirage pour une raison technique -- mais
    l'appelant DIT que la surface n'a pas ete regardee (cf `nits_unavailable`).
    """
    if not numbers:
        return {}
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    import check_unaddressed_nits as nits  # noqa: PLC0415 - import tardif volontaire

    now = dt.datetime.now(dt.timezone.utc)
    out: dict[int, int] = {}
    for n in numbers:
        try:
            data = nits.gh_json(["pr", "view", str(n), "--repo", REPO,
                                 "--json", nits.FIELDS])
            result = nits.analyse(
                data, nits.review_threads(n), now,
                issue_created=nits.gh_issue_created,
                dismissed_improperly=nits.improper_dismissals(n))
        except Exception:  # noqa: BLE001 - une PR illisible ne bloque pas les autres
            continue
        if result.get("blocked"):
            out[n] = len(result.get("blocking") or [])
    return out


def unattributed_blocked_prs(prs: list[dict] | None = None) -> list[dict]:
    """PRs ouvertes bloquees sans tag `Grain:` lisible, AVEC leur route.

    Extraction du calcul historique de `red_backlog` (les untagged ne peuvent
    jamais appartenir a une lane, donc l'ensemble est lane-independant) pour
    que le mode `--orphans-report` et le garde partagent la meme detection --
    deux implementations de la meme question finiraient par diverger, et la
    divergence d'un detecteur se voit toujours du cote du sous-comptage.

    Enrichit l'entree historique (numero, titre, age) de `author` et `branch` :
    un constat sans destinataire n'est pas un routage (#13086). Les untagged
    SANS causes bloquantes ne comptent pas : seule la file qui pourrit est
    routee, pas les PRs en cours de CI.
    """
    if prs is None:
        prs = fetch_open_prs()
    untagged = [pr for pr in prs
                if not pr.get("isDraft") and parse_grain_tag(pr.get("body") or "") is None]
    untagged_states = fetch_pr_states([pr["number"] for pr in untagged]) if untagged else {}
    out = []
    for pr in untagged:
        state = untagged_states.get(pr["number"])
        if state is None or not blocking_causes(state):
            continue
        out.append({"number": pr["number"], "title": pr["title"],
                    "author": ((pr.get("author") or {}).get("login")) or "inconnu",
                    "branch": pr.get("headRefName") or "?",
                    "age_hours": round(_hours_since(pr["createdAt"]))})
    out.sort(key=lambda r: -r["age_hours"])
    return out


def red_backlog(lane: str, threshold_hours: float,
                count_threshold: int = RED_COUNT_DEFAULT,
                saturation_hours: float | None = None) -> dict:
    """PRs de la lane reellement bloquees, avec QUATRE declencheurs de refus.

    `aged` : au moins une rouge ouverte depuis plus de `threshold_hours` --
    la queue longue, celle qui pourrit. `count` : au moins `count_threshold`
    rouges simultanees quel que soit leur age -- le tas, que le seul critere
    d'age ne voyait pas (51/58 invisibles, mesure du 2026-08-23). `nits` : au
    moins un point de review non leve, quel que soit l'age et le nombre.
    `saturation` (#12830) : au moins une PR file-saturated (MERGEABLE mais
    rollup PENDING depuis >saturation_hours, sans rouge substance) -- le
    3e etat qu'on ratait (cf #12108 fondateur : BLOCKED+MERGEABLE+zero-fail
    volontairement ignore pour ne pas piéger la lane sur l'attente-coordinateur,
    mais cette exclusion avalait aussi les file-saturations infra-side).

    Le troisieme n'est pas un ajout de perimetre : il PRESERVE une semantique
    qui existait avant. Le filtre d'age s'appliquait en amont, donc une PR
    portant des points de review non leves n'entrait dans `red` que si elle
    etait deja vieille. Retirer ce filtre pour le declencheur `count` ferait
    tomber les PRs recentes a points non leves dans `red` sans qu'elles
    declenchent quoi que ce soit -- un affaiblissement silencieux du mandat
    user du 2026-08-24 (« les agents ne produisent plus tant qu'il leur reste
    des points a traiter »). Le declencheur `nits` rend cette regle explicite
    au lieu de la laisser dependre d'un filtre retire ailleurs.

    `file_saturation` (issue #12830) : au moins une PR file-saturee (cf
    `blocking_causes` pour le critere exact) ouverte depuis plus de
    `threshold_hours`. C'est le 3ᵉ etat distinct de `mergeStateStatus:
    BLOCKED` (le `BLOCKED + MERGEABLE + checks tous PENDING depuis > N h`)
    que le picker ratait jusqu'ici, et la lane po-2027 en etait la premiere
    victime : narrow persistant ×27 cycles dont la file CI etait la cause
    jamais diagnostiquee. Le declencheur precede `aged` parce qu'il est
    l'attribution directe du narrow : la lane doit SAVOIR qu'elle subit la
    file avant de tenter d'autres rouges.

    Rend aussi `unattributed_blocked` : les PRs bloquees dont le tag `Grain:`
    est illisible. Elles ne peuvent bloquer AUCUNE lane -- c'est la bonne
    arithmetique (deviner une lane serait pire) -- mais les taire donnerait a
    croire que le garde couvre tout l'ouvert. Il ne le couvre pas : leur tag
    manquant est lui-meme le defaut a corriger.
    """
    try:
        prs = fetch_open_prs()
    except Exception as exc:  # noqa: BLE001 - le garde ne doit jamais bloquer sur une panne reseau
        sat_threshold = saturation_hours if saturation_hours is not None else threshold_hours
        return {"unavailable": f"{type(exc).__name__}", "red": [],
                "triggers": [], "unattributed_blocked": [],
                "nits_unavailable": None, "base_inherited": [],
                "base_unresolved": [],
                "saturation_hours": sat_threshold}

    mine, others = [], []
    sat_threshold = saturation_hours if saturation_hours is not None else threshold_hours
    for pr in prs:
        if pr.get("isDraft"):
            continue
        # Plus de filtre d'age ici : une rouge recente compte pour le
        # declencheur `count`. Le tri par age se fait apres l'analyse.
        tag = parse_grain_tag(pr.get("body") or "")
        pr_lane = tag.get("lane") if tag else None
        (mine if pr_lane == lane else others).append(pr)

    states = fetch_pr_states([pr["number"] for pr in mine])
    try:
        nits_by_pr = unaddressed_review_points([pr["number"] for pr in mine])
        nits_unavailable = None
    except Exception as exc:  # noqa: BLE001
        nits_by_pr, nits_unavailable = {}, f"{type(exc).__name__}"
    # #13545 : imputation a la base. Le garde n'interroge les etats que de la
    # lane par cout (docstring fetch_pr_states) ; on ne paie l'echantillon
    # etranger QUE si la lane porte un check rouge a imputer ou non, et borne
    # (16 PRs les plus recentes = 2 lots GraphQL) pour que le garde reste
    # bon marche meme sur un ouvert charge.
    # #14537 : l'unite de corroboration est le TAG DE LANE (author.login est
    # l'identite de poussee partagee des cinq lanes), la cle de regroupement
    # est la CAUSE (organe resolu pour un agregateur, nom sinon), et les
    # agregateurs non resolvables sont dits au lieu de corroborer par nom.
    lane_by: dict[int, str | None] = {}
    for pr in mine + others:
        lane_by[pr["number"]] = (parse_grain_tag(pr.get("body") or "") or {}).get("lane")
    organ_cache: dict[int, list[str]] = {}
    unresolved_aggregates: list[tuple[str, int]] = []
    inherited: dict[str, list[int]] = {}
    if any(_has_failed_check(states.get(pr["number"])) for pr in mine):
        sample = sorted(others, key=lambda p: p.get("createdAt") or "",
                        reverse=True)[:16]
        foreign_states = fetch_pr_states([p["number"] for p in sample])
        inherited = impute_base_reds({**states, **foreign_states}, lane_by,
                                     organ_cache=organ_cache,
                                     unresolved_out=unresolved_aggregates)
    red = []
    for pr in mine:
        state = states.get(pr["number"])
        if state is None:
            continue
        # age_hours sert au critere file_saturation (cf blocking_causes). On le
        # passe ici plutot que dans la query GraphQL parce que le fragment
        # `_PR_STATE_FRAGMENT` ne porte pas `createdAt` et l'ajouter alourdirait
        # chaque appel pour 2 octets deconomie ; le PR-listing le fournit deja.
        age = _hours_since(pr["createdAt"])
        # Cles de cause des checks rouges de CETTE PR -- necessaires seulement
        # si quelque chose est herite : sans heritage l'appartenance n'est
        # jamais testee, et on ne paie aucune resolution d'annotation.
        keys_by_name: dict[str, set[str]] | None = None
        if inherited:
            keys_by_name = {}
            for ctx in _failed_contexts(state):
                ctx_name = ctx.get("name") or ctx.get("context") or "?"
                keys_by_name.setdefault(ctx_name, set()).update(
                    failed_check_keys(ctx, organ_cache))
        causes = blocking_causes(state, age_hours=age, saturation_hours=threshold_hours,
                                 inherited=set(inherited),
                                 resolved_keys_by_name=keys_by_name)
        n_nits = nits_by_pr.get(pr["number"], 0)
        if n_nits:
            # Un point de review non leve est une cause A PART ENTIERE : la PR
            # peut etre verte et sans conflit et rester non mergeable (B.0).
            causes.insert(0, f"{n_nits} point(s) de review non leve(s) -> repondre, "
                             f"corriger en citant le commit, ou ouvrir une issue de suivi nommee")
        # #12830 : 3e etat file-saturation (cf docstring file_saturation_cause).
        # Seuil par defaut = threshold_hours (meme qu'aged) pour ne pas creer
        # un nouveau param a retenir ; surchargeable via --saturation-hours.
        sat_threshold = saturation_hours if saturation_hours is not None else threshold_hours
        sat_cause = file_saturation_cause(state, _hours_since(pr["createdAt"]), sat_threshold)
        if sat_cause:
            causes.append(sat_cause)
        if causes:
            # #13967 : verdict adjacency par organe. La cause ROUGE la plus
            # frequente (mesure 2026-09-01 = 13/25) etait silencieusement
            # recouverte par les trois conseils generiques (update-branch /
            # rebase / pousser) -- invariants au predicat, donc la lane qui
            # les suit BOUCLE. Le picker dispose deja du corps de la PR
            # (`pr["body"]` -- porte du `Grain:`), donc on appelle
            # `variation_adjacency_guard.check` localement : fonction pure,
            # pas de `gh` round-trip, cout negligible vs les 2 lots GraphQL
            # dejas payes dans `red_backlog`. On preserve le contrat
            # d'override (un caller externe peut poser `is_adjacency=False`
            # pour court-circuiter -- utile pour les tests pinnes qui ne
            # veulent pas re-parser un body realiste).
            if "is_adjacency" in pr:
                is_adj = bool(pr["is_adjacency"])
            else:
                is_adj = _is_adjacency_red(pr.get("body") or "")
            red.append({"number": pr["number"], "title": pr["title"],
                        "age_hours": round(age),
                        "causes": causes,
                        "is_adjacency": is_adj})
    red.sort(key=lambda r: -r["age_hours"])

    triggers = []
    if any(nits_by_pr.get(r["number"]) for r in red):
        # D'abord dans la liste : c'est l'ordre dans lequel le mandat du
        # 2026-08-24 veut que la lane les traite.
        triggers.append("nits")
    # `file_saturation` precede `aged` : une PR file-saturee est l'attribution
    # directe d'un narrow de file CI (cf issue #12830), et la lane doit
    # distinguer ce cas des rouges substance. Le critere dans `blocking_causes`
    # exige que rien d'autre ne soit deja en cause -- si la PR a un FAIL
    # substance ET est en file-saturation, elle reste categorisee rouge
    # substance (cause FAIL gagne).
    file_saturated = [r for r in red
                       if any("file_saturation" in c for c in r["causes"])
                       and r["age_hours"] >= threshold_hours]
    if file_saturated:
        triggers.append("file_saturation")
    aged = [r for r in red if r["age_hours"] >= threshold_hours]
    if aged:
        triggers.append("aged")
    if len(red) >= count_threshold:
        triggers.append("count")
    # #12830 : declencheur saturation, distinct de count/aged/nits pour qu'une
    # PR file-saturated isolee (pas de rouge substance, pas de point review)
    # puisse declencher le refus quand meme.
    if any("file-saturation" in c for r in red for c in r["causes"]):
        triggers.append("saturation")

    unattributed = unattributed_blocked_prs(prs)
    # Les NUMEROS, pas un compte : le coordinateur est le seul a pouvoir les
    # reprendre (cf skill coordinate, phase 3.5), et un compte ne se traite pas.
    unresolved_by_name: dict[str, set[int]] = {}
    for name, number in unresolved_aggregates:
        unresolved_by_name.setdefault(name, set()).add(number)
    return {"red": red, "aged": aged, "triggers": triggers,
            "red_hours": threshold_hours, "red_count_threshold": count_threshold,
            "saturation_hours": sat_threshold,
            "unattributed_blocked": unattributed,
            "base_inherited": [{"check": name, "corroborated_by": nums}
                               for name, nums in sorted(inherited.items())],
            # #14567 : quand un agregateur n'a pas pu etre tranche, le dire --
            # sinon l'absence d'imputation se lirait comme une acquittement.
            "base_unresolved": [{"check": name, "prs": sorted(nums)}
                                for name, nums in sorted(unresolved_by_name.items())],
            "nits_unavailable": nits_unavailable}


def print_base_inherited(backlog: dict) -> None:
    """Rouges imputes a la base (#13545) : une tache COORDINATEUR, pas lane.

    Mesure fondatrice 2026-08-29 : un test casse sur main s'est presente comme
    11 defauts de PR independants sur 4 lanes -- chaque lane envoyee reparer
    ce qu'elle n'a pas casse et ne peut pas atteindre, pendant que le seul
    reparateur possible (main) n'etait assigne a personne. Ces rouges ne
    comptent plus dans le refus ; ils sont dits ici, une fois, avec leurs
    corroborations, pour que la base ait un destinataire.
    """
    items = backlog.get("base_inherited") or []
    unresolved = backlog.get("base_unresolved") or []
    if not items and not unresolved:
        return
    print("ROUGE IMPUTE A LA BASE -- pas le votre, pas reparable par la lane :")
    for item in items:
        wits = ", ".join(f"#{n}" for n in item["corroborated_by"][:6])
        more = "" if len(item["corroborated_by"]) <= 6 else ", ..."
        print(f"  - {item['check']} : corrobore par {wits}{more}")
    if items:
        print("Ces rouges ne comptent pas dans le refus. La cause est sur main :")
        print("tache COORDINATEUR (unique reparateur possible), a router sur le")
        print("dashboard ou en DM ai-01.")
    # #14567 : fail-closed dit a voix haute. Un agregateur dont l'organe n'a
    # pas pu etre lu ne corrobore RIEN -- le rouge reste a la lane, seul cote
    # qui peut le reparer ; le taire ferait de l'echec de mesure une acquittement.
    for item in unresolved:
        prs = ", ".join(f"#{n}" for n in item["prs"][:6])
        print(f"  - {item['check']} : organe non lisible sur {prs} -- pas pu")
        print(f"    trancher, le rouge RESTE a la lane (relancer le run ou lire")
        print(f"    l'annotation du check-run avant d'invoquer la base).")
    print()


def print_nits_gap(backlog: dict) -> None:
    """Dire qu'une surface n'a pas ete regardee, plutot que la taire.

    Sans cette ligne, une panne de l'organe rend le meme silence qu'une lane
    sans point en souffrance : un zero de denominateur se lirait comme un zero
    de numerateur, et la lane tirerait un grain neuf en croyant son ardoise
    propre.
    """
    if not backlog.get("nits_unavailable"):
        return
    print(f"ATTENTION -- les points de review n'ont PAS pu etre lus "
          f"({backlog['nits_unavailable']}).")
    print("Ce tirage ne prouve donc pas que l'ardoise de la lane est propre.")
    print("Verifier a la main : `python scripts/check_unaddressed_nits.py <N>`")
    print("sur chaque PR ouverte de la lane avant de produire du neuf.")
    print()


def print_unattributed_blocked(backlog: dict) -> None:
    """Dire ce que le garde NE couvre PAS : les PRs bloquees sans tag lisible.

    Ces PRs ne sont imputables a aucune lane (deviner la lane serait pire), donc
    elles ne bloquent personne -- mais les taire donne a croire que le garde
    couvre tout l'ouvert. Il ne le couvre pas, et le tag manquant est lui-meme
    le defaut a corriger (le coordinateur peut les reprendre via `skill
    coordinate` phase 3.5). Cf #12738 : avant le fix, ce paragraphe vivait
    dans `print_red_assignment` et n'apparaissait que sur le chemin de la
    reparation, pas
    sur le chemin du tirage -- verdict non cable a sa preuve sur le chemin
    ou il sert.
    """
    if not backlog.get("unattributed_blocked"):
        return
    numbers = ", ".join(f"#{u['number']}" for u in backlog["unattributed_blocked"])
    print(f"Portee : {len(backlog['unattributed_blocked'])} autre(s) PR(s) "
          f"bloquee(s) ({numbers})")
    print("n'ont pas de tag")
    print("`Grain:` lisible et ne sont donc imputables a aucune lane -- ce garde ne")
    print("les voit pas. Leur tag manquant est lui-meme le defaut a corriger.")
    print()


ORPHANS_MARKER_START = "<!-- GRAIN-ORPHANS-SWEEP:START -->"
ORPHANS_MARKER_END = "<!-- GRAIN-ORPHANS-SWEEP:END -->"


def build_orphans_comment(orphans: list[dict]) -> str:
    """Corps marker-guarde du balayage des orphelines du tag Grain (#13086).

    Un orphelin n'est imputable a aucune lane (deviner la lane serait pire),
    donc aucun garde ne le proposera jamais : ce commentaire EST le routage.
    Il nomme chaque PR avec auteur et branche pour un dispatch nomme, une
    reparation directe, ou une fermeture assumee (skill coordinate, point 5).
    Upsert marker-guarde : un seul commentaire mis a jour sur place, jamais un
    flot quotidien -- et le cas vide s'ecrit aussi, parce qu'un balayage muet
    est indiscernable d'un balayage mort.
    """
    stamp = NOW.strftime("%Y-%m-%dT%H:%MZ")
    lines = [ORPHANS_MARKER_START]
    if not orphans:
        lines += [
            f"**File d'orphelines : 0.** Toute PR ouverte sans tag `Grain:` "
            f"lisible porte son tag manquant comme seul defaut ; aucune n'est "
            f"bloquee a l'instant du balayage ({stamp}).",
            ORPHANS_MARKER_END,
        ]
        return "\n".join(lines)
    lines.append(f"**File d'orphelines : {len(orphans)} PR(s) ouverte(s) bloquee(s) "
                 f"sans tag `Grain:` lisible** ({stamp}). Imputables a aucune "
                 f"lane, aucun garde ne les proposera : le tag manquant EST le "
                 f"defaut -- ajouter le tag, reparer, ou fermer en le disant. "
                 f"Regroupees par auteur pour dispatch nomme :")
    lines.append("")
    by_author: dict[str, list[dict]] = {}
    for r in orphans:
        by_author.setdefault(r["author"], []).append(r)
    for author in sorted(by_author, key=lambda a: (-len(by_author[a]), a)):
        lines.append(f"- **{author}** ({len(by_author[author])}) :")
        for r in by_author[author]:
            lines.append(f"  - #{r['number']} ({r['age_hours']} h, branche `{r['branch']}`) — {r['title']}")
    lines += ["", f"_Recalcul a la demande : `python scripts/pick_idle_grain.py "
                  f"--orphans-report`. Cf #13086._", ORPHANS_MARKER_END]
    return "\n".join(lines)


def upsert_orphans_comment(number: int, body: str) -> None:
    """Un seul commentaire marker-guarde par issue, mis a jour sur place."""
    comments = json.loads(subprocess.run(
        ["gh", "issue", "view", str(number), "--repo", REPO,
         "--json", "comments"],
        capture_output=True, text=True, encoding="utf-8", check=True, timeout=60,
    ).stdout)
    cid = next((c["id"] for c in (comments.get("comments") or [])
                if ORPHANS_MARKER_START in (c.get("body") or "")), None)
    if cid is not None:
        subprocess.run(
            ["gh", "api", f"repos/{REPO}/issues/comments/{cid}",
             "-X", "PATCH", "-f", f"body={body}"],
            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60)
    else:
        subprocess.run(
            ["gh", "issue", "comment", str(number), "--repo", REPO,
             "--body-file", "-"],
            input=body, capture_output=True, text=True, encoding="utf-8",
            check=True, timeout=60)


def print_red_assignment(lane: str, backlog: dict, threshold_hours: float) -> None:
    red = backlog["red"]
    triggers = backlog.get("triggers") or []
    aged = backlog.get("aged") or []
    n_nits = sum(1 for r in red
                 if any("point(s) de review" in c for c in (r.get("causes") or [])))
    motifs = []
    if "nits" in triggers:
        # En tete : c'est la seule cause qu'un `gh pr update-branch` ne levera
        # jamais -- ce qui leve une remarque est une phrase, pas un SHA.
        motifs.append(f"porte {n_nits} PR(s) a points de review non leves")
    if "count" in triggers:
        motifs.append(f"porte {len(red)} PR(s) bloquee(s) simultanees (seuil "
                      f"{backlog.get('red_count_threshold', RED_COUNT_DEFAULT)})")
    if "aged" in triggers:
        motifs.append(f"porte {len(aged)} PR(s) bloquee(s) ouverte(s) depuis plus "
                      f"de {threshold_hours:g} h")
    print(f"GRAIN DU CYCLE -- lane {lane} : reparer ses propres PRs.")
    print("Motif : la lane " + ", ".join(motifs) + ".")
    print()
    print("Ce n'est PAS un refus de tirage : le travail de ce cycle est nomme")
    print("ci-dessous. Aucune sortie de cet outil n'autorise une lane a ne rien")
    print("produire -- ni celle-ci, ni un tirage dont aucun candidat ne plait.")
    print()
    print_nits_gap(backlog)
    print("Reprendre ses propres PRs est la PREMIERE tache du cycle, avant tout")
    print("grain neuf : la PR ne peut etre reparee que par sa lane, le")
    print("coordinateur ne peut ni rebaser, ni corriger, ni repondre a sa place.")
    print()
    for item in red:
        print(f"  #{item['number']}  ouverte depuis {item['age_hours']} h  -- {item['title'][:66]}")
        for cause in item["causes"]:
            print(f"       {cause}")
    print()
    if red and all(r.get("is_adjacency") for r in red):
        # #13967 : quand la cause du rouge est `adjacency` (G-VAR-3, mesure
        # du 2026-09-01 = 13 PRs / 25 rouges mesurables = premiere cause de
        # rouge de la flotte), les trois conseils generiques
        # (`update-branch` / rebase / pousser) sont invariants au predicat
        # (aucun ne modifie le `prev_genre` ni le `genre` courant), donc
        # aucun ne leve le blocage. L'organe `variation_adjacency_guard`
        # produit deja le bon message (« piochez un grain d'UN AUTRE genre,
        # ne retaguez pas le meme travail ») -- ici on le dit EN CLAIR
        # pour que la lane ne perde pas son cycle a pousser une PR dont
        # la cause est ailleurs.
        print("Cause determinante : `adjacency` (G-VAR-3, organe "
              "variation_adjacency_guard). Aucun des trois gestes generiques")
        print("ne leve ce blocage : la cause n'est pas dans le diff, elle est")
        print("dans le **genre du grain suivant**. Le remede :")
        print()
        print("  -> Piocher un grain d'UN AUTRE genre (LIGHT/{guard,ledger,")
        print("     docs,readme,test} apres un autre grain du meme genre est")
        print("     un monoculture interdit par le protocole variation §2).")
        print("  -> Ne PAS retaguer la PR existante -- le re-tag du meme")
        print("     travail sous un autre genre est l'echappatoire que le")
        print("     protocole ferme explicitement.")
        print("  -> Produire un grain frais (DEEP ou MED, ou un CONTENU dans")
        print("     un genre distinct du precedent merge) : c'est lui qui")
        print("     decale la file et leve le blocage.")
        print()
        print("Mesure du 2026-09-01 : 13 PRs / 25 rouges mesurables tenues par")
        print("adjacency -- premiere cause de rouge de la flotte, devant")
        print("`tag_required` (5), `lane_claim` (3), `perimeter` (2).")
    else:
        print("Trois gestes, dans cet ordre -- le premier repare souvent seul :")
        print("  1. `gh pr update-branch <N>` : rejoue les checks sur une tete fraiche.")
        print("     Un rouge peut dater d'AVANT la correction du garde qui l'a produit")
        print("     (mesure du 2026-08-21 : 5 PRs sur 9 n'avaient rien a corriger).")
        print("     Dater le garde -- `git log -- <script>` -- avant de conclure.")
        print("  2. conflits : rebaser sur origin/main, `--force-with-lease` si la lane")
        print("     est seule sur la branche.")
        print("  3. corriger la substance, pousser, et REPONDRE par ecrit -- au")
        print("     CHANGES_REQUESTED comme au nit : un push muet ne leve aucune")
        print("     remarque. `python scripts/check_unaddressed_nits.py <N>` detaille")
        print("     chaque point non leve, son auteur et sa surface.")
    print()
    print_unattributed_blocked(backlog)
    print_base_inherited(backlog)
    print("Si un rouge n'est PAS reparable par cette lane (garde casse sur main,")
    print("dependance d'une autre PR), l'ECRIRE en commentaire sur la PR concernee,")
    print("puis relancer avec --ignore-red. L'echappatoire se justifie par ecrit,")
    print("elle ne se prend pas en silence.")



# --- Secheresse de substance : G-VAR-1 recoit son organe (#13086) ----------
#
# Mandat user verbatim (#13086, 2026-08-31) : "JE NE VEUX PLUS JAMAIS DE
# SESSION IDLE. Je l'ai signalee une bonne dizaine de fois. Tu escalades tout
# de suite et de la facon la plus ferme possible, et tu prends un deep grain
# stp."
#
# "une bonne dizaine de fois" est le fait qui dicte la forme du remede. La
# regle existe DEJA en prose a quatre endroits -- proactive-coordination
# R1/R5/R6/R7, coordinator-discipline R4, variation-protocol G-VAR-1 -- et
# elle a echoue a chaque fois. En rajouter une cinquieme serait l'echec-
# pendule que le CLAUDE.md global interdit. Ce qui manquait n'est pas une
# phrase : c'est un ORGANE.
#
# Le defaut precis, mesure : ce module PONDERE deja le genre CONTENU dans
# `weight()` et le marque d'une etoile a l'affichage -- mais il pondere le
# CANDIDAT, jamais l'HISTOIRE. Le picker n'a aucune memoire. Une lane qui
# vient de livrer six grains META recoit exactement le meme tirage qu'une
# lane qui vient de livrer une preuve Lean. G-VAR-1 exige que le grain-
# plancher soit DEEP/MED **et** CONTENU ; aucun organe ne l'a jamais mesure.
# `variation_light_cap.py` n'emet que quatre signaux, tous de comptabilite
# LIGHT (TIER-INFLATION, GENRE-RUN, CAP-EXCEEDED-BY-GENRE, GENRE-MISMATCH) :
# une lane qui alterne guard -> tooling -> docs -> test ne declenche JAMAIS
# GENRE-RUN tout en produisant zero contenu indefiniment. C'est exactement le
# profil de l'agent que le user a fait escalader.
#
# Mesure du 2026-08-31 sur les 400 dernieres PRs mergees (398 taguees, 2 sans
# tag), genres passes par `canonicalize_genre` :
#
#   lane                       merges  contenu  runs sans contenu
#   myia-po-2025:CoursIA           45       41  [2, 1, 1]        <- la plus saine
#   myia-po-2024:CoursIA           58       38  [4, 3, 3, 2, ...]
#   myia-po-2026:CoursIA           73       31  [8, 6, 6, 5, ...]
#   myia-ai-01:CoursIA             29        2  [16, 8, 3]       <- la pire
#
# D'ou le seuil par defaut de 3, qui n'est pas un chiffre d'intuition : la
# lane la plus saine de la flotte (po-2025:CoursIA, 41 CONTENU sur 45 merges)
# ne depasse JAMAIS un run de 2. Trois est donc la plus petite valeur qui ne
# peut pas se declencher sur un comportement demontrablement sain. 71 % de
# tous les runs mesures sont <= 2 et restent intouches.
#
# Le geste, quand le seuil est atteint : le tirage n'est pas refuse -- il est
# RESTREINT aux genres CONTENU. La lane recoit un grain, toujours ; c'est le
# "tu prends un deep grain" du mandat, rendu mecanique. La lecon de la forme
# precedente du garde rouge ("REFUS DE TIRAGE", sortie 2, aucun candidat) est
# reprise telle quelle : aucune sortie de cet outil n'autorise une lane a ne
# rien produire.

DROUGHT_RUN_DEFAULT = 3

# Fenetre de lecture. Large : le run se compte sur l'historique de la lane,
# et une lane peu active peut n'avoir que quelques merges dans 400 PRs de
# flotte. Le cout est une seule requete, partagee par tout le tirage.
DROUGHT_FETCH_LIMIT = 400


def fetch_merged_grains(limit: int = DROUGHT_FETCH_LIMIT) -> tuple[list[dict], str | None]:
    """Les PRs mergees recentes, taguees, du plus ANCIEN au plus RECENT.

    Rend `(grains, erreur)`. En cas d'echec de lecture la liste est vide ET
    l'erreur est nommee : un organe qui ne peut pas mesurer doit le DIRE, pas
    rendre un zero indiscernable d'une ardoise propre.
    """
    try:
        out = subprocess.run(
            ["gh", "pr", "list", "--repo", REPO, "--state", "merged",
             "--limit", str(limit), "--json", "number,body,mergedAt,title"],
            capture_output=True, text=True, encoding="utf-8", timeout=120)
    except (OSError, subprocess.SubprocessError) as exc:
        return [], f"{type(exc).__name__}: {exc}"
    if out.returncode != 0:
        return [], (out.stderr or "").strip()[:200] or f"gh exit {out.returncode}"
    try:
        data = json.loads(out.stdout or "[]")
    except json.JSONDecodeError as exc:
        return [], f"JSON illisible: {exc}"
    data.sort(key=lambda p: p.get("mergedAt") or "")
    grains = []
    for pr in data:
        tag = parse_grain_tag(pr.get("body") or "")
        if not tag or not tag.get("lane"):
            continue
        raw = (tag.get("genre") or "").strip().lower()
        grains.append({"number": pr.get("number"),
                       "title": pr.get("title") or "",
                       "lane": tag["lane"],
                       "genre_raw": raw,
                       "genre": canonicalize_genre(raw),
                       "mergedAt": pr.get("mergedAt")})
    return grains, None


def substance_drought(lane: str, grains: list[dict], threshold: int,
                      error: str | None = None) -> dict:
    """Compte les merges consecutifs de `lane` SANS genre CONTENU.

    Le run se lit depuis le merge le plus recent en remontant, et s'arrete au
    premier genre CONTENU. Un genre qui ne se resout pas dans l'enumeration
    close compte NON-CONTENU (fail-CLOSED, meme direction que la politique
    #13475 de `variation_light_cap.genre_counts_light`) mais il est NOMME
    dans la sortie : un mis-tag est un faux positif que la lane conteste en
    re-taguant, alors qu'un silence qui relache le garde ne prouve rien. La
    surface est bornee et mesuree -- 4 PRs sur 398 (1 %) au 2026-08-31.

    `measured` est False quand la lecture a echoue : le run vaut alors 0 et
    ne declenche rien, mais l'appelant doit dire qu'il n'a pas mesure.
    """
    mine = [g for g in grains if g["lane"] == lane]
    run: list[dict] = []
    last_content = None
    for g in reversed(mine):
        if g["genre"] in CONTENU:
            last_content = g
            break
        run.append(g)
    run.reverse()
    unresolved = [g for g in run
                  if g["genre"] not in CONTENU and g["genre"] not in META]
    return {
        "lane": lane,
        "measured": error is None,
        "error": error,
        "threshold": threshold,
        "run": len(run),
        "run_prs": [{"number": g["number"], "genre": g["genre_raw"],
                     "title": g["title"][:70]} for g in run],
        "unresolved": [{"number": g["number"], "genre": g["genre_raw"]}
                       for g in unresolved],
        "last_content": ({"number": last_content["number"],
                          "genre": last_content["genre"],
                          "mergedAt": last_content["mergedAt"]}
                         if last_content else None),
        "lane_merges": len(mine),
        "lane_content": sum(1 for g in mine if g["genre"] in CONTENU),
        "triggered": error is None and len(run) >= threshold,
    }


def print_drought_banner(d: dict, restricted: int, fell_back: bool) -> None:
    """L'escalade, "de la facon la plus ferme possible" (mandat #13086)."""
    bar = "=" * 72
    print(bar)
    print(f"SECHERESSE DE SUBSTANCE -- lane {d['lane']} : {d['run']} merges "
          f"consecutifs sans genre CONTENU (seuil {d['threshold']}).")
    print(bar)
    print()
    print("G-VAR-1 exige que le grain-plancher du cycle soit DEEP ou MED **et**")
    print("porte un genre de la classe CONTENU. Cette lane ne l'a pas tenu sur")
    print(f"ses {d['run']} derniers merges :")
    print()
    for pr in d["run_prs"]:
        print(f"  #{pr['number']}  {pr['genre']:<18s} {pr['title']}")
    print()
    if d["last_content"]:
        lc = d["last_content"]
        print(f"Dernier grain de CONTENU : #{lc['number']} ({lc['genre']}), "
              f"merge {lc['mergedAt']}.")
    else:
        print("Aucun grain de CONTENU dans la fenetre lue : la lane n'a jamais")
        print("tenu le plancher sur l'historique mesure.")
    print(f"Sur toute la fenetre : {d['lane_content']} CONTENU / "
          f"{d['lane_merges']} merges taguees.")
    print()
    if d["unresolved"]:
        print("Genres non resolus dans l'enumeration close (comptes NON-CONTENU,")
        print("fail-CLOSED) -- si l'un d'eux est du contenu, le re-taguer leve")
        print("le compte, et c'est la bonne facon de contester :")
        for u in d["unresolved"]:
            print(f"  #{u['number']}  genre declare : {u['genre']}")
        print()
    print("Mandat user (#13086, verbatim) : \"JE NE VEUX PLUS JAMAIS DE SESSION")
    print("IDLE. Je l'ai signalee une bonne dizaine de fois. Tu escalades tout de")
    print("suite et de la facon la plus ferme possible, et tu prends un deep")
    print("grain stp.\"")
    print()
    if fell_back:
        print("ATTENTION : la restriction aux genres CONTENU ne laissait AUCUN")
        print("candidat admissible. Le tirage ci-dessous est donc RENDU SANS")
        print("restriction -- ne rien rendre fabriquerait l'idle que ce garde")
        print("existe pour empecher. Mais l'absence de grain de contenu piochable")
        print("est elle-meme un defaut de provisionnement : l'ECRIRE au")
        print("coordinateur (variation-protocol section 4), ne pas la traverser")
        print("en silence.")
    else:
        print(f"Le tirage ci-dessous est RESTREINT aux genres CONTENU "
              f"({restricted} candidats). Ce n'est pas un refus : la lane")
        print("recoit un grain, et ce grain tient le plancher. Prendre un META")
        print("de plus avant d'avoir casse la sequence, c'est la monoculture")
        print("que le mandat interdit.")
    print()
    print("Echappatoire : si la secheresse n'est pas reparable par cette lane")
    print("(aucun grain de contenu dans sa capability -- GPU-only, vision-only),")
    print("l'ECRIRE au coordinateur, puis relancer avec --ignore-drought.")
    print("Elle se justifie par ecrit, elle ne se prend pas en silence.")
    print()

def main(argv: list[str] | None = None) -> int:
    # Console Windows cp1252 : un titre d'issue portant un caractere hors table
    # (fleche U+2192 etc.) fait crasher le print en UnicodeEncodeError et perd
    # le tirage entier. UTF-8 + replace : le titre s'affiche degrades, le
    # tirage vit.
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lane", default=None,
                    help="machine:workspace, ex. myia-po-2026:CoursIA (requis hors --orphans-report)")
    ap.add_argument("--prev-genre", default=None,
                    help="genre du grain precedent de la lane (penalise ce genre au tirage)")
    ap.add_argument("--grains", type=int, default=4, help="candidats urne 'grain' (defaut 4)")
    ap.add_argument("--umbrellas", type=int, default=2, help="candidats urne 'umbrella' (defaut 2)")
    ap.add_argument("--delivered", type=int, default=2, help="candidats urne 'delivered' (defaut 2)")
    ap.add_argument("--reroll", type=int, default=0, help="decale la graine pour un nouveau tirage")
    ap.add_argument("--no-check-claims", dest="check_claims",
                    action="store_false",
                    help="ne pas verifier les claims sur les tires "
                         "(par defaut : verifie, et remplace les tenus)")
    ap.add_argument("--red-hours", type=float, default=RED_HOURS_DEFAULT,
                    help=f"seuil du garde 'reparer son rouge d'abord' (defaut {RED_HOURS_DEFAULT} h)")
    ap.add_argument("--red-count", type=int, default=RED_COUNT_DEFAULT,
                    help=f"nombre de rouges simultanees qui refuse le tirage "
                         f"quel que soit leur age (defaut {RED_COUNT_DEFAULT})")
    ap.add_argument("--saturation-hours", type=float, default=None,
                    help="#12830 : seuil du declencheur file-saturation (defaut "
                         f"= --red-hours, soit {RED_HOURS_DEFAULT} h). Separe de "
                         "--red-hours pour ne pas confondre les deux causes "
                         "(rouge substance vs file-saturated infra-side).")
    ap.add_argument("--dwell-hours", type=float, default=DWELL_HOURS_DEFAULT,
                    help="delai avant qu'une issue neuve soit consommable "
                         f"(defaut {DWELL_HOURS_DEFAULT:.0f} h ; 0 desactive le garde)")
    ap.add_argument("--admit-reason", default=None, metavar="TEXTE",
                    help="passer outre le garde d'admission -- exige une "
                         "justification ECRITE, a reporter sur l'issue")
    ap.add_argument("--admissible", type=int, default=None, metavar="ISSUE",
                    help="mode verdict : cette issue est-elle consommable "
                         "maintenant ? sortie 0 = oui, 1 = non. A appeler AVANT "
                         "de dispatcher ou de claim, quel que soit le chemin de "
                         "selection (steer inclus).")
    ap.add_argument("--ignore-red", action="store_true",
                    help="passer outre le garde -- exige une justification ECRITE sur la PR concernee")
    ap.add_argument("--drought-run", type=int, default=DROUGHT_RUN_DEFAULT,
                    metavar="N",
                    help="merges consecutifs sans genre CONTENU a partir "
                         "desquels le tirage est restreint au CONTENU "
                         "(defaut %(default)s)")
    ap.add_argument("--ignore-drought", action="store_true",
                    help="passe outre la restriction CONTENU. A justifier "
                         "PAR ECRIT aupres du coordinateur -- elle ne se "
                         "prend pas en silence.")
    ap.add_argument("--cache", choices=("auto", "off", "refresh"), default="auto",
                    help="cache des payloads GitHub partages (defaut auto)")
    ap.add_argument("--cache-dir", type=pathlib.Path, default=None,
                    help="repertoire cache explicite (utile aux tests/diagnostics)")
    ap.add_argument("--cache-status", action="store_true",
                    help="affiche hit/miss/refresh/stale/bypass en sortie texte")
    ap.add_argument("--exclude-issue", action="append", default=[], metavar="N[,N...]",
                    help="ecarte des issues deja refutees ; option repetable")
    ap.add_argument("--require-label", action="append", default=[], metavar="LABEL[,LABEL...]",
                    help="exige tous ces labels, sans distinction de casse")
    ap.add_argument("--exclude-label", action="append", default=[], metavar="LABEL[,LABEL...]",
                    help="ecarte si au moins un de ces labels est present")
    ap.add_argument("--min-age-days", type=int, default=None)
    ap.add_argument("--max-age-days", type=int, default=None)
    ap.add_argument("--min-idle-days", type=int, default=None)
    ap.add_argument("--max-idle-days", type=int, default=None)
    ap.add_argument("--urns", default="grain,umbrella,delivered",
                    help="urnes admises : grain,umbrella,delivered")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--orphans-report", action="store_true",
                    help="mode rapport : PRs bloquees sans tag Grain lisible, groupees par "
                         "auteur (routage coordinateur, #13086). Ne tire PAS de grain.")
    ap.add_argument("--apply-comment", type=int, default=None, metavar="ISSUE",
                    help="avec --orphans-report : upsert du commentaire marker-guarde sur "
                         "l'issue N (defaut : dry-run, impression seule)")
    ap.set_defaults(check_claims=True)
    args = ap.parse_args(argv)
    if args.apply_comment is not None and not args.orphans_report:
        ap.error("--apply-comment n'a de sens qu'avec --orphans-report")
    if not args.lane and not args.orphans_report and args.admissible is None:
        ap.error("--lane est requis (--orphans-report et --admissible s'en dispensent)")
    for low_name, high_name in (
        ("min_age_days", "max_age_days"),
        ("min_idle_days", "max_idle_days"),
    ):
        low, high = getattr(args, low_name), getattr(args, high_name)
        if low is not None and low < 0:
            ap.error(f"--{low_name.replace('_', '-')} doit etre positif")
        if high is not None and high < 0:
            ap.error(f"--{high_name.replace('_', '-')} doit etre positif")
        if low is not None and high is not None and low > high:
            ap.error(
                f"--{low_name.replace('_', '-')} ne peut pas depasser "
                f"--{high_name.replace('_', '-')}"
            )
    try:
        excluded_issues = {int(value) for value in _csv_values(args.exclude_issue)}
    except ValueError:
        ap.error("--exclude-issue attend des numeros separes par des virgules")
    required_labels = set(_csv_values(args.require_label))
    excluded_labels = set(_csv_values(args.exclude_label))
    selected_urns = {value.casefold() for value in _csv_values([args.urns])}
    invalid_urns = selected_urns - URN_NAMES
    if not selected_urns or invalid_urns:
        detail = ", ".join(sorted(invalid_urns)) or "liste vide"
        ap.error(f"--urns invalide ({detail})")

    effective_cache_mode = args.cache
    if "PYTEST_CURRENT_TEST" in os.environ and args.cache_dir is None:
        effective_cache_mode = "off"
    payload_cache = PayloadCache(args.cache_dir)
    cache_status: dict[str, dict[str, Any]] = {}

    # Mode rapport : le garde rouge (lane) ne concerne pas ce chemin -- la file
    # des orphelines est lane-independante et ce mode ne tire pas de grain.
    if args.orphans_report:
        body = build_orphans_comment(unattributed_blocked_prs())
        print(body)
        if args.apply_comment is not None:
            upsert_orphans_comment(args.apply_comment, body)
            print()
            print(f"[apply] commentaire marker-guarde mis a jour sur #{args.apply_comment}")
        return 0

    # Mode verdict : lane-independant, pas de tirage, pas de garde rouge --
    # la question posee est "ce grain-ci est-il consommable maintenant ?",
    # et elle doit pouvoir etre posee sur un grain STEERE, chemin par lequel
    # arrive l'essentiel du travail (mesure du 2026-08-29).
    if args.admissible is not None:
        pool = fetch_pool(
            cache=payload_cache,
            cache_mode=effective_cache_mode,
            cache_status=cache_status,
        )
        series, issue_to_family, series_err = fetch_series_visits(
            cache=payload_cache,
            cache_mode=effective_cache_mode,
            cache_status=cache_status,
            cache_ttl_seconds=SERIES_CACHE_TTL_SECONDS,
        )
        balance = zone_balance(series, issue_to_family, pool)
        stale = {
            name: entry for name, entry in cache_status.items()
            if entry.get("status") == "stale"
        }
        if stale:
            details = ", ".join(
                f"{name}: {entry.get('error') or 'refresh echoue'}"
                for name, entry in sorted(stale.items())
            )
            print(f"(cache STALE explicite : {details})")
        hit = next((x for x in pool if x["number"] == args.admissible), None)
        if hit is None:
            print(f"#{args.admissible} : absente du pool ouvert "
                  "(fermee, ou au-dela de la limite de la requete).")
            return 1
        cause = admissibility(hit, balance, issue_to_family, args.dwell_hours)
        if series_err:
            if (cache_status.get("series") or {}).get("status") == "stale":
                print(f"(saturation FRAICHE NON MESUREE : {series_err} -- "
                      "parite evaluee sur le payload stale explicitement signale)")
            else:
                print(f"(saturation de zone NON MESUREE : {series_err} -- "
                      "le volet parite n'a PAS ete evalue)")
        print(f"#{hit['number']} {hit['title'][:70]}")
        print(f"  genre {hit['genre']} | polarite {hit['polarity']} | "
              f"age {_hours_old(hit['created_at']):.0f} h")
        if cause is None:
            print("  ADMISSIBLE")
            return 0
        print(f"  REFUS -- {cause}")
        print("  Passer outre exige --admit-reason '<justification>', "
              "a reporter sur l'issue.")
        return 1

    # Garde "reparer son rouge d'abord" : AVANT le tirage, sinon le grain neuf
    # est deja sous les yeux quand le refus arrive, et c'est lui qui gagne.
    backlog = red_backlog(args.lane, args.red_hours, args.red_count,
                            saturation_hours=args.saturation_hours)
    if backlog.get("triggers") and not args.ignore_red:
        # Sortie 0, et le mot "refus" ne parait nulle part : ce chemin REND un
        # grain -- la reparation des PRs de la lane -- il n'en prive pas. La
        # forme precedente ("REFUS DE TIRAGE", sortie 2, aucun candidat) rendait
        # un travail nomme sous l'apparence d'un vide, et se declenchait
        # d'autant plus souvent que la lane etait active.
        if args.json:
            print(json.dumps({"lane": args.lane, "mode": "repair",
                              "assignment": "reparer-son-rouge",
                              "grain": (backlog.get("red") or [None])[0],
                              "red_hours": args.red_hours, **backlog},
                             ensure_ascii=False, indent=2))
        else:
            print_red_assignment(args.lane, backlog, args.red_hours)
        return 0
    if not args.json:
        print_nits_gap(backlog)
        print_base_inherited(backlog)
    if backlog.get("unavailable") and not args.json:
        print(f"(garde rouge indisponible : {backlog['unavailable']} -- tirage rendu sans verification)")
        print()

    pool = fetch_pool(
        cache=payload_cache,
        cache_mode=effective_cache_mode,
        cache_status=cache_status,
    )
    visits, visits_err = fetch_visits(
        cache=payload_cache,
        cache_mode=effective_cache_mode,
        cache_status=cache_status,
    )
    series, issue_to_family, series_err = fetch_series_visits(
        cache=payload_cache,
        cache_mode=effective_cache_mode,
        cache_status=cache_status,
        cache_ttl_seconds=SERIES_CACHE_TTL_SECONDS,
    )
    issue_to_family = enrich_parent_families(
        pool, issue_to_family, series)
    balance = zone_balance(series, issue_to_family, pool)

    # Admission AVANT les urnes : un grain inadmissible ne doit pas
    # apparaitre dans le tirage, sinon il est sous les yeux quand le
    # refus arrive -- et c'est lui qui gagne (meme raison que le garde
    # rouge, qui s'execute avant le tirage pour cette raison exacte).
    # L'urne `delivered` en est exempte : verifier puis fermer une issue
    # deja livree fait REFLUER le pool, c'est l'inverse de l'emballement.
    withheld: list[tuple[dict, str]] = []
    admitted = []
    for it in pool:
        if it["klass"] == "delivered":
            admitted.append(it)
            continue
        cause = admissibility(it, balance, issue_to_family, args.dwell_hours)
        if cause and not args.admit_reason:
            withheld.append((it, cause))
        else:
            admitted.append(it)
    filter_active = {
        "exclude_issue": sorted(excluded_issues),
        "require_label": sorted(required_labels, key=str.casefold),
        "exclude_label": sorted(excluded_labels, key=str.casefold),
        "min_age_days": args.min_age_days,
        "max_age_days": args.max_age_days,
        "min_idle_days": args.min_idle_days,
        "max_idle_days": args.max_idle_days,
        "urns": sorted(selected_urns),
    }
    filtered, filter_funnel = filter_candidates(
        admitted,
        exclude_issues=excluded_issues,
        required_labels=required_labels,
        excluded_labels=excluded_labels,
        min_age_days=args.min_age_days,
        max_age_days=args.max_age_days,
        min_idle_days=args.min_idle_days,
        max_idle_days=args.max_idle_days,
        urns=selected_urns,
    )
    filter_funnel.update({
        "pool_initial": len(pool),
        "admitted": len(admitted),
        "admission_withheld": len(pool) - len(admitted),
    })
    by_class = {k: [it for it in filtered if it["klass"] == k]
                for k in ("grain", "umbrella", "delivered")}

    # Graine : (lane, heure UTC, reroll). Lanes differentes -> tirages
    # differents ; meme lane dans l'heure -> tirage identique (idempotent).
    stamp = NOW.strftime("%Y-%m-%dT%H")
    seed_src = f"{args.lane}|{stamp}|{args.reroll}"
    seed = int(hashlib.sha256(seed_src.encode()).hexdigest()[:16], 16)
    rng = random.Random(seed)

    # Le tirage est claim-aware, et le remplacement est ce qui compte.
    # Mesure du 2026-08-29 : quatre collisions en quatre jours (#13310, et
    # les trois paires #12948<-#12791, #12984<-#12983, #13016<-#12758,
    # PRs ouvertes le 25/08 et supersedees le 28/08 par d'autres lanes sur
    # les MEMES issues). Le gate CI `lane_claim_required` dit lui-meme ce
    # qu'il ne fait pas : << The gate cannot prevent the collision (once
    # the PR exists the work is written) >>. Il empeche le MERGE, pas
    # l'ecriture. La prevention doit donc vivre en amont, ici -- et elle ne
    # peut pas etre optionnelle : un tirage qui propose une issue tenue par
    # une autre lane FABRIQUE la collision qu'il faudra arbitrer ensuite.
    # G-VAR-1 recoit son organe (#13086) : le tirage a une MEMOIRE. Une lane
    # en secheresse de substance ne recoit plus une loterie ou le CONTENU est
    # seulement mieux pondere -- elle recoit un tirage RESTREINT au CONTENU.
    # Place APRES le garde rouge (reparer son rouge reste la premiere tache,
    # mandat user 2026-08-24) et AVANT le tirage, pour la meme raison que lui :
    # un candidat META deja sous les yeux quand la restriction arrive, c'est
    # lui qui gagne.
    drought = {"triggered": False, "measured": False, "run": 0}
    drought_fell_back = False
    if args.lane:
        grains_hist, grains_err = fetch_merged_grains()
        drought = substance_drought(args.lane, grains_hist, args.drought_run,
                                    grains_err)
        if drought["triggered"] and not args.ignore_drought:
            restricted = {k: [it for it in v if it["genre"] in CONTENU]
                          for k, v in by_class.items()}
            # Degradation gracieuse : si la restriction vide les urnes, on rend
            # le tirage NON restreint plutot que rien. Ne rien rendre
            # fabriquerait l'idle que ce garde existe pour empecher -- et
            # l'absence de grain de contenu piochable est un defaut de
            # provisionnement a ECRIRE, pas un motif de silence.
            if restricted["grain"] or restricted["umbrella"]:
                by_class = restricted
                by_class["delivered"] = []
            else:
                drought_fell_back = True
            if not args.json:
                print_drought_banner(
                    drought,
                    len(by_class["grain"]) + len(by_class["umbrella"]),
                    drought_fell_back)
        elif drought["triggered"] and args.ignore_drought and not args.json:
            print(f"(secheresse de substance ignoree : {drought['run']} merges "
                  f"sans CONTENU -- justification ecrite attendue)")
            print()
        elif not drought["measured"] and not args.json:
            print(f"(secheresse NON MESUREE : {drought['error']} -- le tirage "
                  "ne prouve donc rien sur le plancher G-VAR-1)")
            print()

    # Le mode --json doit dire la MEME chose que la banniere texte. Sans ces
    # deux cles, un consommateur machine voit `triggered: true` sans pouvoir
    # distinguer les deux issues opposees : le tirage a-t-il ete RESTREINT aux
    # genres CONTENU (le garde a mordu, la lane recoit un grain qui tient le
    # plancher), ou a-t-il ete rendu SANS restriction faute de candidat de
    # contenu piochable ? Le second cas est un defaut de PROVISIONNEMENT a
    # ecrire au coordinateur (variation-protocol section 4), et c'est
    # precisement celui qu'un silence rendrait invisible. Finding NanoClaw
    # sur #13884, tenue : la forme du payload est stable quel que soit le
    # chemin, pour qu'une absence de cle ne se lise jamais comme un faux.
    drought["fell_back"] = drought_fell_back
    drought["restricted_candidates"] = (
        len(by_class["grain"]) + len(by_class["umbrella"])
        if drought.get("triggered") and not args.ignore_drought
        and not drought_fell_back
        else None)

    picks, claims, claim_conflicts = draw_unclaimed(
        by_class, args, rng, visits, series, issue_to_family)
    withheld.extend(claim_conflicts)
    delivery = recent_delivery(picks)

    if args.json:
        print(json.dumps({
            "lane": args.lane, "seed_src": seed_src,
            "pool": {k: len(v) for k, v in by_class.items()},
            "picks": picks, "claims": {str(k): v for k, v in claims.items()},
            "withheld": [{"number": it["number"], "title": it["title"],
                          "cause": c} for it, c in withheld],
            "dwell_hours": args.dwell_hours,
            "admit_reason": args.admit_reason,
            "series_measured": series_err is None,
            "series_error": series_err,
            "series_zones": sorted(
                ({"family": f, **z} for f, z in series.items()),
                key=lambda d: (-d["new_notebooks"], -d["prs"]))[:10],
            "zone_balance": sorted(
                ({"family": f, **b} for f, b in balance.items()),
                key=lambda d: (-d["new_notebooks"], -d["expansion"]))[:10],
            "visits_window_days": VISITS_WINDOW_DAYS,
            "visits_measured": visits_err is None,
            "visits_error": visits_err,
            "visits_top": sorted(({"issue": k, "n": v} for k, v in visits.items()),
                                 key=lambda d: (-d["n"], d["issue"]))[:10],
            "recent_delivery": {str(k): v for k, v in delivery.items()},
            "red_backlog": backlog,
            "substance_drought": drought,
            "cache": cache_status,
            "filters": {
                "active": filter_active,
                "excluded": filter_funnel["excluded"],
                "funnel": filter_funnel,
            },
        }, ensure_ascii=False, indent=2))
        return 0

    stale_entries = {
        name: entry
        for name, entry in cache_status.items()
        if entry.get("status") == "stale"
    }
    if args.cache_status or stale_entries:
        states = ", ".join(
            f"{name}={entry.get('status')}"
            + (f" ({entry.get('error')})" if entry.get("error") else "")
            for name, entry in sorted(cache_status.items())
        )
        print(f"Cache payloads : {states or 'aucune mesure partageable lue'}")
        if stale_entries:
            print("!! STALE explicite : payload ancien utilise seulement apres "
                  "echec du refresh ; ce n'est pas une mesure fraiche.")
        print()
    non_default_filters = {
        key: value
        for key, value in filter_active.items()
        if value not in (None, [], sorted(URN_NAMES))
    }
    if non_default_filters:
        details = ", ".join(
            f"{name}={count}"
            for name, count in filter_funnel["excluded"].items()
        ) or "aucune exclusion"
        print(
            f"Filtres locaux : {filter_funnel['initial']} admis -> "
            f"{filter_funnel['final']} candidats ({details})."
        )
        if not filtered:
            dominant = max(
                filter_funnel["excluded"],
                key=filter_funnel["excluded"].get,
                default=None,
            )
            if dominant:
                print(
                    f"Aucun candidat final : relacher d'abord `{dominant}` "
                    f"({filter_funnel['excluded'][dominant]} exclusions)."
                )
        print()
    if series_err:
        if (cache_status.get("series") or {}).get("status") == "stale":
            print(f"(saturation FRAICHE NON MESUREE : {series_err} -- "
                  "payload stale explicitement signale et amortissement ancien applique)")
        else:
            print(f"(saturation de zone NON MESUREE : {series_err} -- "
                  "aucun amortissement de serie applique)")
        print()
    else:
        chaudes = [(f, b) for f, b in balance.items()
                   if b["new_notebooks"] >= 3]
        chaudes.sort(key=lambda kv: (-kv[1]["new_notebooks"],
                                     -kv[1]["expansion"]))
        umbrellas = zone_umbrellas(issue_to_family, pool, series)
        if chaudes:
            print("Zones chaudes (14 j) -- parite expansion/consolidation :")
            for f, b in chaudes[:5]:
                exp, con = b["expansion"], b["consolidation"]
                verdict = zone_verdict(b)
                if is_runaway(b):
                    verdict = "EMBALLEMENT"
                parents = sorted((umbrellas.get(f) or {}).items(),
                                 key=lambda kv: -kv[1])
                epic = (" ".join("#{}".format(n) for n, _ in parents[:2])
                        if parents else "(aucun EPIC declare)")
                print("  {:>2d} neufs | {:>2d} expansion / {:>2d} consolidation "
                      "  {:12s} {}".format(
                          b["new_notebooks"], exp, con, verdict, f))
                print("       alimentee par {}".format(epic))
            print("  (un EPIC qui alimente une zone doit produire autant de "
                  "consolidation que d'expansion -- mandat user 2026-08-28)")
            print("  EMBALLEMENT = la zone recoit plus vite qu'elle ne "
                  "consolide. La parite porte sur les grains OUVERTS, elle ne "
                  "voit pas le RYTHME de ce qui est deja tombe : trois remedes "
                  "ouverts ne repondent pas a onze arrivees. Le remede est "
                  "d'ouvrir la consolidation dans l'EPIC nomme -- ou, s'il n'y "
                  "en a aucun, d'en declarer un : une zone chaude sans EPIC "
                  "n'a personne de comptable pour la contrepartie.")
            print()
    print(f"Pool ouvert : {len(pool)} issues.")
    print(f"Candidats apres admission/filtres : "
          f"{len(by_class['grain'])} grains "
          f"+ {len(by_class['umbrella'])} umbrella "
          f"+ {len(by_class['delivered'])} candidate-delivered")
    if args.admit_reason:
        print(f"!! --admit-reason : garde d'admission passe outre "
              f"({args.admit_reason!r}). A reporter sur l'issue retenue.")
    elif withheld:
        dwell_n = sum(1 for _, c in withheld if c.startswith("DWELL"))
        claim_n = sum(1 for _, c in withheld if c.startswith("CLAIM"))
        zone_n = len(withheld) - dwell_n - claim_n
        # Les trois causes ne se rangent pas ensemble : dwell et zone
        # reviennent d'elles-memes, un grain tenu par une autre lane revient
        # quand CETTE lane le relache. Les fondre dans "zone sans remede"
        # afficherait "elle revient d'elle-meme" sur le seul cas ou c'est faux.
        parts = [f"{dwell_n} en attente de dwell",
                 f"{zone_n} en zone sans remede"]
        if claim_n:
            parts.append(f"{claim_n} tenue(s) par une autre lane")
        print(f"Retenues hors tirage : {len(withheld)} "
              f"({', '.join(parts)}). "
              "Dwell et zone reviennent d'elles-memes -- aucune n'est refusee "
              "sur le fond.")
        if claim_n:
            print("   Un grain tenu revient quand sa lane pose [RELEASED], ou "
                  "sur arbitrage [OVERRIDE] du coordinateur.")
        for it, cause in sorted(withheld, key=lambda kv: -kv[0]["number"])[:3]:
            print(f"   #{it['number']:<7} {cause.split(chr(58))[0]:<18} {it['title'][:46]}")
    if backlog.get("triggers"):
        numbers = ", ".join(f"#{r['number']}" for r in backlog["red"])
        print(f"!! --ignore-red : {len(backlog['red'])} PR(s) bloquee(s) de cette lane restent "
              f"a reparer ({numbers}).")
        print("   La justification doit etre ECRITE sur chacune, pas seulement invoquee ici.")
    print(f"Lane {args.lane} | graine {stamp}"
          + (f" | reroll {args.reroll}" if args.reroll else "")
          + (f" | genre precedent penalise : {args.prev_genre}" if args.prev_genre else ""))
    print()
    header = (f"{'urne':<10} {'issue':<8} {'age':>5} {'inact':>6} {'vus':>4}  "
              f"{'genre':<16} {'p':>5}  titre")
    print(header)
    print("-" * len(header))
    for p in picks:
        mark = "*" if p["genre"] in CONTENU else " "
        visits_stale = (cache_status.get("visits") or {}).get("status") == "stale"
        vus = (f"~{p.get('visits', 0)}" if visits_stale
               else "n/m" if visits_err else str(p.get("visits", 0)))
        print(f"{p['klass']:<10} #{p['number']:<7} {p['age']:>4}j {p['idle']:>5}j {vus:>4}  "
              f"{p['genre']:<15}{mark} {p['weight']:>5}  {p['title'][:62]}")
        if p["number"] in claims:
            print(f"{'':>10} {'':>8} {'':>5} {'':>6} {'':>4}  claim: {claims[p['number']]}")
        if p["number"] in delivery:
            note = delivery[p["number"]]
            head, sep, tail = note.partition("-> ")
            print(f"{'':>10} {'':>8} {'':>5} {'':>6} {'':>4}  {head.strip()}")
            if tail:
                print(f"{'':>10} {'':>8} {'':>5} {'':>6} {'':>4}  -> {tail}")
        # Un verdict qui n'est cable a aucune action ne change rien : la zone
        # chaude s'affichait en tete du tirage et le pick d'a cote n'en disait
        # rien. C'est ici que la mesure devient une consigne.
        zb = (balance or {}).get(p.get("family") or "")
        if zb and zb["new_notebooks"] >= 3:
            etat = "EMBALLEMENT" if is_runaway(zb) else "zone chaude"
            pad = f"{'':>10} {'':>8} {'':>5} {'':>6} {'':>4}  "
            print(pad + "{} : {} notebooks neufs / 14 j, {} consolidation "
                        "ouverte(s) pour {} expansion.".format(
                            etat, zb["new_notebooks"], zb["consolidation"],
                            zb["expansion"]))
            if zb["consolidation"] <= zb["expansion"] or is_runaway(zb):
                quoi = ("le SOUS-grain a creer ici est une CONSOLIDATION"
                        if p["klass"] == "umbrella"
                        else "la contrepartie due dans cette zone est une "
                             "CONSOLIDATION")
                print(pad + "-> " + quoi + " (renumeroter un numero eleve en "
                      "lettre d'un numero existant, ou fondre plusieurs "
                      "lettres en un petit nombre), pas une instance de plus.")
    print()
    print_unattributed_blocked(backlog)
    if visits_err:
        if (cache_status.get("visits") or {}).get("status") == "stale":
            print(f"!! affluence FRAICHE NON MESUREE ({visits_err}) : la colonne")
            print("   `vus` prefixe les comptes stale par `~`; un amortissement ancien")
            print("   est applique et ne doit pas etre lu comme une mesure fraiche.")
        else:
            print(f"!! affluence NON MESUREE ({visits_err}) : la colonne `vus` affiche")
            print("   `n/m` et le tirage n'a PAS amorti les sujets deja frequentes.")
            print("   Un zero d'absence de mesure n'est pas un zero d'affluence.")
        print()
    print("* = genre CONTENU (seul un genre CONTENU en DEEP/MED tient le plancher G-VAR-1).")
    print(f"vus = PRs mergees citant cette issue sur {VISITS_WINDOW_DAYS} j, TOUTES LANES.")
    print("      Le cap de veine ne voit qu'une lane a la fois : plusieurs lanes")
    print("      restant chacune sous son cap concentrent quand meme la flotte")
    print("      sur un meme sujet. C'est ce que cette colonne amortit.")
    print("inact = jours depuis la derniere activite. Une inactivite haute est le")
    print("        signe d'un sujet delaisse devant ceux du moment : c'est ce que")
    print("        le tirage remonte, et ce que la lane est attendue de conduire.")
    print("umbrella  -> pioche ou cree un SOUS-grain dedans, ne claim pas l'EPIC entier.")
    print("delivered -> verifie firsthand que la PR livrante satisfait l'acceptance :")
    print("             si oui `gh issue close`, sinon retire le label en disant pourquoi.")
    print("Avant d'EDITER : python scripts/check_lane_claim.py --lane <machine:workspace> <N>")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
