#!/usr/bin/env python3
"""Budget de creation de carnets, a l'echelle de la FLOTTE (#23174).

Mandat (user, session directe du 2026-10-28, via le coordinateur) :

    « Il faut ralentir la creation de carnets, qui ne doit correspondre
    qu'au rythme auquel les issues ouvertes le proposent, c'est a dire une
    minorite a cote des nombreuses issues de corrections ouvertes. »

    « ... ralentir les nouvelles creations (pas les arreter, juste ralentir) »

Ce module porte la DETECTION et la DERIVATION ; le compteur et le
branchement dans le tapis sont ailleurs :

  * `scripts/ci/creation_budget_counter.py` mesure l'etat et ecrit l'etat ;
  * `scripts/pick_idle_grain.py` lit l'etat et ecarte un grain de creation
    quand le compteur depasse le budget, avec la cause nommee
    `BUDGET CREATION`.

Deux decisions de conception, toutes deux mesurees.

1. LE DEPOT EST L'ORACLE, LA PROSE EST UN TEMOIGNAGE DATE
------------------------------------------------------------
« Ce grain livre-t-il un carnet neuf ? » se repond en opposant le depot
(`git ls-tree -r origin/main`) a l'issue :

  O1 serie + rang  -> le rang est-il deja livre dans cette serie ?
  O2 fichier cite  -> l'issue cite-t-elle un `.ipynb` absent du depot ?
  O3 phrase        -> l'issue DECLARE-t-elle la creation ?

Un VETO de reparation (audit, correction, renumerotation, collision, prose)
l'emporte sur les trois : un grain de reparation n'est JAMAIS ecarte. Le sens
de l'erreur est choisi -- on saute un carnet neuf *quand on le sait*, on ne
saute pas un grain qu'on ne sait pas classer.

Mesure du 2026-10-28 (jeu de controle derive des PRs OUVERTES : positifs =
`Add|Feat` qui ajoutent un `.ipynb` absent de main, negatifs =
`Fix|Docs|Refactor` qui modifient un `.ipynb` present) :

    precision 1,00 (0 faux positif sur 55 negatifs)
    rappel    0,92 (11 des 12 positifs classables ; 7 indetermines)

La polarite existante (`scripts/series_saturation.py::polarity`) a ete
mesuree sur le meme jeu, comme l'issue l'exige : **precision 0,67, rappel
0,11**. Elle ne voit que 21 des issues de creation du pool ouvert, et elle
classe « consolidation » **13 issues dont la livraison est un carnet neuf**.
Elle est donc utilisee comme un SIGNAL, jamais comme le critere.

2. L'EPIC EST UN CONTENEUR : LA REGLE S'APPLIQUE AU SOUS-GRAIN
--------------------------------------------------------------
L'issue propose « un grain de creation (un EPIC hors `consolidation`, ou un
grain dont la livraison est un carnet neuf) ». La premiere moitie, lue
literalement, ecarte **30 EPICs qui ne creent rien** : le soutien des
sous-modules, les audits de series, la bibliographie, le slimming du
harnais, les tranches de tests .NET. Un EPIC est un CONTENEUR — la regle du
tapis dit « un EPIC en tete se sert par un sous-grain, jamais par un claim
de l'EPIC entier » — et le classement d'un conteneur n'est pas le classement
de son contenu.

La regle appliquee est donc la regle de l'issue portee au sous-grain
effectif :

  * un grain ordinaire est de creation si sa livraison est un carnet neuf ;
  * un EPIC est de creation si toutes ses filles ouvertes sont de creation
    (servir cet EPIC, c'est alors servir de la creation) ; s'il a une seule
    fille de reparation, il ne l'est jamais.

C'est la lecture qui passe le controle negatif de l'issue (« aucune issue
`consolidation` ni de correction n'est ecartee par le budget »).

LE BUDGET EST DERIVE, JAMAIS POSE
----------------------------------
Le budget se deduit de deux mesures, jamais d'une constante :

    part_creation = (grains de creation du pool ouvert) / (pool ouvert)
    budget        = round(part_creation x grains livres la semaine ecoulee)

C'est la lecture directe de « le rythme auquel les issues ouvertes le
proposent » : la part de creation que le pool propose, appliquee au nombre
de grains que la flotte a livres. Un plancher de 1 carnet subsiste : le
regime RALENTIT la creation, il ne l'ARRETE pas.

L'etat est lu depuis un fichier JSON (variable `COURSIA_CREATION_BUDGET_FILE`).
Un fichier absent, illisible ou perime ne fait ecarter PERSONNE : le regime
ne doit pas vider le tapis parce qu'un compteur n'a pas tourne.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
from collections.abc import Iterable, Sequence

VERDICT_CREATION = "creation"
VERDICT_REPAIR = "repair"
VERDICT_NEUTRAL = "neutre"

DELIVERY_NEW = "carnet_neuf"
DELIVERY_EXISTING = "carnet_existant"
DELIVERY_UNKNOWN = "indetermine"

# La variable d'environnement qui pointe l'etat du budget. Elle est
# VOLONTAIREMENT absente par defaut : sans elle, aucune lane n'ecarte rien.
ENV_STATE = "COURSIA_CREATION_BUDGET_FILE"

# La cause nommee que le tapis affiche quand un grain est ecarte. Le
# libelle est celui de l'issue (#23174), accent compris : une cause nommee
# doit se retrouver telle quelle dans les journaux de tirage.
CAUSE = "BUDGET CRÉATION"


# --- livraison : le depot contre l'issue -------------------------------------

# Un rang de carnet : deux chiffres (+ lettre eventuelle). Le deuxieme chiffre
# est exige parce que « Tweety 1.28 » (une version) ne doit pas etre lu
# comme le rang 1 d'une serie.
#
# La garde d'UNITE empeche une QUANTITE en prose d'etre lue comme un rang :
# mesure du 2026-10-28, #21871 « ... le PDF a ete archive 11 jours apres la
# PR » resolvait la serie « archive » et le rang « 11 » — un grain d'AUDIT
# sur un carnet existant, entendu comme une creation.
_UNIT_GUARD = r"(?!\s*(?:jours?|mois|ans?|semaines?|heures?|minutes?|fois|pour\s*cent)\b)"

_RE_CARNET_KW = re.compile(
    r"\b(?:carnet|notebook|palier|slot)\s*[:\-–]?\s*(\d{2}[a-z]?)" + _UNIT_GUARD,
    re.IGNORECASE)
_RE_SERIE_RANK = re.compile(
    r"\b([A-Za-z][A-Za-z0-9]{1,})[- ]+(\d{2}[a-z]?)" + _UNIT_GUARD)
_RE_BRACKET_RANK = re.compile(r"\]\s*(\d{2}[a-z]?)" + _UNIT_GUARD + r"\s*[—–-]")
_RE_PREFIX_RANK = re.compile(r"([A-Za-z][A-Za-z0-9]{1,})-(\d{2}[a-z]?)" + _UNIT_GUARD)
_RE_R_RANK = re.compile(r"\b([A-Za-z][A-Za-z0-9]{1,})\s+R-(\d{2})\b")
_RE_LEAD_RANK = re.compile(
    r"^\s*([A-Za-z][A-Za-z0-9]{1,})-(\d{2}[a-z]?)" + _UNIT_GUARD)

_RE_IPYNB = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./\- ]*?\.ipynb")

_RE_CREATE_PHRASE = re.compile(
    r"(premier\s+(?:num[eé]ro|trou|slot)\s+libre"
    r"|num[eé]ro\s+libre\s+suivant"
    r"|prochain\s+num[eé]ro\s+libre"
    r"|nouveau\s+carnet|nouvelle\s+carnet"
    r"|carnet\s+neuf|carnets\s+neufs"
    r"|cr[eé]er\s+(?:un|le|ce)\s+carnet"
    r"|aucun\s+carnet\s+\d"
    r"|slot\s*:"
    r"|nouvelle\s+distillation)",
    re.IGNORECASE,
)

_RE_CREATE_INTENT = re.compile(
    r"(nouveau|nouvelle|cr[ée]er|ajouter|add\b|distill\w*|x[ée]cuter|"
    r"construire|r[ée]diger|carnet\s+\d|notebook\s+\d|palier\s+\d)",
    re.IGNORECASE,
)

# VETO : un mot de reparation dans le titre. La liste est courte et
# explicite : elargir le filet sur-accuse (cf #14682 — un detecteur qui
# sur-accuse d'un facteur 5 est un detecteur qu'on contourne).
_RE_REPAIR = re.compile(
    r"(fix\b|corrig|r[ée]par|audit|hermes|consolidat|d[ée]plac|renum|renumérot|"
    r"num[eé]rotation|align|prose|accent|typo|bibliograph|doc\b|docs\b|lecture|"
    r"nettoy|supprim|d[ée]dup|verif|recheck|re[- ]?exec|densit|reachability|"
    r"seed\b|tranche\s+\d|suivi\s+#|r[ée]align|chronologie|collision)",
    re.IGNORECASE,
)

_RE_UMBRELLA = re.compile(r"^\s*\[?\s*EPIC\b", re.IGNORECASE)


def _norm(text: str) -> str:
    return re.sub(r"[^a-z0-9]", "", (text or "").lower())


def _tokens(text: str) -> list[str]:
    return re.findall(r"[A-Za-z][A-Za-z0-9]{1,}", text or "")


class NotebookCatalog:
    """L'etat du depot : les carnets connus, leurs noms et leurs series.

    Construit depuis `git ls-tree -r <ref> --name-only`. Une liste VIDE est
    un catalogue INCONNU : le classement rend alors `indetermine` partout et
    rien n'est ecarte (le regime ne doit pas vider le tapis parce qu'un `git`
    a echoue).
    """

    def __init__(self, ipynb_paths: Sequence[str]):
        self.paths = list(ipynb_paths)
        self.stems = {p.rsplit("/", 1)[-1][:-6] for p in self.paths if p.endswith(".ipynb")}
        self.norm_stems = {_norm(s): s for s in self.stems}
        self.series: dict[str, set[str]] = {}
        for p in self.paths:
            if not p.endswith(".ipynb"):
                continue
            for d in p.split("/")[:-1]:
                self.series.setdefault(_norm(d), set()).add(d)

    @property
    def known(self) -> bool:
        return bool(self.paths)

    @classmethod
    def from_repo(cls, repo_root: str | pathlib.Path | None = None,
                  ref: str = "origin/main") -> NotebookCatalog:
        root = pathlib.Path(repo_root) if repo_root else pathlib.Path.cwd()
        try:
            out = subprocess.run(
                ["git", "-C", str(root), "ls-tree", "-r", ref, "--name-only"],
                capture_output=True, text=True, check=True, timeout=60,
                encoding="utf-8",
            ).stdout
        except Exception:  # noqa: BLE001 - un git muet = catalogue inconnu
            return cls([])
        return cls([p for p in out.splitlines() if p.endswith(".ipynb")])


def _series_of(catalog: NotebookCatalog, tokens: Iterable[str]) -> str | None:
    for token in tokens:
        if _norm(token) in catalog.series:
            return token
    return None


def _series_candidates(prefix: str) -> list[str]:
    """Les noms de serie qu'un prefixe de titre peut designer.

    « Serre 100 » designe le dossier `Serre100`, « Z3 Linq2Z3 » le dossier
    `Z3-Linq2Z3` : la ponctuation du depot n'est pas celle du titre. On
    essaie donc le mot isole, les paires de mots voisins, et le prefixe
    entier normalise.
    """
    tokens = _tokens(prefix)
    out: list[str] = list(tokens)
    out.extend(tokens[i] + tokens[i + 1] for i in range(len(tokens) - 1))
    out.append(prefix)
    return out


def series_and_rank(title: str, catalog: NotebookCatalog) -> tuple[str | None, str | None]:
    """La serie et le rang que le titre nomme, s'il en nomme un."""
    text = title or ""
    m = _RE_CARNET_KW.search(text)
    if m:
        rank = m.group(1)
        before = text[: m.start()]
        serie = _series_of(catalog, reversed(_series_candidates(before)))
        if serie is None:
            serie = _series_of(catalog, _series_candidates(text))
        return serie, rank
    for rx in (_RE_R_RANK, _RE_PREFIX_RANK, _RE_SERIE_RANK, _RE_LEAD_RANK):
        m = rx.search(text)
        if m:
            return _series_of(catalog, [m.group(1)]) or m.group(1), m.group(2)
    m = _RE_BRACKET_RANK.search(text)
    if m:
        return _series_of(catalog, _tokens(text)), m.group(1)
    return None, None


def rank_exists(catalog: NotebookCatalog, serie: str | None, rank: str) -> bool | None:
    """Le depot porte-t-il deja un carnet de ce rang dans cette serie ?

    Le rang est lu sur le NOM du fichier (`07-...`, `Search-07-...`,
    `GameTheory-11c-...`) et la serie sur le CHEMIN (le dossier de la
    serie, a n'importe quel niveau). `None` = serie inconnue du depot : on
    ne peut rien dire.
    """
    if not serie:
        return None
    key = _norm(serie)
    if key not in catalog.series:
        return None
    for path in catalog.paths:
        parts = path.split("/")
        dirs = {_norm(d) for d in parts[:-1]}
        if key not in dirs:
            continue
        stem = parts[-1][:-6]
        m = re.match(r"^(?:([A-Za-z0-9]+)-)?(\d{2}[a-z]?)([-_.].*)?$", stem)
        if not m or m.group(2) != rank:
            continue
        prefix = m.group(1)
        if prefix and _norm(prefix) != key and not _norm(prefix).endswith(key):
            continue
        return True
    return False


def absent_notebooks(text: str, catalog: NotebookCatalog) -> list[str]:
    """Les `.ipynb` cites par le texte dont le nom ne correspond a aucun
    carnet du depot : l'issue en cree un.

    La correspondance est **approximative** (`-Python`, `-en`, `-CSharp`...) :
    c'est ce qui empeche un audit de citer `Serre100/08-serre-dans-mathlib
    .ipynb` alors que le depot porte `08-serre-dans-mathlib-Lean.ipynb` de
    compter pour une creation.
    """
    out: list[str] = []
    for m in _RE_IPYNB.finditer(text or ""):
        path = m.group(0).strip().replace("\\", "/").lstrip("./")
        if "/" not in path:
            continue
        if path in catalog.paths:
            continue
        key = _norm(path.rsplit("/", 1)[-1][:-6])
        if not key:
            continue
        if key in catalog.norm_stems:
            continue
        if any(key in ns or ns in key for ns in catalog.norm_stems):
            continue
        out.append(path)
    return sorted(set(out))


def classify_delivery(item: dict, catalog: NotebookCatalog) -> tuple[str, str]:
    """La livraison de ce grain est-elle un carnet neuf ?

    Rend `(verdict, preuve)` avec verdict dans {`carnet_neuf`,
    `carnet_existant`, `indetermine`}. La preuve est une phrase courte,
    citable telle quelle sur l'issue.
    """
    title = item.get("title") or ""
    body = item.get("body") or ""

    if _RE_REPAIR.search(title):
        return DELIVERY_EXISTING, "titre de reparation -> livraison d'un carnet existant"

    if _RE_UMBRELLA.search(title):
        return DELIVERY_UNKNOWN, "umbrella : le classement se fait sur le sous-grain"

    if not catalog.known:
        return DELIVERY_UNKNOWN, "catalogue du depot indisponible"

    cited = absent_notebooks(title + "\n" + body, catalog)
    if cited and _RE_CREATE_INTENT.search(title):
        return DELIVERY_NEW, f"carnet cite absent du depot : {cited[0]}"

    # L'ORACLE DU DEPOT passe AVANT la prose. Une issue est datee de sa
    # REDACTION : son corps peut encore dire « premier numero libre » alors
    # que le carnet a ete livre depuis (mesure : #21799 « [GameTheory] 11c »,
    # dont le rang 11c est desormais sur `main`).
    serie, rank = series_and_rank(title, catalog)
    if serie and rank:
        exists = rank_exists(catalog, serie, rank)
        if exists is True:
            return DELIVERY_EXISTING, f"rang {rank} deja livre dans la serie {serie}"
        if exists is False:
            return DELIVERY_NEW, f"rang {rank} absent de la serie {serie}"

    if _RE_CREATE_PHRASE.search(title + "\n" + body):
        return DELIVERY_NEW, "l'issue declare la creation d'un carnet"

    return DELIVERY_UNKNOWN, "livrable non nomme"


# --- le grain de creation ----------------------------------------------------

def labels_of(item: dict) -> list[str]:
    out = []
    for x in (item.get("labels") or []):
        out.append(str(x.get("name") if isinstance(x, dict) else x).lower())
    return out


def is_umbrella(item: dict) -> bool:
    """Une issue conteneur (EPIC), declaree par son etiquette ou son titre."""
    if set(labels_of(item)) & {"epic", "umbrella", "ombrelle"}:
        return True
    return bool(_RE_UMBRELLA.search(item.get("title") or ""))


def has_consolidation_label(item: dict) -> bool:
    return "consolidation" in labels_of(item)


_PARENT_BODY_RE = re.compile(r"(?i)\bpart of #(\d+)")
_PARENT_TITLE_RE = re.compile(r"^\s*\[#(\d+)\b")
_PARENT_TITLE_KIND_RE = re.compile(r"(?i)^\s*[\w.\- ]+?\s*\([^)]*\)\s*:")
_PARENT_TITLE_KIND_EPIC_RE = re.compile(r",\s*#(\d+)")


def parent_refs(item: dict) -> set[int]:
    """Les conteneurs que cette issue DECLARE servir.

    Les memes surfaces que `scripts/pick_idle_grain.py::parent_refs`, portees
    ici pour que le module ne depende pas du picker (le picker, lui, depend
    de ce module — le sens de la dependance doit rester unique) :

      * `Part of #N` dans le corps ;
      * `[#N ...]` en tete de titre (forme des sous-grains d'EPIC) ;
      * `kind(zone,#EPIC):` en tete de titre (forme des tranches).
    """
    refs = {int(m) for m in _PARENT_BODY_RE.findall(item.get("body") or "")}
    title = item.get("title") or ""
    m = _PARENT_TITLE_RE.match(title)
    if m:
        refs.add(int(m.group(1)))
    kind = _PARENT_TITLE_KIND_RE.match(title)
    if kind:
        refs.update(int(m) for m in _PARENT_TITLE_KIND_EPIC_RE.findall(kind.group(0)))
    refs.discard(item.get("number"))
    return refs


def children_of(item: dict, pool: Sequence[dict]) -> list[dict]:
    """Les filles ouvertes de cet item (lecture directe, pool par pool)."""
    number = item.get("number")
    return [it for it in pool
            if it.get("number") != number
            and (it.get("parent") == number or number in parent_refs(it))]


def build_children_index(pool: Sequence[dict]) -> dict[int, list[dict]]:
    """Le graphe parent -> filles, calcule UNE FOIS.

    Deux sources, PRISES ENSEMBLE : le `parent` que le picker calcule deja
    (`scripts/pick_idle_grain.py::fetch_pool`) et les renvois declares
    (`parent_refs`). La seconde est plus large — elle lit le titre — et elle
    compte DAVANTAGE de filles : le sens de l'erreur est choisi, on ne saute
    pas un EPIC parce qu'une de ses filles de reparation n'a pas ete vue.

    L'index evite le carre : 629 issues x 629 lectures de regex.
    """
    index: dict[int, list[dict]] = {}
    for it in pool:
        number = it.get("number")
        if number is None:
            continue
        parents = set(parent_refs(it))
        if it.get("parent") is not None:
            parents.add(it["parent"])
        for p in parents:
            index.setdefault(p, []).append(it)
    return index


def classify_grain(item: dict, catalog: NotebookCatalog,
                    pool: Sequence[dict],
                    index: dict[int, list[dict]] | None = None,
                    _seen: frozenset = frozenset()) -> tuple[str, str]:
    """Ce grain est-il de CREATION, au sens de la PORTE ?

    Regle : la creation est jugee sur le SOUS-GRAIN effectif.

      * un grain ordinaire : creation si sa livraison est un carnet neuf ;
      * un EPIC : creation s'il a AU MOINS UNE fille de creation et AUCUNE
        fille de reparation — servir cet EPIC ne peut alors servir que de
        la creation. Une seule fille de reparation suffit a le rendre
        non-creation : un EPIC qui a un pendant de reparation n'est jamais
        ecarte ;
      * un EPIC **consolide** (label `consolidation`) n'est JAMAIS une porte
        de creation : c'est un conteneur de consolidation, et l'ecart se
        porte sur la fille de creation qu'il contient, pas sur lui.

    Le veto de reparation du titre l'emporte sur tout.

    `_seen` coupe les CYCLES de rattachement : le graphe des parents est
    declare par les issues elles-memes, il peut donc contenir une boucle
    (A se declare fille de B, B se declare fille de A). Sans garde, la
    recursion ne s'arrete jamais — mesure du 2026-10-28 : `RecursionError`
    sur le pool reel. Un cycle se traite comme une fille non classable :
    elle ne compte ni comme creation ni comme reparation.
    """
    title = item.get("title") or ""
    if _RE_REPAIR.search(title):
        return VERDICT_REPAIR, "titre de reparation -> jamais ecarte"

    # Le label `consolidation` est un VETO, quelle que soit la livraison :
    # l'issue #23174 impose le controle negatif « aucune issue de
    # `consolidation` ou de correction ne peut etre ecarte ». Un grain
    # declare consolidation par son auteur est un grain de consolidation,
    # meme si son corps parle de carnet neuf.
    #
    # Mesure du 2026-10-28 : #23175 (registre anti-entropie) porte ce label
    # et son corps parle de « carnet » — sans ce veto, le grain etait ecarte.
    if has_consolidation_label(item):
        return (VERDICT_NEUTRAL,
                ("label consolidation : un grain de consolidation n'est "
                "jamais ecarte"))

    number = item.get("number")
    if number is not None:
        if number in _seen:
            return VERDICT_NEUTRAL, "cycle de rattachement : classe sur la fille"
        _seen = _seen | {number}

    if is_umbrella(item):
        if index is None:
            index = build_children_index(pool)
        filles = index.get(number, [])
        if not filles:
            return VERDICT_NEUTRAL, "umbrella sans fille ouverte : rien a servir"
        statuts = [classify_grain(f, catalog, pool, index, _seen)[0]
                   for f in filles]
        creations = statuts.count(VERDICT_CREATION)
        repars = statuts.count(VERDICT_REPAIR)
        if creations and not repars:
            return (VERDICT_CREATION,
                    (f"umbrella : {creations} fille(s) de creation, aucune de "
                    f"reparation sur {len(filles)}"))
        return (VERDICT_REPAIR,
                (f"umbrella : {repars} fille(s) de reparation sur {len(filles)} "
                f"-> jamais ecarte"))

    verdict, why = classify_delivery(item, catalog)
    if verdict == DELIVERY_NEW:
        return VERDICT_CREATION, why
    if verdict == DELIVERY_EXISTING:
        return VERDICT_REPAIR, why
    return VERDICT_NEUTRAL, why


def creation_proposals(pool: Sequence[dict], catalog: NotebookCatalog) -> list[dict]:
    """Les issues du pool qui PROPOSENT de la creation.

    C'est la definition de l'issue, lue littéralement : « un EPIC hors
    `consolidation`, ou un grain dont la livraison est un carnet neuf ».

    Elle ne dit pas ce que SERVIR un candidat produirait — c'est le role de
    `classify_grain`, qui juge le sous-grain effectif. Les deux quantites
    sont differentes et chacune est nommee :

      * une PROPOSITION mesure ce que le pool propose (la part de creation
        dans le pool ouvert, qui donne le budget) ;
      * une PORTE mesure ce que servir produirait (ce que le budget peut
        ecarter sans risquer de perdre un grain de reparation).

    Mesure du 2026-10-28 : 103 propositions sur 629 issues ouvertes, dont
    75 EPIC hors `consolidation` et 28 grains dont la livraison est un
    carnet neuf.
    """
    out: list[dict] = []
    for it in pool:
        # Meme veto que la porte : un grain declare consolidation n'est
        # jamais une proposition de creation.
        if has_consolidation_label(it):
            continue
        if is_umbrella(it):
            out.append(it)
            continue
        if classify_delivery(it, catalog)[0] == DELIVERY_NEW:
            out.append(it)
    return out



# --- le budget, derive -------------------------------------------------------

def derive_budget(pool: Sequence[dict], delivered_last_week: int,
                  catalog: NotebookCatalog) -> tuple[int, dict]:
    """Le budget de creation, DERIVE de deux mesures.

        part_creation = (propositions de creation du pool) / (pool)
        budget        = round(part_creation x grains livres la semaine)

    C'est la lecture directe de « le rythme auquel les issues ouvertes le
    proposent » : la part de creation que le pool propose, appliquee au
    nombre de grains que la flotte a livres la semaine ecoulee.

    Un plancher de 1 : le regime RALENTIT la creation, il ne l'ARRETE pas.
    """
    propositions = creation_proposals(pool, catalog)
    portes = [it for it in pool if classify_grain(it, catalog, pool)[0] == VERDICT_CREATION]
    part = (len(propositions) / len(pool)) if pool else 0.0
    brut = round(part * max(0, delivered_last_week))
    budget = max(1, brut)
    preuve = {
        "pool_ouvert": len(pool),
        "propositions_creation": len(propositions),
        "part_creation": round(part, 4),
        "portes_creation": len(portes),
        "grains_livres_semaine": delivered_last_week,
        "budget_brut": brut,
        "budget": budget,
        "plancher_applique": budget > brut,
    }
    return budget, preuve


# --- l'etat du compteur ------------------------------------------------------

def state_path() -> pathlib.Path | None:
    """Le fichier d'etat, ou None si la variable n'est pas posee.

    Elle n'est PAS posee par defaut : sans elle, aucune lane n'ecarte rien.
    """
    raw = os.environ.get(ENV_STATE, "").strip()
    return pathlib.Path(raw) if raw else None


def load_state(path: pathlib.Path | None = None) -> dict | None:
    """L'etat du budget, ou None s'il est absent/illisible (fail-OPEN)."""
    p = pathlib.Path(path) if path else state_path()
    if p is None:
        return None
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception:  # noqa: BLE001 - un etat illisible n'ecarte personne
        return None
    return data if isinstance(data, dict) else None


def over_budget(state: dict | None) -> tuple[bool, str]:
    """Le compteur depasse-t-il le budget ?

    Sans etat mesurable, la reponse est **NON** : fail-OPEN.
    """
    if not state:
        return False, "etat du budget indisponible : rien n'est ecarte"
    try:
        compte = int(state["carnets_neufs_demarres"])
        budget = int(state["budget"])
    except Exception:  # noqa: BLE001 - un etat mal forme n'ecarte personne
        return False, "etat du budget illisible : rien n'est ecarte"
    if compte > budget:
        return True, f"{compte} carnets neufs demarres sur 7 jours > budget {budget}"
    return False, f"{compte} carnets neufs demarres sur 7 jours <= budget {budget}"


# --- la porte du tapis --------------------------------------------------------

def creation_gate(pool: Sequence[dict],
                  catalog: NotebookCatalog | None = None,
                  state: dict | None = None) -> dict[int, str]:
    """Les grains de creation a ecarter, avec la cause nommee.

    Rend `{numero: cause}` — vide quand rien n'est ecarte. La porte est
    **fail-OPEN** sur ses trois entrees :

      * pas d'etat (le compteur n'a pas tourne) -> rien n'est ecarte ;
      * etat mal forme -> rien n'est ecarte ;
      * catalogue du depot inconnu -> rien n'est ecarte (un `git` muet ne
        doit pas vider le tapis).

    Et elle ne s'active QUE sur un depassement de budget mesure : le regime
    ralentit la creation, il ne l'arrete pas.
    """
    cat = catalog if catalog is not None else NotebookCatalog.from_repo()
    if not cat.known:
        return {}
    index = build_children_index(pool)

    # Le BUDGET : la porte principale, activee par un depassement mesure.
    st = state if state is not None else load_state()
    trop, why = over_budget(st)
    out: dict[int, str] = {}
    if trop:
        for it in pool:
            verdict, proof = classify_grain(it, cat, pool, index)
            if verdict != VERDICT_CREATION:
                continue
            out[it["number"]] = (
                f"{CAUSE} : {why} -- la creation est ralentie, pas arretee ; "
                f"servir un grain de reparation ou un grain de consolidation. "
                f"Motif : {proof}")

    # Le CLIQUET (#23175) : quand le registre anti-entropie ne peut pas
    # prouver que le chantier de padding progresse, un carnet neuf au nom
    # NON CONFORME est retenu — meme si le budget n'est pas depasse. C'est
    # le lien que l'issue #23174 nomme : « le budget de #23174 lit le
    # verdict RECULE de l'entree "padding et nommage" » — et, depuis le
    # rebasage du 2026-10-30, aussi les verdicts non comparables
    # (`INSTRUMENT ILLEGIBLE`), qui ne prouvent rien non plus.
    if cliquet_actif():
        for it in pool:
            if it["number"] in out:
                continue
            verdict, proof = classify_grain(it, cat, pool, index)
            if verdict != VERDICT_CREATION:
                continue
            non_conforme, motif = nom_non_conforme(it, cat)
            if non_conforme:
                out[it["number"]] = (
                    f"{CAUSE_NOM} : le chantier de padding ne progresse "
                    f"pas de facon etablie (registre anti-entropie) -- un "
                    f"carnet neuf au nom non conforme aggraverait le "
                    f"chantier. Motif : {motif}")
    return out


# --- le cliquet anti-entropie (#23175) ---------------------------------------

# L'etat des verdicts du registre anti-entropie. Il est ecrit par
# `scripts/coordination/anti_entropy_register.py`.
ENV_ANTI_ENTROPY = "COURSIA_ANTI_ENTROPY_FILE"

# L'entree du registre qui parle de padding et de nommage.
CLE_PADDING = "padding-nommage"

# La cause nommee du cliquet.
CAUSE_NOM = "NOM NON CONFORME"


def _chemin_anti_entropie() -> pathlib.Path | None:
    raw = os.environ.get(ENV_ANTI_ENTROPY, "").strip()
    if raw:
        return pathlib.Path(raw)
    base = os.environ.get("LOCALAPPDATA") or str(pathlib.Path.home())
    return pathlib.Path(base) / "CoursIA" / "anti_entropy_register.json"


def cliquet_actif(chemin: str | None = None) -> bool:
    """Le chantier de padding progresse-t-il ?

    Le cliquet retient un carnet neuf au nom non conforme **tant qu'on ne
    peut pas prouver que le chantier progresse** :

      * `RECULE` — le chantier recule : on retient ;
      * `STAGNE` — le chantier n'a pas bouge : le progres n'est pas prouve,
        donc on retient ;
      * `INSTRUMENT ILLEGIBLE` — la mesure n'est **pas comparable** (l'instrument
        a change, ou il est muet) : on ne peut rien prouver, donc on retient ;
      * une **comparaison suspendue** (fenetre de rebasage : la reference
        n'est pas une publication de sept jours) : le verdict porte sur un
        intervalle plus court, donc il ne prouve rien — on retient.

    C'est un garde fail-CLOSED sur la *comparabilite* de la mesure : avant
    le rebasage du 2026-10-30, l'entree « padding et nommage » comparait la
    valeur du jour (44, nouvel instrument) a une reference produite par
    l'ancien instrument (776) et affichait un `AVANCE` fabrique -- le cliquet
    s'ouvrait a contresens sur une base qui ne mesurait rien. Le verdict
    `INSTRUMENT ILLEGIBLE` existe deja dans l'organe ; il n'etait produit
    que par un echec de lecture.

    L'absence d'etat reste fail-OPEN : un etat absent, illisible, ou qui ne
    parle pas de padding, ne retient **rien** — l'absence de mesure n'est
    pas une sanction, et le registre n'a encore rien publie.
    """
    p = pathlib.Path(chemin) if chemin else _chemin_anti_entropie()
    if p is None:
        return False
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception:  # noqa: BLE001 - etat illisible = pas de cliquet
        return False
    if not isinstance(data, dict):
        return False
    entrees = data.get("entrees")
    if not isinstance(entrees, dict):
        return False
    entree = entrees.get(CLE_PADDING)
    if not isinstance(entree, dict):
        return False
    # La fenetre de comparaison est lue AVANT le verdict : une comparaison
    # SUSPENDUE (fenetre de rebasage : la reference n'est pas une
    # publication de sept jours) ne prouve aucun progres, quel que soit
    # le verdict affiche. Le fail-CLOSED doit etre VISIBLE -- un lecteur
    # qui ne voit que le verdict lit « STAGNE » comme « le chantier n'a
    # pas bouge depuis sept jours », et « aucune retention » comme « le
    # chantier s'est ameneliore ».
    if entree.get("comparaison_suspendue"):
        return True
    verdict = str(entree.get("verdict") or "").upper()
    # Seul un verdict etabli qui PROUVE le progres libere. Tout le reste
    # retient :
    #
    #   * `RECULE` — le chantier recule ;
    #   * `STAGNE` — le chantier n'a pas bouge : rien n'est prouve, donc
    #     rien n'est libere (c'est le meme principe que pour une mesure
    #     non comparable) ;
    #   * `INSTRUMENT ILLEGIBLE` — la mesure n'est pas comparable ;
    #   * `PREMIERE MESURE`, verdict inconnu — rien a dire.
    #
    # On ne presume jamais le progres : le cliquet retient par defaut et
    # ne s'ouvre que sur une preuve.
    return verdict != "AVANCE"


def _organe_noms():
    """L'organe d'inventaire des noms, ou None s'il est absent."""
    try:
        dossier = pathlib.Path(__file__).resolve().parent / "notebook_tools"
        if str(dossier) not in sys.path:
            sys.path.insert(0, str(dossier))
        import inventory_notebook_names as inv
    except Exception:  # noqa: BLE001 - organe absent = pas de classification
        return None
    return inv


def _organe_renommage():
    """L'organe de renommage canonique, ou None s'il est absent."""
    try:
        dossier = pathlib.Path(__file__).resolve().parent / "notebook_tools"
        if str(dossier) not in sys.path:
            sys.path.insert(0, str(dossier))
        import rename_notebooks as rn
    except Exception:  # noqa: BLE001 - organe absent = pas de renommage
        return None
    return rn


def classer_nom(chemin: str) -> str:
    """La classification du nom d'un carnet, par l'organe canonique.

    L'organe est `scripts/notebook_tools/inventory_notebook_names.py` : on
    l'appelle, on ne reimplement pas ses regles (organ-first). Si l'import
    echoue, on ne classe rien — le cliquet ne retient alors personne.

    Le noyau est passe a `None` : un carnet qui n'existe pas encore n'a pas
    de noyau lisible. Cela ne fausse que les jugements qui en dependent, et
    le cliquet n'actionne QUE la classe `rename_proposed` (un defaut de
    zero-pad, independant du noyau) — voir `nom_non_conforme`.
    """
    inv = _organe_noms()
    if inv is None:
        return ""
    try:
        stem = re.sub(r"\.ipynb$", "", chemin, flags=re.IGNORECASE)
        basename = chemin.rsplit("/", 1)[-1]
        return inv._classify(chemin, stem, inv.index_key(basename), None,
                             inv._suffix(stem), inv._index_zero_padded(basename))
    except Exception:  # noqa: BLE001 - classification impossible = pas de verdict
        return ""


def defaut_zero_pad(chemin: str) -> str:
    """Le nom porte-t-il un rang qui n'est PAS zero-pad ?

    **Une seule des deux moities du defaut de padding.** Les deux
   organes canoniques le voient chacun sur une forme de nom differente,
    et cette fonction ne couvre que la seconde :

      * l'organe d'inventaire (`inventory_notebook_names`) voit le rang
        d'un nom a index EN TETE (`1_OpenAI_Intro`) et le rend
        `rename_proposed` ;
      * l'organe de renommage (`rename_notebooks`) voit le rang d'un nom
        a PREFIXE DE SERIE (`ML-7-Recommendation`) et le rendrait
        `ML-07-Recommendation`.

    Mesure du 2026-10-28 : 708 des 813 `ambigu` de l'inventaire sont des
    noms a prefixe de serie — son `INDEX_RE` ne lit qu'un index en tete.
    L'inventaire les appelle donc `ambigu`, ce qui est un **verdict
    d'INCERTITUDE**, pas un defaut : les retenir tous reviendrait a
    bloquer 6 des 11 creations reelles du pool (#23142, #23140, #22810,
    #21881, #21752) pour des noms parfaitement conformes.

    On compare donc le rang du nom au rang que le renommage canonique
    produirait : s'ils different, le nom sera renumerote — c'est le
    chantier de padding qui grossit. Le calcul passe par
    `canonical_target` de l'organe, on ne reimplement pas sa grammaire.
    """
    rn = _organe_renommage()
    if rn is None:
        return ""
    try:
        basename = chemin.rsplit("/", 1)[-1]
        stem = re.sub(r"\.ipynb$", "", basename, flags=re.IGNORECASE)
        m = rn.STEM_RE.match(stem)
        if not m:
            # Hors grammaire de serie (index en tete, separateur `_`) :
            # ce n'est PAS le chantier du padding, c'est celui du prefixe.
            return ""
        rang = m.group("num")
        # Le noyau est inconnu (fichier a creer) : il ne change que la
        # queue du nom, jamais le rang. On compare donc les RANGS.
        cible = rn.canonical_target(basename, "python")
        m2 = rn.STEM_RE.match(re.sub(r"\.ipynb$", "", cible, flags=re.IGNORECASE))
        if not m2:
            return ""
        rang_cible = m2.group("num")
        if rang_cible and rang_cible != rang:
            return (f"le rang {rang} n'est pas zero-pad : le renommage "
                    f"canonique le donnerait {rang_cible} (convention `0N`)")
    except Exception:  # noqa: BLE001 - mesure impossible = pas de verdict
        return ""
    return ""


def nom_non_conforme(item: dict, catalog: NotebookCatalog) -> tuple[bool, str]:
    """Le carnet que ce grain creerait porterait-il un nom non conforme ?

    Une seule source : **le nom du fichier que l'issue nomme**. Un issue
    qui ne nomme pas son fichier ne permet aucun jugement de nom — et le
    cliquet ne retient que ce qu'il sait.

    Deux organes canoniques, chacun sur sa forme de nom :

      * `inventory_notebook_names` rend `rename_proposed` quand le rang
        d'un nom a index EN TETE n'est pas zero-pad (`1_OpenAI_Intro`) ;
      * `rename_notebooks` renumerote le rang d'un nom a PREFIXE DE SERIE
        (`ML-7-Recommendation` -> `ML-07-Recommendation`).

    Les deux sont lus, jamais reimplementes (organ-first).

    **Ce qui n'est PAS un defaut** : la classe `ambigu` de l'inventaire.
    Mesure du 2026-10-28 sur le pool reel : 708 des 813 `ambigu` sont des
    noms a prefixe de serie (`Complexity-02b-...`), que l'inventaire ne
    sait pas lire — son `INDEX_RE` ne voit qu'un index en tete. Les
    retenir reviendrait a ecarter 6 des 11 creations reelles du pool
    (#23142, #23140, #22810, #21881, #21752) alors que leurs noms sont
    conformes : c'est un verdict d'INCERTITUDE, pas un defaut. Le cliquet
    n'actionne que les DEUX defauts de zero-pad, mesures par l'organe.
    """
    title = item.get("title") or ""
    body = item.get("body") or ""
    cites = absent_notebooks(title + "\n" + body, catalog)
    if not cites:
        return False, ""
    chemin = cites[0]

    # 1. L'inventaire : zero-pad d'un index en tete.
    classe = classer_nom(chemin)
    if classe == "rename_proposed":
        return True, (f"le carnet `{chemin}` a un rang non zero-pad "
                      f"(l'inventaire le classe {classe})")

    # 2. Le renommage : zero-pad d'un rang a prefixe de serie.
    motif = defaut_zero_pad(chemin)
    if motif:
        return True, f"le carnet `{chemin}` : {motif}"

    return False, ""
