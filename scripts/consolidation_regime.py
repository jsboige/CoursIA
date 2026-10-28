#!/usr/bin/env python3
"""Regime consolidation : le tapis cesse de servir les grains dont la
livraison est un CARNET NEUF.

Contexte (arbitrage user du 2026-10-28, propagé par le coordinateur)
-----------------------------------------------------------------------
« on a un besoin enorme de consolidation et les issues d'audit s'accumulent,
les agents continuent à produire de nouveaux Notebooks à un rythme encore
supérieur à celui qui m'a fait ticker sur la série Serre. On déraille
complètement. »

Regle appliquee : tant que le regime tient, **un grain tire dont la
livraison est un carnet neuf se saute** (le coordinateur l'ecrit en une
ligne sur l'issue, puis tire le suivant). Le plancher G-VAR-1 se tient des
ormais par une reparation de fond d'un carnet EXISTANT, avec re-execution.

Pourquoi ce module existe
-------------------------
Sans organe, la regle reste une phrase : elle depend de la memoire de la
lane, et les 22 PRs ouvertes qui ajoutaient chacune un carnet neuf au
moment de l'arbitrage montent que la phrase ne tient pas. L'organe rend la
regle **mesurable** et **rejouable** : il classe chaque candidat du tapis
et dit pourquoi il l'ecarte.

Ce que le module ne fait PAS
----------------------------
Il ne devine pas. Il oppose le depot a l'issue :

  O1 SIEGE   : le titre nomme une serie et un rang a deux chiffres
               (« Serre 100 — carnet 30 », « NLP — carnet 07 »). Si
               `origin/main` porte deja un carnet de ce rang dans cette
               serie, le grain parle d'un carnet EXISTANT ; sinon d'un
               carnet NEUF. Le depot est l'oracle, pas la prose.
  O2 FICHIER : l'issue cite un chemin `.ipynb` dont le NOM ne correspond a
               aucun carnet du depot ET son TITRE annonce une creation.
  O3 PHRASE  : l'issue DECLARE la creation (« premier numero libre »,
               « Slot: », « nouveau carnet », « numero libre suivant »).

L'ordre compte : **O1 passe avant O3**. Une issue est datee de sa REDACTION
— son corps peut encore dire « premier numero libre » alors que le carnet a
ete livre depuis (mesure : #21799 « [GameTheory] 11c », dont le rang 11c est
desormais sur `main`). Le depot est l'etat courant, la prose un temoignage
date ; l'inverse ecarterait un grain dont la livraison est deja faite.

Il n'y a PAS d'oracle d'umbrella, et c'est un choix mesure : une EPIC qui
cite une sous-issue de creation herite de son classement, et l'EPIC qui cite
UNE EPIC qui cite une sous-issue de creation l'herite aussi. Sur les 629
issues ouvertes, cette cascade a retourne **plus de 60 EPIC** du depot --
dont des EPIC de gouvernance (« Les body d'Epic ne sont jamais reecrits »).
Une cascade est une machine a faux positifs : l'EPIC n'est pas un grain
(la regle du tapis le dit : « un EPIC en tete se sert par un sous-grain »),
et le classement d'un conteneur n'est pas le classement de son contenu.

Un VETO de reparation (un mot d'audit, de correction, de deplacement, de
prose dans le TITRE) annule le classement : un grain de reparation ne doit
 JAMAIS etre saute, car cela ferait perdre des grains de consolidation --
 exactement ce que le regime demande.

Mesure (2026-10-28, `origin/main` = 8e9eaaaa0ef)
------------------------------------------------
Jeu de controle derive des PRs OUVERTES (donc de la realite, pas d'une
intention) :

  positifs  = issues citees par une PR `Add|Feat` qui AJOUTE un `.ipynb`
               absent de `main` aujourd'hui  -> grain de CREATION ;
  negatifs  = issues citees par une PR `Fix|Docs|Refactor|Rename|Update`
               qui MODIFIE un `.ipynb` present sur `main` -> grain de
               REPARATION.

Sur 19 positifs et 55 negatifs (une issue presente dans les deux lots est
exclue), le classement rend :

    precision 1,00 (0 faux positif sur 55 negatifs)
    rappel    0,92 (11 des 12 positifs classables detectes ; 7
                     indetermines : ce sont les cas ou la livraison n'est
                     pas nommee, ou ou le grain est une EPIC — un
                     CONTENEUR, dont le classement se fait sur le
                     sous-grain)

Le sens de l'erreur est choisi : on **saute** un grain de creation quand
on le sait, on **ne saute pas** un grain qu'on ne sait pas classer. Un
faux positif ferait perdre un grain de reparation ; un faux negatif laisse
passer un carnet neuf, que la lane declare alors sur l'issue.

La METRIQUE ne suffit pas : la liste reelle des ecarts a ete lue a l'oeil,
sur les 629 issues ouvertes. Elle a revele deux faux positifs que le jeu
de controle ne portait pas (il est lui-meme derive des PRs, donc biaise
vers les formes que les PRs couvrent) :

  #22056 « Collision d'identifiant 04-17 dans GenAI/Audio » — une
         RENUMEROTATION, donc un grain de consolidation : le veto a gagne
         le mot « collision » ;
  #21871 « ... le PDF a ete archive 11 jours apres la PR » — le « 11 » est
         une DUREE, pas un rang : la garde d'unite l'emporte.

Le module est sans effet tant qu'on ne l'appelle pas : le picker expose un
interrupteur explicite (`--consolidation-regime`), pose par le
coordinateur pendant le regime et retire quand le user leve le regime. La
meme regle se pose FLEETE par la variable d'environnement
`COURSIA_CONSOLIDATION_REGIME=1` — sans elle, le coordinateur devrait
demander a chaque lane de modifier sa propre ligne de commande, et le
regime tiendrait a la memoire de douze lignes : c'est precisement ce que
l'organe pretend supprimer.
"""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
from collections.abc import Iterable, Sequence

VERDICT_NEW = "carnet_neuf"
VERDICT_EXISTING = "carnet_existant"
VERDICT_UNKNOWN = "indetermine"

# La variable d'environnement du regime FLEETE. Sans elle, le coordinateur
# devrait demander a chaque lane de modifier sa propre ligne de commande :
# le regime tiendrait alors a la memoire de douze lignes, ce que l'organe
# pretend justement supprimer.
ENV_VAR = "COURSIA_CONSOLIDATION_REGIME"


def regime_enabled(flag: bool = False, env: str | None = None) -> bool:
    """L'interrupteur du regime : drapeau de ligne de commande OU variable
    d'environnement fleet.

    Les deux sont **sans effet tant qu'ils ne sont pas poses** : c'est ce qui
    permet de livrer l'organe sans changer le comportement d'une seule lane.
    """
    if flag:
        return True
    value = env if env is not None else os.environ.get(ENV_VAR, "")
    return value.strip().lower() in {"1", "true", "yes", "on"}

# --- motifs de titre -------------------------------------------------------

# Un rang de carnet : deux chiffres (+ lettre eventuelle). Le deuxieme chiffre
# est exige parce que « Tweety 1.28 » (une version) ne doit pas etre lu
# comme le rang 1 d'une serie.
#
# La garde d'UNITE est ce qui empeche une QUANTITE en prose d'etre lue comme
# un rang : mesure du 2026-10-28, #21871 « ... le PDF archive, et le PDF a
# ete archive 11 jours apres la PR » resolvait la serie « archive » et le
# rang « 11 » — un grain d'AUDIT sur un carnet existant, entendu comme une
# creation. Un rang suivi d'une unite de duree n'est pas un rang.
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

# Un chemin de carnet cite par l'issue.
_RE_IPYNB = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./\- ]*?\.ipynb")

# Les phrases par lesquelles une issue DECLARE qu'elle cree un carnet.
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

# L'INTENTION de creation, lue dans le TITRE. Elle ne suffit pas a conclure
# (O2 a besoin d'elle pour corroborer un fichier absent), mais elle evite
# qu'un audit qui cite un carnet au nom approximatif soit pris pour une
# creation.
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

# Une issue umbrella (EPIC) est un CONTENEUR, pas un grain : la regle du
# tapis dit « un EPIC en tete se sert par un sous-grain, jamais par un
# claim de l'EPIC entier ». Elle n'est donc jamais sautee -- son classement
# se fait sur le sous-grain que la lane tirera.
_RE_UMBRELLA = re.compile(r"^\s*\[?\s*EPIC\b", re.IGNORECASE)



def _norm(text: str) -> str:
    return re.sub(r"[^a-z0-9]", "", (text or "").lower())


def _tokens(text: str) -> list[str]:
    return re.findall(r"[A-Za-z][A-Za-z0-9]{1,}", text or "")


class NotebookCatalog:
    """L'etat du depot : les carnets connus, leurs noms et leurs series.

    Construit depuis `git ls-tree -r <ref> --name-only`. Une liste VIDE est
    un catalogue INCONNU : le classement rend alors `indetermine` partout et
    rien n'est saute (le regime ne doit pas vider le tapis parce qu'un
    `git` a echoue).
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


def classify(item: dict, catalog: NotebookCatalog) -> tuple[str, str]:
    """Classe un candidat du tapis.

    Rend `(verdict, preuve)` avec verdict dans
    {`carnet_neuf`, `carnet_existant`, `indetermine`}. La preuve est une
    phrase courte, citable telle quelle sur l'issue.
    """
    title = item.get("title") or ""
    body = item.get("body") or ""

    if _RE_REPAIR.search(title):
        return VERDICT_EXISTING, "titre de reparation -> livraison d'un carnet existant"

    if _RE_UMBRELLA.search(title):
        return VERDICT_UNKNOWN, "umbrella : le classement se fait sur le sous-grain"

    if not catalog.known:
        return VERDICT_UNKNOWN, "catalogue du depot indisponible"

    cited = absent_notebooks(title + "\n" + body, catalog)
    if cited and _RE_CREATE_INTENT.search(title):
        return VERDICT_NEW, f"carnet cite absent du depot : {cited[0]}"

    # L'ORACLE DU DEPOT passe AVANT la prose. Une issue est datee de sa
    # REDACTION : son corps peut encore dire « premier numero libre »
    # alors que le carnet a ete livre depuis (mesure : #22488 « Serre 100 --
    # carnet 28 », dont le rang 28 est sur `main`). Le depot est l'etat
    # courant ; la prose est un temoignage date. L'inverse servirait a
    # ecarter un grain dont la livraison est deja faite.
    serie, rank = series_and_rank(title, catalog)
    if serie and rank:
        exists = rank_exists(catalog, serie, rank)
        if exists is True:
            return VERDICT_EXISTING, f"rang {rank} deja livre dans la serie {serie}"
        if exists is False:
            return VERDICT_NEW, f"rang {rank} absent de la serie {serie}"

    if _RE_CREATE_PHRASE.search(title + "\n" + body):
        return VERDICT_NEW, "l'issue declare la creation d'un carnet"

    return VERDICT_UNKNOWN, "livrable non nomme"


def filter_pool(pool: Sequence[dict], catalog: NotebookCatalog
                ) -> tuple[list[dict], list[tuple[dict, str, str]]]:
    """Separe le pool en (candidats servis, candidats sautes).

    Un candidat n'est saute que si le classement rend `carnet_neuf` : le
    veto de reparation garantit qu'un grain de consolidation n'est jamais
    ecarte.
    """
    kept: list[dict] = []
    skipped: list[tuple[dict, str, str]] = []
    for it in pool:
        verdict, why = classify(it, catalog)
        if verdict == VERDICT_NEW:
            skipped.append((it, verdict, why))
        else:
            kept.append(it)
    return kept, skipped
