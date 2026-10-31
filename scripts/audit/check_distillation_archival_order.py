#!/usr/bin/env python3
"""check_distillation_archival_order.py — ordre redaction / archivage des distillations.

Classe de defaut visee (#21858, regle ``bibliography-hygiene.md`` « lire avant
d'attribuer », #21848) : un livrable de distillation est redige **avant** que sa
publication source n'atterrisse dans le gisement bibliographique, et n'est
jamais relu contre elle ensuite.

Cas fondateur : le carnet ICT-36c (#20668) est committe le 2026-10-14 a 05:46Z,
son papier est archive a 06:08Z ; deux attributions au papier sont fausses. Les
trois reviewers etaient verts (NanoClaw, Hermes, APPROVE du coordinateur) : aucun
n'a compare le livrable au PDF, parce qu'a l'heure de la review le PDF n'existait
pas encore dans le gisement.

L'audit de #21858 a rejoue la mesure a la main sur 137 paires PR x issue x
papier et trouve **13 PRs redigees avant l'archivage** et **50 PRs a source
absente**. Il conclut lui-meme que la mesure est rejouable et souhaite cet
organe (« Si la mesure se revele repetable, un organe ``scripts/audit/`` qui la
rejoue est bienvenu, en PR separee »).

## Ce que l'organe mesure

Deux causes MECANIQUES, et elles seules :

1. **Presence de la source** — le PDF cite dans le fil de l'issue ou de la PR
   existe-t-il dans le gisement ?
2. **Ordre** — le premier commit de la PR precede-t-il la date d'archivage ?

Il ne juge **pas** les attributions : confronter chaque phrase au PDF
(``pdftotext`` + grep du terme attribue + page citee) demande une lecture, que
la regle place explicitement du cote humain. Un ``CONFORME`` de cet organe dit
« la source etait la, et l'ordre est bon » — jamais « les attributions sont
justes ».

## Verdicts

| Verdict | Sens |
|---|---|
| ``CONFORME`` | source presente, et premier commit posterieur a l'archivage (+ tolerance) |
| ``ECART_ORDRE`` | source presente, mais le livrable a ete redige avant l'archivage par plus que la tolerance |
| ``SOURCE_ABSENTE`` | le PDF cite n'est pas dans le gisement : regle 1 de la regle violee, depot a demander |
| ``INDETERMINE`` | une des deux dates est illisible (pas de commit lisible, pas d'archivage datable) |
| ``UMBRELLE`` | l'issue cite plus de ``MAX_SOURCES_LIVRABLE`` papiers : c'est un conteneur (audit, EPIC), la paire ne mesure rien et sort du decompte |

## Priorite de la source : le livrable d'abord

Les citations sont lues dans les textes de la **PR** ; le fil de l'issue n'est
qu'un repli, et ``origine_source`` dit lequel a servi. Mesure du 29/10 : sans
cette priorite, trois PRs correctes de #21858 — qui citent chacune leur papier
dans leur corps — etaient appariees au papier du fil de l'issue d'audit, donc a
une source qui n'etait pas la leur. Et quand un livrable cite **deux** papiers
(distillation en deux parties, #21875), l'ordre doit tenir pour **les deux** :
c'est la plus tardive des archives qui fait foi.

## Dates, et pourquoi deux provenances

L'archivage se date de deux facons, dans cet ordre :

1. le commentaire ``[INFO] archivage`` du fil, quand il porte une date ISO —
   c'est la parole de la lane qui a archive ;
2. a defaut, le ``ctime`` du fichier.

Le ``ctime`` n'a pas le meme sens partout : sous Windows c'est la **creation**
(mesure de l'audit, fiable au fichier pres) ; sous POSIX c'est le **changement
d'inode**, qu'une copie ou une synchro GDrive peut faire avancer. Le rapport
nomme donc toujours la provenance retenue (``archivage_provenance``), pour
qu'un ``ECART_ORDRE`` fonde sur un ``ctime`` POSIX se discute au lieu de se
croire.

Tolerance par defaut : **180 s**. Mesure de l'audit — sur les trois cas ou le
commentaire et le ``ctime`` sont tous deux disponibles, l'ecart va jusqu'a 3 min
(Subramani : ``ctime`` 06:07:58Z, commentaire 06:08:10Z).

## Usage

    py scripts/audit/check_distillation_archival_order.py --self-test
    py scripts/audit/check_distillation_archival_order.py --since 2026-09-01
    py scripts/audit/check_distillation_archival_order.py --since 2026-09-01 \\
        --gisement "G:/Mon Drive/MyIA/IA/Bibliographie IA" --json
    py scripts/audit/check_distillation_archival_order.py --paires paires.json

Codes de sortie : ``0`` mesure faite (quel que soit le verdict), ``1`` self-test
en echec, ``3`` instrument indisponible (``gh`` absent, gisement absent, reseau).
Un ``3`` est une **question**, jamais un « aucune distillation fautive » : sans
instrument, l'organe ne mesure rien et le dit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence

TOLERANCE_S = 180
SEUIL_TITRE = 0.60

MARQUEURS_ISSUE = ("[Distillation]", "[Veille→Distillation]", "[Veille->Distillation]")

CONFORME = "CONFORME"
ECART_ORDRE = "ECART_ORDRE"
SOURCE_ABSENTE = "SOURCE_ABSENTE"
INDETERMINE = "INDETERMINE"
UMBRELLE = "UMBRELLE"

# Au-dela de ce nombre de papiers cites par le SEUL fil de l'issue, l'issue est
# un conteneur (audit, EPIC) et non un livrable : la paire ne mesure rien.
MAX_SOURCES_LIVRABLE = 6


# --------------------------------------------------------------------------
# Normalisation de texte
# --------------------------------------------------------------------------

def normaliser(texte: str) -> str:
    """Minuscule, sans accents, separateurs unifies.

    « Trèfle knots » et « trefle-knots » doivent produire les memes jetons :
    les noms de fichiers du gisement et les titres d'issues ne s'accordent ni
    sur les accents ni sur les separateurs.
    """
    if not texte:
        return ""
    decompose = unicodedata.normalize("NFKD", texte)
    sans_accent = "".join(c for c in decompose if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", " ", sans_accent.lower()).strip()


def jetons(texte: str) -> set[str]:
    """Jetons significatifs : au moins 3 caracteres, hors connecteurs."""
    vides = {"the", "and", "les", "des", "une", "par", "pour", "sur", "dans", "avec", "pdf"}
    return {j for j in normaliser(texte).split() if len(j) >= 3 and j not in vides}


def score_titre(nom_fichier: str, titre: str) -> float:
    """Recouvrement du titre par les jetons du nom de fichier, dans [0, 1].

    Asymetrique a dessein : on demande « le titre est-il dans ce nom de
    fichier », pas l'inverse — un nom de fichier porte en plus des auteurs et
    une annee, qu'un titre n'a pas.
    """
    jetons_titre = jetons(titre)
    if not jetons_titre:
        return 0.0
    return len(jetons_titre & jetons(nom_fichier)) / len(jetons_titre)


# --------------------------------------------------------------------------
# Resolution de la source
# --------------------------------------------------------------------------

_RE_PDF = re.compile(r"\.pdf\b", re.IGNORECASE)
# Delimitatifs de PROSE. Ni les parentheses ni les crochets n'y figurent : les
# noms du gisement en contiennent (« … (arXiv 2609.14555).pdf »), et les
# traiter comme des delimiteurs reduisait la citation a « .pdf » — mesure sur
# #21875, ou les deux papiers de l'issue devenaient introuvables.
_DELIMITANTS = set("`\"'<>|*;!?=\n\r\t")
_LONGUEUR_MAX_CITATION = 240


def extraire_chemins_pdf(textes: Iterable[str]) -> list[str]:
    """Citations de PDF dans des corps de texte, basename garde, dedoublonnees.

    Les noms de fichiers du gisement contiennent des **espaces**
    (« 2026 - Michael and Kenta - Trefoil knots in algebraic geometry.pdf ») :
    un motif ``[^\\s]+\\.pdf`` ne capturait que « Trefoil.pdf », et
    l'appariement exact echouait. On procede donc a l'envers — on cherche
    ``.pdf`` et on **remonte** a gauche tant que le caractere appartient au nom
    (espaces et separateurs de chemin compris), en s'arretant sur le premier
    delimitatif de prose (backtick, guillemet, parenthese, ponctuation forte).

    Une citation en prose nue (« voir Sona Technical Report.pdf ») garde son
    preambule : c'est la **resolution** qui l'absorbe par couverture de jetons,
    pas l'extraction qui devine ou commence le nom.
    """
    vus: dict[str, None] = {}
    for texte in textes:
        texte = texte or ""
        for m in _RE_PDF.finditer(texte):
            fin = m.end()
            debut = m.start()
            while (
                debut > 0
                and (fin - debut) < _LONGUEUR_MAX_CITATION
                and texte[debut - 1] not in _DELIMITANTS
            ):
                debut -= 1
            brut = texte[debut:fin].strip()
            if not brut:
                continue
            nom = re.split(r"[\\/]", brut)[-1].strip()
            # Une citation reduite a « .pdf » ne porte aucun nom : la garder
            # ferait echouer l'appariement exact ET le repli elide, donc
            # fabriquerait un SOURCE_ABSENTE a partir de rien.
            if nom and jetons(nom) and nom.lower() not in {v.lower() for v in vus}:
                vus[nom] = None
    return list(vus)


def indexer_gisement(gisement: Path) -> dict[str, Path]:
    """Index basename normalise -> chemin, pour tous les PDF du gisement."""
    index: dict[str, Path] = {}
    if not gisement.is_dir():
        return index
    for chemin in gisement.rglob("*.pdf"):
        index.setdefault(normaliser(chemin.stem), chemin)
    return index


def _sans_suffixe(texte: str) -> str:
    """Cle d'appariement d'une citation : normalisee, sans le ``.pdf`` final."""
    return re.sub(r"\s*pdf$", "", normaliser(texte)).strip()


def _couverture(reference: Iterable[str], cible: set[str]) -> float:
    """Part des jetons de ``reference`` presents dans ``cible``."""
    jetons_reference = set(reference)
    if not jetons_reference:
        return 0.0
    return len(jetons_reference & cible) / len(jetons_reference)


def resoudre_sources(
    index: dict[str, Path],
    chemins_cites: Sequence[str],
    titre: str = "",
    seuil: float = SEUIL_TITRE,
    min_jetons: int = 3,
    limite: int = 4,
) -> list[dict[str, Any]]:
    """Toutes les sources citees resolues, du plus sur au plus faible.

    Trois regimes, du plus sur au plus faible, et chacun s'arrete des qu'il a
    rendu quelque chose :

    1. **nom_cite** — la citation normalisee est exactement une cle du gisement.
       Toutes les exactes sont rendues : une distillation en deux parties cite
       legitiment deux papiers (#21875) ;
    2. **nom_cite** (elision) — un fil cite tantot le chemin complet, tantot le
       seul titre du fichier : on compare par **couverture de jetons** dans les
       deux sens. Le sens inverse rattrape un chemin absolu (le nom du fichier
       est dedans) ; le sens direct rattrape une citation qui a laisse tomber
       l'annee et les auteurs. Une citation de moins de ``min_jetons`` jetons ne
       passe **jamais** par ce regime : un ``report.pdf`` generique apparierait
       n'importe quoi ;
    3. **titre** — repli declare, pour les fils qui ne nomment jamais le
       fichier. Une absence obtenue par ce repli ne se lit donc pas comme un
       nom cite introuvable, et le rapport le dit.
    """
    exactes: list[dict[str, Any]] = []
    vus: set[str] = set()
    for cite in chemins_cites:
        chemin = index.get(_sans_suffixe(cite))
        if chemin is not None and str(chemin) not in vus:
            vus.add(str(chemin))
            exactes.append({"methode": "nom_cite", "chemin": str(chemin), "score": 1.0})
    if exactes:
        return exactes[:limite]

    scores: dict[str, tuple[float, str]] = {}
    for cite in chemins_cites:
        jetons_cite = jetons(cite)
        if len(jetons_cite) < min_jetons:
            continue
        for cle, chemin in index.items():
            jetons_cle = jetons(cle)
            score = max(
                _couverture(jetons_cite, jetons_cle),
                _couverture(jetons_cle, jetons_cite),
            )
            if score >= seuil and score > scores.get(str(chemin), (0.0, ""))[0]:
                scores[str(chemin)] = (score, "nom_cite")
    if scores:
        retenues = sorted(scores.items(), key=lambda kv: -kv[1][0])[:limite]
        return [{"methode": m, "chemin": c, "score": round(s, 3)} for c, (s, m) in retenues]

    if titre:
        scores = {}
        for cle, chemin in index.items():
            score = score_titre(cle, titre)
            if score >= seuil:
                scores[str(chemin)] = (score, "titre")
        if scores:
            retenues = sorted(scores.items(), key=lambda kv: -kv[1][0])[:limite]
            return [{"methode": m, "chemin": c, "score": round(s, 3)} for c, (s, m) in retenues]
    return []


def resoudre_source(
    index: dict[str, Path],
    chemins_cites: Sequence[str],
    titre: str = "",
    seuil: float = SEUIL_TITRE,
    min_jetons: int = 3,
) -> dict[str, Any]:
    """Meilleure source unique, ou un verdict d'absence declare.

    Enveloppe de :func:`resoudre_sources` pour les appels qui n'ont besoin que
    d'une reponse binaire — et pour dire par quelle methode l'absence a ete
    etablie.
    """
    trouvees = resoudre_sources(index, chemins_cites, titre=titre, seuil=seuil, min_jetons=min_jetons)
    if trouvees:
        return {"trouvee": True, **trouvees[0]}
    methode = "titre" if titre else "aucune"
    meilleur = 0.0
    for cle in index:
        meilleur = max(meilleur, score_titre(cle, titre) if titre else 0.0)
    return {"trouvee": False, "methode": methode, "chemin": None, "score": round(meilleur, 3)}


# --------------------------------------------------------------------------
# Dates
# --------------------------------------------------------------------------

_RE_ISO = re.compile(r"(\d{4}-\d{2}-\d{2})[T ](\d{2}:\d{2})(?::(\d{2}))?\s*(Z|[+-]\d{2}:?\d{2})?")


def date_iso(valeur: str) -> datetime | None:
    """Parse une date ISO (suffixe ``Z`` compris) en datetime UTC conscient.

    Une date sans fuseau est refusee : la supposer locale est exactement le
    « faux skew cross-clock » qui fait conclure a un ecart d'ordre inexistant.
    """
    if not valeur:
        return None
    m = _RE_ISO.search(valeur)
    if not m:
        return None
    jour, heure, seconde, fuseau = m.groups()
    if fuseau is None:
        return None
    if fuseau == "Z":
        decalage = timedelta(0)
    else:
        signe = 1 if fuseau[0] == "+" else -1
        brut = fuseau[1:].replace(":", "")
        decalage = signe * timedelta(hours=int(brut[:2]), minutes=int(brut[2:4]))
    try:
        naif = datetime.fromisoformat(f"{jour}T{heure}:{seconde or '00'}")
    except ValueError:
        return None
    return naif.replace(tzinfo=timezone(decalage)).astimezone(timezone.utc)


def date_archivage_commentaire(commentaires: Iterable[str]) -> datetime | None:
    """Date ISO portee par un commentaire ``[INFO] archivage``, s'il y en a une seule.

    Deux dates contradictoires ne se departagent pas mecaniquement : on rend
    ``None`` plutot que d'en choisir une, et le rapport retombe sur le ``ctime``.
    """
    dates: list[datetime] = []
    for corps in commentaires:
        texte = corps or ""
        if "[INFO] archivage" not in texte.lower() and "archivage" not in texte.lower():
            continue
        for m in _RE_ISO.finditer(texte):
            d = date_iso(m.group(0))
            if d is not None and d not in dates:
                dates.append(d)
    return dates[0] if len(dates) == 1 else None


def date_ctime(chemin: Path) -> datetime | None:
    """``ctime`` du fichier, en UTC explicite.

    Sous Windows : date de creation (mesure de l'audit). Sous POSIX : date de
    changement d'inode — le rapport le dit, il ne le corrige pas.
    """
    try:
        return datetime.fromtimestamp(os.stat(chemin).st_ctime, tz=timezone.utc)
    except OSError:
        return None


# --------------------------------------------------------------------------
# Classement
# --------------------------------------------------------------------------

def classer(
    premier_commit: datetime | None,
    archivage: datetime | None,
    source_trouvee: bool,
    tolerance_s: int = TOLERANCE_S,
) -> str:
    """Verdict mecanique d'une paire (livrable, source).

    L'ordre de priorite n'est pas neutre : une source absente est un defaut
    **plus fort** qu'un ecart d'ordre (le livrable est ecrit sans source du
    tout), et il reste vrai meme quand les dates manquent. On le tranche donc
    en premier.
    """
    if not source_trouvee:
        return SOURCE_ABSENTE
    if premier_commit is None or archivage is None:
        return INDETERMINE
    if premier_commit.tzinfo is None:
        premier_commit = premier_commit.replace(tzinfo=timezone.utc)
    if archivage.tzinfo is None:
        archivage = archivage.replace(tzinfo=timezone.utc)
    if (archivage - premier_commit).total_seconds() > tolerance_s:
        return ECART_ORDRE
    return CONFORME


def classer_sources(
    premier_commit: datetime | None,
    datations: Sequence[tuple[datetime | None, str]],
    tolerance_s: int = TOLERANCE_S,
) -> str:
    """Verdict d'une paire dont le livrable cite **plusieurs** sources.

    Une distillation en deux parties doit trouver **ses deux** papiers en place :
    l'ordre est bon quand la **plus tardive** des archives precede le commit.
    Une seule source non datable ne suffit pas a acquitter — et ne suffit pas
    non plus a accuser : si une autre source prouve l'ecart, l'ecart est etabli.
    """
    if not datations:
        return SOURCE_ABSENTE
    ecart = False
    dates: list[datetime] = []
    for date, _provenance in datations:
        if date is None:
            continue
        dates.append(date)
    if premier_commit is None or not dates:
        return INDETERMINE
    if premier_commit.tzinfo is None:
        premier_commit = premier_commit.replace(tzinfo=timezone.utc)
    for date in dates:
        if (date - premier_commit).total_seconds() > tolerance_s:
            ecart = True
    if ecart:
        return ECART_ORDRE
    return CONFORME if len(dates) == len(datations) else INDETERMINE


@dataclass
class Mesure:
    """Resultat d'une paire PR x issue x papier(s)."""

    issue: int | None
    pr: int | None
    titre: str = ""
    premier_commit: datetime | None = None
    archivage: datetime | None = None
    archivage_provenance: str = "aucune"
    sources: list[dict[str, Any]] = field(default_factory=list)
    origine_source: str = "aucune"
    verdict: str = INDETERMINE

    @property
    def source(self) -> dict[str, Any]:
        """Source principale — compatibilite d'affichage et de rapport."""
        if self.sources:
            return {"trouvee": True, **self.sources[0]}
        return {"trouvee": False, "methode": "aucune", "chemin": None, "score": 0.0}

    def as_dict(self) -> dict[str, Any]:
        return {
            "issue": self.issue,
            "pr": self.pr,
            "titre": self.titre,
            "premier_commit": _iso(self.premier_commit),
            "archivage": _iso(self.archivage),
            "archivage_provenance": self.archivage_provenance,
            "origine_source": self.origine_source,
            "source_trouvee": bool(self.sources),
            "source_methode": self.source.get("methode"),
            "source_chemin": self.source.get("chemin"),
            "source_score": self.source.get("score"),
            "sources": [
                {**s, "archivage": _iso(s.get("archivage"))} if "archivage" in s else dict(s)
                for s in self.sources
            ],
            "verdict": self.verdict,
        }


def _iso(valeur: datetime | None) -> str | None:
    if valeur is None:
        return None
    return valeur.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def mesurer_paire(
    issue: int | None,
    pr: int | None,
    texte_fil: Sequence[str],
    premier_commit: datetime | None,
    index: dict[str, Path],
    commentaires: Sequence[str] = (),
    titre: str = "",
    tolerance_s: int = TOLERANCE_S,
    texte_livrable: Sequence[str] = (),
) -> Mesure:
    """Assemble une mesure complete pour une paire, sans reseau ni disque hors index.

    **Priorite de la source : le livrable d'abord.** Les citations sont lues
    dans les textes de la PR ; le fil de l'issue n'est qu'un repli, et
    ``origine_source`` dit lequel a servi. Mesure du 29/10 sur #21858 : sans
    cette priorite, quatre PRs correctes (qui citent chacune leur papier dans
    leur corps) etaient appariees au papier cite par l'issue d'audit — une issue
    qui en cite des dizaines, donc une source fausse, et un verdict qui ne
    mesurait plus rien.
    """
    sources: list[dict[str, Any]] = []
    origine = "aucune"
    if texte_livrable:
        sources = resoudre_sources(index, extraire_chemins_pdf(texte_livrable), titre=titre)
        if sources:
            origine = "livrable"
    if not sources:
        sources = resoudre_sources(
            index, extraire_chemins_pdf(texte_fil), titre=titre,
            limite=MAX_SOURCES_LIVRABLE + 1,
        )
        if sources:
            origine = "fil"

    # Un fil qui cite une foule de papiers est un conteneur (audit, EPIC), pas
    # un livrable : mesurer « l'ordre » d'un audit n'a pas de sens, et ses
    # lignes fausseraient le decompte des defauts. On le declare.
    if origine == "fil" and len(sources) > MAX_SOURCES_LIVRABLE:
        return Mesure(
            issue=issue, pr=pr, titre=titre, premier_commit=premier_commit,
            sources=sources[:MAX_SOURCES_LIVRABLE], origine_source=origine,
            verdict=UMBRELLE,
        )

    provenance = "aucune"
    datations: list[tuple[datetime | None, str]] = []
    if sources:
        date_commentaire = date_archivage_commentaire(commentaires)
        for source in sources:
            if date_commentaire is not None:
                source["archivage"], source["provenance"] = date_commentaire, "commentaire"
            else:
                date = date_ctime(Path(source["chemin"]))
                source["archivage"], source["provenance"] = date, ("ctime" if date else "aucune")
            datations.append((source["archivage"], source["provenance"]))
        provs = {p for _d, p in datations if p != "aucune"}
        provenance = provs.pop() if len(provs) == 1 else ("mixte" if provs else "aucune")

    dates = [d for d, _p in datations if d is not None]
    verdict = classer_sources(premier_commit, datations, tolerance_s)
    return Mesure(
        issue=issue,
        pr=pr,
        titre=titre,
        premier_commit=premier_commit,
        archivage=max(dates) if dates else None,
        archivage_provenance=provenance,
        sources=sources,
        origine_source=origine,
        verdict=verdict,
    )


# --------------------------------------------------------------------------
# Mode live (gh + gisement)
# --------------------------------------------------------------------------

def _gh(args: Sequence[str], timeout: int = 60) -> Any:
    """Appelle ``gh`` et rend le JSON decode. Leve ``RuntimeError`` si muet."""
    try:
        sortie = subprocess.run(
            ["gh", *args], capture_output=True, text=True, timeout=timeout, encoding="utf-8"
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeError(f"gh injoignable : {exc}") from exc
    if sortie.returncode != 0:
        raise RuntimeError(f"gh rc={sortie.returncode} : {(sortie.stderr or '').strip()[:300]}")
    try:
        return json.loads(sortie.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"gh : sortie non-JSON ({exc})") from exc


def issues_distillation(since: str, limite: int = 400) -> list[dict[str, Any]]:
    """Issues portant un marqueur de distillation, modifiees depuis ``since``."""
    sortie = _gh([
        "issue", "list", "--state", "all", "--limit", str(limite),
        "--search", f"updated:>={since}",
        "--json", "number,title,body,comments",
    ])
    retenues = []
    for issue in sortie:
        corpus = f"{issue.get('title') or ''}\n{issue.get('body') or ''}"
        corpus += "\n" + "\n".join((c.get("body") or "") for c in issue.get("comments") or [])
        if any(m in corpus for m in MARQUEURS_ISSUE):
            retenues.append(issue)
    return retenues


def prs_mergees_citant(issue: int, since: str) -> list[dict[str, Any]]:
    """PRs mergees citant ``#N``, dans la fenetre."""
    return _gh([
        "pr", "list", "--state", "merged", "--limit", "30",
        "--search", f"#{issue} merged:>={since}",
        "--json", "number,title,body,mergedAt,comments",
    ])


def premier_commit(pr: int) -> datetime | None:
    """Date du premier commit de la PR, au sens de ``min(committedDate)``."""
    detail = _gh(["pr", "view", str(pr), "--json", "commits"])
    dates = [date_iso(c.get("committedDate") or "") for c in detail.get("commits") or []]
    lisibles = [d for d in dates if d is not None]
    return min(lisibles) if lisibles else None


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------

def self_test() -> int:
    """Controles synthetiques, positifs ET negatifs. Rend 0 si tout passe."""
    echecs: list[str] = []

    def attendre(nom: str, obtenu: Any, voulu: Any) -> None:
        if obtenu != voulu:
            echecs.append(f"{nom} : obtenu {obtenu!r}, voulu {voulu!r}")

    # -- normalisation
    attendre("normaliser accents", normaliser("Trèfle"), "trefle")
    attendre("normaliser separateurs", normaliser("a-b_c.d"), "a b c d")

    # -- score de titre
    attendre(
        "score titre present",
        score_titre("2026 michael and kenta trefoil knots in algebraic geometry",
                    "Trefoil knots in algebraic geometry") >= SEUIL_TITRE,
        True,
    )
    attendre(
        "score titre absent",
        score_titre("2026 sona team sona technical report", "Trefoil knots in algebraic geometry") >= SEUIL_TITRE,
        False,
    )

    # -- chemins cites : noms de fichiers a espaces, basename garde
    chemins = extraire_chemins_pdf([
        "PDF archive `Hidden-Phenomena/2026 - Michael and Kenta - Trefoil.pdf` (31 p.)",
        "et une seconde mention `2026 - Michael and Kenta - Trefoil.pdf`",
    ])
    attendre("chemins dedoublonnes", len(chemins), 1)
    attendre("basename conserve les espaces", chemins[0], "2026 - Michael and Kenta - Trefoil.pdf")
    # citation en prose nue : le preambule est absorbe par la resolution, pas ici
    nu = extraire_chemins_pdf(["voir Sona Technical Report - arXiv 2608.11015.pdf"])
    attendre("citation nue non vide", bool(nu and nu[0].endswith(".pdf")), True)

    # -- dates
    attendre("iso Z", _iso(date_iso("2026-10-14T06:08Z")), "2026-10-14T06:08:00Z")
    attendre("iso decalage", _iso(date_iso("2026-10-14T08:08+02:00")), "2026-10-14T06:08:00Z")
    attendre("iso sans fuseau refusee", date_iso("2026-10-14 06:08"), None)
    attendre("iso illisible", date_iso("pas une date"), None)

    # -- archivage par commentaire : une seule date => retenue
    attendre(
        "commentaire une date",
        _iso(date_archivage_commentaire(["[INFO] archivage fait a 2026-10-14T06:08:10Z"])),
        "2026-10-14T06:08:10Z",
    )
    # deux dates contradictoires => pas de choix mecanique
    attendre(
        "commentaire deux dates",
        date_archivage_commentaire([
            "[INFO] archivage a 2026-10-14T06:08:10Z",
            "[INFO] archivage corrige a 2026-10-15T09:00:00Z",
        ]),
        None,
    )
    attendre("commentaire sans marqueur", date_archivage_commentaire(["rien a voir"]), None)

    # -- classement : les cinq branches, dont le cas fondateur
    t0 = date_iso("2026-10-14T05:46:00Z")
    attendre("ecart (cas fondateur ICT-36c)", classer(t0, date_iso("2026-10-14T06:08:00Z"), True), ECART_ORDRE)
    attendre("conforme (archivage avant redaction)", classer(date_iso("2026-10-18T17:08:00Z"), date_iso("2026-10-18T13:55:00Z"), True), CONFORME)
    attendre("tolerance 12 s", classer(date_iso("2026-10-14T06:07:58Z"), date_iso("2026-10-14T06:08:10Z"), True), CONFORME)
    attendre("tolerance borne exacte", classer(date_iso("2026-10-14T06:05:00Z"), date_iso("2026-10-14T06:08:00Z"), True), CONFORME)
    attendre("tolerance depassee d'une seconde", classer(date_iso("2026-10-14T06:04:59Z"), date_iso("2026-10-14T06:08:00Z"), True), ECART_ORDRE)
    attendre("source absente prime", classer(t0, None, False), SOURCE_ABSENTE)
    attendre("date manquante => indetermine", classer(None, date_iso("2026-10-14T06:08:00Z"), True), INDETERMINE)

    # -- resolution de source sur un gisement synthetique
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        racine = Path(tmp)
        (racine / "MachineLearning").mkdir()
        cible = racine / "MachineLearning" / "2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf"
        cible.write_bytes(b"%PDF-1.4 synthetique")
        index = indexer_gisement(racine)
        attendre("index gisement", len(index), 1)

        par_nom = resoudre_source(index, ["Sona Technical Report - arXiv 2608.11015.pdf"])
        attendre("source par nom cite elide", par_nom["trouvee"], True)
        attendre("methode nom_cite", par_nom["methode"], "nom_cite")

        par_chemin = resoudre_source(
            index,
            ["G:\\Mon Drive\\MyIA\\IA\\Bibliographie IA\\MachineLearning\\"
             "2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf"],
        )
        attendre("source par chemin absolu", par_chemin["trouvee"], True)

        cite_trop_court = resoudre_source(index, ["report.pdf"])
        attendre("citation d'un seul jeton refusee", cite_trop_court["trouvee"], False)

        par_titre = resoudre_source(index, [], titre="Sona Technical Report")
        attendre("source par titre", par_titre["trouvee"], True)
        attendre("methode titre", par_titre["methode"], "titre")

        absente = resoudre_source(index, ["papier jamais depose.pdf"], titre="Un titre sans rapport aucun")
        attendre("source absente", absente["trouvee"], False)

        mesure = mesurer_paire(
            issue=19438, pr=19438, texte_fil=["voir Sona Technical Report - arXiv 2608.11015.pdf"],
            premier_commit=date_iso("2026-10-06T05:34:00Z"), index=index,
            commentaires=["[INFO] archivage a 2026-10-06T10:27:00Z"],
        )
        attendre("mesure verdict", mesure.verdict, ECART_ORDRE)
        attendre("mesure origine", mesure.origine_source, "fil")
        attendre("mesure provenance", mesure.archivage_provenance, "commentaire")
        attendre("mesure date archivage", _iso(mesure.archivage), "2026-10-06T10:27:00Z")

        # Le livrable passe avant le fil : deux textes qui citent deux papiers
        # differents doivent resoudre sur celui du livrable.
        priorite = mesurer_paire(
            issue=21858, pr=21888,
            texte_fil=["le fil cite Sona Technical Report - arXiv 2608.11015.pdf"],
            texte_livrable=["la PR cite Sona Technical Report - arXiv 2608.11015.pdf"],
            premier_commit=date_iso("2026-10-21T19:36:36Z"), index=index,
        )
        attendre("priorite livrable", priorite.origine_source, "livrable")

        # Conteneur : trop de papiers cites par le fil, on declare au lieu de mesurer.
        for i in range(MAX_SOURCES_LIVRABLE + 1):
            (racine / "MachineLearning" / f"2026 - Auteur {i} - Papier {i} sur un sujet.pdf").write_bytes(b"%PDF-1.4")
        index_large = indexer_gisement(racine)
        conteneur = mesurer_paire(
            issue=21858, pr=22896,
            texte_fil=[f"2026 - Auteur {i} - Papier {i} sur un sujet.pdf" for i in range(MAX_SOURCES_LIVRABLE + 1)],
            premier_commit=date_iso("2026-10-27T06:32:57Z"), index=index_large,
        )
        attendre("conteneur declare UMBRELLE", conteneur.verdict, UMBRELLE)

    if echecs:
        print(f"SELFTEST ECHEC ({len(echecs)})")
        for e in echecs:
            print(f"  - {e}")
        return 1
    print("SELFTEST OK (normalisation, score, chemins, dates, 6 verdicts, priorite livrable, gisement synthetique)")
    return 0


# --------------------------------------------------------------------------
# Rapport
# --------------------------------------------------------------------------

def rendre_rapport(mesures: Sequence[Mesure]) -> str:
    """Tableau des verdicts, en markdown — la forme attendue par l'issue."""
    ordre = [SOURCE_ABSENTE, ECART_ORDRE, INDETERMINE, UMBRELLE, CONFORME]
    compte = {v: sum(1 for m in mesures if m.verdict == v) for v in ordre}
    lignes = [
        f"paires mesurees : {len(mesures)}",
        "  " + " · ".join(f"{v} {compte[v]}" for v in ordre),
        "",
        "| PR | issue | verdict | 1er commit | archivage | provenance | origine | source |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for m in sorted(mesures, key=lambda x: (ordre.index(x.verdict), x.pr or 0)):
        if m.sources:
            source_court = " ; ".join(Path(s["chemin"]).name for s in m.sources)
            if len(m.sources) > 1:
                source_court = f"{len(m.sources)} papiers : {source_court}"
        else:
            source_court = f"— ({m.source.get('methode')}, score {m.source.get('score')})"
        lignes.append(
            f"| #{m.pr} | #{m.issue} | **{m.verdict}** | {_iso(m.premier_commit) or '?'} "
            f"| {_iso(m.archivage) or '?'} | {m.archivage_provenance} | {m.origine_source} | {source_court} |"
        )
    return "\n".join(lignes)


def main(argv: Sequence[str] | None = None) -> int:
    parseur = argparse.ArgumentParser(
        description="Ordre redaction / archivage des livrables de distillation (#21858)."
    )
    parseur.add_argument("--self-test", action="store_true", help="controles synthetiques puis sortie")
    parseur.add_argument("--since", default="", help="fenetre, date ISO (ex. 2026-09-01)")
    parseur.add_argument("--gisement", default=os.environ.get("BIBLIO_GISEMENT", ""), help="racine du gisement bibliographique")
    parseur.add_argument("--paires", default="", help="fichier JSON de paires a rejouer hors ligne")
    parseur.add_argument("--limit", type=int, default=40, help="nombre max d'issues examinees")
    parseur.add_argument("--tolerance", type=int, default=TOLERANCE_S, help="tolerance d'ordre, en secondes")
    parseur.add_argument("--json", action="store_true", help="sortie machine")
    args = parseur.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.paires:
        donnees = json.loads(Path(args.paires).read_text(encoding="utf-8"))
        gisement = Path(args.gisement) if args.gisement else None
        index = indexer_gisement(gisement) if gisement else {}
        mesures = []
        for p in donnees:
            mesures.append(mesurer_paire(
                issue=p.get("issue"), pr=p.get("pr"),
                texte_fil=p.get("textes") or [],
                premier_commit=date_iso(p.get("premier_commit") or ""),
                index=index,
                commentaires=p.get("commentaires") or [],
                titre=p.get("titre") or "",
                tolerance_s=args.tolerance,
            ))
        _rendre(mesures, args.json)
        return 0

    if not args.since:
        parseur.error("--since ou --self-test ou --paires est requis")
    if not args.gisement:
        parseur.error("--gisement (ou BIBLIO_GISEMENT) est requis pour mesurer la presence des sources")

    gisement = Path(args.gisement)
    if not gisement.is_dir():
        print(f"INSTRUMENT INDISPONIBLE : gisement absent -> {gisement}", file=sys.stderr)
        return 3
    index = indexer_gisement(gisement)
    if not index:
        print(f"INSTRUMENT INDISPONIBLE : aucun PDF sous {gisement}", file=sys.stderr)
        return 3

    mesures: list[Mesure] = []
    try:
        issues = issues_distillation(args.since)[: args.limit]
        for issue in issues:
            commentaires = [c.get("body") or "" for c in issue.get("comments") or []]
            texte_issue = [issue.get("title") or "", issue.get("body") or "", *commentaires]
            for pr in prs_mergees_citant(int(issue["number"]), args.since):
                texte_pr = [pr.get("body") or ""] + [c.get("body") or "" for c in pr.get("comments") or []]
                mesures.append(mesurer_paire(
                    issue=int(issue["number"]),
                    pr=int(pr["number"]),
                    texte_fil=texte_issue,
                    texte_livrable=texte_pr,
                    premier_commit=premier_commit(int(pr["number"])),
                    index=index,
                    commentaires=commentaires,
                    titre=issue.get("title") or "",
                    tolerance_s=args.tolerance,
                ))
    except RuntimeError as exc:
        print(f"INSTRUMENT INDISPONIBLE : {exc}", file=sys.stderr)
        return 3

    _rendre(mesures, args.json)
    return 0


def _rendre(mesures: Sequence[Mesure], en_json: bool) -> None:
    if en_json:
        print(json.dumps([m.as_dict() for m in mesures], ensure_ascii=False, indent=2))
    else:
        print(rendre_rapport(mesures))


if __name__ == "__main__":
    sys.exit(main())
