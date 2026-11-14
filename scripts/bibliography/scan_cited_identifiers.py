#!/usr/bin/env python3
"""Census de la population de citations du dépôt, et table du gisement citée par chemin.

Taches A1 / A5 de l'umbrella #14407 (« alimenter le gisement canonique »).

Ce que l'instrument corrige
---------------------------
Le census de référence de l'EPIC (#14407, 2026-09-03) ne capturait qu'une
**forme** d'identifiant : l'URL ``arxiv.org/abs/NNNN.NNNNN``. La forme
**tampon** ``arXiv:NNNN.NNNNN`` — celle qu'emploie la majorité des carnets —
passait au travers. Mesure sur ``origin/main`` (2026-11-14, commit
``649647421806a``), sur le **même périmètre** que l'organe — les quatre
surfaces ``.ipynb .md .py .cs``, répertoires hors périmètre exclus :

| forme capturée | identifiants arXiv distincts |
|---|---:|
| URL seule (``ARXIV_URL_RE``, le motif de cet organe) | 175 |
| tampon seule | 321 |
| legacy seule | 9 |
| **union des trois** | **352** |

Le census de référence sous-compte donc la moitié de la population citée : il
ne voit aucun des identifiants que les carnets citent sous forme tampon.
L'union des formes n'est pas un détail de forme : c'est la population réelle
que A1 doit résoudre.

Le compte de la forme URL dépend de la convention de motif, et il faut la
nommer pour que le chiffre soit comparable. Au périmètre de cet organe
(``tests/`` exclu, comme partout ici), ``abs`` seul rend **172**, l'alternance
``abs|pdf`` (la commande de l'EPIC) rend **174**, et ``abs|pdf|html|format`` —
le motif de cet organe, ``ARXIV_URL_RE`` — rend **175**. Réintégrer les
fixtures de ``tests/`` donne 173, 175 et 176 : l'écart entre les deux séries
est une convention de périmètre, et l'écart à l'intérieur d'une série une
convention de motif — dans les deux cas, pas un désaccord sur la population.

La forme **nue** (``NNNN.NNNNN`` sans marqueur) est, elle, exclue par
défaut : elle sur-compte massivement (mesuré par une tranche de la famille
IIT : 105 faux positifs sur le seul dossier IIT). Elle reste accessible par
``--nu-arxiv`` pour un diagnostic.

Ce que l'instrument rend
-------------------------
1. Le **census** de la population citée (arXiv + DOI), avec pour chaque
   identifiant ses fichiers, ses occurrences et les formes sous lesquelles il
   est cité.
2. La **table du gisement citée par chemin** : la jointure entre ce census et
   le catalogue A5 (``IDENTIFIANTS-catalogue-*.csv``), qui relie chaque
   identifiant cité au chemin canonique du document détenu. C'est la
   question « l'avons-nous déjà ? », rendue lisible ligne par ligne.
3. Sur demande (``--resoudre``), la **résolution** de chaque identifiant en
   ``(auteur, titre, année)`` — l'API arXiv pour les identifiants arXiv,
   l'API Crossref pour les DOI — puis le verdict de détention
   ``DETENU`` / ``ABSENT`` / ``NON_RESOLU``. C'est le critère **A1** de
   l'EPIC : « les 235 identifiants résolus en (auteur, titre, année), verdict
   DETENU / ABSENT / NON_RESOLU par référence ».

L'API arXiv rend en plus le **DOI de la version publiée** de chaque preprint :
c'est le crosswalk arXiv <-> DOI qui manquait au catalogue A5 (#21631).

Aucune publication n'est lue ni copiée ici : le catalogue est un CSV de
chemins. Aucun fichier du dépôt n'est modifié.

Usage :
    python scripts/bibliography/scan_cited_identifiers.py --root . --json rapport.json
    python scripts/bibliography/scan_cited_identifiers.py --csv table.csv
    python scripts/bibliography/scan_cited_identifiers.py --catalogue "G:/.../IDENTIFIANTS-catalogue-2026-10-25.csv"
    python scripts/bibliography/scan_cited_identifiers.py --resoudre --cache cache.json --csv table.csv

Options :
    --root PATH            Racine du dépôt à balayer (defaut : la racine du dépôt)
    --csv PATH             Table du gisement citée par chemin (sortie CSV)
    --json PATH            Rapport de census (sortie JSON)
    --catalogue PATH       Catalogue A5 a joindre (repetable ; defaut : tous les
                           IDENTIFIANTS-catalogue-*.csv du dossier de travail)
    --travaux PATH         Dossier de travail du gisement (defaut :
                           G:/Mon Drive/MyIA/IA/Bibliographie-travaux)
    --surfaces LIST        Extensions balayees (defaut : .ipynb,.md,.py,.cs)
    --nu-arxiv             Capturer aussi la forme nue (hors registre, par defaut)
    --inclure-archives     Ne pas exclure les repertoires `_archives`
    --resoudre             Resoudre chaque identifiant et statuer la detention
    --gisement PATH        Racine du gisement canonique (defaut :
                           G:/Mon Drive/MyIA/IA/Bibliographie IA)
    --cache PATH           Cache JSON des metadonnees resolues
    --sans-reseau          N'appeler aucune API (cache seul)
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import shutil
import sys
import tempfile
import time
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from pathlib import Path

#: Repertoires hors perimetre : dependances, artefacts et sous-modules.
#: Meme liste que le detecteur de `scripts/check_arxiv_attributions.py`, pour
#: que les deux instruments mesurent la meme surface.
EXCLUS_DIRS = frozenset({
    ".git", ".lake", "node_modules", ".ipynb_checkpoints",
    "_archives", "foundry-lib", ".tmp", "scratchpad",
    # Les fixtures de tests portent des identifiants synthetiques
    # (`9999.99999`, `8888.88888`) : ce ne sont pas des citations, et les
    # compter gonflerait la population de references a resoudre.
    "tests",
})

#: Extensions balayees par defaut : la surface de citation du depot telle que
#: l'EPIC la decrit (`*.ipynb`, `*.md`, `*.py`, `*.cs`).
SURFACES_DEFAUT = (".ipynb", ".md", ".py", ".cs")

#: Forme URL : `arxiv.org/abs/2401.05375`, `arxiv.org/pdf/2401.05375v2`.
ARXIV_URL_RE = re.compile(
    r"arxiv\.org/(?:abs|pdf|html|format)/(\d{4}\.\d{4,5})", re.IGNORECASE)

#: Forme tampon : `arXiv:2401.05375`, `arXiv 2401.05375`, `arXiv:2401.05375v2`.
ARXIV_TAMPON_RE = re.compile(r"\barXiv[:\s]\s*(\d{4}\.\d{4,5})", re.IGNORECASE)

#: Forme legacy : `arXiv:cs/0011047` — le prefixe d'archive fait partie de
#: l'identifiant (l'API arXiv rejette l'identifiant reduit a ses 7 chiffres).
ARXIV_LEGACY_RE = re.compile(
    r"\barXiv[:\s]\s*((?:[a-z\-]+(?:\.[A-Z]{2})?/\d{7}))", re.IGNORECASE)

#: DOI marque : `https://doi.org/10.1000/x`, `DOI: 10.1000/x`.
#: Les parentheses sont **autorisees** dans le suffixe : un DOI Elsevier
#: (`10.1016/0304-4068(74)90217-3`) les porte legitimement. Les exclure
#: tronquait l'identifiant a `10.1016/0304-4068(74` (mesure : 2 DOI
#: tronques dans le census du 14/11).
DOI_MARQUE_RE = re.compile(
    r"(?:doi\.org/|doi\s*[:=]\s*|DOI\s*[:=]\s*)(10\.\d{4,9}/[^\s\"'`<>,;]+)",
    re.IGNORECASE)

#: DOI nu : `10.1000/x` sans marqueur — confiance standard (bruit possible).
DOI_NU_RE = re.compile(r"\b(10\.\d{4,9}/[^\s\"'`<>,;]+)", re.IGNORECASE)


#: Identifiant arXiv nu, sans marqueur — hors registre, sur-compte en masse.
ARXIV_NU_RE = re.compile(r"\b(\d{4}\.\d{4,5})\b")

#: Longueur du contexte conserve autour d'une occurrence.
RAYON_CONTEXTE = 120


def _nettoyer_doi(brut: str) -> str:
    """Retire la ponctuation terminale avalée par la regex.

    Les parentheses ne sont retirées que lorsqu'elles sont **déséquilibrées** :
    une parenthese fermante non ouvrante appartient a la ponctuation de la
    citation, une parenthese interne (`0304-4068(74)90217-3`) appartient au
    DOI.

    Les **liens markdown** sont également tronques : le DOI d'un lien
    `[texte](https://doi.org/10.4230/dagrep.9.2.27)` est capture avec son
    residu `](https://doi.org/...)`. Mesure du 2026-11-14 : 33 des 46 DOI
    declares `NON_RESOLU` portaient ce residu, qui les rendait
    introuvables alors qu'ils se resolvent.
    """
    doi = brut.strip()
    # Residu d'un lien markdown : `10.x/y](https://doi.org/10.x/y)`.
    if "](" in doi:
        doi = doi.split("](", 1)[0]
    doi = doi.rstrip(".,;:").strip().strip("`\"'")
    # Emphasis markdown : `10.x/y*`.
    doi = doi.rstrip("*").strip()
    while doi.endswith(")") and doi.count(")") > doi.count("("):
        doi = doi[:-1].rstrip(".,;:").strip()
    return doi.lower()


def _doi_valide(brut: str) -> bool:
    """Un DOI a-t-il un suffixe plausible ?

    La forme nue d'un DOI (`10.1002/...`, `10.1000/x`) circule dans les
    docstrings et les fixtures de test : la capturer sans la filtrer ferait
    compter des DOI inexistants. Un suffixe de moins de quatre caractères, ou
    fait uniquement de ponctuation, n'est pas un suffixe de DOI.
    """
    doi = _nettoyer_doi(brut)
    if "/" not in doi:
        return False
    suffixe = doi.split("/", 1)[1].strip().strip("`\"'")
    if len(suffixe) < 4:
        return False
    return any(c.isalnum() for c in suffixe)


def normaliser_arxiv(brut: str) -> str:
    """Forme de comparaison d'un identifiant arXiv (minuscules, sans version).

    Le prefixe d'archive est conserve dans l'identifiant (l'API le exige) mais
    la **cle** de comparaison ne retient que le segment numerique terminal :
    `cs/0011047` et `0011047` designent le meme article.
    """
    return re.sub(r"v\d+$", "", brut.strip().lower())


def cle_arxiv(brut: str) -> str:
    """Cle de jointure d'un identifiant arXiv (segment numerique terminal)."""
    return normaliser_arxiv(brut).rsplit("/", 1)[-1]


@dataclass
class Occurrence:
    """Une occurrence d'identifiant, avec sa provenance."""

    type_id: str
    identifiant: str
    forme: str
    fichier: str
    contexte: str = ""
    confiance: str = "elevee"


@dataclass
class Entree:
    """Un identifiant cite, avec son etat agrege."""

    type_id: str
    identifiant: str
    formes: set[str] = field(default_factory=set)
    fichiers: set[str] = field(default_factory=set)
    occurrences: int = 0
    exemple_fichier: str = ""
    exemple_contexte: str = ""


def _contexte(texte: str, debut: int, fin: int) -> str:
    """Fragment lisible autour d'une occurrence."""
    fragment = texte[max(0, debut - 60):fin + 60]
    compact = re.sub(r"\s+", " ", fragment).strip()
    if len(compact) <= RAYON_CONTEXTE:
        return compact
    return compact[:RAYON_CONTEXTE - 3] + "..."


def extraire(texte: str, fichier: str, nu_arxiv: bool = False) -> list[Occurrence]:
    """Toutes les occurrences d'identifiants dans un texte.

    Chaque forme est capturee une fois : un identifiant cite sous les deux
    formes (tampon + URL dans la meme cellule) compte deux occurrences, mais
    une seule entree.
    """
    trouvees: list[Occurrence] = []

    def ajouter(type_id: str, identifiant: str, forme: str, debut: int, fin: int,
                confiance: str = "elevee") -> None:
        trouvees.append(Occurrence(
            type_id=type_id, identifiant=identifiant, forme=forme,
            fichier=fichier, contexte=_contexte(texte, debut, fin),
            confiance=confiance))

    for m in ARXIV_URL_RE.finditer(texte):
        ajouter("arxiv", m.group(1), "url", m.start(), m.end())
    for m in ARXIV_TAMPON_RE.finditer(texte):
        ajouter("arxiv", m.group(1), "tampon", m.start(), m.end())
    for m in ARXIV_LEGACY_RE.finditer(texte):
        ajouter("arxiv", m.group(1), "legacy", m.start(), m.end())
    for m in DOI_MARQUE_RE.finditer(texte):
        if _doi_valide(m.group(1)):
            ajouter("doi", _nettoyer_doi(m.group(1)), "doi_marque", m.start(), m.end())
    for m in DOI_NU_RE.finditer(texte):
        if _doi_valide(m.group(1)):
            ajouter("doi", _nettoyer_doi(m.group(1)), "doi_nu", m.start(), m.end(),
                    confiance="standard")
    if nu_arxiv:
        for m in ARXIV_NU_RE.finditer(texte):
            ajouter("arxiv", m.group(1), "nu", m.start(), m.end(),
                    confiance="standard")
    return trouvees


def texte_notebook(chemin: Path) -> str:
    """Texte utile d'un notebook : sources des cellules + sorties textuelles.

    Les images (base64) sont ignorees : elles ne portent pas de citation et
    leur volume dominerait le balayage.
    """
    try:
        donnees = json.loads(chemin.read_text(encoding="utf-8", errors="replace"))
    except (OSError, ValueError):
        return ""
    morceaux: list[str] = []
    for cellule in donnees.get("cells", []):
        source = cellule.get("source", "")
        morceaux.append("".join(source) if isinstance(source, list) else str(source))
        for sortie in cellule.get("outputs", []):
            texte = sortie.get("text", "")
            if isinstance(texte, list):
                morceaux.append("".join(texte))
            data = sortie.get("data", {}) or {}
            for cle in ("text/plain", "text/html", "text/markdown"):
                valeur = data.get(cle, "")
                if isinstance(valeur, list):
                    morceaux.append("".join(valeur))
                elif isinstance(valeur, str):
                    morceaux.append(valeur)
    return "\n".join(morceaux)


def fichiers_a_balayer(root: Path, surfaces: tuple[str, ...],
                       inclure_archives: bool) -> list[Path]:
    """Fichiers du perimetre, dans un ordre stable."""
    exclus = set(EXCLUS_DIRS)
    if inclure_archives:
        exclus = exclus - {"_archives"}
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in exclus)
        for nom in sorted(filenames):
            if Path(nom).suffix.lower() in surfaces:
                out.append(Path(dirpath) / nom)
    return out


def census(root: Path, surfaces: tuple[str, ...] = SURFACES_DEFAUT,
           inclure_archives: bool = False, nu_arxiv: bool = False) -> dict:
    """Census de la population citee.

    Rend un dictionnaire `{cle: Entree}` où la cle est `(type_id, identifiant)`.
    """
    entrees: dict[tuple[str, str], Entree] = {}
    for chemin in fichiers_a_balayer(root, surfaces, inclure_archives):
        if chemin.suffix.lower() == ".ipynb":
            texte = texte_notebook(chemin)
        else:
            try:
                texte = chemin.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
        if not texte:
            continue
        relatif = chemin.relative_to(root).as_posix()
        for occurrence in extraire(texte, relatif, nu_arxiv=nu_arxiv):
            identifiant = (normaliser_arxiv(occurrence.identifiant)
                           if occurrence.type_id == "arxiv"
                           else occurrence.identifiant)
            cle = (occurrence.type_id, identifiant)
            entree = entrees.get(cle)
            if entree is None:
                entree = Entree(type_id=occurrence.type_id, identifiant=identifiant)
                entrees[cle] = entree
            entree.formes.add(occurrence.forme)
            entree.fichiers.add(occurrence.fichier)
            entree.occurrences += 1
            if not entree.exemple_fichier:
                entree.exemple_fichier = occurrence.fichier
                entree.exemple_contexte = occurrence.contexte
    return entrees


def _identifiant_valide(valeur: str) -> bool:
    """Un champ identifiant plausible (arXiv ou DOI) ?"""
    valeur = valeur.strip()
    if not valeur:
        return False
    return bool(re.match(r"^\d{4}\.\d{4,5}$", valeur)
                or re.match(r"^10\.\d{4,9}/\S+$", valeur, re.IGNORECASE))


def _ancrer(champs: list[str]) -> dict | None:
    """Ancre une ligne de catalogue sur ses colonnes.

    Une ligne bien formee a autant de champs que l'entete. Une ligne dont le
    chemin contient une **virgule non quotee** en a un de plus, et toutes les
    colonnes sont decalees d'un rang : le catalogue du 2026-10-25 en porte une
    (`... (arXiv 2403.06629v6, OA).pdf,arxiv,2403.06629,...`). Sans reparation,
    l'identifiant `2403.06629` passerait pour absent du catalogue alors que
    le gisement le detient.

    La reparation est un **ancrage par la queue** : on cherche le dernier
    champ de la ligne qui porte un type d'identifiant (`arxiv` ou `doi`) suivi
    d'un identifiant plausible ; tout ce qui precede est le chemin.
    """
    if not champs:
        return None
    for i in range(len(champs) - 2, -1, -1):
        if champs[i].strip() not in ("arxiv", "doi"):
            continue
        if not _identifiant_valide(champs[i + 1]):
            continue
        chemin = ",".join(champs[:i]).strip()
        return {
            "chemin_gisement": chemin,
            "type_id": champs[i].strip(),
            "id": champs[i + 1].strip(),
            "source_extraction": champs[i + 2].strip() if i + 2 < len(champs) else "",
            "confiance": champs[i + 3].strip() if i + 3 < len(champs) else "",
            "contexte": ",".join(c.strip() for c in champs[i + 4:]) if i + 4 < len(champs) else "",
            "repare": i != 1,
        }
    return None


def charger_catalogue(chemins: list[Path]) -> tuple[dict[tuple[str, str], dict], list[dict], list[dict]]:
    """Charge un ou plusieurs catalogues A5.

    Rend `(index, lignes_reparees, lignes_malformees)`. Une ligne malformee
    est un enregistrement dont on ne retrouve ni le type d'identifiant ni
    l'identifiant : elle signale un defaut de saisie, pas une donnee
    exploitable.
    """
    index: dict[tuple[str, str], dict] = {}
    repares: list[dict] = []
    malformees: list[dict] = []
    for chemin in chemins:
        try:
            with chemin.open("r", encoding="utf-8-sig", newline="") as f:
                lecteur = csv.reader(f)
                next(lecteur, [])
                for numero, champs in enumerate(lecteur, start=2):
                    if not champs or not any(c.strip() for c in champs):
                        continue
                    enregistrement = _ancrer(champs)
                    if enregistrement is None:
                        malformees.append({"fichier": chemin.name, "ligne": numero,
                                           "type_id": "", "id": ""})
                        continue
                    if enregistrement["repare"]:
                        repares.append({"fichier": chemin.name, "ligne": numero,
                                        "id": enregistrement["id"],
                                        "type_id": enregistrement["type_id"]})
                    type_id = enregistrement["type_id"]
                    identifiant = enregistrement["id"]
                    cle = (type_id, identifiant.lower())
                    if cle not in index:
                        index[cle] = {"chemin_gisement": enregistrement["chemin_gisement"],
                                       "source_extraction": enregistrement["source_extraction"],
                                       "confiance": enregistrement["confiance"],
                                       "catalogue": chemin.name}
        except OSError:
            continue
    return index, repares, malformees


def table_du_gisement(entrees: dict[tuple[str, str], Entree],
                      index: dict[tuple[str, str], dict]) -> list[dict]:
    """Table du gisement citee par chemin : une ligne par identifiant cite."""
    lignes: list[dict] = []
    for (type_id, identifiant), entree in entrees.items():
        cle = (type_id, identifiant.lower())
        if type_id == "arxiv":
            cle = ("arxiv", cle_arxiv(identifiant))
        fiche = index.get(cle)
        lignes.append({
            "type_id": type_id,
            "id": identifiant,
            "statut": "DETENU_CATALOGUE" if fiche else "ABSENT_CATALOGUE",
            "chemin_gisement": fiche["chemin_gisement"] if fiche else "",
            "source_extraction": fiche["source_extraction"] if fiche else "",
            "confiance_catalogue": fiche["confiance"] if fiche else "",
            "nb_fichiers": len(entree.fichiers),
            "nb_occurrences": entree.occurrences,
            "formes": "|".join(sorted(entree.formes)),
            "exemple_fichier": entree.exemple_fichier,
            "exemple_contexte": entree.exemple_contexte,
        })
    lignes.sort(key=lambda l: (l["type_id"], l["statut"], l["id"]))
    return lignes


# ---------------------------------------------------------------------------
# Etape de resolution : (auteur, titre, annee) par identifiant cite
# ---------------------------------------------------------------------------

GISEMENT = "G:/Mon Drive/MyIA/IA/Bibliographie IA"

ARXIV_API = "https://export.arxiv.org/api/query?id_list={ids}&max_results={n}"
CROSSREF_API = "https://api.crossref.org/works/{doi}"
#: Repli DataCite : Crossref ne couvre ni Zenodo, ni DBLP, ni Dagstuhl, ni
#: Dataverse. Mesure du 2026-11-14 : 12 des 46 DOI declares `NON_RESOLU` par
#: Crossref se resolvent chez DataCite -- les declarer non resolus aurait
#: route a #11168 des references parfaitement valides.
DATACITE_API = "https://api.datacite.org/dois/{doi}"

#:/arXiv demande au plus une requete toutes les trois secondes.
PAUSE_ARXIV_S = 3.0

#: Taille d'un lot d'identifiants arXiv dans une requete.
LOT_ARXIV = 100


def normaliser_texte(valeur: str) -> str:
    """Cle de comparaison : minuscules, sans accent, seuls alphanumeriques.

    Le titre d'une publication et le titre d'un nom de fichier canonique ne
    s'ecrivent pas de la meme facon (``Attention is All you need`` contre
    ``2017 - Attention is All you need.pdf``). La comparaison de detention
    doit porter sur une forme insensible a la casse, aux accents et a la
    ponctuation.
    """
    decompose = unicodedata.normalize("NFKD", valeur)
    sans_accent = "".join(c for c in decompose if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", " ", sans_accent.lower()).strip()


def _fetcher_par_defaut(url: str) -> bytes:
    """Lecture HTTP minimale (le client est injectable pour les tests)."""
    requete = urllib.request.Request(url, headers={"User-Agent": "CoursIA-biblio/1.0"})
    with urllib.request.urlopen(requete, timeout=60) as reponse:
        return reponse.read()


def resoudre_arxiv(identifiants: list[str], fetcher=None,
                   pause: float = PAUSE_ARXIV_S) -> dict[str, dict]:
    """Resout des identifiants arXiv en `(auteur, titre, annee)`.

    L'API arXiv accepte un lot d'identifiants par requete et rend, pour
    chaque entree, le titre, les auteurs, l'annee de publication et -- ce que
    le catalogue A5 ne portait pas -- le **DOI de la version publiee** : c'est
    le crosswalk arXiv <-> DOI qui manquait au catalogue (#21631).

    Deux pieges mesures :

    - l'API **rejette un lot qui melange identifiants modernes et legacy**
      (`HTTP 400`) : les deux formes sont donc interrogees separement ;
    - un lot qui echoue ne doit pas condamner les identifiants qu'il porte :
      le lot est alors scinde et rejoue, et un echec unitaire laisse son
      identifiant en `NON_RESOLU` plutot que de contaminer le lot.

    Un identifiant absent de la reponse n'est pas une erreur : il est
    `NON_RESOLU` (l'API ne le connait pas).
    """
    fetcher = fetcher or _fetcher_par_defaut
    resolus: dict[str, dict] = {}
    uniques = sorted({i for i in identifiants})
    modernes = [i for i in uniques if "/" not in i]
    legacy = [i for i in uniques if "/" in i]
    for index, restants in enumerate((modernes, legacy)):
        for debut in range(0, len(restants), LOT_ARXIV):
            lot = restants[debut:debut + LOT_ARXIV]
            if debut and pause:
                time.sleep(pause)
            for identifiant, fiche in _lot_arxiv(lot, fetcher):
                resolus[identifiant] = fiche
    return resolus


def _lot_arxiv(lot: list[str], fetcher) -> list[tuple[str, dict]]:
    """Interroge un lot d'identifiants arXiv, avec repli par scission."""
    if not lot:
        return []
    url = ARXIV_API.format(ids=",".join(lot), n=len(lot))
    try:
        contenu = fetcher(url)
    except Exception:
        if len(lot) == 1:
            return []
        milieu = len(lot) // 2
        return (_lot_arxiv(lot[:milieu], fetcher)
                + _lot_arxiv(lot[milieu:], fetcher))
    return _parser_arxiv(contenu)


def _parser_arxiv(contenu: bytes) -> list[tuple[str, dict]]:
    """Extrait `(identifiant, fiche)` d'une reponse Atom de l'API arXiv."""
    racine = ET.fromstring(contenu)
    atom = "{http://www.w3.org/2005/Atom}"
    arxiv = "{http://arxiv.org/schemas/atom}"
    sortie: list[tuple[str, dict]] = []
    for entree in racine.findall(f"{atom}entry"):
        brut = (entree.findtext(f"{atom}id") or "").strip()
        identifiant = brut.rsplit("/abs/", 1)[-1]
        identifiant = re.sub(r"v\d+$", "", identifiant)
        if not identifiant:
            continue
        auteurs = [n.text.strip() for n in entree.findall(f"{atom}author/{atom}name")
                   if n.text and n.text.strip()]
        publie = (entree.findtext(f"{atom}published") or "")[:4]
        sortie.append((identifiant, {
            "titre": " ".join((entree.findtext(f"{atom}title") or "").split()),
            "auteurs": auteurs,
            "auteur": auteurs[0] if auteurs else "",
            "annee": publie,
            "doi_publie": (entree.findtext(f"{arxiv}doi") or "").strip(),
            "revue": (entree.findtext(f"{arxiv}journal_ref") or "").strip(),
        }))
    return sortie


def resoudre_dois(identifiants: list[str], fetcher=None) -> dict[str, dict]:
    """Resout des DOI en `(auteur, titre, annee)`.

    Crossref est interroge en premier ; **DataCite est le repli** : Crossref
    ne couvre ni Zenodo, ni DBLP, ni Dagstuhl, ni Dataverse. Mesure du
    2026-11-14 : 12 des 46 DOI que Crossref ne connaisait pas se resolvent
    chez DataCite. Les declarer `NON_RESOLU` aurait route a #11168 des
    references parfaitement valides.

    Un DOI absent des deux registres est `NON_RESOLU` : c'est le signal que
    l'EPIC route vers #11168 (une reference irresolvable est un candidat
    citation fabriquee).
    """
    fetcher = fetcher or _fetcher_par_defaut
    resolus: dict[str, dict] = {}
    for identifiant in sorted({i for i in identifiants}):
        propre = _nettoyer_doi(identifiant)
        quote = urllib.parse.quote(propre, safe="")
        fiche = _fiche_crossref(fetcher, quote)
        if fiche is None:
            fiche = _fiche_datacite(fetcher, quote)
        if fiche is not None:
            resolus[propre] = fiche
    return resolus


def _fiche_crossref(fetcher, doi_quote: str) -> dict | None:
    """Fiche `(auteur, titre, annee)` depuis Crossref, ou `None`."""
    try:
        contenu = fetcher(CROSSREF_API.format(doi=doi_quote))
    except Exception:
        return None
    try:
        message = json.loads(contenu.decode("utf-8"))["message"]
    except (ValueError, KeyError, TypeError):
        return None
    titres = message.get("title") or []
    auteurs = []
    for auteur in message.get("author") or []:
        nom = " ".join(part for part in (auteur.get("given"), auteur.get("family"))
                        if part)
        if nom:
            auteurs.append(nom.strip())
    annee = ""
    for cle in ("published-print", "published-online", "issued", "created"):
        parties = (message.get(cle) or {}).get("date-parts") or []
        if parties and parties[0]:
            annee = str(parties[0][0])
            break
    return {
        "titre": " ".join((titres[0] if titres else "").split()),
        "auteurs": auteurs,
        "auteur": auteurs[0] if auteurs else "",
        "annee": annee,
        "revue": (message.get("container-title") or [""])[0],
        "source_api": "CROSSREF",
    }


def _fiche_datacite(fetcher, doi_quote: str) -> dict | None:
    """Fiche `(auteur, titre, annee)` depuis DataCite, ou `None`.

    DataCite rend une structure differente de Crossref : les attributs sont
    dans `data.attributes`, les auteurs dans `creators`, l'annee de
    publication dans `published`.
    """
    try:
        contenu = fetcher(DATACITE_API.format(doi=doi_quote))
    except Exception:
        return None
    try:
        attributs = json.loads(contenu.decode("utf-8"))["data"]["attributes"]
    except (ValueError, KeyError, TypeError):
        return None
    titres = attributs.get("titles") or []
    titre = ""
    if titres:
        titre = " ".join((titres[0].get("title") or "").split())
    auteurs = []
    for createur in attributs.get("creators") or []:
        nom = (createur.get("name") or "").strip()
        if nom:
            auteurs.append(nom)
    annee = ""
    for cle in ("published", "created", "registered"):
        valeur = attributs.get(cle) or ""
        if isinstance(valeur, str) and len(valeur) >= 4 and valeur[:4].isdigit():
            annee = valeur[:4]
            break
    if not titre and not auteurs:
        return None
    conteneur = attributs.get("container") or {}
    return {
        "titre": titre,
        "auteurs": auteurs,
        "auteur": auteurs[0] if auteurs else "",
        "annee": annee,
        "revue": (conteneur.get("title") or "").strip(),
        "source_api": "DATACITE",
    }


def _titre_du_fichier(nom: str) -> tuple[str, str, str]:
    """Decoupe un nom canonique ``YYYY - Auteur(s) - Titre.pdf``."""
    corps = Path(nom).stem
    morceaux = [m.strip() for m in corps.split(" - ")]
    if len(morceaux) >= 3:
        annee, auteurs, titre = morceaux[0], morceaux[1], " - ".join(morceaux[2:])
    elif len(morceaux) == 2:
        annee, auteurs, titre = morceaux[0], "", morceaux[1]
    else:
        annee, auteurs, titre = "", "", corps
    return annee, auteurs, titre


def inventaire_gisement(racine: Path) -> list[dict]:
    """Inventaire des documents detenus par le gisement canonique.

    Le gisement n'est visible que depuis un siege avec lecteur GDrive ; son
    absence ne doit pas faire echouer l'etape -- l'inventaire vide signifie
    alors « detention non mesurable ici », pas « rien n'est detenu ».
    """
    inventaire: list[dict] = []
    if not racine.is_dir():
        return inventaire
    for chemin in sorted(racine.rglob("*.pdf")):
        annee, auteurs, titre = _titre_du_fichier(chemin.name)
        inventaire.append({
            "chemin": chemin.as_posix(),
            "annee": annee,
            "auteurs": auteurs,
            "titre": titre,
            "cle": normaliser_texte(titre),
        })
    return inventaire


def _rapprocher_titre(titre: str, inventaire: list[dict]) -> dict | None:
    """Cherche un document du gisement par titre normalise.

    Deux niveaux : l'egalite exacte (le titre **est** celui du document) et
    l'inclusion (le titre du document contient le titre resolu, ou l'inverse,
    sur au moins 40 caracteres -- en dessous, la coincidence est trop faible
    pour etre une preuve de detention).
    """
    cle = normaliser_texte(titre)
    if not cle:
        return None
    for fiche in inventaire:
        if fiche["cle"] == cle:
            return {"fiche": fiche, "preuve": "TITRE_EXACT"}
    for fiche in inventaire:
        autre = fiche["cle"]
        if len(cle) >= 40 and len(autre) >= 40 and (cle in autre or autre in cle):
            return {"fiche": fiche, "preuve": "TITRE_PARTIEL"}
    return None


def statuts_resolus(lignes: list[dict], resolus_arxiv: dict[str, dict],
                    resolus_dois: dict[str, dict],
                    inventaire: list[dict]) -> list[dict]:
    """Enrichit la table du gisement d'un verdict par identifiant cite.

    Verdicts :

    - ``DETENU``  -- le document est dans le gisement (identifiant au
      catalogue A5, ou titre rapproche d'un nom de fichier canonique) ;
    - ``ABSENT``  -- l'identifiant se resout (metadonnees obtenues) mais
      aucun document correspondant n'est detecte dans le gisement ;
    - ``NON_RESOLU`` -- l'identifiant ne se resout pas : c'est le signal que
      l'EPIC #14407 route vers #11168.
    """
    enrichies: list[dict] = []
    for ligne in lignes:
        type_id = ligne["type_id"]
        identifiant = ligne["id"]
        if type_id == "arxiv":
            fiche = resolus_arxiv.get(identifiant)
            if fiche is None:
                fiche = resolus_arxiv.get(cle_arxiv(identifiant))
        else:
            fiche = resolus_dois.get(_nettoyer_doi(identifiant))
        copie = dict(ligne)
        copie["auteur"] = fiche["auteur"] if fiche else ""
        copie["titre"] = fiche["titre"] if fiche else ""
        copie["annee"] = fiche["annee"] if fiche else ""
        copie["revue"] = fiche.get("revue", "") if fiche else ""
        copie["doi_publie"] = fiche.get("doi_publie", "") if fiche else ""
        copie["source_api"] = fiche.get("source_api", "") if fiche else ""
        if ligne["statut"] == "DETENU_CATALOGUE":
            copie["statut"] = "DETENU"
            copie["preuve"] = "CATALOGUE_ID"
            copie["confiance"] = "HAUTE"
        elif fiche is None:
            copie["statut"] = "NON_RESOLU"
            copie["preuve"] = "API_SANS_REPONSE"
            copie["confiance"] = "FAIBLE"
        else:
            rapproche = _rapprocher_titre(fiche["titre"], inventaire)
            if rapproche is not None:
                copie["statut"] = "DETENU"
                copie["preuve"] = rapproche["preuve"]
                copie["confiance"] = ("HAUTE" if rapproche["preuve"] == "TITRE_EXACT"
                                      else "MOYENNE")
                if not copie["chemin_gisement"]:
                    copie["chemin_gisement"] = rapproche["fiche"]["chemin"]
            else:
                copie["statut"] = "ABSENT"
                copie["preuve"] = "RESOLU_NON_DETENU"
                copie["confiance"] = "MOYENNE"
        enrichies.append(copie)
    return enrichies


def _charger_cache(chemin: Path) -> dict:
    """Relit le cache de metadonnees (vide s'il n'existe pas)."""
    try:
        return json.loads(chemin.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def _ecrire_csv(chemin: Path, lignes: list[dict], colonnes: list[str]) -> Path:
    """Ecrit la table en CSV : ecriture locale puis copie.

    Le gisement est monte en DriveFS : une ecriture directe peut echouer
    (`OSError: [Errno 22]`) alors que l'ecriture locale, puis la copie,
    reussissent. La copie locale est conservee en cas d'echec, et son chemin
    est renvoye : la mesure n'est jamais perdue.
    """
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", newline="",
                                     suffix=".csv", delete=False) as f:
        temporaire = Path(f.name)
        redacteur = csv.DictWriter(f, fieldnames=colonnes, extrasaction="ignore")
        redacteur.writeheader()
        for ligne in lignes:
            redacteur.writerow(ligne)
    try:
        chemin.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(temporaire, chemin)
        return chemin
    except OSError as erreur:
        print("copie impossible vers %s (%s) -- copie locale : %s"
              % (chemin, erreur, temporaire))
        return temporaire


def _ecrire_table_csv(chemin: Path | None, lignes: list[dict]) -> None:
    """Ecrit la table du gisement au format des tables A1 du gisement.

    Le gisement a un format de table A1 deja etabli par les tranches par
    famille (``id,verdict,titre_api,auteurs,annee,score,...``) : la table
    resolue reprend ces noms de colonnes, pour que les deux productions
    soient lisibles par le meme lecteur.
    """
    if chemin is None:
        return
    colonnes = ["type_id", "id", "statut", "chemin_gisement",
                "source_extraction", "confiance_catalogue", "nb_fichiers",
                "nb_occurrences", "formes", "exemple_fichier",
                "exemple_contexte"]
    if lignes and "auteur" in lignes[0]:
        colonnes += ["auteur", "titre", "annee", "revue", "doi_publie",
                     "source_api", "preuve", "confiance"]
    table = []
    for ligne in lignes:
        copie = dict(ligne)
        copie["verdict"] = copie.get("statut", "")
        copie["titre_api"] = copie.get("titre", "")
        copie["auteurs"] = copie.get("auteur", "")
        copie["citations"] = copie.get("nb_occurrences", "")
        copie["fichiers"] = copie.get("exemple_fichier", "")
        copie["score"] = copie.get("confiance", "")
        table.append(copie)
    exclues = ("id", "statut", "titre", "auteur", "annee", "nb_occurrences",
               "exemple_fichier", "confiance_catalogue")
    colonnes_compatibles = ["id", "verdict", "titre_api", "auteurs", "annee",
                            "score", "source_verdict", "chemin_gisement",
                            "candidat_flux1", "citations", "fichiers"]
    colonnes_compatibles += [c for c in colonnes if c not in exclues]
    _ecrire_csv(chemin, table, colonnes_compatibles)


def _ecrire_cache(chemin: Path, donnees: dict) -> None:
    """Ecrit le cache de metadonnees (hors dépôt : le cache n'est pas un livrable).

    Le cache est ecrit par fichier temporaire puis renomme : une ecriture
    directe sur un lecteur reseau (DriveFS) peut echouer en cours d'ecriture
    (`OSError: [Errno 22]`), et un cache a moitie ecrit est pire qu'un cache
    absent. Une ecriture en echec n'interrompt pas la mesure : elle est
    signalee, et la resolution est refaite au tour suivant.
    """
    try:
        chemin.parent.mkdir(parents=True, exist_ok=True)
        temporaire = chemin.with_name(chemin.name + ".tmp")
        temporaire.write_text(json.dumps(donnees, indent=1, ensure_ascii=False),
                             encoding="utf-8")
        temporaire.replace(chemin)
    except OSError as erreur:
        print("ecriture impossible vers %s (%s)" % (chemin, erreur))


def _racine_depot() -> Path:
    """Racine du depot (deux niveaux au-dessus de `scripts/bibliography/`)."""
    return Path(__file__).resolve().parent.parent.parent


def _catalogues_par_defaut(travaux: Path) -> list[Path]:
    """Tous les catalogues A5 presents dans le dossier de travail."""
    if not travaux.is_dir():
        return []
    return sorted(travaux.glob("IDENTIFIANTS-catalogue-*.csv"))


def avertir_si_catalogues_vides(catalogues: list[Path], index: dict,
                                source: str) -> str:
    """Alerte quand le verdict `ABSENT` ne mesure plus rien.

    Le verdict `absent_catalogue` signifie « l'identifiant ne figure dans
    aucun catalogue charge ». Si **aucun catalogue n'est charge**, ce verdict
    ne mesure plus la detention : il mesure l'absence de catalogue, et la
    table sort 100 % `ABSENT` — la meme sortie qu'un gisement completement
    vide. C'est un organe qui ne voit rien qui rend un vert qui ne mesure
    rien.

    Mesure fondatrice (2026-11-14, review Hermes sur #26493) : le defaut
    `--travaux` est un chemin **Windows** (`G:/...`). Sur un siege sans ce
    montage, le dossier est absent, la liste des catalogues est vide, et la
    table produite est silencieusement 100 % `ABSENT_CATALOGUE`. Le defaut
    est documente dans le docstring, mais un document ne se voit pas : seul
    un avertissement sur stderr se voit.

    Retourne le texte d'avertissement (vide s'il n'y a rien a dire), pour
    que l'appelant l'ecrive sur stderr et que le test puisse l'examiner.
    """
    if not catalogues:
        return ("AVERTISSEMENT : aucun catalogue A5 charge (source : %s). Le "
                "verdict « absent_catalogue » ne mesure alors rien : il "
                "signifie « aucun document trouve dans un catalogue vide ». "
                "Passer --catalogue <fichier> ou --travaux <dossier> avant "
                "de lire la table." % source)
    if not index:
        return ("AVERTISSEMENT : %d catalogue(s) charge(s) (%s), mais aucun "
                "identifiant indexe. Le verdict « absent_catalogue » ne "
                "mesure rien : verifier le format des fichiers charges."
                % (len(catalogues), ", ".join(c.name for c in catalogues)))
    return ""


def _appliquer_resolution(lignes: list[dict], args) -> list[dict]:
    """Resout les identifiants de la table et statue leur detention.

    Le cache est relu d'abord : une resolution deja faite n'est pas refaite,
    et une execution interrompue ne perd pas le travail deja mesure.
    """
    cache = _charger_cache(Path(args.cache)) if args.cache else {}
    ids_arxiv = sorted({l["id"] for l in lignes if l["type_id"] == "arxiv"})
    ids_doi = sorted({l["id"] for l in lignes if l["type_id"] == "doi"})
    resolus_arxiv = dict(cache.get("arxiv", {}))
    resolus_dois = dict(cache.get("doi", {}))
    if not args.sans_reseau:
        manquants_arxiv = [i for i in ids_arxiv if i not in resolus_arxiv]
        if manquants_arxiv:
            resolus_arxiv.update(resoudre_arxiv(manquants_arxiv))
        manquants_doi = [i for i in ids_doi if i.lower() not in resolus_dois]
        if manquants_doi:
            resolus_dois.update(resoudre_dois(manquants_doi))
        if args.cache:
            _ecrire_cache(Path(args.cache), {"arxiv": resolus_arxiv,
                                             "doi": resolus_dois})
    inventaire = inventaire_gisement(Path(args.gisement))
    return statuts_resolus(lignes, resolus_arxiv, resolus_dois, inventaire)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--root", default=str(_racine_depot()))
    parser.add_argument("--csv", dest="sortie_csv")
    parser.add_argument("--json", dest="sortie_json")
    parser.add_argument("--catalogue", action="append", default=[])
    parser.add_argument("--travaux", default="G:/Mon Drive/MyIA/IA/Bibliographie-travaux")
    parser.add_argument("--surfaces", default=",".join(SURFACES_DEFAUT))
    parser.add_argument("--nu-arxiv", action="store_true")
    parser.add_argument("--inclure-archives", action="store_true")
    parser.add_argument("--resoudre", action="store_true",
                        help="Resoudre chaque identifiant en (auteur, titre, annee)")
    parser.add_argument("--gisement", default=GISEMENT)
    parser.add_argument("--cache", default="",
                        help="Cache JSON des metadonnees resolues (relu puis ecrit)")
    parser.add_argument("--sans-reseau", action="store_true",
                        help="N'appeler aucune API : ne lire que le cache")
    parser.add_argument("--depuis-json", default="",
                        help="Reprendre la table d'un rapport JSON deja produit "
                             "(pas de balayage, pas d'API)")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    surfaces = tuple(s.strip() for s in args.surfaces.split(",") if s.strip())

    if args.depuis_json:
        rapport_precedent = json.loads(
            Path(args.depuis_json).read_text(encoding="utf-8"))
        lignes = rapport_precedent.get("table", [])
        if args.resoudre:
            lignes = _appliquer_resolution(lignes, args)
        _ecrire_table_csv(Path(args.sortie_csv) if args.sortie_csv else None, lignes)
        if args.sortie_json:
            _ecrire_cache(Path(args.sortie_json), {"table": lignes})
        print("table reprise : %d lignes" % len(lignes))
        return 0

    entrees = census(root, surfaces, args.inclure_archives, args.nu_arxiv)

    catalogues = [Path(p) for p in args.catalogue]
    if not catalogues:
        catalogues = _catalogues_par_defaut(Path(args.travaux))
    index, repares, malformees = charger_catalogue(catalogues)

    # Un catalogue absent ne se voit pas dans la table : la table sort 100 %
    # `ABSENT_CATALOGUE`, la meme sortie qu'un gisement vide. L'avertissement
    # est sur stderr, la ou l'operateur le voit (cf la fonction).
    source = (", ".join(args.catalogue) if args.catalogue
              else str(args.travaux))
    avertissement = avertir_si_catalogues_vides(catalogues, index, source)
    if avertissement:
        sys.stderr.write(avertissement + "\n")

    lignes = table_du_gisement(entrees, index)

    if args.resoudre:
        lignes = _appliquer_resolution(lignes, args)

    arxiv = [e for (t, _), e in entrees.items() if t == "arxiv"]
    doi = [e for (t, _), e in entrees.items() if t == "doi"]
    formes: dict[str, int] = {}
    for entree in entrees.values():
        for forme in entree.formes:
            formes[forme] = formes.get(forme, 0) + 1
    tenus = [l for l in lignes if l["statut"].startswith("DETENU")]
    absents = [l for l in lignes if l["statut"].startswith("ABSENT")]
    non_resolus = [l for l in lignes if l["statut"] == "NON_RESOLU"]

    rapport = {
        "racine": str(root),
        "surfaces": list(surfaces),
        "fichiers_balayes": len(set().union(*[e.fichiers for e in entrees.values()])
                                ) if entrees else 0,
        "identifiants_total": len(entrees),
        "arxiv_total": len(arxiv),
        "doi_total": len(doi),
        "formes": formes,
        "detenu_catalogue": len(tenus),
        "absent_catalogue": len(absents),
        "non_resolu": len(non_resolus),
        "catalogues": [c.name for c in catalogues],
        "avertissement": avertissement,
        "lignes_catalogue_reparees": repares,
        "lignes_catalogue_malformees": malformees,
        "table": lignes,
    }

    if args.sortie_json:
        _ecrire_cache(Path(args.sortie_json), rapport)
    if args.sortie_csv:
        _ecrire_table_csv(Path(args.sortie_csv), lignes)


    print("census : %d identifiants cites (%d arXiv, %d DOI)"
          % (len(entrees), len(arxiv), len(doi)))
    print("formes : %s" % ", ".join("%s=%d" % kv for kv in sorted(formes.items())))
    print("gisement : %d DETENU (chemin connu), %d ABSENT du catalogue"
          % (len(tenus), len(absents)))
    if avertissement:
        if catalogues:
            print("ATTENTION : %d catalogue(s) charge(s) mais aucun identifiant "
                  "indexe — le verdict ABSENT ne mesure rien (voir stderr)"
                  % len(catalogues))
        else:
            print("ATTENTION : aucun catalogue charge — le verdict ABSENT ne "
                  "mesure rien (voir stderr)")
    if args.resoudre:
        print("resolution : %d DETENU, %d ABSENT, %d NON_RESOLU"
              % (len(tenus), len(absents), len(non_resolus)))
    if malformees:
        print("lignes de catalogue malformees : %d" % len(malformees))
    if repares:
        print("lignes de catalogue reparees (virgule non quotee) : %d" % len(repares))
    return 0


if __name__ == "__main__":
    sys.exit(main())
