#!/usr/bin/env python3
"""Census de la population de citations du dépôt, et table du gisement citée par chemin.

Taches A1 / A5 de l'umbrella #14407 (« alimenter le gisement canonique »).

Ce que l'instrument corrige
---------------------------
Le census de référence de l'EPIC (#14407, 2026-09-03) ne capturait qu'une
**forme** d'identifiant : l'URL ``arxiv.org/abs/NNNN.NNNNN``. La forme
**tampon** ``arXiv:NNNN.NNNNN`` — celle qu'emploie la majorité des carnets —
passait au travers. Mesure sur ``origin/main`` (2026-11-14) :

| forme capturée | identifiants arXiv distincts |
|---|---:|
| URL seule (méthode EPIC) | 175 |
| tampon seule | 326 |
| **union des deux** | **348** |

Le census de référence sous-compte donc la moitié de la population citée : il
ne voit aucun des identifiants que les carnets citent sous forme tampon.
L'union des formes n'est pas un détail de forme : c'est la population réelle
que A1 doit résoudre.

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

Aucune publication n'est lue ni copiée ici : le catalogue est un CSV de
chemins. Aucun fichier du dépôt n'est modifié.

Usage :
    python scripts/bibliography/scan_cited_identifiers.py --root . --json rapport.json
    python scripts/bibliography/scan_cited_identifiers.py --csv table.csv
    python scripts/bibliography/scan_cited_identifiers.py --catalogue "G:/.../IDENTIFIANTS-catalogue-2026-10-25.csv"

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
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

#: Repertoires hors perimetre : dependances, artefacts et sous-modules.
#: Meme liste que le detecteur de `scripts/check_arxiv_attributions.py`, pour
#: que les deux instruments mesurent la meme surface.
EXCLUS_DIRS = frozenset({
    ".git", ".lake", "node_modules", ".ipynb_checkpoints",
    "_archives", "foundry-lib", ".tmp", "scratchpad",
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
    """
    doi = brut.rstrip(".,;:").strip().strip("`\"'")
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


def _racine_depot() -> Path:
    """Racine du depot (deux niveaux au-dessus de `scripts/bibliography/`)."""
    return Path(__file__).resolve().parent.parent.parent


def _catalogues_par_defaut(travaux: Path) -> list[Path]:
    """Tous les catalogues A5 presents dans le dossier de travail."""
    if not travaux.is_dir():
        return []
    return sorted(travaux.glob("IDENTIFIANTS-catalogue-*.csv"))


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
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    surfaces = tuple(s.strip() for s in args.surfaces.split(",") if s.strip())

    entrees = census(root, surfaces, args.inclure_archives, args.nu_arxiv)

    catalogues = [Path(p) for p in args.catalogue]
    if not catalogues:
        catalogues = _catalogues_par_defaut(Path(args.travaux))
    index, repares, malformees = charger_catalogue(catalogues)

    lignes = table_du_gisement(entrees, index)

    arxiv = [e for (t, _), e in entrees.items() if t == "arxiv"]
    doi = [e for (t, _), e in entrees.items() if t == "doi"]
    formes: dict[str, int] = {}
    for entree in entrees.values():
        for forme in entree.formes:
            formes[forme] = formes.get(forme, 0) + 1
    tenus = [l for l in lignes if l["statut"] == "DETENU_CATALOGUE"]
    absents = [l for l in lignes if l["statut"] == "ABSENT_CATALOGUE"]

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
        "catalogues": [c.name for c in catalogues],
        "lignes_catalogue_reparees": repares,
        "lignes_catalogue_malformees": malformees,
        "table": lignes,
    }

    if args.sortie_json:
        Path(args.sortie_json).write_text(
            json.dumps(rapport, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.sortie_csv:
        colonnes = ["type_id", "id", "statut", "chemin_gisement",
                    "source_extraction", "confiance_catalogue", "nb_fichiers",
                    "nb_occurrences", "formes", "exemple_fichier",
                    "exemple_contexte"]
        with Path(args.sortie_csv).open("w", encoding="utf-8", newline="") as f:
            redacteur = csv.DictWriter(f, fieldnames=colonnes)
            redacteur.writeheader()
            for ligne in lignes:
                redacteur.writerow(ligne)

    print("census : %d identifiants cites (%d arXiv, %d DOI)"
          % (len(entrees), len(arxiv), len(doi)))
    print("formes : %s" % ", ".join("%s=%d" % kv for kv in sorted(formes.items())))
    print("gisement : %d DETENU (chemin connu), %d ABSENT du catalogue"
          % (len(tenus), len(absents)))
    if malformees:
        print("lignes de catalogue malformees : %d" % len(malformees))
    if repares:
        print("lignes de catalogue reparees (virgule non quotee) : %d" % len(repares))
    return 0


if __name__ == "__main__":
    sys.exit(main())
