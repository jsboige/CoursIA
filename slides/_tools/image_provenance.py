"""Census de provenance des images referencees par les decks Slidev (etape 0 de #28828).

L'arbre ne porte aucun manifeste disant d'ou vient chaque image d'un deck. Cet organe mesure
ce que l'arbre **etablit**, et rien de plus, image par image :

  - ``porteur`` : par quelle voie le fichier est entre dans l'arbre ;
  - ``diapositive`` : les diapositives Slidev qui le montrent, et la diapositive du PPTX
    d'origine quand elle se reconstitue ;
  - ``origine`` : la source declaree, quand le texte du deck ou le fichier de declarations
    en nomme une ;
  - ``licence_etablie``, ``remplacable`` : des jugements, jamais mesures ici -- ils viennent
    du fichier de declarations, ou restent vides.

Il ne mesure ni l'auteur d'une figure, ni sa licence : ce sont les deux colonnes que les
tranches de l'EPIC remplissent, une image a la fois, en ecrivant une declaration.

Usage ::

    python slides/_tools/image_provenance.py            # ecrit la page et la table
    python slides/_tools/image_provenance.py --check    # exit 1 si elles ont derive
    python slides/_tools/image_provenance.py --json     # verdict machine

Sorties, generees, jamais editees a la main :

  - ``docs/reference/slides-image-provenance.md`` : resume par deck et listes ;
  - ``docs/reference/slides-image-provenance.tsv`` : une ligne par image referencee.

Declarations, ecrites a la main et relues par l'organe :
``slides/_tools/image_provenance_declarations.tsv``. Une ligne qui nomme une image
non referencee, qui declare deux fois la meme image ou qui porte une valeur hors bareme
fait sortir l'organe en 2 : une declaration fausse ne se devine pas, elle se refuse.

Ce que l'organe etablit, et sur quelle preuve
----------------------------------------------

**``img_NNN`` est un media embarque du PPTX, pas une decoupe de page.** Le convertisseur
``slides/_tools/pptx_to_marp.py`` (retire en #21361) copiait dans ``<deck>/images/`` les
medias extraits par ``slide_tools.extract_images``, numerotes ``img_001``, ``img_002``...
dans l'ordre des diapositives du PPTX. Tout fichier a rang numerique est entre par un seul
commit, la baseline ``29531827cf9`` (679 ajouts, par aucun autre) ; cinq ``img_*`` au nom
descriptif sont entres plus tard par quatre commits, et la regle de classement les met a part.
La decoupe de page est ecartee par la mesure : aucun ``img_*`` du deck 06
ne s'apparie aux rendus ``pptx-reference/`` (correlation normalisee maximale 0,89 sur 12
images essayees a sept echelles, pour un seuil de 0,98).

**La diapositive PPTX d'origine se reconstitue par cumul.** ``extracted/inventory.json``
compte les images de chaque diapositive du PPTX ; le rang d'un ``img_NNN`` tombe dans une
tranche cumulee, donc sur une diapositive. La reconstitution n'est publiee que jusqu'au
premier rang manquant sur le disque : un fichier retire decale tous les suivants, et
l'organe prefere ne rien dire plutot que deplacer une image sur une mauvaise diapositive.
Le deck est dit ``certifie`` quand il porte exactement les ``total_images`` rangs annonces.

**Un ``img_*`` n'est pas forcement un media du PPTX.** Une image remplacee depuis la
baseline garde son nom : ``S3-acculturation/images/img_101.png`` est generee par le
``gen_img_101.py`` voisin (#12278). La regle lit donc le generateur voisin avant le nom.

Le temoin a reponse connue vit dans ``tests/test_image_provenance.py``
(``test_temoin_sur_arbre_reel``) : sur les decks certifies, un mot de contenu de l'``alt``
se retrouve dans le texte de la diapositive PPTX reconstituee bien plus souvent que dans
celui d'une diapositive tiree au hasard. Sans cet ecart, deux erreurs de cumul pourraient
se compenser sans qu'on le voie.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parents[2]
DECLARATIONS = "slides/_tools/image_provenance_declarations.tsv"
PAGE_MD = "docs/reference/slides-image-provenance.md"
PAGE_TSV = "docs/reference/slides-image-provenance.tsv"
BASELINE_COMMIT = "29531827cf9"

IMG_EXT = {".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".bmp"}

PORTEUR_MEDIA = "PPTX-media"
PORTEUR_RENDU = "PPTX-rendu"
PORTEUR_CAPTURE = "capture"
PORTEUR_GENERE = "genere"
PORTEUR_NOMME = "nomme"
PORTEUR_INCONNU = "non-classe"

STATUT_HORS = "hors-EPIC"
STATUT_DECLAREE = "origine-declaree-licence-non-etablie"
STATUT_NON_ETABLIE = "origine-non-etablie"

LICENCE_OUI = "oui"
LICENCE_NON = "non"
REMPLACABLE = {"oui", "non", "nc"}
DECL_COLUMNS = ["deck", "image", "origine", "licence", "remplacable", "preuve"]

# Un alt qui nomme une source tiersse declare d'ou vient la figure.
MARQUEURS_SOURCE = re.compile(r"\b(AIMA|Russell|Norvig|Wikipedia|Wikimedia|Wikiversity)\b")

TAG_IMG = re.compile(r"<img\b[^>]*>|!\[[^\]]*\]\([^)]*\)")
SRC = re.compile(r'(?:src|srcset)="([^"]+)"|\]\(([^)\s]+)[^)]*\)')
ALT = re.compile(r'alt="([^"]*)"')
URL_CSS = re.compile(r"url\(['\"]?([^)'\"]+)['\"]?\)")
DISTANT = re.compile(r"^(https?:|data:|//)")
NOM_MEDIA = re.compile(r"img_(\d+)$")
NOM_BRUT = re.compile(r"slide_(\d+)_img_\d+$")
NOM_RENDU = re.compile(r"slide-(\d+)$")
CLE_YAML = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*:")


class ErreurDeclarations(Exception):
    """Le fichier de declarations contredit l'arbre ou se contredit lui-meme."""


@dataclass(frozen=True)
class Reference:
    """Une occurrence d'image dans une diapositive."""

    src: str
    alt: str


@dataclass(frozen=True)
class Declaration:
    origine: str
    licence: str
    remplacable: str
    preuve: str


@dataclass
class Ligne:
    """Une image referencee, avec tout ce que l'arbre etablit sur elle."""

    deck: str
    image: str  # chemin relatif au deck, separateur /
    porteur: str
    diapositives: list[int] = field(default_factory=list)
    pptx: int | None = None
    alt: str = ""
    origine: str = ""
    licence: str = LICENCE_NON
    remplacable: str = "nc"
    statut: str = STATUT_NON_ETABLIE
    preuve: str = ""


@dataclass(frozen=True)
class IndexPptx:
    """Reconstitution du rang d'un media vers la diapositive du PPTX d'origine."""

    total: int
    presents: int
    diapositive_du_rang: dict[int, int]
    rang_manquant: int | None

    @property
    def certifie(self) -> bool:
        return self.rang_manquant is None and self.presents == self.total


def split_slides(texte: str) -> list[str]:
    """Decoupe un source Slidev en corps de diapositives, numerotes comme au rendu.

    Meme regle que ``slide_tools.count_slidev_slides`` : un ``---`` dans un bloc de code ou
    dans une frontmatter ne separe rien, et une frontmatter par diapositive est attachee a
    la diapositive qui la suit.
    """
    morceaux: list[list[str]] = []
    en_cours: list[str] = []
    cloture: str | None = None
    frontmatter = False
    for i, ligne in enumerate(texte.split("\n")):
        nue = ligne.strip()
        marque = nue[:3]
        if marque in ("```", "~~~"):
            if cloture is None:
                cloture = marque
            elif cloture == marque:
                cloture = None
            en_cours.append(ligne)
            continue
        if cloture is not None:
            en_cours.append(ligne)
            continue
        if i == 0 and nue == "---":
            frontmatter = True
            continue
        if frontmatter and nue == "---":
            frontmatter = False
            continue
        if not frontmatter and nue == "---":
            morceaux.append(en_cours)
            en_cours = []
            continue
        en_cours.append(ligne)
    morceaux.append(en_cours)

    corps: list[str] = []
    for morceau in morceaux:
        lignes = [x.strip() for x in morceau if x.strip()]
        est_frontmatter = bool(lignes) and len(lignes) <= 12 and all(CLE_YAML.match(x) for x in lignes)
        if not est_frontmatter:
            corps.append("\n".join(morceau))
    return corps


def references_diapositive(corps: str) -> list[Reference]:
    """Les images montrees par une diapositive : balise img, markdown, puis url() CSS."""
    vues: list[Reference] = []
    for marquage in TAG_IMG.finditer(corps):
        texte = marquage.group(0)
        cible = SRC.search(texte)
        if not cible:
            continue
        src = (cible.group(1) or cible.group(2) or "").strip()
        alt = ALT.search(texte)
        vues.append(Reference(src, (alt.group(1) if alt else "").strip()))
    dans_balise = {v.src for v in vues}
    for cible in URL_CSS.finditer(TAG_IMG.sub("", corps)):
        src = cible.group(1).strip()
        if src and src not in dans_balise:
            vues.append(Reference(src, ""))
    return vues


def resoudre(src: str, deck: Path, racine: Path) -> Path | None | str:
    """Chemin du fichier vise, ``None`` s'il est absent de l'arbre, ``"distant"`` si reseau.

    Un deck peut ranger ses images sous ``public/`` et les referencer depuis la racine du
    site (``/images/x.png``) : la racine du site est ``<deck>/public`` d'abord, puis la
    racine ``slides/`` comme pour un chemin relatif.
    """
    brut = unquote(src.split("?")[0].split("#")[0].strip())
    if not brut:
        return None
    if DISTANT.match(brut):
        return "distant"
    candidats: list[Path]
    if brut.startswith("/"):
        rel = brut.lstrip("/")
        candidats = [deck / "public" / rel, racine / rel]
    else:
        candidats = [deck / brut, racine / brut]
    for chemin in candidats:
        try:
            if chemin.is_file():
                return chemin.resolve()
        except OSError:
            continue
    return None


def index_pptx(deck: Path, dossier_images: Path) -> IndexPptx | None:
    """Rang d'un ``img_NNN`` vers la diapositive du PPTX, jusqu'au premier rang manquant."""
    inventaire = deck / "extracted" / "inventory.json"
    if not inventaire.is_file():
        return None
    try:
        donnees: dict[str, Any] = json.loads(inventaire.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    rang_par_diapositive: dict[int, int] = {}
    rang = 0
    for diapo in donnees.get("slides", []):
        compte = int(diapo.get("image_count") or 0)
        for r in range(rang + 1, rang + compte + 1):
            rang_par_diapositive[r] = int(diapo["number"])
        rang += compte

    presents: set[int] = set()
    try:
        for fichier in dossier_images.iterdir():
            nom = NOM_MEDIA.match(fichier.stem)
            if nom and fichier.is_file():
                presents.add(int(nom.group(1)))
    except OSError:
        return None

    diapositive_du_rang: dict[int, int] = {}
    r = 1
    while r <= rang and r in presents:
        diapositive_du_rang[r] = rang_par_diapositive[r]
        r += 1
    return IndexPptx(rang, len(presents), diapositive_du_rang, r if r <= rang else None)


def classer(fichier: Path, racine: Path) -> tuple[str, int | None, str]:
    """Porteur d'un fichier d'apres sa voie d'entree, sa diapositive au nom, sa preuve."""
    rel = fichier.relative_to(racine)
    deck = rel.parts[0]
    dans_deck = fichier.relative_to(racine / deck)
    dossiers = dans_deck.parts[:-1]

    generateur = fichier.parent / f"gen_{fichier.stem}.py"
    if generateur.is_file():
        return PORTEUR_GENERE, None, f"generateur voisin {generateur.name}"

    if NOM_MEDIA.match(fichier.stem) and "images" in dossiers:
        return PORTEUR_MEDIA, None, f"renomme par pptx_to_marp.py (baseline {BASELINE_COMMIT})"

    brut = NOM_BRUT.match(fichier.stem)
    if brut:
        return PORTEUR_MEDIA, int(brut.group(1)), "media PPTX au nom de l'extracteur (slide_tools.extract_images)"

    if "pptx-reference" in dossiers and NOM_RENDU.match(fichier.stem):
        return PORTEUR_RENDU, None, "rendu de page du PPTX (slide_tools.render_slides)"

    if "screenshots" in dossiers:
        return PORTEUR_CAPTURE, None, "dossier screenshots/"

    if "slidev-export" in dossiers:
        return PORTEUR_GENERE, None, "export du deck Slidev"

    if "images" in dossiers:
        return PORTEUR_NOMME, None, "nom pose a la main (voie d'entree non etablie)"

    return PORTEUR_INCONNU, None, "voie d'entree non etablie"


def lire_declarations(chemin: Path, connues: set[tuple[str, str]]) -> dict[tuple[str, str], Declaration]:
    """Relit le fichier de declarations : une ligne doit nommer une image referencee, une fois."""
    if not chemin.is_file():
        return {}
    lignes = chemin.read_text(encoding="utf-8").splitlines()
    if not lignes:
        return {}
    entete = lignes[0].split("\t")
    if entete != DECL_COLUMNS:
        raise ErreurDeclarations(f"entete attendu {DECL_COLUMNS}, lu {entete}")
    sorties: dict[tuple[str, str], Declaration] = {}
    for numero, ligne in enumerate(lignes[1:], 2):
        if not ligne.strip() or ligne.lstrip().startswith("#"):
            continue
        champs = [c.strip() for c in ligne.split("\t")]
        if len(champs) != len(DECL_COLUMNS):
            raise ErreurDeclarations(f"ligne {numero} : {len(champs)} champs, {len(DECL_COLUMNS)} attendus")
        deck, image, origine, licence, remplacable, preuve = champs
        cle = (deck, image)
        if cle not in connues:
            raise ErreurDeclarations(f"ligne {numero} : {deck}/{image} n'est pas une image referencee par un deck")
        if cle in sorties:
            raise ErreurDeclarations(f"ligne {numero} : {deck}/{image} declaree deux fois")
        if licence not in (LICENCE_OUI, LICENCE_NON):
            raise ErreurDeclarations(f"ligne {numero} : licence {licence!r}, attendu oui ou non")
        if remplacable not in REMPLACABLE:
            raise ErreurDeclarations(
                f"ligne {numero} : remplacable {remplacable!r}, attendu {'/'.join(sorted(REMPLACABLE))}"
            )
        if not origine:
            raise ErreurDeclarations(f"ligne {numero} : origine vide")
        sorties[cle] = Declaration(origine, licence, remplacable, preuve)
    return sorties


def _collecter(racine: Path) -> tuple[
    dict[tuple[str, str], Ligne], list[tuple[str, int, str]], list[tuple[str, int, str]]
]:
    """Les lignes brutes (porteur seulement), les references non resolues, les images distantes."""
    lignes: dict[tuple[str, str], Ligne] = {}
    non_resolues: list[tuple[str, int, str]] = []
    distantes: list[tuple[str, int, str]] = []

    for source in sorted(p for p in racine.rglob("slides.md") if "node_modules" not in p.parts):
        deck = source.parent
        nom_deck = deck.relative_to(racine).as_posix()
        for numero, corps in enumerate(split_slides(source.read_text(encoding="utf-8")), 1):
            for reference in references_diapositive(corps):
                cible = resoudre(reference.src, deck, racine)
                if cible == "distant":
                    distantes.append((nom_deck, numero, reference.src))
                    continue
                if cible is None:
                    non_resolues.append((nom_deck, numero, reference.src))
                    continue
                image = cible.relative_to(deck).as_posix()
                cle = (nom_deck, image)
                ligne = lignes.get(cle)
                if ligne is None:
                    porteur, pptx, preuve = classer(cible, racine)
                    ligne = Ligne(nom_deck, image, porteur, pptx=pptx, preuve=preuve)
                    lignes[cle] = ligne
                ligne.diapositives.append(numero)
                if reference.alt and not ligne.alt:
                    ligne.alt = reference.alt
    return lignes, non_resolues, distantes


def recenser(racine: Path, declarations_chemin: Path) -> dict[str, Any]:
    """Le census : une ligne par image referencee, les comptes par deck, les references cassees."""
    racine = racine.resolve()
    lignes, non_resolues, distantes = _collecter(racine)
    declarations = lire_declarations(declarations_chemin, set(lignes))

    # Diapositive PPTX : un index par deck, lu sur le dossier d'images de la premiere ligne.
    indices: dict[str, IndexPptx | None] = {}
    for ligne in lignes.values():
        if ligne.porteur != PORTEUR_MEDIA or ligne.pptx is not None:
            continue
        nom = NOM_MEDIA.match(Path(ligne.image).stem)
        if not nom:
            continue
        if ligne.deck not in indices:
            indices[ligne.deck] = index_pptx(
                racine / ligne.deck, racine / ligne.deck / Path(ligne.image).parent
            )
        index = indices[ligne.deck]
        rang = int(nom.group(1))
        if index is None:
            ligne.preuve += " ; pas d'inventaire PPTX lisible"
        elif rang in index.diapositive_du_rang:
            ligne.pptx = index.diapositive_du_rang[rang]
            ligne.preuve += " ; inventaire cumule, certifie" if index.certifie else " ; inventaire cumule"
        else:
            ligne.preuve += (
                f" ; reconstitution arretee au rang {index.rang_manquant} "
                f"({index.presents} presents pour {index.total} a l'inventaire)"
            )

    # Origine, licence, statut : la declaration d'abord, le texte du deck ensuite.
    for cle, ligne in lignes.items():
        declaration = declarations.get(cle)
        marqueur = MARQUEURS_SOURCE.search(ligne.alt)
        if declaration is not None:
            ligne.origine = declaration.origine
            ligne.licence = declaration.licence
            ligne.remplacable = declaration.remplacable
            if declaration.preuve:
                ligne.preuve = f"{ligne.preuve} ; declaration : {declaration.preuve}"
            ligne.statut = STATUT_HORS if declaration.licence == LICENCE_OUI else STATUT_DECLAREE
        elif marqueur:
            ligne.origine = f"alt : « {ligne.alt} »"
            ligne.statut = STATUT_DECLAREE
        elif ligne.porteur == PORTEUR_RENDU:
            page = NOM_RENDU.match(Path(ligne.image).stem)
            ligne.origine = f"rendu de la page {page.group(1) if page else '?'} du PPTX du deck"

    # Ce qui est sur le disque sans qu'aucun deck ne le montre : la frontiere du census.
    referencees = {(l.deck, l.image) for l in lignes.values()}
    sur_disque: dict[str, Counter[str]] = defaultdict(Counter)
    vues: set[tuple[str, str]] = set()
    for fichier in sorted(racine.rglob("*")):
        if not fichier.is_file() or "node_modules" in fichier.parts:
            continue
        if fichier.suffix.lower() not in IMG_EXT:
            continue
        rel = fichier.relative_to(racine)
        deck = rel.parts[0]
        image = fichier.relative_to(racine / deck).as_posix()
        if (deck, image) in referencees or (deck, image) in vues:
            continue
        vues.add((deck, image))
        dossier = Path(image).parts[0] if len(Path(image).parts) > 1 else "."
        sur_disque[deck][dossier] += 1

    ordonnees = sorted(lignes.values(), key=lambda l: (l.deck, l.image))
    par_deck: dict[str, dict[str, Any]] = {}
    for deck in sorted({l.deck for l in ordonnees} | set(sur_disque)):
        mes = [l for l in ordonnees if l.deck == deck]
        index = indices.get(deck)
        par_deck[deck] = {
            "referencees": len(mes),
            "porteurs": dict(sorted(Counter(l.porteur for l in mes).items())),
            "statuts": dict(sorted(Counter(l.statut for l in mes).items())),
            "non_referencees": sum(sur_disque.get(deck, Counter()).values()),
            "non_referencees_par_dossier": dict(sorted(sur_disque.get(deck, Counter()).items())),
            "pptx_total": index.total if index is not None else None,
            "pptx_presents": index.presents if index is not None else None,
            "pptx_certifie": index.certifie if index is not None else None,
        }

    return {
        "lignes": ordonnees,
        "par_deck": par_deck,
        "non_resolues": non_resolues,
        "distantes": distantes,
        "declarations": len(declarations),
    }


def table_tsv(census: dict[str, Any]) -> str:
    """Une ligne par image referencee : les sept colonnes de l'EPIC, plus le statut et la preuve."""
    colonnes = [
        "deck", "image", "porteur", "diapositive_slidev", "diapositive_pptx",
        "origine", "licence_etablie", "remplacable", "statut", "preuve",
    ]
    sorties = ["\t".join(colonnes)]
    for l in census["lignes"]:
        sorties.append(
            "\t".join(
                [
                    l.deck,
                    l.image,
                    l.porteur,
                    ",".join(str(n) for n in sorted(set(l.diapositives))),
                    str(l.pptx) if l.pptx is not None else "",
                    (l.origine or "-").replace("\t", " "),
                    l.licence,
                    l.remplacable,
                    l.statut,
                    l.preuve.replace("\t", " "),
                ]
            )
        )
    return "\n".join(sorties) + "\n"


def _noms(lignes: list[Ligne]) -> str:
    """Les noms d'un deck, en chemin relatif quand deux fichiers partagent leur nom de fichier."""
    basenoms = Counter(Path(l.image).name for l in lignes)
    return ", ".join(
        f"`{l.image if basenoms[Path(l.image).name] > 1 else Path(l.image).name}`" for l in lignes
    )


def page_markdown(census: dict[str, Any]) -> str:
    """La page de reference : methode, resume par deck, puis les listes."""
    lignes: list[Ligne] = census["lignes"]
    par_deck: dict[str, dict[str, Any]] = census["par_deck"]
    out: list[str] = []
    aj = out.append

    aj("# Provenance des images des decks Slidev — census (étape 0 de #28828)")
    aj("")
    aj("REFERENCE — page **générée** : ne pas l'éditer à la main. Régénérer par")
    aj("")
    aj("```bash")
    aj("python slides/_tools/image_provenance.py")
    aj("```")
    aj("")
    aj("La table complète, une ligne par image, est dans")
    aj("[`slides-image-provenance.tsv`](slides-image-provenance.tsv) ; les jugements s'écrivent dans")
    aj("`slides/_tools/image_provenance_declarations.tsv`, que l'organe relit et refuse dès qu'une")
    aj("ligne contredit l'arbre.")
    aj("")
    aj("## Ce que mesure ce census")
    aj("")
    aj("L'univers est **l'image qu'un lecteur voit** : tout fichier d'image qu'un `slides.md`")
    aj("référence. Une image présente sur le disque mais montrée par aucun deck n'est pas une ligne")
    aj("du census ; elle est comptée par deck, pour qu'une tranche sache ce qu'elle laisse dehors.")
    aj("")
    aj("Sept colonnes, celles que l'EPIC demande :")
    aj("")
    aj("| Colonne | Mesuré ou déclaré | Ce qu'elle dit |")
    aj("|---|---|---|")
    aj("| `image`, `deck` | mesuré | le fichier et son deck |")
    aj("| `diapositive_slidev` | mesuré | les diapositives du deck qui montrent l'image |")
    aj("| `diapositive_pptx` | reconstitué | la diapositive du PPTX d'origine, quand le cumul tient |")
    aj("| `porteur` | mesuré | par quelle voie le fichier est entré dans l'arbre |")
    aj("| `origine` | déclaré | la source nommée par le deck (texte `alt`) ou par une déclaration |")
    aj("| `licence_etablie` | déclaré | `oui` seulement sur déclaration ; `non` par défaut |")
    aj("| `remplacable` | déclaré | `oui` / `non` / `nc` (non tranché), jamais déduit |")
    aj("")
    aj("## Méthode — et ce qu'elle ne mesure pas")
    aj("")
    aj("Un `img_NNN` est un **média embarqué du PPTX**, copié par le convertisseur")
    aj("`slides/_tools/pptx_to_marp.py` (retiré en #21361) depuis les médias extraits par")
    aj(f"`slide_tools.extract_images`, lors d'un seul commit, la baseline `{BASELINE_COMMIT}`")
    aj("(679 ajouts, par aucun autre commit). Cinq `img_*` au nom descriptif sont")
    aj("entrés plus tard par quatre commits (`img_pptx_52_aspirateur.png`, `img_pptx_53_belief.png`,")
    aj("`img_043_local_search.png`, `img_robot_extracted.png`, `img_ga_8queens_solution.png`) :")
    aj("l'organe les classe `nomme`, jamais `PPTX-media`. Ce n'est pas une découpe de page : aucun")
    aj("`img_*` du deck 06 ne s'apparie aux rendus `pptx-reference/` (corrélation normalisée")
    aj("maximale 0,89 sur 12 images essayées à sept échelles, pour un seuil de 0,98).")
    aj("")
    aj("La diapositive PPTX d'origine se reconstitue en cumulant les `image_count` de")
    aj("`extracted/inventory.json`. Elle n'est publiée que jusqu'au premier rang manquant sur le")
    aj("disque — un fichier retiré décale tous les suivants, et l'organe préfère ne rien dire")
    aj("plutôt que déplacer une image sur une mauvaise diapositive. Un deck est dit **certifié**")
    aj("quand il porte exactement les `total_images` rangs de son inventaire.")
    aj("")
    aj("Témoin à réponse connue, rejoué par `pytest tests/test_image_provenance.py -k temoin` : un")
    aj("mot de contenu de l'`alt` se retrouve dans le texte de la diapositive PPTX reconstituée")
    aj("**118 fois sur 189 essais**, contre **29** pour une diapositive tirée au hasard (graine 7,")
    aj("six decks certifiés). Sans cet écart, deux erreurs de cumul pourraient se compenser sans")
    aj("qu'on le voie.")
    aj("")
    aj("**Première piste d'origine, pour une image nommée à la main** : son commit d'entrée.")
    aj("")
    aj("```bash")
    aj("git log --diff-filter=A --format='%h %ad %s' --date=short -- slides/<deck>/<chemin>")
    aj("```")
    aj("")
    aj("C'est ainsi que les déclarations déjà versées ont été établies : les six images du deck 07")
    aj("viennent d'un seul commit, `554062be033`, qui les dit « from Wikimedia Commons » ; les deux")
    aj("QR codes d'Argumentum encodent la même URL ; le robot du deck S3 est extrait de son PPTX")
    aj("(`05cba7e95fd`). Un commit qui nomme la source établit l'origine ; il n'établit pas la")
    aj("licence par fichier, et c'est la distinction que portent les deux colonnes.")
    aj("")
    aj("**Ce que l'arbre ne porte pas** : l'auteur d'une figure et sa licence. Un média du PPTX")
    aj("peut être un schéma maison comme une figure recopiée d'un manuel ; seul un texte qui nomme")
    aj("sa source, ou une déclaration, l'établit. La colonne `origine` reste donc vide pour la")
    aj("grande majorité, et c'est la mesure, pas un oubli.")
    aj("")
    aj("## Résultat — un deck, une ligne")
    aj("")
    aj(
        "| Deck | Images référencées | Origine non établie | Origine déclarée, licence non établie "
        "| Hors EPIC | Porteurs | PPTX | Sur disque, non référencées |"
    )
    aj("|---|---|---|---|---|---|---|---|")
    for deck, d in par_deck.items():
        statuts = d["statuts"]
        porteurs = ", ".join(f"{k} {v}" for k, v in d["porteurs"].items()) or "—"
        if d["pptx_certifie"] is None:
            pptx = "—"
        elif d["pptx_certifie"]:
            pptx = "certifié"
        else:
            pptx = f"partiel ({d['pptx_presents']}/{d['pptx_total']})"
        aj(
            f"| {deck} | {d['referencees']} | {statuts.get(STATUT_NON_ETABLIE, 0)} | "
            f"{statuts.get(STATUT_DECLAREE, 0)} | {statuts.get(STATUT_HORS, 0)} | {porteurs} | {pptx} | "
            f"{d['non_referencees']} |"
        )
    total_ref = sum(d["referencees"] for d in par_deck.values())
    total_non = sum(d["statuts"].get(STATUT_NON_ETABLIE, 0) for d in par_deck.values())
    total_decl = sum(d["statuts"].get(STATUT_DECLAREE, 0) for d in par_deck.values())
    total_hors = sum(d["statuts"].get(STATUT_HORS, 0) for d in par_deck.values())
    aj("")
    aj(
        f"**{total_ref} images référencées** : {total_non} d'origine non établie, {total_decl} d'origine "
        "déclarée sans licence établie, hors EPIC. Les fichiers d'image qu'aucun `slides.md` ne "
        "montre sont hors du census, comptés par deck dans la dernière colonne du tableau."
    )
    aj("")

    non_etablies: dict[str, list[Ligne]] = defaultdict(list)
    declarees: dict[str, list[Ligne]] = defaultdict(list)
    hors: dict[str, list[Ligne]] = defaultdict(list)
    for l in lignes:
        if l.statut == STATUT_NON_ETABLIE:
            non_etablies[l.deck].append(l)
        elif l.statut == STATUT_DECLAREE:
            declarees[l.deck].append(l)
        else:
            hors[l.deck].append(l)

    aj("## La liste — images dont l'origine n'est pas établie")
    aj("")
    aj("C'est elle qui ouvre les tranches. Une image en sort par une déclaration qui nomme son")
    aj("origine **et** une licence claire.")
    aj("")
    for deck in sorted(non_etablies):
        mes = non_etablies[deck]
        aj(f"### {deck} — {len(mes)} image(s)")
        aj("")
        aj(_noms(mes))
        aj("")

    aj("## Origine déclarée, licence non établie")
    aj("")
    aj("La source est nommée dans le deck ; la licence de la figure ne l'est pas. C'est le cas des")
    aj("figures d'AIMA, de Russell & Norvig, de Wikipedia : remplacer la figure par une sortie de")
    aj("carnet est souvent la seule voie, et la déclaration doit le dire.")
    aj("")
    if declarees:
        for deck in sorted(declarees):
            mes = declarees[deck]
            aj(f"### {deck} — {len(mes)} image(s)")
            aj("")
            for l in mes:
                diapo = f"diapo Slidev {','.join(str(n) for n in sorted(set(l.diapositives)))}"
                pptx = f", PPTX {l.pptx}" if l.pptx is not None else ""
                aj(f"- `{l.image}` ({diapo}{pptx}) — {l.origine}")
            aj("")
    else:
        aj("Aucune.")
        aj("")

    aj("## Hors EPIC — origine et licence établies")
    aj("")
    aj("Ces images sortent de l'EPIC : leur origine est déclarée et leur licence est établie.")
    aj("")
    if hors:
        for deck in sorted(hors):
            mes = hors[deck]
            aj(f"### {deck} — {len(mes)} image(s)")
            aj("")
            for l in mes:
                aj(f"- `{l.image}` — {l.origine} ; remplaçable : {l.remplacable}")
            aj("")
    else:
        aj("Aucune.")
        aj("")

    if census["non_resolues"]:
        aj("## Références qui ne résolvent pas")
        aj("")
        aj("Un deck cite un fichier absent de l'arbre. C'est un défaut de deck, pas une image :")
        aj("il est listé pour qu'une tranche le répare.")
        aj("")
        for deck, numero, src in census["non_resolues"]:
            aj(f"- {deck}, diapo {numero} : `{src}`")
        aj("")

    if census["distantes"]:
        aj("## Images distantes")
        aj("")
        aj("Un deck montre une image servie par un tiers. Elle n'est pas dans l'arbre, donc hors du")
        aj("census, mais sa provenance est une question de licence à part entière :")
        aj("")
        for deck, numero, src in census["distantes"]:
            aj(f"- {deck}, diapo {numero} : {src}")
        aj("")

    aj("## Frontière du census")
    aj("")
    aj("Ce qui n'est pas une ligne, et pourquoi :")
    aj("")
    aj("- les **rendus de page** `pptx-reference/slide-NNN.png` que nul `slides.md` ne montre : ce")
    aj("  sont des références de comparaison, pas du contenu de deck ;")
    aj("- les **exports** `slidev-export/` et les **captures** `screenshots/` d'un deck qui ne les")
    aj("  référence pas dans son `slides.md` ;")
    aj("- les sources `deck-*.md` d'un deck multi-fichiers, quand l'énumération des decks ne lit que")
    aj("  `slides.md` : leurs images restent hors census tant que la structure ne les expose pas.")
    aj("")
    aj("Reprise : `python slides/_tools/image_provenance.py --check` sort en 1 si cette page ou la")
    aj("table ont dérivé de ce que l'organe produit.")
    return "\n".join(out) + "\n"


def _ecrire(chemin: Path, texte: str) -> None:
    chemin.parent.mkdir(parents=True, exist_ok=True)
    with chemin.open("w", encoding="utf-8", newline="\n") as f:
        f.write(texte)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Census de provenance des images des decks Slidev.")
    ap.add_argument("--check", action="store_true", help="compare aux fichiers committes, exit 1 sur derive")
    ap.add_argument("--json", action="store_true", help="verdict machine sur la sortie standard")
    ap.add_argument("--repo-root", type=Path, default=REPO_ROOT, help="racine du depot")
    ap.add_argument(
        "--declarations", type=Path, default=None, help="fichier de declarations (defaut : celui du depot)"
    )
    args = ap.parse_args(argv)

    racine = args.repo_root.resolve()
    declarations = args.declarations if args.declarations is not None else racine / DECLARATIONS
    try:
        census = recenser(racine / "slides", declarations)
    except ErreurDeclarations as erreur:
        print(f"DECLARATIONS-INVALIDES : {erreur}", file=sys.stderr)
        return 2

    md = page_markdown(census)
    tsv = table_tsv(census)
    cibles = [(racine / PAGE_MD, md), (racine / PAGE_TSV, tsv)]

    if args.check:
        derivees = []
        for chemin, attendu in cibles:
            if not chemin.is_file():
                derivees.append(f"{chemin} : absent")
            elif chemin.read_text(encoding="utf-8") != attendu:
                derivees.append(f"{chemin} : different de ce que l'organe produit")
        if derivees:
            for ligne in derivees:
                print(f"DERIVE : {ligne}", file=sys.stderr)
            return 1
        if args.json:
            print(json.dumps({"verdict": "A-JOUR", "lignes": len(census["lignes"])}, ensure_ascii=False))
        else:
            print(f"A-JOUR : {len(census['lignes'])} images referencees, page et table identiques")
        return 0

    for chemin, texte in cibles:
        _ecrire(chemin, texte)
    if args.json:
        print(
            json.dumps(
                {
                    "verdict": "ECRIT",
                    "lignes": len(census["lignes"]),
                    "par_deck": {
                        deck: {k: d[k] for k in ("referencees", "non_referencees", "pptx_certifie")}
                        for deck, d in census["par_deck"].items()
                    },
                    "non_resolues": len(census["non_resolues"]),
                    "distantes": len(census["distantes"]),
                    "declarations": census["declarations"],
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print(f"ECRIT : {PAGE_MD} et {PAGE_TSV} ({len(census['lignes'])} images referencees)")
        if census["non_resolues"]:
            print(f"  {len(census['non_resolues'])} references non resolues (listees dans la page)")
        if census["distantes"]:
            print(f"  {len(census['distantes'])} images distantes (listees dans la page)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
