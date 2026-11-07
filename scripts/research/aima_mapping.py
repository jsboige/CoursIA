#!/usr/bin/env python3
"""Extraction des tables des matieres d'AIMA (3e et 4e editions) et comparaison.

Issue #24997 (enfant de l'EPIC #24993). Les PDF sources sont les copies
archivees dans le gisement bibliographique (regle `bibliography-hygiene`) :
elles ne sont jamais committes, ce script les lit sur place et n'ecrit que
les donnees derivees.

Trois etapes reproductibles :

1. `extract`  -- produit `aima3e-toc.json` et `aima4e-toc.json`, une entree par
   section, chaque entree portant la page du PDF qui l'ouvre (l'ancre de
   verification demandee par l'issue).
2. `diff`     -- produit `ecarts-3e-4e.json` : chapitres et sections ajoutes,
   retires, renommes ou deplaces entre les deux editions.
3. `coverage` -- rattache chaque section aux carnets du corpus qui l'enseignent,
   sur evidence (le terme de la section apparait dans le carnet).

Usage :
    python scripts/research/aima_mapping.py extract --pdf-dir "<dossier des PDF>"
    python scripts/research/aima_mapping.py diff
    python scripts/research/aima_mapping.py coverage
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "docs" / "curriculum" / "aima-mapping"
DEFAULT_PDF_DIR = Path(
    r"G:\Mon Drive\MyIA\IA\Bibliographie IA\AI"
)

PDF_3E = "2010 - Russell Norvig - Artificial Intelligence - A Modern Approach (3rd Edition).pdf"
PDF_4E = "2021 - Russell Norvig - Artificial Intelligence - A Modern Approach (4th Edition).pdf"

# ---------------------------------------------------------------------------
# Normalisation
# ---------------------------------------------------------------------------


def norm(text: str) -> str:
    """Normalise un titre pour la comparaison (ligatures, tirets, espaces)."""
    text = unicodedata.normalize("NFKC", text)
    text = text.replace("–", "-").replace("—", "-").replace("−", "-")
    text = text.replace("‘", "'").replace("’", "'")
    text = text.replace("“", '"').replace("”", '"')
    return re.sub(r"\s+", " ", text).strip()


def slug(text: str) -> str:
    """Cle de jointure stable entre les deux editions."""
    s = norm(text).lower()
    s = re.sub(r"[^a-z0-9]+", "-", s).strip("-")
    return s


# ---------------------------------------------------------------------------
# Lecture des PDF
# ---------------------------------------------------------------------------


def _open_pdf(pdf_dir: Path, filename: str):
    """Ouvre une copie archivee, en tolérant deux rangements du gisement.

    Le dossier `AI/` et la racine du gisement ont tous deux port les PDF
    selon l'etat du rangement bibliographique ; on accepte les deux, et on
    retombe sur un motif de nom si le prefixe de date change.
    """
    import pymupdf

    candidats = [pdf_dir / filename]
    if pdf_dir.parent != pdf_dir:
        candidats.append(pdf_dir.parent / filename)
    motif = "*3rd Edition*.pdf" if "3rd" in filename else "*4th Edition*.pdf"
    for dossier in (pdf_dir, pdf_dir.parent):
        candidats.extend(sorted(dossier.glob(motif)))

    for path in candidats:
        if path.exists():
            return pymupdf.open(path), path

    raise SystemExit(
        f"PDF introuvable : {pdf_dir / filename}\n"
        "Les copies archivees ne sont pas committes (regle bibliography-hygiene) ; "
        "passe --pdf-dir pointant sur le gisement."
    )


def _page_lines(doc, index: int) -> list[str]:
    return [l.strip() for l in doc[index].get_text().splitlines() if l.strip()]


def _rows(doc, index: int) -> list[list[str]]:
    """Mots d'une page regroupes par ligne (bande horizontale de 3 points).

    Le regroupement par coordonnees est ce qui permet de lire un sommaire
    imprime ou le titre, les points de conduite et le numero de page sont
    dans la meme ligne mais dans des zones distinctes de la page.
    """
    buckets: dict[int, list[tuple[float, str]]] = {}
    for x0, y0, _x1, _y1, word, *_ in doc[index].get_text("words"):
        buckets.setdefault(round(y0 / 3.0), []).append((x0, word))
    return [[w for _, w in sorted(bucket)] for _k, bucket in sorted(buckets.items())]


# ---------------------------------------------------------------------------
# 3e edition -- structure depuis l'outline du PDF
# ---------------------------------------------------------------------------

_ROMAN = re.compile(r"^[IVXLC]+$")
_PART_TITLE = re.compile(r"^([IVXLC]{1,4}):\s*(.+)$")
_ANNEXE_TITLE = re.compile(r"^([A-Z]):\s*(.+)$")
_NUMBERED = re.compile(r"^(\d+(?:\.\d+)*)\s+(.+)$")
_DOTS_ONLY = re.compile(r"^[.\s]+$")
_ROMAN_WORD = re.compile(r"^[ivxlcdm]+$", re.IGNORECASE)

# Bornes du sommaire 3e (pages PDF, index 0-based) : le sommaire occupe les
# pages xiii a xviii ; le corps commence a la page de l'outline du chapitre 1.
TOC_3E_FIRST = 13
TOC_3E_LAST = 18


def extract_3e(pdf_dir: Path) -> dict:
    """Table des matieres de la 3e edition.

    Structure : l'outline du PDF (niveaux 1/2/3 = partie/chapitre/section ;
    le niveau 1 porte "I: Artificial Intelligence" ... "VII: Conclusions", puis
    les annexes "A:" et "B:").

    Page imprimee : derivee de l'offset constant du corps (le PDF 3e est en une
    colonne, une page imprimee par page PDF). L'offset est cale sur le
    sommaire imprime (lu ligne par ligne) puis verifie sur TOUTES les entrees ;
    toute entree dont la page imprimee ne suit pas l'offset est signalee.
    """
    doc, path = _open_pdf(pdf_dir, PDF_3E)
    outline = doc.get_toc()  # [level, title, page] -- page 1-indexee

    entries = []
    for level, title, page in outline:
        title = norm(title)
        if level == 1:
            m = _PART_TITLE.match(title)
            if m:
                entries.append(
                    {
                        "kind": "part",
                        "num": m.group(1),
                        "title": norm(m.group(2)),
                        "pdf_page": page,
                    }
                )
                continue
            m = _ANNEXE_TITLE.match(title)
            if m:
                entries.append(
                    {
                        "kind": "annexe",
                        "num": m.group(1),
                        "title": norm(m.group(2)),
                        "pdf_page": page,
                    }
                )
                continue
            continue  # pages de garde, sommaire, bibliographie, index
        if level == 2:
            kind = "chapter"
        elif level == 3:
            kind = "section"
        else:
            continue
        m = _NUMBERED.match(title)
        if not m:
            continue  # lettres de l'index final
        entries.append(
            {
                "kind": kind,
                "num": m.group(1),
                "title": norm(m.group(2)),
                "pdf_page": page,
            }
        )

    # Sommaire imprime : pages des parties, chapitres et sections.
    toc = parse_3e_toc_pages(doc)

    # Offset : page PDF - page imprimee, pris en mode sur toutes les entrees
    # trouvees dans le sommaire.
    offsets: list[int] = []
    for e in entries:
        if e["kind"] == "part":
            continue
        for printed in toc.get(e["num"], e["title"], loose=True):
            if printed is not None:
                offsets.append(e["pdf_page"] - printed)
    if not offsets:
        raise SystemExit("3e : aucune page imprimee lue dans le sommaire, offset indeterminable")
    offset = max(set(offsets), key=offsets.count)

    divergent = []
    for e in entries:
        if e["kind"] == "part":
            continue
        printed = e["pdf_page"] - offset
        e["printed_page"] = printed
        cands = toc.get(e["num"], e["title"], loose=True)
        if not cands:
            divergent.append({"num": e["num"], "pdf_page": e["pdf_page"],
                              "printed_page": printed, "statut": "absent-du-sommaire"})
        elif printed not in cands:
            divergent.append({"num": e["num"], "pdf_page": e["pdf_page"],
                              "printed_page": printed, "candidats": cands,
                              "statut": "page-imprimee-divergente"})

    # Une partie s'ouvre sur son premier chapitre : sa page imprimee est celle
    # de ce chapitre (c'est ainsi que le sommaire l'imprime).
    _attach_parts(entries)
    first_chapter = {}
    for e in entries:
        if e["kind"] == "chapter":
            first_chapter.setdefault(e["part"], e)
    for e in entries:
        if e["kind"] == "part":
            ch = first_chapter.get(e["num"])
            e["printed_page"] = ch["printed_page"] if ch else None
            e["premier_chapitre"] = ch["num"] if ch else None

    doc.close()
    return {
        "edition": "3e",
        "titre": "Artificial Intelligence: A Modern Approach (3rd Edition)",
        "auteurs": "Stuart Russell, Peter Norvig",
        "pdf": path.name,
        "pdf_pages": 1151,
        "extraction": {
            "structure": "outline du PDF (pymupdf get_toc) ; parties par leur prefixe romain",
            "pages_imprimees": f"page PDF - {offset} (offset cale sur le sommaire imprime)",
            "toc_pdf_pages": [TOC_3E_FIRST + 1, TOC_3E_LAST + 1],
            "offset": offset,
            "entrees_divergentes": divergent,
        },
        "entrees": entries,
    }


def _attach_parts(entries: list[dict]) -> None:
    """Rattache chaque chapitre et section a sa partie (ordre de l'outline)."""
    current = None
    chapter_part = {}
    for e in entries:
        if e["kind"] == "part":
            current = e["num"]
        elif e["kind"] == "chapter":
            chapter_part[e["num"]] = current
            e["part"] = current
    for e in entries:
        if e["kind"] == "section":
            e["part"] = chapter_part.get(e["num"].split(".")[0])


def parse_3e_toc_pages(doc) -> "_Toc3e":
    """Pages imprimees lues dans le sommaire imprime de la 3e edition.

    Le sommaire 3e est compose de lignes de conduite : a gauche le numero
    (partie ou chapitre), au centre le titre, a droite la page imprimee. La
    lecture se fait donc par coordonnees : les mots d'une page sont regroupes
    par bande horizontale (ligne), les points de conduite sont ecartes, et le
    dernier mot de la ligne est la page s'il est numerique.

    Une ligne sans page est un titre de partie (le sommaire n'y imprime pas de
    page) ou un en-tete/pied de page : elle est donc ignoree.
    """
    toc = _Toc3e()
    for i in range(TOC_3E_FIRST, TOC_3E_LAST + 1):
        if i >= doc.page_count:
            break
        for toks in _rows(doc, i):
            toks = [t for t in toks if not _DOTS_ONLY.match(t)]
            if not toks:
                continue
            printed = None
            if toks[-1].isdigit() and len(toks[-1]) <= 4:
                printed = int(toks[-1])
                toks = toks[:-1]
            if printed is None or not toks:
                continue
            label = norm(" ".join(toks))
            if not label or label == "Contents" or label.endswith("Contents"):
                continue
            if _ROMAN_WORD.match(label):
                continue
            m = _NUMBERED.match(label)
            if not m:
                continue
            toc.add(m.group(1), norm(m.group(2)), printed)
    return toc


class _Toc3e:
    """Sommaire 3e indexe par (numero, titre), avec une cle souple.

    La cle souple ignore les separateurs : elle rattrape les titres dont
    l'outline a perdu un espace (l'outline 3e porte "ALogical Formulation of
    Learning" la ou le sommaire imprime "A Logical Formulation of Learning").
    """

    def __init__(self) -> None:
        self._exact: dict[tuple[str, str], list[int]] = {}
        self._loose: dict[tuple[str, str], list[int]] = {}

    @staticmethod
    def _key(num: str, title: str) -> tuple[str, str]:
        return (num, slug(title))

    @staticmethod
    def _loose_key(num: str, title: str) -> tuple[str, str]:
        return (num, re.sub(r"[^a-z0-9]", "", slug(title)))

    def add(self, num: str, title: str, printed: int) -> None:
        self._exact.setdefault(self._key(num, title), []).append(printed)
        self._loose.setdefault(self._loose_key(num, title), []).append(printed)

    def get(self, num: str, title: str, loose: bool = False) -> list[int]:
        out = self._exact.get(self._key(num, title))
        if out is None and loose:
            out = self._loose.get(self._loose_key(num, title))
        return list(out) if out else []

    def __len__(self) -> int:
        return len(self._exact)


# ---------------------------------------------------------------------------
# 4e edition -- structure depuis le sommaire, ancre par le corps
# ---------------------------------------------------------------------------

_4E_SECTION = re.compile(r"^(\d{1,2}(?:\.\d{1,2})*)\.?\s+(.+?)\s+(\d{1,4})$")
_4E_ANNEXE_SECTION = re.compile(r"^([A-Z]\.\d+)\s+(.+?)\s+(\d{1,4})$")
_4E_ANNEXE = re.compile(r"^([A-Z])\s+(.+?)\s+(\d{1,4})$")
_4E_PART = re.compile(r"^([IVXLC]{1,3})\s+(.+)$")
_4E_BACK = re.compile(r"^(Summary|Bibliographical and Historical Notes|Notes|Problems)$")

# Bornes du sommaire 4e (index 0-based) : le sommaire occupe les pages PDF
# 16 a 26 ; la page 27 est la page de titre de la partie I du corps, dont le
# titre ("Part I Artificial Intelligence") ne doit pas etre lu comme une partie
# du sommaire.
TOC_4E_FIRST = 16
TOC_4E_LAST = 26
BODY_4E_FIRST = 27


def extract_4e(pdf_dir: Path) -> dict:
    """Table des matieres de la 4e edition.

    Structure : le sommaire imprime (parties, chapitres, sections avec leur
    page imprimee). Ancre de verification : la page du PDF ou le titre de la
    section est retrouve dans le corps du texte.
    """
    doc, path = _open_pdf(pdf_dir, PDF_4E)

    # 1. Lecture du sommaire (pages PDF 16 a 26).
    raw = []
    for i in range(TOC_4E_FIRST, TOC_4E_LAST + 1):
        if i >= doc.page_count:
            break
        raw.extend((i, l) for l in _page_lines(doc, i))

    entries = []
    for page_pdf, line in raw:
        if _4E_BACK.match(line):
            continue
        m = _4E_SECTION.match(line)
        if m:
            num, title, printed = m.group(1), norm(m.group(2)), int(m.group(3))
            kind = "chapter" if "." not in num else "section"
            entries.append(
                {
                    "kind": kind,
                    "num": num,
                    "title": title,
                    "printed_page": printed,
                    "pdf_page": None,
                    "toc_pdf_page": page_pdf,
                }
            )
            continue
        # Annexes : "A Mathematical Background 1023", "A.1 Complexity ... 1023"
        m = _4E_ANNEXE_SECTION.match(line)
        if m:
            entries.append(
                {
                    "kind": "section",
                    "num": m.group(1),
                    "title": norm(m.group(2)),
                    "printed_page": int(m.group(3)),
                    "pdf_page": None,
                    "toc_pdf_page": page_pdf,
                }
            )
            continue
        m = _4E_ANNEXE.match(line)
        if m:
            entries.append(
                {
                    "kind": "annexe",
                    "num": m.group(1),
                    "title": norm(m.group(2)),
                    "printed_page": int(m.group(3)),
                    "pdf_page": None,
                    "toc_pdf_page": page_pdf,
                }
            )
            continue
        m = _4E_PART.match(line)
        if m and not line.strip().isdigit():
            entries.append(
                {
                    "kind": "part",
                    "num": m.group(1),
                    "title": norm(m.group(2)),
                    "printed_page": None,
                    "pdf_page": None,
                    "toc_pdf_page": page_pdf,
                }
            )

    # 2. Ancre : page du PDF ou chaque section s'ouvre.
    locator = locate_4e_sections(doc, entries)
    for e in entries:
        e["pdf_page"] = locator.get((e["kind"], e["num"], e["title"]))

    # 3. Une partie s'ouvre sur son premier chapitre : elle est ancree sur lui.
    current = None
    first_chapter = {}
    for e in entries:
        if e["kind"] == "part":
            current = e["num"]
        elif e["kind"] == "chapter":
            first_chapter.setdefault(current, e)
    for e in entries:
        if e["kind"] == "part":
            ch = first_chapter.get(e["num"])
            if ch:
                e["pdf_page"] = ch["pdf_page"]
                e["printed_page"] = ch["printed_page"]
                e["premier_chapitre"] = ch["num"]
        elif e["kind"] == "annexe":
            # Une annexe s'ouvre sur sa premiere section.
            sec = next(
                (s for s in entries
                 if s["kind"] == "section" and s["num"].startswith(e["num"] + ".")),
                None,
            )
            if sec and sec["pdf_page"]:
                e["pdf_page"] = sec["pdf_page"]
                e["premiere_section"] = sec["num"]

    doc.close()
    return {
        "edition": "4e",
        "titre": "Artificial Intelligence: A Modern Approach (4th Edition)",
        "auteurs": "Stuart Russell, Peter Norvig",
        "pdf": path.name,
        "pdf_pages": 2579,
        "extraction": {
            "structure": "sommaire imprime du PDF (pages PDF 16 a 26)",
            "pages_imprimees": "lues dans le sommaire",
            "ancre_pdf": "page du corps ou le titre de section est retrouve",
            "toc_pdf_pages": [TOC_4E_FIRST + 1, TOC_4E_LAST + 1],
            "entrees_non_ancrees": [
                {"num": e["num"], "title": e["title"], "printed_page": e["printed_page"]}
                for e in entries
                if e["kind"] != "part" and not e["pdf_page"]
            ],
        },
        "entrees": entries,
    }


def _loose(text: str) -> str:
    """Comparaison de titres insensible aux separateurs et aux apostrophes."""
    s = norm(text).lower()
    s = s.replace("'", "").replace("’", "")
    return re.sub(r"[^a-z0-9]+", "", s)


def locate_4e_sections(doc, entries) -> dict:
    """Retrouve, pour chaque section, la page du PDF qui l'ouvre.

    Dans le corps 4e, une section s'ouvre par une ligne "N.M Titre" placee en
    tete de page, et un chapitre par la ligne "Chapter N" suivie du titre.
    L'ancre d'un chapitre exige la presence des DEUX lignes : sinon le titre
    seul ("Robotics") est retrouve dans une figure ou un encadre bien avant le
    chapitre lui-meme.
    """
    wanted_sections = {}
    wanted_chapters = {}
    for e in entries:
        if e["kind"] == "section":
            wanted_sections.setdefault(_loose(f"{e['num']} {e['title']}"), e)
        elif e["kind"] == "chapter":
            wanted_chapters.setdefault((e["num"], _loose(e["title"])), e)

    found = {}
    total = len(wanted_sections) + len(wanted_chapters)
    for i in range(BODY_4E_FIRST, doc.page_count):
        lines = [norm(l) for l in _page_lines(doc, i)]
        if not lines:
            continue
        # Un titre de section peut etre coupe en deux lignes dans le corps
        # ("4.5 Online Search Agents and Unknown" / "Environments") : les
        # couples de lignes consecutives sont donc candidats aussi.
        candidates = list(lines)
        candidates += [f"{a} {b}" for a, b in zip(lines, lines[1:])]
        for cand in candidates:
            e = wanted_sections.get(_loose(cand))
            if e is not None:
                found.setdefault((e["kind"], e["num"], e["title"]), i + 1)
        chapter_nums = set()
        for l in lines:
            m = re.fullmatch(r"Chapter\s+(\d{1,2})", l)
            if m:
                chapter_nums.add(m.group(1))
        if chapter_nums:
            joined = " ".join(candidates)
            for num in chapter_nums:
                for (cnum, loose), e in wanted_chapters.items():
                    if cnum != num:
                        continue
                    if loose and loose in _loose(joined):
                        found.setdefault((e["kind"], e["num"], e["title"]), i + 1)
        if len(found) == total:
            break
    return found


# ---------------------------------------------------------------------------
# Ecarts entre editions
# ---------------------------------------------------------------------------


def compute_diffs(toc3: dict, toc4: dict) -> dict:
    """Compare les deux editions.

    La comparaison principale porte sur les TITRES : la 4e edition a refait
    sa numerotation (les numeros de section ne sont plus les memes), donc un
    ecart de numero ne prouve rien. La comparaison par numero est quand meme
    produite, sous le nom `*_par_numero` : elle mesure la restructuration.
    """
    ch3 = {e["num"]: e["title"] for e in toc3["entrees"] if e["kind"] == "chapter"}
    ch4 = {e["num"]: e["title"] for e in toc4["entrees"] if e["kind"] == "chapter"}
    s3 = {e["num"]: e["title"] for e in toc3["entrees"] if e["kind"] == "section"}
    s4 = {e["num"]: e["title"] for e in toc4["entrees"] if e["kind"] == "section"}

    t3 = {slug(t): n for n, t in s3.items()}
    t4 = {slug(t): n for n, t in s4.items()}

    out = {
        "criteres": {
            "ajouts_retraits": "comparaison par titre (racine sans separateurs)",
            "renumerotation": "meme titre, numero different",
            "renommage": "meme numero, titre different",
        },
        "sections_ajoutees_4e": [
            {"num": t4[k], "title": s4[t4[k]]} for k in sorted(t4) if k not in t3
        ],
        "sections_retirees_4e": [
            {"num": t3[k], "title": s3[t3[k]]} for k in sorted(t3) if k not in t4
        ],
        "sections_renumerotees": [
            {"3e": t3[k], "4e": t4[k], "titre": s3[t3[k]]}
            for k in sorted(t3)
            if k in t4 and t3[k] != t4[k]
        ],
        "sections_renommees": [
            {"num": n, "3e": s3[n], "4e": s4[n]}
            for n in sorted(s3)
            if n in s4 and slug(s3[n]) != slug(s4[n])
        ],
        "sections_par_numero_ajoutees_4e": [
            {"num": n, "title": t} for n, t in sorted(s4.items()) if n not in s3
        ],
        "sections_par_numero_retirees_4e": [
            {"num": n, "title": t} for n, t in sorted(s3.items()) if n not in s4
        ],
        "chapters_ajoutes_4e": [
            {"num": n, "title": t}
            for k, (n, t) in sorted({slug(t): (n, t) for n, t in ch4.items()}.items())
            if k not in {slug(t) for t in ch3.values()}
        ],
        "chapters_retires_4e": [
            {"num": n, "title": t}
            for k, (n, t) in sorted({slug(t): (n, t) for n, t in ch3.items()}.items())
            if k not in {slug(t) for t in ch4.values()}
        ],
        "chapters_renommes": [
            {"num": n, "3e": ch3[n], "4e": ch4[n]}
            for n in sorted(ch3)
            if n in ch4 and slug(ch3[n]) != slug(ch4[n])
        ],
        "chapters_par_numero_ajoutes_4e": [
            {"num": n, "title": t} for n, t in sorted(ch4.items()) if n not in ch3
        ],
        "chapters_par_numero_retires_4e": [
            {"num": n, "title": t} for n, t in sorted(ch3.items()) if n not in ch4
        ],
    }

    # Parties : titres et bornes (chapitres de la partie).
    for edition, toc in (("3e", toc3), ("4e", toc4)):
        current = None
        bornes: dict[str, dict] = {}
        for e in toc["entrees"]:
            if e["kind"] == "part":
                current = e["num"]
                bornes[e["num"]] = {"num": e["num"], "title": e["title"], "chapitres": []}
            elif e["kind"] == "chapter" and current in bornes:
                bornes[current]["chapitres"].append(e["num"])
        out[f"parties_{edition}"] = [bornes[k] for k in sorted(bornes)]
    return out


# ---------------------------------------------------------------------------
# Couverture du corpus : section -> concepts -> carnets
# ---------------------------------------------------------------------------

CORPUS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"
EXCLUDED_DIRS = ("_archive", ".lake", "node_modules", ".ipynb_checkpoints", ".venv")

# Nombre de carnets cites en exemple par section. La liste complete n'est
# pas commitee : elle se regenere par `coverage` (le compte, lui, est exact).
CARNETS_EXEMPLES = 8

# Mots sans valeur probante pour une correspondance : ils designent la
# structure du livre, pas un theme.
STOPWORDS = {
    "about", "above", "after", "again", "against", "algorithms", "also", "and",
    "any", "are", "because", "been", "before", "being", "below", "between",
    "both", "but", "by", "can", "chapter", "concepts", "could", "does", "doing",
    "down", "during", "each", "equation", "example", "examples", "exercise",
    "exercises", "first", "following", "for", "from", "further", "general",
    "given", "has", "have", "having", "hence", "history", "however", "including",
    "into", "introduction", "its", "itself", "just", "learn", "learning", "less",
    "like", "made", "make", "makes", "many", "may", "more", "most", "must",
    "need", "notes", "often", "only", "other", "others", "over", "part",
    "particular", "parts", "per", "possible", "problems", "provide", "provided",
    "provides", "question", "questions", "section", "sections", "several",
    "shall", "should", "since", "some", "such", "summary", "than", "that", "the",
    "their", "them", "then", "there", "these", "they", "this", "those", "through",
    "thus", "under", "use", "used", "uses", "using", "very", "was", "way", "well",
    "were", "what", "when", "where", "which", "while", "who", "why", "will",
    "with", "within", "without", "would", "your",
    "ainsi", "alors", "avec", "cette", "chapitre", "comme", "comment", "dans",
    "des", "est", "etre", "exemple", "exemples", "faire", "fait", "introduction",
    "la", "le", "les", "leur", "plus", "pour", "quand", "qui", "sans", "section",
    "sont", "sous", "sur", "tous", "tout", "une", "vers",
}


def _stem(word: str) -> str:
    """Rapproche les formes : "learning" et "learn" se rejoignent."""
    w = word.lower()
    if len(w) > 5 and w.endswith("ing"):
        return w[:-3]
    if len(w) > 4 and w.endswith("s") and not w.endswith("ss"):
        return w[:-1]
    if len(w) > 4 and w.endswith("ed"):
        return w[:-2]
    return w


def _tokens(text: str) -> set[str]:
    """Jetons significatifs d'un texte (markdown + code, hors sorties)."""
    words = re.findall(r"[a-zA-ZÀ-ÿ][a-zA-ZÀ-ÿ0-9\-]{2,}", text.lower())
    out = set()
    for w in words:
        w = w.strip("-")
        if len(w) < 4 or w in STOPWORDS:
            continue
        out.add(_stem(w))
    return out


def _notebook_paths(corpus: Path) -> list[Path]:
    out = []
    for path in corpus.rglob("*.ipynb"):
        rel = path.relative_to(corpus).as_posix()
        if any(part in EXCLUDED_DIRS for part in path.parts):
            continue
        out.append(path)
    return sorted(out)


def _notebook_text(path: Path) -> str:
    """Texte utile d'un carnet : markdown et code source, hors sorties."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return ""
    chunks = []
    for cell in nb.get("cells", []):
        source = cell.get("source") or []
        if isinstance(source, str):
            chunks.append(source)
        else:
            chunks.extend(source)
    return "\n".join(chunks)


def _title_terms(titles: list[str]) -> list[str]:
    """Termes candidats d'une section : mots significatifs de son titre."""
    terms = []
    for title in titles:
        for word in re.findall(r"[a-zA-ZÀ-ÿ][a-zA-ZÀ-ÿ0-9\-]{2,}", title.lower()):
            w = word.strip("-")
            if len(w) < 4 or w in STOPWORDS:
                continue
            terms.append(_stem(w))
    seen = []
    for t in terms:
        if t not in seen:
            seen.append(t)
    return seen


def compute_coverage(toc: dict, corpus: Path = CORPUS_ROOT,
                     max_ratio: float = 0.20) -> dict:
    """Rattache chaque section aux carnets du corpus qui l'enseignent.

    Preuve : le terme de la section (racine de son titre) apparait dans le
    carnet -- markdown ou code. Un terme present dans plus de `max_ratio` des
    carnets est ecarte : il ne prouve rien.

    Le corpus lu est le repertoire des carnets ; les sorties de cellules ne
    sont pas lues (elles porteraient le texte du livre recopie, pas
    l'enseignement du depot).
    """
    entries = [e for e in toc["entrees"] if e["kind"] in ("chapter", "section")]
    terms_by_entry = {
        (e["kind"], e["num"]): _title_terms([e["title"]]) for e in entries
    }
    all_terms = sorted({t for ts in terms_by_entry.values() for t in ts})

    paths = _notebook_paths(corpus)
    postings: dict[str, list[int]] = {t: [] for t in all_terms}
    for i, path in enumerate(paths):
        tokens = _tokens(_notebook_text(path))
        for t in all_terms:
            if t in tokens:
                postings[t].append(i)

    total = max(len(paths), 1)
    generic = [t for t in all_terms if len(postings[t]) > max_ratio * total]
    keep = {t for t in all_terms if t not in generic}

    out_entries = []
    for e in entries:
        terms = [t for t in terms_by_entry[(e["kind"], e["num"])] if t in keep]
        hits: dict[int, list[str]] = {}
        for t in terms:
            for i in postings[t]:
                hits.setdefault(i, []).append(t)
        carnets = []
        for i, matched in sorted(hits.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            path = paths[i]
            rel = path.relative_to(corpus).as_posix()
            carnets.append({"chemin": rel, "serie": _serie_of(rel), "termes": sorted(matched)})
        compte_series: dict[str, int] = {}
        for c in carnets:
            compte_series[c["serie"]] = compte_series.get(c["serie"], 0) + 1
        out_entries.append(
            {
                "kind": e["kind"],
                "num": e["num"],
                "title": e["title"],
                "printed_page": e.get("printed_page"),
                "pdf_page": e.get("pdf_page"),
                "termes": terms,
                "couverte": bool(carnets),
                "nb_carnets": len(carnets),
                "series": {s: n for s, n in sorted(compte_series.items(),
                                                 key=lambda kv: (-kv[1], kv[0]))},
                "carnets": [f"{c['chemin']} :: {', '.join(c['termes'])}"
                            for c in carnets[:CARNETS_EXEMPLES]],
            }
        )

    return {
        "edition": toc["edition"],
        "corpus": {
            "racine": corpus.relative_to(REPO_ROOT).as_posix(),
            "carnets": len(paths),
        },
        "criteres": {
            "termes": "racines des mots significatifs du titre de la section",
            "termes_generiques_exclus": len(generic),
            "seuil_generique": max_ratio,
            "preuve": "le terme apparait dans le markdown ou le code du carnet",
            "carnets_exemples_par_section": CARNETS_EXEMPLES,
            "carnets_liste_complete": "regeneree par la commande `coverage`",
        },
        "termes_generiques_exclus": sorted(generic),
        "entrees": out_entries,
        "sections_non_couvertes": [
            {"num": e["num"], "title": e["title"]}
            for e in out_entries
            if e["kind"] == "section" and not e["couverte"]
        ],
        "chapitres_sans_carnet": [
            {"num": e["num"], "title": e["title"]}
            for e in out_entries
            if e["kind"] == "chapter" and not e["couverte"]
        ],
    }



# ---------------------------------------------------------------------------
# Armature : correspondance chapitre -> serie (source : docs/cadrage)
# ---------------------------------------------------------------------------

ARMATURE_DOC = REPO_ROOT / "docs" / "cadrage" / "aima-armature.md"
_ROW = re.compile(r"^\|\s*(?P<chap>[^|]+?)\s*\|\s*(?P<titre>[^|]+?)\s*\|\s*(?P<series>[^|]*?)\s*\|")


def parse_armature(path: Path = ARMATURE_DOC) -> dict:
    """Lit la table chapitre/serie de l'armature AIMA deja publiee.

    La colonne "Serie porteuse" contient des chemins de series entre
    accents graves, separes par des points median. Ce sont eux qui disent
    quelle serie du depot execute quel chapitre.
    """
    out: dict[str, dict] = {}
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        m = _ROW.match(line)
        if not m:
            continue
        chap = m.group("chap").strip()
        if not re.fullmatch(r"(?:App\. )?[A-Z]|\d+", chap):
            continue
        series = re.findall(r"`([^`]+)`", m.group("series"))
        out[chap] = {
            "titre": m.group("titre").strip(),
            "series": [s for s in series if "/" in s or s.isidentifier()],
        }
    return out


# ---------------------------------------------------------------------------
# Ecriture
# ---------------------------------------------------------------------------


def _compact_dump(payload) -> str:
    """JSON lisible : un element de liste par ligne, le reste en ligne.

    Un JSON indenté de 2 espaces sur ce corpus fait plus de 100 000 lignes :
    la version compacte tient le diff lisible sans l'écrasement.
    """
    def enc(o):
        if isinstance(o, dict):
            body = ", ".join(
                f"{json.dumps(k, ensure_ascii=False)}: {enc(v)}" for k, v in o.items()
            )
            return "{" + body + "}"
        if isinstance(o, list):
            if not o:
                return "[]"
            if all(isinstance(x, (dict, list)) for x in o):
                return "[\n" + ",\n".join("  " + enc(x) for x in o) + "\n]"
            return "[" + ", ".join(enc(x) for x in o) + "]"
        return json.dumps(o, ensure_ascii=False)

    return enc(payload)


def write_json(out_dir: Path, name: str, payload: dict) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / name
    path.write_text(_compact_dump(payload) + "\n", encoding="utf-8")
    return path


def _serie_of(rel: str) -> str:
    """Serie d'un carnet : ses deux premiers niveaux de repertoire."""
    dirs = Path(rel).parts[:-1]
    if not dirs:
        return "(racine)"
    return "/".join(dirs[:2]) if len(dirs) > 1 else dirs[0]


def corpus_series(corpus: Path = CORPUS_ROOT) -> dict[str, int]:
    """Nombre de carnets par serie (deux premiers niveaux de repertoire)."""
    out: dict[str, int] = {}
    for path in _notebook_paths(corpus):
        rel = path.relative_to(corpus).as_posix()
        serie = _serie_of(rel)
        out[serie] = out.get(serie, 0) + 1
    return dict(sorted(out.items()))


def _referenced(serie: str, references: list[str]) -> bool:
    """Une serie est-elle couverte par une serie referencee par l'armature ?"""
    for ref in references:
        if serie == ref or serie.startswith(ref + "/") or ref.startswith(serie + "/"):
            return True
    return False


def write_rapport(out_dir: Path, corpus: Path = CORPUS_ROOT) -> Path:
    """Ecrit le document de correspondance (markdown) et ses annexes.

    Le document est genere : chaque chiffre vient des JSON de l'etape
    `coverage`/`diff`, chaque nom de serie de l'armature publiee.
    """
    toc3 = json.loads((out_dir / "aima3e-toc.json").read_text(encoding="utf-8"))
    toc4 = json.loads((out_dir / "aima4e-toc.json").read_text(encoding="utf-8"))
    cov4 = json.loads((out_dir / "couverture-4e.json").read_text(encoding="utf-8"))
    diffs = json.loads((out_dir / "ecarts-3e-4e.json").read_text(encoding="utf-8"))
    armature = parse_armature()
    references = sorted({s for chap in armature.values() for s in chap["series"]})
    series = corpus_series(corpus)
    hors_carte = {s: n for s, n in series.items() if not _referenced(s, references)}

    def counts(toc):
        c = {}
        for e in toc["entrees"]:
            c[e["kind"]] = c.get(e["kind"], 0) + 1
        return c

    c3, c4 = counts(toc3), counts(toc4)
    ancrees3 = sum(1 for e in toc3["entrees"] if e["kind"] != "part" and e["pdf_page"])
    ancrees4 = sum(1 for e in toc4["entrees"] if e["kind"] != "part" and e["pdf_page"])

    L: list[str] = []
    L.append("# AIMA : des tables des matieres aux carnets du dépôt")
    L.append("")
    L.append("> Données : les deux éditions d'*Artificial Intelligence: A Modern Approach*")
    L.append("> (Russell & Norvig), lues dans les copies archivées du gisement")
    L.append("> (`G:\\Mon Drive\\MyIA\\IA\\Bibliographie IA\\AI`) ; les PDF ne sont jamais committés.")
    L.append("> Ce document est **généré** par `scripts/research/aima_mapping.py`.")
    L.append("")
    L.append("## Ce que contient ce dossier")
    L.append("")
    L.append("| Fichier | Contenu |")
    L.append("|---|---|")
    L.append("| `aima3e-toc.json` | table des matières de la 3e édition (parties, chapitres, sections, page imprimée, page PDF) |")
    L.append("| `aima4e-toc.json` | idem pour la 4e édition |")
    L.append("| `ecarts-3e-4e.json` | ce qui est ajouté, retiré, renommé ou renuméroté entre les deux éditions |")
    L.append("| `couverture-3e.json` · `couverture-4e.json` | section → concepts → carnets du dépôt, avec la preuve (terme trouvé) |")
    L.append("")
    L.append("## 1. Méthode — quatre étapes reproductibles")
    L.append("")
    L.append("```bash")
    L.append("python scripts/research/aima_mapping.py extract   # les deux tables des matières")
    L.append("python scripts/research/aima_mapping.py diff      # les écarts 3e → 4e")
    L.append("python scripts/research/aima_mapping.py coverage  # la correspondance avec les carnets")
    L.append("python scripts/research/aima_mapping.py rapport   # ce document")
    L.append("```")
    L.append("")
    L.append("**3e édition** — la structure vient de l'outline du PDF (niveaux 1/2/3 = partie/chapitre/section). "
             "La page imprimée est lue dans le sommaire imprimé, ligne par ligne et par coordonnées : "
             "à gauche le numéro, au centre le titre, à droite la page. L’offset du corps "
             "(page PDF − page imprimée) est ensuite appliqué à toutes les entrées et vérifié une à une.")
    L.append("")
    L.append("**4e édition** — la structure et la page imprimée sont lues dans le sommaire imprimé "
             "(pages PDF 16 à 26). L’ancre de vérification est la page du corps où le titre de la section "
             "s’ouvre : une section par sa ligne « N.M Titre », un chapitre par la ligne « Chapter N » "
             "suivie de son titre. Les titres coupés sur deux lignes dans le corps sont reconstruits.")
    L.append("")
    L.append("**Correspondance** — les termes d’une section sont les racines des mots significatifs de son titre. "
             "Un carnet « couvre » une section si l’un de ces termes apparaît dans son markdown ou son code "
             f"(les sorties de cellules ne sont pas lues). Un terme présent dans plus de "
             f"{int(cov4['criteres']['seuil_generique'] * 100)} % des carnets est écarté : il ne prouve rien "
             f"({len(cov4['termes_generiques_exclus'])} termes écartés). "
             f"Les JSON de couverture citent {CARNETS_EXEMPLES} carnets d’exemple par section et la liste de "
             "ses séries ; la liste complète se régénère par la commande `coverage`.")
    L.append("")
    L.append("## 2. Les deux éditions en données")
    L.append("")
    L.append("| | 3e édition | 4e édition |")
    L.append("|---|---:|---:|")
    for kind, label in (("part", "parties"), ("chapter", "chapitres"), ("section", "sections"), ("annexe", "annexes")):
        L.append(f"| {label} | {c3.get(kind, 0)} | {c4.get(kind, 0)} |")
    L.append(f"| entrées ancrées sur une page PDF | {ancrees3} | {ancrees4} |")
    L.append("")
    L.append(f"Offset du corps 3e : **{toc3['extraction'].get('offset')}** "
             f"(page PDF − offset = page imprimée). "
             f"Entrées divergentes : {len(toc3['extraction'].get('entrees_divergentes', []))}.")
    L.append("")
    L.append("Écart avec l’[armature AIMA](../../cadrage/aima-armature.md) : sa prose annonce « 27 chapitres "
             f"en 7 parties », la table des matières en compte **{c4.get('chapter', 0)}** (son propre tableau en "
             "liste 28). L’écart est dans la prose de l’armature, pas dans sa carte ; ce document ne la modifie pas.")
    L.append("")
    L.append("## 3. Ce qui change de la 3e à la 4e édition")
    L.append("")
    L.append(f"- chapitres ajoutés : **{len(diffs['chapters_ajoutes_4e'])}** ; "
             f"retirés : **{len(diffs['chapters_retires_4e'])}** ; "
             f"renommés : **{len(diffs['chapters_renommes'])}**")
    L.append(f"- sections ajoutées : **{len(diffs['sections_ajoutees_4e'])}** ; "
             f"retirées : **{len(diffs['sections_retirees_4e'])}** ; "
             f"renommées : **{len(diffs['sections_renommees'])}** ; "
             f"renumérotées : **{len(diffs['sections_renumerotees'])}**")
    L.append("")
    L.append("La comparaison porte sur les **titres**, pas sur les numéros : la 4e édition a refait sa "
             "numérotation, donc un écart de numéro ne prouve rien. Les chapitres présents en 4e et "
             f"absents de la 3e ({len(diffs['chapters_ajoutes_4e'])}) :")
    L.append("")
    for c in diffs["chapters_ajoutes_4e"]:
        L.append(f"- **{c['num']} — {c['title']}**")
    L.append("")
    L.append(f"Les chapitres de la 3e édition absents de la 4e ({len(diffs['chapters_retires_4e'])}) :")
    L.append("")
    for c in diffs["chapters_retires_4e"]:
        L.append(f"- **{c['num']} — {c['title']}**")
    L.append("")
    L.append("## 4. Correspondance 4e édition → carnets")
    L.append("")
    L.append("La colonne « série » est celle de l’[armature AIMA](../../cadrage/aima-armature.md) "
             "(l’organe qui exécute) ; la colonne « sections couvertes » vient de la recherche dans le corpus "
             "(le contenu qui enseigne).")
    L.append("")
    L.append("| Chap. | Titre (4e) | Série porteuse | Sections | Couvertes | Séries couvertes (3 premières, par nombre de carnets) |")
    L.append("|---|---|---|---:|---:|---|")
    for e in cov4["entrees"]:
        if e["kind"] != "chapter":
            continue
        chap = armature.get(e["num"])
        serie = ", ".join(f"`{s}`" for s in (chap["series"] if chap else [])) or "—"
        sections = [s for s in cov4["entrees"]
                    if s["kind"] == "section" and s["num"].startswith(e["num"] + ".")]
        covered = sum(1 for s in sections if s["couverte"])
        compte: dict[str, int] = {}
        for s in sections + [e]:
            for serie_couverte, n in s.get("series", {}).items():
                compte[serie_couverte] = compte.get(serie_couverte, 0) + n
        top = [k for k, _v in sorted(compte.items(), key=lambda kv: (-kv[1], kv[0]))[:3]]
        L.append(f"| {e['num']} | {e['title']} | {serie} | {len(sections)} | {covered} | "
                 f"{', '.join('`' + t + '`' for t in top) or '—'} |")
    L.append("")
    L.append("## 5. Sections non couvertes")
    L.append("")
    non_couv = cov4["sections_non_couvertes"]
    L.append(f"{len(non_couv)} sections de la 4e édition n’ont **aucun** carnet dont le markdown ou le code "
             "porte un terme de leur titre. La liste complète est dans `couverture-4e.json` ; voici les "
             "chapitres concernés :")
    L.append("")
    L.append("| Chap. | Sections non couvertes |")
    L.append("|---|---|")
    for e in cov4["entrees"]:
        if e["kind"] != "chapter":
            continue
        miss = [s["num"] for s in non_couv if s["num"].startswith(e["num"] + ".")]
        if miss:
            L.append(f"| {e['num']} | {len(miss)} — {', '.join(miss[:8])}{' …' if len(miss) > 8 else ''} |")
    L.append("")
    L.append("## 6. Au-delà du livre")
    L.append("")
    L.append(f"Le dépôt exécute des séries qu’aucun chapitre de l’AIMA ne réclame : "
             f"**{len(hors_carte)} séries** hors de la carte de l’armature, "
             f"{sum(hors_carte.values())} carnets au total.")
    L.append("")
    L.append("| Série (hors carte) | Carnets |")
    L.append("|---|---:|")
    for s, n in sorted(hors_carte.items(), key=lambda kv: (-kv[1], kv[0])):
        L.append(f"| `{s}` | {n} |")
    L.append("")
    L.append("## 7. Chapitres sans organe ou à couverture partielle")
    L.append("")
    L.append("Deux mesures distinctes, à ne pas confondre : l’**organe** (la bibliothèque ou le moteur que "
             "la série appelle) et le **contenu** (un carnet dont le texte porte un terme de la section). "
             "Un chapitre peut avoir l’un sans l’autre.")
    L.append("")
    L.append("| Chapitre | Organe (armature) | Sections couvertes |")
    L.append("|---|---|---:|")
    for e in cov4["entrees"]:
        if e["kind"] != "chapter":
            continue
        chap = armature.get(e["num"])
        organe = ", ".join(f"`{s}`" for s in (chap["series"] if chap else [])) or "— aucun —"
        sections = [s for s in cov4["entrees"]
                    if s["kind"] == "section" and s["num"].startswith(e["num"] + ".")]
        covered = sum(1 for s in sections if s["couverte"])
        if not chap or not chap["series"] or covered < len(sections):
            L.append(f"| {e['num']} — {e['title']} | {organe} | {covered}/{len(sections)} |")
    L.append("")
    L.append("---")
    L.append("")
    L.append("Reproduction : `python scripts/research/aima_mapping.py extract && "
             "python scripts/research/aima_mapping.py diff && "
             "python scripts/research/aima_mapping.py coverage && "
             "python scripts/research/aima_mapping.py rapport`.")
    L.append("")

    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / "README.md"
    path.write_text("\n".join(L), encoding="utf-8")
    return path


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("etape", choices=["extract", "diff", "coverage", "rapport"])
    ap.add_argument("--pdf-dir", type=Path, default=DEFAULT_PDF_DIR)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--corpus", type=Path, default=CORPUS_ROOT)
    args = ap.parse_args(argv)

    if args.etape == "extract":
        toc3 = extract_3e(args.pdf_dir)
        toc4 = extract_4e(args.pdf_dir)
        p3 = write_json(args.out, "aima3e-toc.json", toc3)
        p4 = write_json(args.out, "aima4e-toc.json", toc4)
        n3 = len(toc3["entrees"])
        n4 = len(toc4["entrees"])
        anchored4 = sum(1 for e in toc4["entrees"] if e["pdf_page"])
        print(f"3e : {n3} entrees -> {p3}")
        print(f"4e : {n4} entrees ({anchored4} ancrees par une page PDF) -> {p4}")
        return 0

    if args.etape == "diff":
        toc3 = json.loads((args.out / "aima3e-toc.json").read_text(encoding="utf-8"))
        toc4 = json.loads((args.out / "aima4e-toc.json").read_text(encoding="utf-8"))
        diffs = compute_diffs(toc3, toc4)
        path = write_json(args.out, "ecarts-3e-4e.json", diffs)
        print(f"ecarts -> {path}")
        for k, v in diffs.items():
            if isinstance(v, list):
                print(f"  {k}: {len(v)}")
        return 0

    if args.etape == "coverage":
        for edition, name in (("3e", "aima3e-toc.json"), ("4e", "aima4e-toc.json")):
            toc = json.loads((args.out / name).read_text(encoding="utf-8"))
            cov = compute_coverage(toc, corpus=args.corpus)
            path = write_json(args.out, f"couverture-{edition}.json", cov)
            print(f"{edition} : {len(cov['entrees'])} entrees, "
                  f"{len(cov['sections_non_couvertes'])} sections non couvertes -> {path}")
        return 0

    if args.etape == "rapport":
        path = write_rapport(args.out, corpus=args.corpus)
        print(f"rapport -> {path}")
        return 0

    print("coverage : etape non implementee dans cette version", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
