"""Cartographie du cursus CoursIA sur les tables des matieres d'AIMA (3e et 4e edition).

Grain #24997 (EPIC #24993). Trois livrables, tous reproductibles :

1. `toc`  : extrait les deux tables des matieres des PDF archives dans le gisement
   bibliographique et ecrit deux CSV dont chaque ligne est verifiable contre une page
   du PDF (colonne `pdf_page`).
2. `map`  : croise ces tables avec le parcours pilote (`docs/curriculum/aima-walk.md`)
   et sa cartographie de competences (`docs/curriculum/aima-walk-competences.md`) pour
   produire la correspondance section -> phase -> carnets -> competences, la liste des
   sections sans couverture, les ecarts entre editions, et le contenu qui depasse le
   livre.
3. `check`: controle la coherence interne des CSV produits (les lignes de TOC
   conservent leur marque de verification, et chaque ligne de couverture renvoie
   a une section presente dans la table) ; ne rouvre pas les PDF, dont la
   re-verification des ancres est le role de `toc` (garde anti-drift).

Regles appliquees :
- les PDF ne sont jamais copies dans le depot ; seule l'ancre (numero de page) sort ;
- les competences viennent de la source unique `aima-walk-competences.md` (regle de
  projection exacte : le tableau est lu, pas recalcule) ;
- rien n'est invente : une correspondance impossible est declaree, pas comblee.

Usage :
  python scripts/research/aima_mapping.py toc  --out-dir docs/curriculum/aima-mapping
  python scripts/research/aima_mapping.py map  --out-dir docs/curriculum/aima-mapping
  python scripts/research/aima_mapping.py check --out-dir docs/curriculum/aima-mapping
"""

from __future__ import annotations

import argparse
import csv
import difflib
import json
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

DEFAULT_BIB_DIR = Path(r"G:\Mon Drive\MyIA\IA\Bibliographie IA\AI")
PDF_3E = "2010 - Russell Norvig - Artificial Intelligence - A Modern Approach (3rd Edition).pdf"
PDF_4E = "2021 - Russell Norvig - Artificial Intelligence - A Modern Approach (4th Edition).pdf"

WALK_MD = "docs/curriculum/aima-walk.md"
COMPETENCES_MD = "docs/curriculum/aima-walk-competences.md"

RE_CHAPTER = re.compile(r"^(\d+(?:\.\d+)*)\s+(\S.*?)\s+(\d+)$")
RE_PART = re.compile(r"^([IVX]+)\s+(\S.*)$")
RE_APPENDIX_SECTION = re.compile(r"^([A-Z]\.\d+)\s+(\S.*?)\s+(\d+)$")
RE_APPENDIX = re.compile(r"^([A-Z])(?:\s+(\S.*?)\s+(\d+))?$")
RE_FRONT = re.compile(r"^(Summary|Bibliographical and Historical Notes|References|Index)\b")
RE_BACKMATTER = re.compile(r"^(Summary|Bibliographical and Historical Notes)\s+(\d+)$")
RE_INDEX_ENTRY = re.compile(r"^[A-Z]$")
RE_PHASE = re.compile(r"^###\s+(Phase\s+(\d+)|Épilogue)\b")
RE_AIMA_REF = re.compile(r"\(AIMA\s+ch\.\s*([^)]*)\)")
RE_STEP = re.compile(r"^(\d+)\.\s")
RE_LINK = re.compile(r"\[`?([^\]`]+)`?\]\(([^)]+)\)")
RE_COMP_ROW = re.compile(r"^\|\s*(\d+)\s*\(([^)]*)\)\s*\|")

FRONT_MATTER = {
    "Cover", "Title Page", "Copyright", "Contents", "Preface", "Foreword",
    "Acknowledgments", "Index", "Exercises", "Bibliography",
}

STOPWORDS = {"and", "or", "the", "of", "in", "a", "to", "for", "notes", "exercises",
             "summary", "bibliographical", "historical"}

# marqueurs que le parcours pose lui-meme sur ce qui depasse le livre
BEYOND_MARKERS = ("au-delà d'AIMA", "au-dela d'AIMA", "hors AIMA", "propre au dépôt")

# marqueurs d'une REREADURE : le passage reste rattache a un chapitre du livre,
# mais il est relu par le depot dans ses termes modernes. Ce n'est pas un
# depassement du livre ; c'est une adaptation. La distinction est portee par la
# nature du marqueur, parce que la question « qu'est-ce qui depasse le livre »
# ne se confond pas avec « qu'est-ce qui a ete relu ».
JONCTION_MARKERS = ("ce qu'AIMA appelait", "la jonction moderne")


def _norm(text: str) -> str:
    out = text.replace("\ufb01", "fi").replace("\ufb02", "fl")
    out = out.replace("\u2019", "'").replace("\u2018", "'")
    out = out.replace("\u2013", "-").replace("\u2014", "-").replace("\x00", " ")
    return re.sub(r"\s+", " ", out).strip().lower()


def _tokens(text: str) -> list[str]:
    return [t for t in re.findall(r"[a-z0-9']+", _norm(text)) if len(t) > 2 and t not in STOPWORDS]


def _title_on_page(page_text: str, title: str, number: str = "") -> bool:
    hay = _norm(page_text)
    needle = _norm(title)
    if needle and needle in hay:
        return True
    if needle and needle.replace(" ", "") in hay.replace(" ", ""):
        return True
    toks = _tokens(title)
    if toks:
        return all(tok in hay for tok in toks)
    first_word = re.sub(r"[^a-z0-9 ]", "", _norm(title).split(" ")[0])
    if not first_word:
        return False
    if number and number in hay:
        return first_word in hay
    return first_word in hay


# --------------------------------------------------------------------------- TOC

def _require_pymupdf() -> None:
    """Charge PyMuPDF uniquement pour les commandes qui lisent les PDF."""
    global pymupdf
    try:
        import pymupdf
    except ImportError as exc:  # dependance requise par `toc`, pas par `map` ou `check`
        sys.stderr.write(
            "pymupdf absent : installez-le avec `pip install pymupdf` pour la commande toc\n"
        )
        raise SystemExit(1) from exc


@dataclass
class Entry:
    kind: str
    number: str
    title: str
    printed_page: str = ""
    pdf_page: str = ""
    verified: bool = False
    chapter: str = ""
    notes: list = field(default_factory=list)


def extract_3e(pdf_path: Path) -> list[Entry]:
    _require_pymupdf()
    doc = pymupdf.open(pdf_path)
    try:
        entries: list[Entry] = []
        current_chapter = ""
        for level, title, page in doc.get_toc():
            title = re.sub(r"\s+", " ", title.replace("\x00", " ")).strip()
            if not title or title in FRONT_MATTER:
                continue
            if level == 1 and RE_INDEX_ENTRY.match(title):
                continue
            m = re.match(r"^(\d+(?:\.\d+)*)\s+(.*)$", title)
            if m:
                number, rest = m.group(1), m.group(2)
                kind = "chapter" if "." not in number else "section"
                if kind == "section" and rest.startswith("Summary, Bibliographical"):
                    # la 3e agrege en une seule section de fin de chapitre le
                    # sommaire, les notes et les exercices ; la 4e les liste a part.
                    kind = "backmatter"
                if kind == "chapter":
                    current_chapter = number
                entries.append(Entry(kind=kind, number=number, title=rest,
                                     pdf_page=str(page), chapter=current_chapter))
            elif re.match(r"^[IVX]+:", title):
                entries.append(Entry(kind="part", number=title.split(":")[0].strip(),
                                     title=title.split(":", 1)[1].strip(), pdf_page=str(page)))
        return entries
    finally:
        doc.close()


def _find_part_in_printed_toc(doc, entry) -> int:
    """Page PDF (1-based) de la table des matieres imprimee qui porte l'intitule
    de partie : le numero romain y est seul sur sa ligne, l'intitule juste
    dessous. C'est la seule occurrence du texte de l'intitule dans le livre.
    """
    needle = _norm(entry.title)
    roman = entry.number.strip().upper()
    for index in range(8, 40):
        if index >= doc.page_count:
            break
        text = doc[index].get_text()
        if "Contents" not in text:
            continue
        lines = [l.strip() for l in text.splitlines() if l.strip()]
        for pos, line in enumerate(lines):
            if line.upper() != roman:
                continue
            for follow in lines[pos + 1:]:
                if follow.upper() == roman:
                    break
                if _norm(follow) == needle:
                    return index + 1
                break
    return 0


def verify_3e(pdf_path: Path, entries: list[Entry]) -> None:
    _require_pymupdf()
    doc = pymupdf.open(pdf_path)
    try:
        for e in entries:
            if not e.pdf_page:
                e.notes.append("pas d'ancre")
                continue
            page = int(e.pdf_page)
            if not 1 <= page <= doc.page_count:
                e.notes.append("page PDF hors document")
                continue
            if e.kind == "part":
                # La 3e ne porte pas d'intitule de partie sur une page de garde :
                # l'intitule figure dans la table des matieres imprimee, ou le
                # numero romain est seul sur sa ligne. On y ancre donc la ligne,
                # et on conserve la page de depart de la partie (celle du
                # premier chapitre) comme information de parcours.
                toc_page = _find_part_in_printed_toc(doc, e)
                if toc_page:
                    e.pdf_page = str(toc_page)
                    e.verified = True
                    e.notes.append(
                        f"intitule verifie dans la table des matieres imprimee ; "
                        f"la partie commence a la page PDF {page}")
                else:
                    e.notes.append("intitule de partie non retrouve dans la table des "
                                   "matieres imprimee ; l'ancre est la premiere page "
                                   "de la partie (premier chapitre)")
                continue
            text = doc[page - 1].get_text()
            e.verified = _title_on_page(text, e.title, e.number)
            if not e.verified:
                spaced = re.sub(r"(?<=[A-Z])(?=[a-z])", " ", e.title)
                if spaced != e.title and _title_on_page(text, spaced, e.number):
                    e.title = spaced
                    e.verified = True
                    e.notes.append("espace insere (collage du signet PDF)")
            if not e.verified:
                e.notes.append("titre non retrouve sur la page de l'outline")
    finally:
        doc.close()


def parse_4e_toc(pdf_path: Path) -> list[Entry]:
    _require_pymupdf()
    doc = pymupdf.open(pdf_path)
    try:
        lines: list[str] = []
        for i in range(16, 27):
            for raw in doc[i].get_text().splitlines():
                line = raw.strip()
                if line:
                    lines.append(line)
        entries: list[Entry] = []
        current_chapter = ""
        for line in lines:
            if RE_FRONT.match(line):
                m = RE_BACKMATTER.match(line)
                if m:
                    entries.append(Entry(kind="backmatter", number="",
                                         title=m.group(1), printed_page=m.group(2)))
                continue
            m = RE_CHAPTER.match(line)
            if m:
                number, title, page = m.group(1), m.group(2), m.group(3)
                kind = "chapter" if "." not in number else "section"
                if kind == "chapter":
                    current_chapter = number
                entries.append(Entry(kind=kind, number=number, title=title,
                                     printed_page=page, chapter=current_chapter))
                continue
            m = RE_APPENDIX_SECTION.match(line)
            if m:
                entries.append(Entry(kind="appendix_section", number=m.group(1),
                                     title=m.group(2), printed_page=m.group(3)))
                continue
            m = RE_APPENDIX.match(line)
            if m:
                entries.append(Entry(kind="appendix", number=m.group(1),
                                     title=(m.group(2) or "").strip(),
                                     printed_page=m.group(3) or ""))
                continue
            m = RE_PART.match(line)
            if m:
                entries.append(Entry(kind="part", number=m.group(1), title=m.group(2).strip()))
        return entries
    finally:
        doc.close()


def _match_forms(entry: Entry) -> set[str]:
    title = _norm(entry.title)
    number = _norm(entry.number)
    forms = {title}
    if number:
        forms.add(f"{number} {title}")
    if entry.kind == "part":
        forms.add(f"part {number} {title}")
    return forms


def anchor_4e(pdf_path: Path, entries: list[Entry]) -> None:
    """Ancre chaque entree sur sa page PDF par un balayage sequentiel du corps.

    L'ordre de la table des matieres est l'ordre du livre : les entrees sont donc
    avancees dans l'ordre, page par page, ce qui rend l'ancre non ambigue. Un repli
    « souple » (titre present dans le texte sans ligne isolee) est note comme tel.
    """
    _require_pymupdf()
    doc = pymupdf.open(pdf_path)
    try:
        cursor = 0
        pending = list(entries)
        for i in range(26, doc.page_count):
            text = doc[i].get_text()
            lines = {_norm(l) for l in text.splitlines() if l.strip()}
            hay = _norm(text)
            progressed = True
            while progressed and cursor < len(pending):
                progressed = False
                entry = pending[cursor]
                if _match_forms(entry) & lines:
                    entry.pdf_page = str(i + 1)
                    entry.verified = True
                    cursor += 1
                    progressed = True
                    continue
                needle = _norm(entry.title)
                if len(_tokens(entry.title)) >= 2 and needle and needle in hay:
                    entry.pdf_page = str(i + 1)
                    entry.verified = True
                    entry.notes.append("ancre souple (titre non isole en ligne)")
                    cursor += 1
                    progressed = True
        for entry in pending[cursor:]:
            entry.notes.append("non ancre dans le corps")
    finally:
        doc.close()


def verify_4e(pdf_path: Path, entries: list[Entry]) -> None:
    _require_pymupdf()
    doc = pymupdf.open(pdf_path)
    try:
        for e in entries:
            if not e.pdf_page:
                e.notes.append("pas d'ancre")
                continue
            page = int(e.pdf_page)
            if not 1 <= page <= doc.page_count:
                e.notes.append("page PDF hors document")
                continue
            if _title_on_page(doc[page - 1].get_text(), e.title):
                e.verified = True
            else:
                e.verified = False
                e.notes.append("titre non retrouve sur la page ancree")
    finally:
        doc.close()


TOC_FIELDS = ["edition", "kind", "number", "title", "printed_page", "pdf_page", "verified", "notes"]


def _rows_of(edition: str, entries: list[Entry]) -> list[dict]:
    return [{
        "edition": edition,
        "kind": e.kind,
        "number": e.number,
        "title": e.title,
        "printed_page": e.printed_page,
        "pdf_page": e.pdf_page,
        "verified": "oui" if e.verified else "non",
        "notes": "; ".join(e.notes),
    } for e in entries]


def _write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


# ----------------------------------------------------------------- sources du parcours

@dataclass
class Step:
    number: int
    phase: str
    notebooks: list[str]
    text: str
    competences: list[str] = field(default_factory=list)
    hors_livre: str = ""   # extrait du texte qui marque ce qui depasse le livre
    jonction: str = ""    # extrait du texte qui marque une relecture moderne



@dataclass
class Phase:
    label: str          # "Phase 3" ou "Épilogue"
    number: str         # "3" ou ""
    title: str
    aima_ref: str       # texte brut de la reference AIMA, "" si absente
    chapters: list[str] # numeros de chapitres cites (numerotation de l'edition de reference)
    beyond: str         # part de la reference qui sort du livre
    steps: list[Step] = field(default_factory=list)


def _notebooks_in(text: str) -> list[str]:
    found = []
    for label, target in RE_LINK.findall(text):
        if label.endswith(".ipynb") or target.rstrip("/").endswith(".ipynb") or "/" in label:
            found.append(label)
    return found


def _hors_livre_in(text: str) -> str:
    """Extrait de l'etape ce qui depasse le livre : le parcours le marque lui-meme
    (« hors AIMA », « au-dela d'AIMA », « propre au depot »).

    Le marqueur peut etre coupe par un retour a la ligne (le parcours replie ses
    lignes), la recherche se fait donc sur le texte plat, et l'extrait rendu est
    la phrase qui porte le marqueur.
    """
    return _extract_marker(text, BEYOND_MARKERS)


def _jonction_in(text: str) -> str:
    """Extrait de l'etape ce que le parcours a RELU dans ses termes modernes."""
    return _extract_marker(text, JONCTION_MARKERS)


def _extract_marker(text: str, markers) -> str:
    plat = re.sub(r"\s+", " ", text).strip()
    for marker in markers:
        pos = plat.find(marker)
        if pos < 0:
            continue
        start = plat.rfind(" — ", 0, pos)
        start = start + 3 if start >= 0 else max(0, pos - 60)
        return plat[start:_sentence_end(plat, pos)].strip(" ,;")
    return ""


ABREVIATIONS = {"ch", "chap", "cf", "n", "no", "fig", "p"}


def _sentence_end(plat: str, pos: int) -> int:
    """Index de la fin de la phrase qui porte le marqueur. Un point suivi d'un
    espace ne clot pas la phrase si le mot qui le precede est une abreviation
    (« AIMA ch. 16 »)."""
    cursor = pos
    while True:
        found = plat.find(". ", cursor)
        if found < 0:
            return len(plat)
        word = re.search(r"([A-Za-zÀ-ÿ]+)\.$", plat[:found + 1])
        if word and word.group(1).lower() in ABREVIATIONS:
            cursor = found + 2
            continue
        return found + 1


def parse_walk(path: Path) -> list[Phase]:
    """Lit le parcours pilote et en extrait phases, references AIMA et etapes."""
    phases: list[Phase] = []
    current: Phase | None = None
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        m = RE_PHASE.match(line)
        if m:
            label = m.group(1).strip()
            number = m.group(2) or ""
            body = line.split("—", 1)[1].strip() if "—" in line else ""
            title = body
            ref = ""
            rm = RE_AIMA_REF.search(body)
            if rm:
                ref = rm.group(1).strip()
                title = (body[:rm.start()] + body[rm.end():]).strip(" —,")
            chapters = re.findall(r"\d+", ref)
            beyond = re.sub(r"\d+[\s\-–]?", "", ref).strip(" ,+")
            current = Phase(label=label, number=number, title=title, aima_ref=ref,
                            chapters=chapters, beyond=beyond)
            phases.append(current)
            continue
        if current is None:
            continue
        sm = RE_STEP.match(line)
        if sm:
            number = int(sm.group(1))
            body = [lines[i]]
            for follow in lines[i + 1:]:
                if RE_STEP.match(follow) or RE_PHASE.match(follow):
                    break
                body.append(follow)
            text = "\n".join(body)
            current.steps.append(Step(number=number, phase=current.label,
                                       notebooks=_notebooks_in(text), text=text,
                                       hors_livre=_hors_livre_in(text),
                                       jonction=_jonction_in(text)))
    return phases



def parse_competences(path: Path) -> dict[int, dict]:
    """Lit la table de cartographie des competences (source unique des codes)."""
    out: dict[int, dict] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = RE_COMP_ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        step = int(m.group(1))
        phase = m.group(2)
        codes = [c.strip() for c in cells[2].split(",") if c.strip()]
        out[step] = {"phase": phase, "notebooks": cells[1], "competences": codes}
    return out


def match_chapters(correspondance: list[dict], toc_3e: list[dict],
                   toc_4e: list[dict]) -> dict[str, dict]:
    """Apparie les chapitres des deux editions par les sections communes.

    L'appariement n'utilise **pas** la memoire ni une similitude de titres : il se
    compte. Pour chaque chapitre de la 4e, on regarde quel chapitre de la 3e porte le
    plus de sections de meme titre ; l'appariement est retenu s'il est supported par au
    moins deux sections communes et par une part suficiente des sections du chapitre.
    Un chapitre sans pendant reste non apparie : l'ecart est declare, pas comble.
    """
    sections_4e_par_chapitre: dict[str, int] = {}
    for row in toc_4e:
        if row["kind"] == "section":
            chapitre = _chapter_of(row)
            sections_4e_par_chapitre[chapitre] = sections_4e_par_chapitre.get(chapitre, 0) + 1

    votes: dict[str, dict[str, int]] = {}
    for row in correspondance:
        if row["statut"] not in ("commun", "renomme"):
            continue
        votes.setdefault(row["chapitre_4e"], {})
        votes[row["chapitre_4e"]][row["chapitre_3e"]] = \
            votes[row["chapitre_4e"]].get(row["chapitre_3e"], 0) + 1

    scored = []
    for chapitre_4e, candidats in votes.items():
        total_4e = sections_4e_par_chapitre.get(chapitre_4e, 0)
        for chapitre_3e, communes in candidats.items():
            ratio = communes / total_4e if total_4e else 0.0
            scored.append((communes, ratio, chapitre_4e, chapitre_3e))
    scored.sort(key=lambda item: (item[0], item[1]), reverse=True)

    mapping: dict[str, dict] = {}
    used_3e: set[str] = set()
    for communes, ratio, chapitre_4e, chapitre_3e in scored:
        if chapitre_4e in mapping or chapitre_3e in used_3e:
            continue
        if communes < 2 or ratio < 0.25:
            continue
        mapping[chapitre_4e] = {"chapitre_3e": chapitre_3e, "chapitres_3e": [chapitre_3e],
                                 "sections_communes": communes, "ratio": round(ratio, 3),
                                 "origine": "vote", "motif": ""}
        used_3e.add(chapitre_3e)

    # correspondance declaree : elle prime sur le vote pour le chapitre qu'elle
    # decrit (l'edition a fusionne, scinde ou renomme des chapitres). Un meme
    # chapitre 3e peut alimenter plusieurs chapitres 4e : c'est une scission.
    for chapitre_4e, chapitres_3e, motif in CORRESPONDANCE_CHAPITRES_DECLAREE:
        mapping.pop(chapitre_4e, None)
        communes = sum(1 for row in correspondance
                       if row["chapitre_4e"] == chapitre_4e
                       and row["chapitre_3e"] in chapitres_3e
                       and row["statut"] != "absent_de_la_3e")
        mapping[chapitre_4e] = {
            "chapitre_3e": chapitres_3e[0] if chapitres_3e else "",
            "chapitres_3e": list(chapitres_3e),
            "sections_communes": communes,
            "ratio": 0.0,
            "origine": "declare",
            "motif": motif,
        }
    return mapping


def _chapter_of(row: dict) -> str:
    """Chapitre parent d'une section, deduit de son numero (« 3.1 » -> « 3 »)."""
    return row["number"].split(".")[0]


TITRES_GENERIQUES = {
    "state of the art", "applications", "generalization", "introduction",
    "summary", "overview", "conclusion", "references", "exercises",
    "learning algorithms", "notes", "bibliography", "agents",
}

RENOMMAGES_DECLARES: list[tuple[str, str, str]] = [
    # (numero 3e, numero 4e, motif) — appariement declare a la main, lisible et
    # verifiable dans les CSV : chaque ligne porte le titre et la page PDF des deux
    # cotes. Un renommage n'est pas un rapprochement calcule : c'est une decision
    # d'edition, signalee comme telle.
    ("4.4", "4.4", "reformulation : « Searching with Partial Observations » devient "
                   "« Search in Partially Observable Environments »"),
    ("5.1", "5.1", "reformulation : « Games » devient « Game Theory »"),
    ("5.3", "5.3", "reformulation : « Alpha-Beta Pruning » devient "
                   "« Heuristic Alpha-Beta Tree Search »"),
    ("5.7", "5.7", "reformulation : « State-of-the-Art Game Programs » devient "
                   "« Limitations of Game Search Algorithms »"),
    ("9.2", "9.2", "reformulation : « Unification and Lifting » devient "
                   "« Unification and First-Order Inference »"),
    ("12.4", "10.4", "reformulation : « Mental Events and Mental Objects » devient "
                    "« Mental Objects and Modal Logic »"),
    ("10.1", "11.1", "renommage et deplacement : « Definition of Classical Planning » "
                    "passe du ch. 10 au ch. 11 de la 4e"),
    ("10.2", "11.2", "renommage : « Algorithms for Planning as State-Space Search » "
                    "devient « Algorithms for Classical Planning »"),
    ("10.5", "11.7", "renommage et deplacement : « Analysis of Planning Approaches » "
                    "passe du ch. 10 au ch. 11 de la 4e"),
    ("11.1", "11.6", "renommage et deplacement : « Time, Schedules, and Resources » "
                    "passe du ch. 11 au ch. 11 de la 4e (chapters fusionnes)"),
    ("11.2", "11.4", "renommage et deplacement : « Hierarchical Planning » passe du "
                    "ch. 11 au ch. 11 de la 4e (chapters fusionnes)"),
    ("11.3", "11.5", "renommage et deplacement : « Planning and Acting in "
                    "Nondeterministic Domains » passe du ch. 11 au ch. 11 de la 4e "
                    "(chapters fusionnes)"),
    ("17.5", "18.2", "reformulation : « Decisions with Multiple Agents: Game Theory » "
                    "devient « Non-Cooperative Game Theory », dans un chapitre "
                    "multiagent propre a la 4e"),
    ("17.6", "18.3", "reformulation : « Mechanism Design » devient "
                    "« Cooperative Game Theory »"),
    ("18.4", "19.4", "reformulation : « Evaluating and Choosing the Best Hypothesis » "
                    "devient « Model Selection and Optimization »"),
    ("18.6", "19.6", "reformulation : « Regression and Classification with Linear "
                    "Models » devient « Linear Regression and Classification »"),
    ("18.11", "19.9", "reformulation : « Practical Machine Learning » devient "
                     "« Developing Machine Learning Systems »"),
    ("21.1", "22.1", "reformulation : « Introduction » (RL) devient "
                     "« Learning from Rewards »"),
    ("22.2", "23.6", "regroupement : « Text Classification » entre dans "
                     "« Natural Language Tasks » de la 4e"),
    ("22.3", "23.6", "regroupement : « Information Retrieval » entre dans "
                     "« Natural Language Tasks » de la 4e"),
    ("22.4", "23.6", "regroupement : « Information Extraction » entre dans "
                     "« Natural Language Tasks » de la 4e"),
    ("23.1", "23.2", "reformulation : « Phrase Structure Grammars » devient "
                     "« Grammar »"),
    ("23.2", "23.3", "reformulation : « Syntactic Analysis (Parsing) » devient "
                     "« Parsing »"),
    ("23.3", "23.4", "reformulation : « Augmented Grammars and Semantic Interpretation » "
                     "devient « Augmented Grammars »"),
    ("3.3", "3.3", "reformulation : « Searching for Solutions » devient "
                   "« Search Algorithms »"),
    ("24.4", "25.6", "renommage : « Reconstructing the 3D World » devient "
                    "« The 3D World » au ch. 25"),
    ("24.6", "25.7", "renommage : « Using Vision » devient « Using Computer Vision » "
                    "au ch. 25"),
    ("25.1", "26.1", "renommage : « Introduction » (robotique) devient « Robots » "
                    "au ch. 26"),
    ("25.4", "26.5", "renommage : « Planning to Move » devient « Planning and "
                    "Control » au ch. 26"),
    ("26.1", "27.1", "renommage : « Weak AI: Can Machines Act Intelligently? » "
                    "devient « The Limits of AI »"),
    ("26.2", "27.2", "renommage : « Strong AI: Can Machines Really Think? » devient "
                    "« Can Machines Really Think? »"),
    ("26.3", "27.3", "renommage : « The Ethics and Risks of Developing Artificial "
                    "Intelligence » devient « The Ethics of AI »"),
    ("27.1", "28.1", "renommage : « Agent Components » devient « AI Components »"),
    ("27.2", "28.2", "renommage : « Agent Architectures » devient « AI "
                    "Architectures »"),
]

CORRESPONDANCE_CHAPITRES_DECLAREE: list[tuple[str, list[str], str]] = [
    # (numero 4e, numeros 3e, motif) — correspondance declaree entre chapitres.
    # Elle prime sur l'appariement automatique (qui ne compte que les sections de
    # meme titre) quand l'edition a fusionne, scinde ou renomme des chapitres.
    ("10", ["12"], "la 4e porte la representation des connaissances au ch. 10, la 3e "
                   "au ch. 12 : decalage de deux chapitres"),
    ("11", ["10", "11"], "la 4e fusionne en un seul ch. 11 les ch. 10 (« Classical "
                        "Planning ») et 11 (« Planning and Acting in the Real World ») "
                        "de la 3e"),
    ("15", [], "« Probabilistic Programming » n'existe pas dans la 3e : chapitre propre "
               "a la 4e"),
    ("18", ["17"], "la 4e fait du multiagent un chapitre a part entiere ; la 3e "
                   "l'aborde dans les sections 17.5 et 17.6 de « Making Complex "
                   "Decisions »"),
    ("17", ["17"], "la 4e scinde le ch. 17 de la 3e : la partie multiagent part au "
                   "ch. 18, la partie decisionnelle reste au ch. 17"),
    ("19", ["18"], "la 4e supprime le ch. 19 de la 3e (« Knowledge in Learning » : "
                   "apprentissage par explication, information de pertinence, "
                   "programmation inductive) et confirme le ch. 18 comme "
                   "« Learning from Examples »"),
    ("21", [], "« Deep Learning » n'existe pas dans la 3e : chapitre propre a la 4e"),
    ("23", ["22", "23"], "la 4e fusionne en un seul ch. 23 les ch. 22 (« Natural "
                        "Language Processing ») et 23 (« Natural Language for "
                        "Communication ») de la 3e"),
    ("24", [], "« Deep Learning for Natural Language Processing » n'existe pas dans "
               "la 3e : chapitre propre a la 4e"),
    ("25", ["24"], "la 4e renomme « Perception » en « Computer Vision »"),
    ("26", ["25"], "memes sections, la robotique passe du ch. 25 au ch. 26"),
    ("27", ["26"], "la 4e renomme « Philosophical Foundations » en « Philosophy, "
                   "Ethics, and Safety of AI »"),
    ("28", ["27"], "la 4e renomme « AI: The Present and Future » en « The Future "
                   "of AI »"),
]


def _title_score(a: str, b: str) -> float:
    """Similarite entre deux titres de section : max(ratio de sequence, jaccard de jetons).

    Le jaccard de jetons rattrape les formulations qui different d'un mot
    (« Local Search Algorithms and Optimization Problems » contre « Local Search and
    Optimization Problems ») ; le ratio de sequence rattrape les variantes
    orthographiques.
    """
    norm_a, norm_b = _norm(a), _norm(b)
    if not norm_a or not norm_b:
        return 0.0
    ratio = difflib.SequenceMatcher(None, norm_a, norm_b).ratio()
    set_a, set_b = set(_tokens(a)), set(_tokens(b))
    if not set_a or not set_b:
        return ratio
    jaccard = len(set_a & set_b) / len(set_a | set_b)
    return max(ratio, jaccard)


def _appariement_flou_possible(titre_a: str, titre_b: str) -> bool:
    """Le rapprochement flou exige deux jetons significatifs communs.

    Un seul mot commun ne prouve rien : « Applications » et « Generalization » ne
    se ressemblent que par leur faible longueur. Deux jetons communs, eux, sont un
    signal de reformulation. Les titres generiques sont exclus du rapprochement flou
    : ils ne designent aucune section en particulier.
    """
    if _norm(titre_a) in TITRES_GENERIQUES or _norm(titre_b) in TITRES_GENERIQUES:
        return False
    set_a, set_b = set(_tokens(titre_a)), set(_tokens(titre_b))
    return len(set_a & set_b) >= 2


def match_sections(sections_3e: list[dict], sections_4e: list[dict],
                   seuil: float = 0.75) -> list[dict]:
    """Apparie les sections des deux editions, titre a titre.

    Trois passes, dans cet ordre :
    1. **identite de titre** — les deux titres normalises sont egaux ;
    2. **renommage declare** — la table `RENOMMAGES_DECLARES` ;
    3. **reformulation** — similarite au-dessus du seuil, avec deux jetons
       significatifs communs.

    L'appariement est injectif : une section ne peut servir qu'une fois. Ce qui
    reste sans pendant est un ecart declare, jamais un rapprochement invente.
    """
    par_numero_3e = {row["number"]: row for row in sections_3e}
    par_numero_4e = {row["number"]: row for row in sections_4e}

    appaires: dict[int, list[tuple[int, float, str]]] = {}
    pris_3e: set[int] = set()

    # passe 1 — identite de titre
    index_3e: dict[str, list[int]] = {}
    for j, row_3e in enumerate(sections_3e):
        index_3e.setdefault(_norm(row_3e["title"]), []).append(j)
    for i, row_4e in enumerate(sections_4e):
        for j in index_3e.get(_norm(row_4e["title"]), []):
            if j not in pris_3e:
                appaires[i] = [(j, 1.0, "commun")]
                pris_3e.add(j)
                break

    # passe 2 — renommages declares (une section 4e peut regrouper plusieurs
    # sections 3e : c'est un regroupement d'edition, pas un appariement un-a-un)
    declares: list[tuple[int, int]] = []
    for numero_3e, numero_4e, motif in RENOMMAGES_DECLARES:
        row_4e = par_numero_4e.get(numero_4e)
        row_3e = par_numero_3e.get(numero_3e)
        if row_4e is None or row_3e is None:
            continue
        i = sections_4e.index(row_4e)
        j = sections_3e.index(row_3e)
        if j in pris_3e:
            continue
        declares.append((i, j))
        pris_3e.add(j)
    par_section_4e: dict[int, int] = {}
    for i, _ in declares:
        par_section_4e[i] = par_section_4e.get(i, 0) + 1
    for i, j in declares:
        statut = "regroupe" if par_section_4e[i] > 1 else "renomme"
        appaires.setdefault(i, []).append((j, 1.0, statut))

    # passe 3 — reformulation
    candidates: list[tuple[float, int, int]] = []
    for i, row_4e in enumerate(sections_4e):
        if i in appaires:
            continue
        for j, row_3e in enumerate(sections_3e):
            if j in pris_3e:
                continue
            if not _appariement_flou_possible(row_4e["title"], row_3e["title"]):
                continue
            score = _title_score(row_4e["title"], row_3e["title"])
            if score >= seuil:
                candidates.append((score, i, j))
    candidates.sort(reverse=True)
    for score, i, j in candidates:
        if i in appaires or j in pris_3e:
            continue
        appaires[i] = [(j, score, "commun")]
        pris_3e.add(j)

    rows = []
    for i, row_4e in enumerate(sections_4e):
        matchs = appaires.get(i)
        if not matchs:
            rows.append({
                "titre_4e": row_4e["title"],
                "section_4e": row_4e["number"],
                "chapitre_4e": _chapter_of(row_4e),
                "titre_3e": "",
                "section_3e": "",
                "chapitre_3e": "",
                "similarite": "",
                "statut": "absent_de_la_3e",
            })
            continue
        for j, score, statut in matchs:
            twin = sections_3e[j]
            rows.append({
                "titre_4e": row_4e["title"],
                "section_4e": row_4e["number"],
                "chapitre_4e": _chapter_of(row_4e),
                "titre_3e": twin["title"],
                "section_3e": twin["number"],
                "chapitre_3e": _chapter_of(twin),
                "similarite": f"{score:.2f}" if statut == "commun" else "declare",
                "statut": statut,
            })
    return rows


def build_coverage(edition: str, toc: list[dict], phases: list[Phase],
                   comps: dict[int, dict], chapter_map: dict[str, dict],
                   cite_to_phase_4e: dict[str, list[Phase]]) -> list[dict]:
    """(section, phase, carnets, competences, couvert) pour une edition donnee.

    Les references de chapitre du parcours sont ecrites dans la numerotation de la 4e
    (verifie : ch. 23-24 = NLP 4e). Pour la 3e, la correspondance se fait par le
    chapitre apparie (`chapter_map`), jamais par identite de numero.
    """
    cite_to_phase: dict[str, list[Phase]] = {}
    for chapter, phases_4e in cite_to_phase_4e.items():
        if edition == "4e":
            cite_to_phase.setdefault(chapter, []).extend(phases_4e)
        else:
            for twin in chapter_map.get(chapter, {}).get("chapitres_3e", []):
                cite_to_phase.setdefault(twin, []).extend(phases_4e)

    rows = []
    for row in toc:
        if row["kind"] not in ("section", "chapter"):
            continue
        chapter = _chapter_of(row) if row["kind"] == "section" else row["number"]
        phases_citing = cite_to_phase.get(chapter, [])
        notebooks, competences, labels = [], [], []
        for phase in phases_citing:
            labels.append(phase.label)
            for step in phase.steps:
                notebooks.extend(step.notebooks)
                info = comps.get(step.number)
                if info:
                    competences.extend(info["competences"])
        rows.append({
            "edition": edition,
            "niveau": row["kind"],
            "numero": row["number"],
            "titre": row["title"],
            "chapitre": chapter,
            "page_pdf": row["pdf_page"],
            "phases": "; ".join(labels),
            "carnets": "; ".join(dict.fromkeys(notebooks)),
            "competences": "; ".join(dict.fromkeys(competences)),
            "couvert": "oui" if labels else "non",
        })
    return rows


# --------------------------------------------------------------------------- commandes

def cmd_toc(args) -> int:
    all_rows: list[dict] = []
    if args.edition in ("3e", "both"):
        entries = extract_3e(args.bib_dir / PDF_3E)
        verify_3e(args.bib_dir / PDF_3E, entries)
        rows = _rows_of("3e", entries)
        _write_csv(args.out_dir / "aima3e-toc.csv", rows, TOC_FIELDS)
        all_rows += rows
    if args.edition in ("4e", "both"):
        entries4 = parse_4e_toc(args.bib_dir / PDF_4E)
        anchor_4e(args.bib_dir / PDF_4E, entries4)
        verify_4e(args.bib_dir / PDF_4E, entries4)
        rows4 = _rows_of("4e", entries4)
        _write_csv(args.out_dir / "aima4e-toc.csv", rows4, TOC_FIELDS)
        all_rows += rows4
    total = len(all_rows)
    verified = sum(1 for r in all_rows if r["verified"] == "oui")
    print(f"toc : lignes={total} verifiees={verified} non_verifiees={total - verified}")
    return 0


def _read_toc(path: Path) -> list[dict]:
    with path.open(encoding="utf-8", newline="") as fh:
        return list(csv.DictReader(fh))


def cmd_map(args) -> int:
    toc3 = _read_toc(args.out_dir / "aima3e-toc.csv")
    toc4 = _read_toc(args.out_dir / "aima4e-toc.csv")
    phases = parse_walk(REPO_ROOT / WALK_MD)
    comps = parse_competences(REPO_ROOT / COMPETENCES_MD)

    chapters_3e = {r["number"]: r["title"] for r in toc3 if r["kind"] == "chapter"}
    chapters_4e = {r["number"]: r["title"] for r in toc4 if r["kind"] == "chapter"}

    cite_to_phase_4e: dict[str, list[Phase]] = {}
    for phase in phases:
        for chapter in phase.chapters:
            cite_to_phase_4e.setdefault(chapter, []).append(phase)

    sections_3e = [r for r in toc3 if r["kind"] == "section"]
    sections_4e = [r for r in toc4 if r["kind"] == "section"]
    correspondance = match_sections(sections_3e, sections_4e)
    _write_csv(args.out_dir / "aima-editions-correspondance.csv", correspondance,
               ["titre_4e", "section_4e", "chapitre_4e", "titre_3e", "section_3e",
                "chapitre_3e", "similarite", "statut"])

    chapter_map = match_chapters(correspondance, toc3, toc4)

    couverture_3e = build_coverage("3e", toc3, phases, comps, chapter_map, cite_to_phase_4e)
    couverture_4e = build_coverage("4e", toc4, phases, comps, chapter_map, cite_to_phase_4e)
    _write_csv(args.out_dir / "aima-walk-sections.csv", couverture_3e + couverture_4e,
               ["edition", "niveau", "numero", "titre", "chapitre", "page_pdf",
                "phases", "carnets", "competences", "couvert"])

    chapitres = []
    for phase in phases:
        notebooks, competences = [], []
        hors_livre = []
        for step in phase.steps:
            notebooks.extend(step.notebooks)
            if step.hors_livre:
                hors_livre.append(f"etape {step.number} : {step.hors_livre}")
            info = comps.get(step.number)
            if info:
                competences.extend(info["competences"])
        for chapter in phase.chapters:
            appariement = chapter_map.get(chapter, {})
            jumeaux = appariement.get("chapitres_3e", [])
            twin = appariement.get("chapitre_3e", "")
            chapitres.append({
                "phase": phase.label,
                "titre_phase": phase.title,
                "chapitre_4e_cite": chapter,
                "titre_4e": chapters_4e.get(chapter, ""),
                "chapitre_3e_apparie": ", ".join(jumeaux),
                "titre_3e": "; ".join(chapters_3e.get(num, "") for num in jumeaux),
                "decalage": (str(int(twin) - int(chapter))
                             if len(jumeaux) == 1 and twin and chapter.isdigit()
                             and twin.isdigit() else ""),
                "sections_communes": str(appariement.get("sections_communes", 0)),
                "origine": appariement.get("origine", ""),
                "motif": appariement.get("motif", ""),
                "carnets": "; ".join(dict.fromkeys(notebooks)),
                "competences": "; ".join(dict.fromkeys(competences)),
                "hors_livre": " | ".join([phase.beyond] + hors_livre) if (phase.beyond or hors_livre) else "",
            })
    _write_csv(args.out_dir / "aima-walk-chapitres.csv", chapitres,
               ["phase", "titre_phase", "chapitre_4e_cite", "titre_4e", "chapitre_3e_apparie",
                "titre_3e", "decalage", "sections_communes", "origine", "motif",
                "carnets", "competences", "hors_livre"])

    # Ce qui depasse le livre, etape par etape : le parcours le marque lui-meme.
    hors_livre_rows = []
    for phase in phases:
        for step in phase.steps:
            if not step.hors_livre:
                continue
            hors_livre_rows.append({
                "phase": phase.label,
                "titre_phase": phase.title,
                "etape": str(step.number),
                "nature": "hors_livre",
                "marqueur": step.hors_livre,
                "carnets": "; ".join(dict.fromkeys(step.notebooks)),
            })
    # Ce que le parcours a relu dans ses termes modernes : rattache au livre,
    # mais reecrit par le depot.
    for phase in phases:
        for step in phase.steps:
            if not step.jonction:
                continue
            hors_livre_rows.append({
                "phase": phase.label,
                "titre_phase": phase.title,
                "etape": str(step.number),
                "nature": "jonction",
                "marqueur": step.jonction,
                "carnets": "; ".join(dict.fromkeys(step.notebooks)),
            })
    _write_csv(args.out_dir / "aima-hors-livre.csv", hors_livre_rows,
               ["phase", "titre_phase", "etape", "nature", "marqueur", "carnets"])

    resume = {
        "phases": len(phases),
        "etapes": sum(len(p.steps) for p in phases),
        "sections_3e": len(sections_3e),
        "sections_4e": len(sections_4e),
        # Les lignes de couverture portent des sections ET des chapitres :
        # un compteur nomme "sections" ne doit en compter que les sections.
        "sections_couvertes_4e": sum(
            1 for r in couverture_4e if r["couvert"] == "oui" and r["niveau"] == "section"),
        "sections_couvertes_3e": sum(
            1 for r in couverture_3e if r["couvert"] == "oui" and r["niveau"] == "section"),
        "chapitres_couverts_4e": sum(
            1 for r in couverture_4e if r["couvert"] == "oui" and r["niveau"] == "chapter"),
        "chapitres_couverts_3e": sum(
            1 for r in couverture_3e if r["couvert"] == "oui" and r["niveau"] == "chapter"),
        "chapitres_apparies": len(chapter_map),
        "sections_communes_entre_editions": sum(1 for r in correspondance if r["statut"] == "commun"),
        "sections_renommees": sum(1 for r in correspondance if r["statut"] == "renomme"),
        "sections_regroupees": sum(1 for r in correspondance if r["statut"] == "regroupe"),
        "sections_absentes_de_la_3e": sum(1 for r in correspondance if r["statut"] == "absent_de_la_3e"),
        # Un chapitre sans pendant est un chapitre dont la liste de pendants 3e est
        # VIDE : la presence dans la table ne suffit pas a dire qu'il a un jumeau.
        "chapitres_4e_sans_pendant_3e": sorted(
            (num for num in chapters_4e
             if not chapter_map.get(num, {}).get("chapitres_3e")
             and any(r["chapitre_4e"] == num for r in correspondance)),
            key=lambda n: int(n)),
        "chapitres_3e_sans_pendant_4e": sorted(
            (num for num in chapters_3e
             if not any(num in entry.get("chapitres_3e", []) for entry in chapter_map.values())),
            key=lambda n: int(n)),
    }
    (args.out_dir / "aima-mapping-resume.json").write_text(
        json.dumps(resume, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(resume, ensure_ascii=False))
    return 0


def cmd_check(args) -> int:
    """Controle la coherence interne des CSV produits (TOC vers couverture).

    Ne rouvre pas les PDF : la re-verification des ancres contre les pages est
    le role de `toc`.
    """
    rc = 0
    for name in ("aima3e-toc.csv", "aima4e-toc.csv"):
        path = args.out_dir / name
        if not path.exists():
            sys.stderr.write(f"absent : {path}\n")
            rc = 1
            continue
        rows = _read_toc(path)
        bad = [r for r in rows if r["verified"] != "oui"]
        print(f"{name}: {len(rows)} lignes, {len(rows) - len(bad)} verifiees, {len(bad)} non verifiees")
        for r in bad:
            print(f"   non verifiee : {r['kind']} {r['number']} {r['title'][:60]} (pdf {r['pdf_page']})")
        rc = 1 if bad else rc

    # Rejoue uniquement `map` avec les TOC épinglées : aucun PDF n'est rouvert.
    # Les fichiers produits restent dans un répertoire temporaire, jamais dans
    # le dossier des artefacts commités.
    map_artifacts = (
        "aima-walk-sections.csv",
        "aima-walk-chapitres.csv",
        "aima-hors-livre.csv",
        "aima-mapping-resume.json",
    )
    toc_paths = [args.out_dir / name for name in ("aima3e-toc.csv", "aima4e-toc.csv")]
    if all(path.is_file() for path in toc_paths):
        with tempfile.TemporaryDirectory(prefix="aima-mapping-check-") as temp:
            replay_dir = Path(temp)
            for path in toc_paths:
                shutil.copyfile(path, replay_dir / path.name)
            cmd_map(argparse.Namespace(out_dir=replay_dir))

            for name in map_artifacts:
                committed = args.out_dir / name
                replayed = replay_dir / name
                if not committed.is_file():
                    sys.stderr.write(f"artefact absent : {name}\n")
                    rc = 1
                    continue
                # Les CSV/JSON commités peuvent être en CRLF selon le checkout ;
                # les fins de ligne ne constituent pas un drift de contenu.
                contenu_commite = committed.read_bytes().replace(b"\r\n", b"\n")
                contenu_rejoue = replayed.read_bytes().replace(b"\r\n", b"\n")
                if contenu_commite == contenu_rejoue:
                    continue

                sys.stderr.write(f"drift détecté : {name}\n")
                committed_lines = committed.read_text(encoding="utf-8").splitlines(keepends=True)
                replayed_lines = replayed.read_text(encoding="utf-8").splitlines(keepends=True)
                diff = list(difflib.unified_diff(
                    committed_lines,
                    replayed_lines,
                    fromfile=f"commité/{name}",
                    tofile=f"map rejoué/{name}",
                ))
                extrait = diff[:40]
                sys.stderr.writelines(extrait)
                if len(diff) > len(extrait):
                    sys.stderr.write("... extrait tronqué ...\n")
                rc = 1
    else:
        for path in toc_paths:
            if not path.is_file():
                sys.stderr.write(f"source épinglée absente : {path.name}\n")
        rc = 1

    # coherence : chaque ligne de couverture renvoie a une section presente dans la TOC
    couverture = args.out_dir / "aima-walk-sections.csv"
    if couverture.exists():
        cov = _read_toc(couverture)
        for edition, toc_name in (("3e", "aima3e-toc.csv"), ("4e", "aima4e-toc.csv")):
            known = {(r["kind"], r["number"]) for r in _read_toc(args.out_dir / toc_name)}
            orphelines = [r for r in cov if r["edition"] == edition
                          and (r["niveau"], r["numero"]) not in known]
            print(f"couverture {edition} : {len(cov)} lignes au total, "
                  f"{len(orphelines)} sans section correspondante")
            rc = 1 if orphelines else rc
    return rc


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("commande", choices=["toc", "map", "check"])
    ap.add_argument("--edition", choices=["3e", "4e", "both"], default="both")
    ap.add_argument("--bib-dir", type=Path, default=DEFAULT_BIB_DIR)
    ap.add_argument("--out-dir", type=Path, default=Path("docs/curriculum/aima-mapping"))
    args = ap.parse_args(argv)
    if args.commande == "toc":
        return cmd_toc(args)
    if args.commande == "map":
        return cmd_map(args)
    return cmd_check(args)


if __name__ == "__main__":
    raise SystemExit(main())
