"""Detecte le recit d'activite (cycles, lanes, corrigenda) dans la prose des carnets.

Epic #20250 (decision du mainteneur 2026-10-10) : un carnet presente l'etat
final corrige de son contenu a l'apprenant. Les corrigenda, identifiants de
cycle (``c.NNNN``), noms de machines et de lanes, verdicts de review et
annonces de tranches n'y ont pas leur place -- ce recit vit dans git, les PR
et les issues. Cas fondateur : SC-09 (#19372), dont la seule cellule
« Conclusion » porte 14 334 caracteres dont deux sections « Corrigendum » et
une troisieme en cellule suivante, avec noms de lanes et verdict ``domain:
fail`` -- passe par toutes les gates le jour meme.

Le critere n'est PAS la presence d'un mot (precision du mainteneur, DM
ai01-c2142-coursia2-20250-p0-amend) : quelques mentions isolees sont
acceptables. Le defaut est la PART du carnet occupee par ce recit. L'organe
mesure donc, par carnet, la fraction de caracteres markdown vivant dans des
passages (paragraphes) a densite de marqueurs elevee.

Forme reprise de ``check_prose_quantitative_claims.py`` (#9377/#9434) :
mode audit sur le stock, mode ratchet sur les passages AJOUTES d'une PR.
Le ratchet ne juge qu'un passage dense ajoute (section ou paragraphe) --
une mention isolee ajoutee ne declenche jamais.

Marqueurs (taxonomie #20250 + amend)
------------------------------------
FORTS (poids 2) : ``corrigendum`` ; identifiant de cycle ``c.NNNN`` /
``c.NNNN-N1`` ; nom de machine (``myia-po-20xx``, ``po-20xx``) ; workspace
(``CoursIA-2``) ; bots reviewers (NanoClaw, Hermes) ; verdicts (``SOTA-OK``,
``axe 2``, ``domain: fail``, ``CHANGES_REQUESTED``) ; jargon de coordination
(preflight, dossier de domaine/fermeture/prevalidation, merge-ready) ;
``tranche N`` / « prochaine PR » ; reference de commit ou de tete avec SHA ;
horodatage ISO ; tag de lecon ``L576`` / ``L677-L4`` ; ``DM`` (hors contexte
Diebold-Mariano / dual momentum).

FAIBLES (poids 1) : ``lane`` ; ``commit`` nu ; ``cellule N`` ; « corrige
dans/par » ; « reserve » ; ``dispatch`` (hors dispatch dynamique/economique) ;
``adjoint`` (hors adjoint mathematique) ; ``PR #N``.

Faux positifs mesures a exclure (Epic #20250, teste) : « DM » pour
Diebold-Mariano ou dual momentum ; « adjoint » au sens mathematique ;
« dispatch dynamique » au sens informatique. Angle mort assume : un carnet
qui ENSEIGNE git peut denser « commit » seul -- aucun marqueur fort ne
l'accompagne, et un passage dense exige soit 2 points forts, soit 1 fort +
densite elevee (cf ``DENSE_RULE``) ; le cas n'existe pas dans le corpus.

Perimetre : carnets ``*.ipynb`` seulement (la mesure fondatrice porte les
1520 carnets ; les README de series sont une extension possible, phase 2).
Hors perimetre, comme l'Epic : ``docs/ledgers/``, ``.claude``, cellules code
(phase 2 traite les debords en commentaires de code par correction + re-exec,
regle 6 de secrets-hygiene).

Usage
-----
    # CI sur une PR : refuse les passages DENSES ajoutes (mentions isolees OK)
    python check_activity_leak.py --diff origin/main...HEAD --strict

    # Audit du stock : classement des carnets par part de prose d'activite
    python check_activity_leak.py --all
    python check_activity_leak.py --all --top 25

    # Detail d'un carnet (calibration) : chaque passage, son score, son verdict
    python check_activity_leak.py --notebook MyIA.AI.Notebooks/.../SC-09.ipynb
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ----------------------------------------------------------------------------
# Marqueurs
# ----------------------------------------------------------------------------
# Chaque entree : (nom, regex, poids). Les gardes anti-FP (DM, dispatch,
# adjoint) sont appliquees dans ``_markers_in_text`` apres le match brut --
# une regex seule ne peut pas exprimer « pas a cote de Diebold-Mariano ».

_CORRIGENDUM_RE = re.compile(r"corrigendum", re.IGNORECASE)
_CYCLE_RE = re.compile(r"\bc\.\d{2,5}(?:[-\u2013]N\d+)?\b")
# myia-po-2024, myia-ai-01, po-2025 (nom court de machine, utilise tel quel
# dans la prose de coordination ; « po-2025 » seul ne peut pas etre un mot).
_MACHINE_RE = re.compile(r"\bmyia-[a-z0-9]+(?:-[a-z0-9]+)*\b|\bpo-20\d\d\b", re.IGNORECASE)
_WORKSPACE_RE = re.compile(r"\bCoursIA-\d\b")
# jsboige volontairement absent : les URLs de depots (github.com/jsboige/...)
# sont du contenu legitime.
_BOT_RE = re.compile(r"\bNanoClaw\b|\bHermes\b|\bclusterManager(?:-Myia)?\b")
_VERDICT_RE = re.compile(
    r"SOTA-(?:OK|INTRINSIC|RECOVERABLE-\w+)"
    r"|axe\s?2\b"
    r"|domain:\s*`?(?:fail|pass)`?"
    r"|CHANGES_REQUESTED"
    r"|COMMENT_WITH_CONCERNS",
    re.IGNORECASE,
)
_COORD_NOUN_RE = re.compile(
    r"\bpreflight\b"
    r"|\bdossier de (?:domaine|fermeture|pr[eé]validation)\b"
    r"|\bmerge-ready\b",
    re.IGNORECASE,
)
# Annonces de tranche/PR a venir. Le bare « Tranche N » est ECARTE : mesure
# du premier audit plein (2026-10-10, 1524 carnets), les series CSP/Search/
# Tweety/Planners l'emploient comme vocabulaire pedagogique INTRA-carnet
# (« la Tranche 1 ci-dessus resout... », « cette tranche ») -- une etiquette
# de structure, pas une annonce de coordination. Ce qui signale l'activite,
# c'est l'annonce orientee futur : « prochaine tranche », « tranche
# suivante », « prochaine PR », « PR suivante(s) ».
_TRANCHE_RE = re.compile(
    r"\b(?:prochaine|suivante|suivant)\s+tranches?\b"
    r"|\btranches?\s+(?:suivante|suivant|[eé] venir)\b"
    r"|\bprochaine PR\b"
    r"|\bPRs?\s+suivantes?\b",
    re.IGNORECASE,
)
_COMMIT_REF_RE = re.compile(r"\b(?:commit|t[eê]te)\s+`?[0-9a-f]{7,12}`?", re.IGNORECASE)
_ISO_TS_RE = re.compile(r"\b20\d\d-\d\d-\d\dT\d\d:\d\d")
_LESSON_TAG_RE = re.compile(r"\bL\d{3,4}(?:-L\d)?\b")
_DM_RE = re.compile(r"\bDM\b")

_LANE_RE = re.compile(r"\blanes?\b", re.IGNORECASE)
_COMMIT_BARE_RE = re.compile(r"\bcommits?\b", re.IGNORECASE)
_CELLULE_RE = re.compile(r"\bcellules?\s+\d+\b", re.IGNORECASE)
_CORRIGE_DANS_RE = re.compile(r"\bcorrig[eé]{1,2}\s+(?:dans|par)\b", re.IGNORECASE)
_RESERVE_RE = re.compile(r"\br[eé]serves?\b", re.IGNORECASE)
_DISPATCH_RE = re.compile(r"\bdispatch(?:er|[eé]e?)?\b", re.IGNORECASE)
_ADJOINT_RE = re.compile(r"\badjoint\b", re.IGNORECASE)
_PR_REF_RE = re.compile(r"\bPR\s*#\d+\b")

# Fenetres de garde anti-FP : le contexte autour du match decide.
_DM_OK_CONTEXT = re.compile(
    r"Diebold|Mariano|momentum|p-value|p_valeur|statistique|test", re.IGNORECASE
)
_DISPATCH_OK_CONTEXT = re.compile(
    r"dynamique|dynamic|[eé]conomique|[eé]lectrique", re.IGNORECASE
)
_ADJOINT_OK_CONTEXT = re.compile(
    r"matrice|op[eé]rateur|operator|endomorphisme|hermitien", re.IGNORECASE
)
_GUARD_WINDOW = 60  # caracteres de contexte avant/apres le match

STRONG_MARKERS: tuple[tuple[str, re.Pattern[str], int], ...] = (
    ("corrigendum", _CORRIGENDUM_RE, 2),
    ("cycle", _CYCLE_RE, 2),
    ("machine", _MACHINE_RE, 2),
    ("workspace", _WORKSPACE_RE, 2),
    ("bot", _BOT_RE, 2),
    ("verdict", _VERDICT_RE, 2),
    ("coord_noun", _COORD_NOUN_RE, 2),
    ("tranche", _TRANCHE_RE, 2),
    ("commit_ref", _COMMIT_REF_RE, 2),
    ("iso_ts", _ISO_TS_RE, 2),
    ("lesson_tag", _LESSON_TAG_RE, 2),
    ("dm", _DM_RE, 2),
)

WEAK_MARKERS: tuple[tuple[str, re.Pattern[str], int], ...] = (
    ("lane", _LANE_RE, 1),
    ("commit", _COMMIT_BARE_RE, 1),
    ("cellule", _CELLULE_RE, 1),
    ("corrige_dans", _CORRIGE_DANS_RE, 1),
    ("reserve", _RESERVE_RE, 1),
    ("dispatch", _DISPATCH_RE, 1),
    ("adjoint", _ADJOINT_RE, 1),
    ("pr_ref", _PR_REF_RE, 1),
)

ALL_MARKERS = STRONG_MARKERS + WEAK_MARKERS

# ----------------------------------------------------------------------------
# Regle de densite (amend : la PART, pas la presence)
# ----------------------------------------------------------------------------
# Un passage est DENSE s'il cumule assez de poids de marqueurs rapporte a sa
# longueur. Trois conditions conjointes :
#   - longueur >= MIN_PASSAGE_CHARS (une ligne de titre courte reste eligible
#     : « ## Corrigendum c.1209 » fait 23 caracteres et doit etre vu) ;
#   - score >= MIN_SCORE : au moins l'equivalent de 2 marqueurs forts, ou
#     1 fort + 2 faibles -- une mention isolee, meme forte, ne suffit pas ;
#   - densite >= MIN_DENSITY (points par 1000 caracteres) : un long passage
#     historique du cours peut citer un commit et une PR sans etre un recit
#     de coordination.
#
# Calibration (SC-09 @7a05215842, cellules 20-21) : les paragraphes
# « Corrigendum » rendent score 4-11 pour 70-160 caracteres (densite 25-70) ;
# les paragraphes de cours de la meme cellule rendent 0-2 pour 200-500
# caracteres. Les valeurs ci-dessous placent la frontiere entre les deux.
MIN_PASSAGE_CHARS = 40
MIN_SCORE = 4
MIN_DENSITY = 8.0  # points de marqueurs par 1000 caracteres

# Part d'un carnet au-dela de laquelle l'audit le classe « a traiter ».
# Cale sur SC-09 (part mesuree ~1/3, cf calibration du body de #20250) avec
# marge sous le cas fondateur : un carnet dont un sixieme de la prose est du
# recit d'activite est deja malade, un carnet qui cite une PR en pied de
# carnet reste a ~0.
DEFAULT_PART_THRESHOLD = 0.15

# ----------------------------------------------------------------------------
# Perimetre
# ----------------------------------------------------------------------------
SKIP_PARTS = (
    ".claude",
    ".lake",
    "node_modules",
    ".git",
    "_peters",
    "foundry-lib/lib",
    ".pytest_cache",
    "docs",       # hors perimetre #20250 : ledgers, docs de reference
    "probes",     # carnets-sondes de diagnostic (ex dotnet-restore-bug-17361) :
                  # leur objet EST l'incident, ils ne servent pas l'apprenant
    "bin",
    "obj",
    "tmp",
)


def _skipped(path: Path) -> bool:
    return any(part in SKIP_PARTS for part in path.parts)


# ----------------------------------------------------------------------------
# Passage = paragraphe markdown
# ----------------------------------------------------------------------------
_PARA_SPLIT_RE = re.compile(r"\n\s*\n")


def split_paragraphs(md_text: str) -> list[str]:
    """Decoupe une cellule markdown en passages (paragraphes).

    Le niveau paragraphe est l'unite de l'amend (« paragraphes/sections ») :
    une section « ## Corrigendum » dont le titre et le premier paragraphe
    sont colles ne forment qu'un passage, ce qui est correct -- le titre
    contribue au score du passage qu'il ouvre.
    """
    return [p.strip() for p in _PARA_SPLIT_RE.split(md_text) if p.strip()]


def _context_guarded(text: str, at: int, end: int, ok_context: re.Pattern[str]) -> bool:
    window = text[max(0, at - _GUARD_WINDOW):end + _GUARD_WINDOW]
    return bool(ok_context.search(window))


# Marqueurs qui ne comptent QUE s'ils sont accompagnes d'un autre marqueur
# dans le meme passage. « cellule N » est le cas mesure : dans le corpus il
# sert massivement de renvoi INTRA-carnet (« Sharpe 0.063 (cellule 12) »,
# quantbook Multi-Layer-EMA, 4 occurrences dans un paragraphe de resultats) --
# navigation pedagogique, pas vocabulaire de correction. Il ne compte que
# lorsqu'il voisine un marqueur de correction ou de coordination, ce qui est
# la forme de l'amend (« le vocabulaire de correction rapportee », « cellule
# N »).
CO_MARKER_ONLY = frozenset({"cellule"})


def markers_in_text(text: str) -> list[tuple[str, str, int]]:
    """Rend [(nom, extrait, poids)] pour tous les marqueurs de ``text``.

    Les gardes anti-FP s'appliquent par occurrence, sur son contexte :
    un « DM » colle a « Diebold-Mariano » ou « p-value » est le test
    statistique, pas un message du coordinateur. Les marqueurs de
    ``CO_MARKER_ONLY`` ne sont retenus que si un AUTRE marqueur est present
    dans le meme passage.
    """
    out: list[tuple[str, str, int]] = []
    for name, rx, weight in ALL_MARKERS:
        for m in rx.finditer(text):
            if name == "dm" and _context_guarded(text, m.start(), m.end(), _DM_OK_CONTEXT):
                continue
            if name == "dispatch" and _context_guarded(text, m.start(), m.end(), _DISPATCH_OK_CONTEXT):
                continue
            if name == "adjoint" and _context_guarded(text, m.start(), m.end(), _ADJOINT_OK_CONTEXT):
                continue
            out.append((name, m.group(0), weight))
    if any(name in CO_MARKER_ONLY for name, _, _ in out):
        others = [m for m in out if m[0] not in CO_MARKER_ONLY]
        if not others:
            out = others
    return out


SECTION_HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s")
HEADING_MIN_SCORE = 2


@dataclass
class PassageVerdict:
    cell_index: int
    text: str
    score: int
    density: float
    strong: int
    dense: bool
    inherited: bool = False
    markers: list[tuple[str, str, int]] = field(default_factory=list)

    @property
    def preview(self) -> str:
        first = self.text.splitlines()[0] if self.text else ""
        return (first[:70] + "...") if len(first) > 70 else first


def judge_passage(cell_index: int, text: str) -> PassageVerdict:
    markers = markers_in_text(text)
    score = sum(w for _, _, w in markers)
    strong = sum(1 for _, _, w in markers if w >= 2)
    density = score * 1000.0 / max(len(text), 1)
    is_heading = bool(SECTION_HEADING_RE.match(text))
    # Un TITRE est juge plus court qu'un paragraphe : il est court par nature
    # (« ## Corrigendum c.1209 » = 22 caracteres), donc le garde de longueur
    # l'exclurait -- or un titre qui porte un identifiant de cycle est un
    # defaut cite par l'Epic lui-meme (« # Percolation 03b ... (c.1105) »).
    # Un titre portant >= 1 marqueur FORT est dense, sans garde de longueur.
    dense = (
        (is_heading and score >= HEADING_MIN_SCORE)
        or (
            not is_heading
            and len(text) >= MIN_PASSAGE_CHARS
            and score >= MIN_SCORE
            and density >= MIN_DENSITY
        )
    )
    return PassageVerdict(cell_index, text, score, density, strong, dense, False, markers)


def dense_reason(v: PassageVerdict) -> str:
    """Motif honnete du verdict dense -- la preuve affichee doit decrire le
    verdict rendu, pas la regle generique. Un passage herite porte un score
    nul (ses marqueurs vivent dans le titre de section) : afficher
    « score>=4 » sur un score de 0 contredit sa propre ligne."""
    if v.inherited:
        return f"herite d'une section porteuse (score local={v.score})"
    if SECTION_HEADING_RE.match(v.text):
        return f"titre porteur de marqueur (score={v.score}>={HEADING_MIN_SCORE})"
    return (f"score={v.score}>={MIN_SCORE}, len={len(v.text)}>={MIN_PASSAGE_CHARS}, "
            f"densite={v.density:.0f}>={MIN_DENSITY:.0f}/1000")


# Heritage de section (amend : « paragraphes/sections »). Le recit d'un
# Corrigendum ne porte pas ses marqueurs sur chaque ligne : la section
# « ## Corrigendum c.1209 » contient de longs paragraphes de prose propre
# (la reproduction du defaut) qui sont POURTANT le journal de correction --
# c'est la section entiere qui est le recit. Un paragraphe sous un titre
# porteur d'au moins un marqueur FORT (score de titre >= 2, ex. cycle ou
# corrigendum) est compte dense par heritage ; un titre de cours (« ##
# Conclusion », « ## Pour aller plus loin ») ne l'herite pas. Le seuil de
# titre est bas (un seul marqueur fort suffit) parce qu'un titre qui porte
# un identifiant de cycle a deja tout dit -- le cas SC-09 mesure les titres
# « Corrigendum c.NNNN » a score 4-12.
def judge_cell(cell_index: int, md_text: str) -> list[PassageVerdict]:
    """Juge chaque paragraphe d'une cellule, avec heritage de section.

    La cellule est parcourue dans l'ordre : un paragraphe-titre ouvre une
    section ; les paragraphes qui suivent heritent de sa densite jusqu'au
    titre suivant. Un paragraphe peut etre dense par ses propres marqueurs
    OU par heritage -- les deux sont du recit d'activite.

    Le titre H1 de tete de carnet ne PROPAGE PAS son heritage : un carnet
    dont le titre seul porte un identifiant de cycle (« # Percolation 03b
    -- extensions (c.1105) », mesure au premier audit) verrait sinon la
    totalite de sa prose heriter d'un marqueur unique. Le titre est juge
    comme passage (il est signale), seule une section H2+ propage.
    """
    verdicts: list[PassageVerdict] = []
    section_dense = False
    for para in split_paragraphs(md_text):
        v = judge_passage(cell_index, para)
        heading = SECTION_HEADING_RE.match(para)
        is_h1 = bool(heading and len(heading.group(1)) == 1)
        is_section_heading = bool(heading and not is_h1)
        if section_dense and not heading:
            v.dense = True
            v.inherited = True
        # un titre ne herite jamais : il est juge par ses propres marqueurs
        verdicts.append(v)
        if is_section_heading:
            section_dense = v.score >= HEADING_MIN_SCORE
        elif is_h1:
            section_dense = False
    return verdicts


@dataclass
class NotebookReport:
    path: str
    total_md_chars: int = 0
    dense_chars: int = 0
    dense_passages: list[PassageVerdict] = field(default_factory=list)
    all_passages: list[PassageVerdict] = field(default_factory=list)

    @property
    def part(self) -> float:
        return self.dense_chars / self.total_md_chars if self.total_md_chars else 0.0


def scan_notebook(nb_path: Path, root: Path | None = None) -> NotebookReport | None:
    """Mesure la part de prose d'activite d'un carnet.

    Rend None si le fichier est illisible ou hors perimetre (l'appelant
    distingue « rien trouve » de « pas regarde »).
    """
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    rel = None
    if root:
        try:
            rel = nb_path.resolve().relative_to(root).as_posix()
        except ValueError:
            rel = None
    report = NotebookReport(path=rel or str(nb_path))
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        report.total_md_chars += len(src)
        for verdict in judge_cell(idx, src):
            report.all_passages.append(verdict)
            if verdict.dense:
                report.dense_chars += len(verdict.text)
                report.dense_passages.append(verdict)
    return report


# ----------------------------------------------------------------------------
# Mode diff : passages AJOUTES (comparaison d'ensembles base <-> tete)
# ----------------------------------------------------------------------------
# Le ratchet ne juge pas le stock : un passage n'est mesure que s'il est
# APPARU dans la tete. La comparaison porte sur le texte normalise du
# paragraphe (whitespace replie) : un deplacement a l'identique n'est pas un
# ajout, une edition interne est un ajout du nouveau texte.

_NORM_WS_RE = re.compile(r"\s+")


def _paragraph_key(para: str) -> str:
    return _NORM_WS_RE.sub(" ", para).strip()


def _markdown_paragraphs_of_blob(blob: str | None) -> set[str]:
    """Clefs des paragraphes markdown d'un contenu .ipynb (JSON)."""
    if blob is None:
        return set()
    try:
        nb = json.loads(blob)
    except json.JSONDecodeError:
        return set()
    keys: set[str] = set()
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        for para in split_paragraphs(src):
            keys.add(_paragraph_key(para))
    return keys


@dataclass
class AddedPassage:
    path: str
    verdict: PassageVerdict


def scan_diff(diff_range: str) -> tuple[list[AddedPassage], list[str], list[str]]:
    """Rend (passages denses AJOUTES, fichiers analyses, incidents).

    ``diff_range`` de la forme ``origin/main...HEAD`` : le premier terme est
    la base, la tete est le dernier terme (un COMMIT -- la forme trois-points
    compare la base au commit, pas a l'arbre de travail ; en CI l'arbre est
    le commit de tete, donc les deux coincident). Pour chaque .ipynb modifie,
    compare l'ensemble des paragraphes markdown de la base et de la tete, et
    juge uniquement les paragraphes nouveaux.

    Un fichier AJOUTE (statut ``A``) n'a legitimement pas de blob de base :
    tous ses paragraphes sont neufs. Un fichier MODIFIE (``M``) dont le blob
    de base est ILLISIBLE n'est PAS un fichier dont tout le contenu est
    neuf : c'est un incident. Confondre les deux fait de chaque paragraphe
    du carnet un « ajout » et fabrique un refus fantome sur du contenu
    preexistant (classe mesuree a repetition sur la flotte).

    Un fichier RENOMME (statut ``RXXX\tancien\tnouveau``) est couvert au meme
    titre que ``M`` : son blob de base se lit a l'ANCIEN chemin -- sinon le
    renommage accompagne d'enrichissement echappe entierement a la garde
    (trou mesure par l'adjoint, dossier c6098782633 : ``--diff-filter=AM``
    l'ignorait). Symetriquement, une TETE absente de l'arbre de travail ou
    au JSON illisible est un INCIDENT (rc=2), jamais un « carnet analyse »
    vert muet : sans cela l'organe annonce une mesure qui n'a pas eu lieu.
    """
    try:
        proc_status = subprocess.run(
            ["git", "diff", "--name-status", "--diff-filter=AMR", diff_range],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=120, check=False,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        print(f"[ERREUR] git diff a echoue : {exc}", file=sys.stderr)
        return [], [], [f"git diff : {exc}"]
    if proc_status.returncode != 0:
        # Un `git diff` en echec rend un stdout VIDE : sans cette lecture du
        # code retour, l'organe concluait « aucun passage ajoute » sur une
        # plage illisible -- un vert muet la ou rien n'a ete mesure.
        detail = proc_status.stderr.strip()[:120] or f"rc={proc_status.returncode}"
        print(f"[ERREUR] git diff {diff_range} a echoue : {detail}", file=sys.stderr)
        return [], [], [f"git diff {diff_range} : {detail}"]
    status_lines = proc_status.stdout.splitlines()

    base_ref = diff_range.split("...")[0]
    added: list[AddedPassage] = []
    seen: set[str] = set()
    incidents: list[str] = []
    for line in status_lines:
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        status, rel = parts[0].strip(), parts[-1]
        if not rel.endswith(".ipynb") or _skipped(Path(rel)):
            continue
        seen.add(rel)
        if status.startswith("A"):
            base_blob = None  # absence legitime : le fichier est nouveau
        else:
            # Renommage : le blob de base vit a l'ANCIEN chemin (colonne du
            # milieu de la ligne RXXX). Le lire au nouveau chemin rendrait la
            # base « illisible » et ignorerait le renommage+enrichissement.
            base_rel = (
                parts[1] if status.startswith("R") and len(parts) >= 3 else rel
            )
            proc = subprocess.run(
                ["git", "show", f"{base_ref}:{base_rel}"],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=60, check=False,
            )
            if proc.returncode != 0:
                # Base illisible : on ne juge PAS (pas de refus fantome).
                incidents.append(f"{rel} : base illisible ({proc.stderr.strip()[:80]})")
                continue
            base_blob = proc.stdout
        base_keys = _markdown_paragraphs_of_blob(base_blob)
        head_path = Path(rel)
        if not head_path.is_file():
            # Tete absente : la mesure n'a pas eu lieu -- un vert muet ici
            # annoncerait « N carnets analyses » en n'en analysant aucun.
            incidents.append(f"{rel} : tete absente de l'arbre de travail")
            continue
        try:
            head_nb = json.loads(head_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            incidents.append(f"{rel} : tete illisible ({str(exc)[:80]})")
            continue
        for idx, cell in enumerate(head_nb.get("cells", [])):
            if cell.get("cell_type") != "markdown":
                continue
            src = cell.get("source", "")
            if isinstance(src, list):
                src = "".join(src)
            for verdict in judge_cell(idx, src):
                key = _paragraph_key(verdict.text)
                if key in base_keys:
                    continue
                if verdict.dense:
                    added.append(AddedPassage(rel, verdict))
    return added, sorted(seen), incidents


# ----------------------------------------------------------------------------
# Sorties
# ----------------------------------------------------------------------------


def emit_audit(reports: list[NotebookReport], top: int, strict: bool,
               threshold: float) -> int:
    flagged = [r for r in reports if r.part >= threshold]
    flagged.sort(key=lambda r: r.part, reverse=True)
    total_md = sum(r.total_md_chars for r in reports)
    total_dense = sum(r.dense_chars for r in reports)
    print(
        f"[AUDIT] {len(reports)} carnet(s) scannes, "
        f"{total_dense}/{total_md} caracteres markdown dans des passages denses "
        f"({total_dense * 100.0 / max(total_md, 1):.1f} %). "
        f"{len(flagged)} carnet(s) au-dessus du seuil de part {threshold:.2f}."
    )
    for r in flagged[:top]:
        preview = "; ".join(p.preview for p in r.dense_passages[:3])
        print(f"  part={r.part:5.1%}  {r.path}  [{preview}]")
    if flagged:
        print(
            "\nLe recit d'activite (corrigenda, cycles, lanes, verdicts) vit dans"
            "\ngit et les PR, pas dans le carnet servi a l'apprenant (#20250)."
        )
    return 1 if (strict and flagged) else 0


def emit_diff(added: list[AddedPassage], files: list[str], strict: bool,
              incidents: list[str] | None = None) -> int:
    incidents = incidents or []
    if not added:
        if incidents:
            print(
                f"[INCONNU] aucun passage d'activite dense ajoute, mais "
                f"{len(incidents)} incident(s) de mesure -- le diff n'a PAS "
                f"pu etre lu integralement :"
            )
            for inc in incidents:
                print(f"  - {inc}")
            print("  Un incident n'est ni un quitus ni une faute de la PR.")
            return 2
        print(
            f"[OK] aucun passage d'activite dense ajoute "
            f"({len(files)} carnet(s) modifie(s) analyses, mentions isolees tolerees)."
        )
        return 0
    label = "REFUS" if strict else "ADVISORY"
    print(f"[{label}] {len(added)} passage(s) d'activite dense(s) AJOUTE(S), "
          f"{len({a.path for a in added})} carnet(s) :\n")
    by_path: dict[str, list[AddedPassage]] = {}
    for a in added:
        by_path.setdefault(a.path, []).append(a)
    for path in sorted(by_path):
        for a in by_path[path]:
            mk = ", ".join(sorted({f"{name}:{snip}" for name, snip, _ in a.verdict.markers})[:6])
            print(
                f"  {path} MD[{a.verdict.cell_index}]  "
                f"score={a.verdict.score} densite={a.verdict.density:.0f}/1000  "
                f"{dense_reason(a.verdict)}"
            )
            print(f"    passage : {a.verdict.preview}")
            print(f"    marqueurs : {mk}")
        print()
    print(
        "Le recit d'activite (corrigenda, cycles, lanes, verdicts) vit dans git"
        "\net les PR, pas dans le carnet servi a l'apprenant (#20250)."
        "\nUne mention isolee est admise ; un passage dense ajoute ne l'est pas."
    )
    return 1 if strict else 0


def emit_notebook(report: NotebookReport) -> int:
    print(f"# {report.path}")
    print(
        f"part = {report.dense_chars}/{report.total_md_chars} "
        f"= {report.part:.1%} ({len(report.dense_passages)} passage(s) dense(s) "
        f"sur {len(report.all_passages)})"
    )
    for v in report.all_passages:
        state = "DENSE " if v.dense else "  -   "
        mk = ",".join(sorted({name for name, _, _ in v.markers})) or "-"
        inh = " (herite)" if v.inherited else ""
        print(f"  [{state}] MD[{v.cell_index:3d}] len={len(v.text):5d} "
              f"score={v.score:3d} dens={v.density:6.1f} [{mk}]{inh} {v.preview}")
    return 0


# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true",
                   help="audit du stock : classement par part de prose d'activite")
    g.add_argument("--diff", metavar="RANGE",
                   help="ne juge que les passages markdown AJOUTES (ex: origin/main...HEAD)")
    g.add_argument("--notebook", metavar="PATH",
                   help="detail d'un carnet : chaque passage, score, verdict")
    ap.add_argument("--strict", action="store_true",
                    help="rc=1 sur finding (defaut : advisory, rc=0)")
    ap.add_argument("--top", type=int, default=20,
                    help="nombre de carnets listes en audit (defaut 20)")
    ap.add_argument("--part-threshold", type=float, default=DEFAULT_PART_THRESHOLD,
                    help=f"seuil de part en audit --strict (defaut {DEFAULT_PART_THRESHOLD})")
    ap.add_argument("--root", default=".", help="racine du depot")
    args = ap.parse_args()

    root = Path(args.root).resolve()

    if args.notebook:
        report = scan_notebook(Path(args.notebook), root)
        if report is None:
            print(f"[ERREUR] carnet illisible : {args.notebook}", file=sys.stderr)
            return 2
        return emit_notebook(report)

    if args.all:
        reports = []
        for nb in root.rglob("*.ipynb"):
            if _skipped(nb):
                continue
            report = scan_notebook(nb, root)
            if report is not None:
                reports.append(report)
        return emit_audit(reports, args.top, args.strict, args.part_threshold)

    added, files, incidents = scan_diff(args.diff)
    return emit_diff(added, files, args.strict, incidents)


if __name__ == "__main__":
    sys.exit(main())
