#!/usr/bin/env python3
"""Detecte la perte d'une section du PLAN entre la base et la tete d'une PR (#14532).

Pourquoi cet outil existe
-------------------------
``detect_md_content_loss.py`` (#8655) mesure le volume de prose par cellule --
il attrape les troncatures (cellule 941c -> 16c) mais reste AVEUGLE aux
**disparitions de sections** quand la PR restructure les titres : une
retrogradation (`## X` -> `**X**` en intro de cellule), un renommage (`###
Objectifs d'apprentissage` -> `**Objectifs de la seance**`), ou une absorption
(`### Quand utiliser quel endpoint ?` -> tableau `### Interpretation : DBpedia
vs Wikidata`) ne font baisser AUCUN volume par cellule, parce que le contenu
reste et migre ailleurs dans le head.

Le test fondateur le montre sur #14117 (mesure premiere main du ticket,
table de la ligne 6 a 11 du body) :

| Titre de main                                          | Au head                              | Verdict                  |
|--------------------------------------------------------|--------------------------------------|--------------------------|
| `## Donnees Liees : DBpedia, Wikidata et le Web`       | intro de cell[0], sans titre H2      | retrograde -- conserve    |
| `### Objectifs d'apprentissage` (4 items)               | `**Objectifs de la seance**` (5)     | retrograde + enrichi     |
| `### Prerequis`                                         | `**Prerequis** : SW-3 Graph Ops...`  | retrograde + precise      |
| `### Quand utiliser quel endpoint ?`                    | `### Interpretation : DBpedia vs...` | renomme + enrichi        |
| `### Duree estimee : 50 minutes`                       | absent, 0 occurrence `duree`/`minutes`| **VRAIE PERTE**          |

Sans ce garde, les 4 cas de la premiere colonne passent inapercus -- le seul
cas reel (Duree estimee) reste invisible au gate markdown. Avec lui, les 4
premiers sont reconnus comme ``SUBSTANCE_FOUND_ELSEWHERE`` (retrogradation,
renommage, absorption) et le cinquieme rougit en ``LOST_SECTION``.

Trois exigences, mesurees et consignees dans le ticket, chacune FONDEE sur un
taux de sur-accusation reel :

1. **Normalisation accents + numerals** : sans elle, 10 faux positifs sur 15
   mesures brutes sur #14117 (re-accentuations comptees comme disparitions).
2. **Comparaison CONTENU, pas titres** : le diff de titres produit des
   **candidats** ; pour chaque candidat, chercher la substance dans le head
   (paragraphe en gras, section renommee, tableau d'interpretation) avant de
   conclure. Sans cette deuxieme passe, 3 des 4 accusations de la premiere
   redaction du ticket etaient des faux positifs sur des sections ameliorees.
3. **Rougir sur substance introuvable ET non arbitree** : un marker
   ``plan-loss: section assumee -- <notebook> section: <titre_normalise> : <raison>``
   dans le body de la PR justifie la disparition au cas par cas. Le marker
   est la porte assumee par l'auteur, pas une dispense ; il est visible dans
   la sortie machine comme ``LOST_SECTION_JUSTIFIED_BY_BODY``.

Comparaison STRUCTURELLEMENT bornee : un notebook ou le nombre de cellules
markdown differe entre base et head est REPORTE en ``STRUCTURE_DRIFT`` --
un finding INFORMATIF, NON bloquant. La premiere redaction court-circuitait
l'analyse sur ce drift (borne transposee de `_compare_cells` de
`detect_md_content_loss.py`, design #1 de #8655, ou la comparaison de
volume PAR CELLULE exige un appariement positionnel) ; or le diff de PLAN
compare des ENSEMBLES de titres puis cherche la substance par texte, aucune
passe n'apparie des positions : le drift ne peut y cacher aucune perte, et
la borne rougissait sur tout enrichissement AJOUTANT une cellule markdown
(le geste pedagogique standard du depot -- FP mesures : #15403 ajout pur, 0
titre perdu ; #15390). La detection de perte tourne donc toujours, drift ou
pas ; un titre reellement disparu et introuvable reste ``LOST_SECTION``
bloquant meme sous drift.

Usage
-----
    # un notebook, diff vs origin/main (head = working tree)
    python detect_notebook_plan_loss.py NB.ipynb --check
    python detect_notebook_plan_loss.py NB.ipynb --base origin/main --head origin/fix/ma-branche --check

    # sortie machine
    python detect_notebook_plan_loss.py NB.ipynb --json

    # CI gate avec justification par-section dans le body PR (#14532 item 3)
    python detect_notebook_plan_loss.py NB.ipynb --check --pr-body-file /tmp/pr-body.md

Exit codes
----------
    0 -- aucune perte detectee (ou mode non --check), y compris un notebook
         NOUVEAU (absent a la base -> rien a perdre -> exempt)
    1 -- une ou plusieurs ``LOST_SECTION`` non justifiees par le body
         (les ``LOST_SECTION_JUSTIFIED_BY_BODY`` ne bloquent PAS le verdict,
         cf. meme politique que detect_md_content_loss.py #13491)
    2 -- erreur : notebook EXISTANT illisible ou ref git introuvable. Un
         notebook NOUVEAU (absent a la base) renvoie rc=0 et non rc=2 -- la
         distinction se fait par ``path_exists_at_ref``.

Voir aussi
----------
- detect_md_content_loss.py : mesure le VOLUME par cellule ; complementaire
  (volume-aveugle aux disparitions de section, plan-aveugle aux troncatures
  intra-cellulaires).
- issue #14532 : 4 sections disparues sur 1 reel, mesure premiere main.
- issue #8655 : design #1 (STRUCTURE_DRIFT au lieu de match index-par-index).
- issue #13491 : politique de justification par-cellule transposee ici en
  justification par-section.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import unicodedata
from pathlib import Path


# Tokens consideres comme du bruit dans la normalisation d'un titre de plan
# (numerals de section `1.`, `2.3.1`, etc. + ponctuation terminale). Un titre
# `### 1. Installation et imports` et `### Installation et imports` normalisent
# identiquement -- sinon une simple renumerotation de la PR (genre 1.x vers 1.y
# pour inserer une nouvelle section) fausserait 100 % du diff.
_NUMERAL_PREFIX_RE = re.compile(r"^\s*\d+(?:\.\d+)*\.?\s+")
_TRAILING_PUNCT_RE = re.compile(r"[^\w\s]+$", re.UNICODE)


def _normalize_heading(text: str) -> str:
    """Normalise un titre de plan pour la comparaison ENSEMBLE.

    Etapes (dans l'ordre, chacune fondee sur une mesure reelle du ticket) :

    1. ``unicodedata.normalize('NFKD', text)`` decompose les caracteres
       composes (`Prerequis` -> `Prerèquis`) ; retire les marques
       diacritiques (`̀..ͯ`). Sans cette passe, 10 titres de
       #14117 sont declares disparus alors qu'ils sont re-accentues.
    2. Lowercase (insensible a `Objectifs` vs `OBJECTIFS`).
    3. Retire le prefixe numeral de section `1.`, `2.3.1`, `1.2 ` -- sinon
       une renumerotation honnete (deplacee par l'auteur pour inserer une
       section) fausse l'ensemble des titres de 100 %.
    4. Retire la ponctuation terminale (un titre `Quand utiliser X ?` et
       `Quand utiliser X` sont le meme plan).
    5. Collapse les espaces blancs.

    La normalisation est UNIQUEMENT pour la comparaison ; les titres
    remontes dans les findings sont la forme ORIGINALLE (cf. ``base_heading``
    dans le finding), pour que le reviewer pointe immediatement la section
    dans le body de la PR.
    """
    if not text:
        return ""
    nfkd = unicodedata.normalize("NFKD", text)
    ascii_form = "".join(c for c in nfkd if not unicodedata.combining(c))
    lower = ascii_form.lower()
    no_numeral = _NUMERAL_PREFIX_RE.sub("", lower)
    no_punct = _TRAILING_PUNCT_RE.sub("", no_punct := no_numeral)
    collapsed = re.sub(r"\s+", " ", no_punct).strip()
    return collapsed


def _significant_tokens(text: str) -> set[str]:
    """Tokens significatifs d'un titre pour la passe 3 (recherche fuzzy).

    Le contrat IDEMPOTENT : la fonction normalise en interne (NFKD + strip
    combining + lowercase + collapse whitespace) AVANT de tokenizer, de sorte
    qu'un caller peut lui passer un titre brut (accents, casse variables)
    sans avoir a appeller ``_normalize_heading`` au prealable. Cette API est
    plus sure que la stricte entree-normalisee : un oubli de normalisation
    cote appelant ne change pas le verdict.

    Un titre `Objectifs d'apprentissage` rend {'objectifs', 'apprentissage'}
    apres strip accents. Un titre `Prérequis opérationnels` rend le meme
    ensemble que sa version ASCII-isee -- sinon une recherche de substance
    sur un titre accentue a la base aurait un comportement non-intuitif.
    Tokens < 4 caracteres exclus (le bruit `de` / `la` / `les` ferait
    apparaitre de la substance dans le head partout). Un titre vide rend
    l'ensemble vide et la passe 3 ne le retrouvera jamais -- c'est
    exactement le comportement desire (un titre vide ne porte pas de
    substance identifiable).
    """
    if not text:
        return set()
    normalized = _normalize_heading(text)
    if not normalized:
        return set()
    return {tok for tok in re.split(r"\s+", normalized) if len(tok) >= 4}


# Patterns de substance a chercher dans le head, avec leur level de robustesse.
# Ordre du plus strict au plus souple :
#   1. Titre exact (apres normalisation) -- rare en pratique mais propre.
#   2. Titre en gras inline `**Mon titre**` (retrogradation legitime).
#   3. Au moins un token significatif dans le head, en prose bold (`**Mon ...**`)
#      -- capte une absorption dans une section renommee.
#
# Les recherches sont faites sur le head NORMALISE (memes transformations que
# pour les titres) pour absorber les variations de casse et d'accents dans
# le texte du head.

# Capture le contenu d'un bloc bold inline, et OPTIONNELLEMENT le complement
# textuel immediat (jusqu'au prochain `**`, fin de paragraphe ou point final).
# Le cas fondateur est `**Prerequis** : SW-3 Graph Operations.` -- la substance
# complete (`prerequis : sw-3 graph operations`) sert d'ancre pour la passe 2
# du predicat anti-FP, alors que le strict titre `prerequis` raterait
# l'enrichissement que l'auteur a mis dans la phrase. Le sous-groupe optionnel
# 2 capte la queue ` : SW-3 Graph Operations` quand elle existe, et le sous-
# groupe 1 seul rend la substance deja vue avant.
_BOLD_INLINE_RE = re.compile(
    r"\*\*([^*\n]+?)\*\*([^\n]*?)(?=\n\n|\*\*|\Z)",
    re.DOTALL,
)
_HEADING_LINE_RE = re.compile(r"^[ \t]*(#{1,6})\s+(.+?)\s*$", re.MULTILINE)


def extract_headings(nb: dict) -> list[tuple[int, str, str]]:
    """Retourne ``[(cell_idx, level, heading_text)]`` pour les cellules markdown.

    ``level`` est le numero de `#` (1..6) du titre -- memorise pour permettre
    une passe de robustesse future (la perte d'un H2 est plus grave que celle
    d'un H5), mais cette discrimination n'est pas exploitee dans le predicat
    actuel : un titre absent du plan reste un titre absent, quel que soit
    son niveau.

    Le SOURCE d'une cellule est generalement une liste de lignes en nbformat ;
    on joint avec saut de ligne pour permettre la detection multi-ligne.
    """
    out: list[tuple[int, str, str]] = []
    for idx, c in enumerate(nb.get("cells", [])):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", [])
        src = "\n".join(src) if isinstance(src, list) else (src or "")
        for m in _HEADING_LINE_RE.finditer(src):
            level = len(m.group(1))
            text = m.group(2).strip()
            if text:
                out.append((idx, level, text))
    return out


def _load_notebook_text(nb: dict) -> str:
    """Texte markdown complet d'un notebook pour la recherche de substance.

    Utilise pour la passe 3 (token-significatif-survit-dans-le-head). Le
    contenu des cellules markdown est joint avec double saut de ligne pour
    eviter qu'une fin de cellule colle avec un debut de cellule suivante
    cree une fausse continuite de phrase.
    """
    parts: list[str] = []
    for c in nb.get("cells", []):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", [])
        src = "\n".join(src) if isinstance(src, list) else (src or "")
        if src.strip():
            parts.append(src)
    return "\n\n".join(parts)


def _substance_present_heuristic(
    base_heading_norm: str,
    head_headings_norm: set[str],
    head_bold_norm: set[str],
    head_text_norm: str,
) -> tuple[bool, str | None]:
    """Cherche la substance d'un titre absent dans le head.

    Trois passes, du plus strict au plus souple :

    1. **Titre exact** : le titre normalise est-il parmi les titres du head ?
       Si oui, `SUBSTANCE_FOUND_RENAMED_SECTION` -- c'est une migration
       minimale (rare en pratique, mais la passe la plus sure).
    2. **Inline bold** : le titre normalise est-il le contenu d'un bloc
       `**...**` du head ? Si oui, `SUBSTANCE_FOUND_INLINE_BOLD` --
       retrogradation legitime (titre H2 -> paragraphe bold `#3966` ou
       transformation analogue).
    3. **Token significatif** : au moins un token significatif du titre survit-il
       dans le head ? Si oui, `SUBSTANCE_FOUND_TOKEN_MATCH` -- c'est le cas
       d'absorption dans une section renommee (le titre `### Quand utiliser
       quel endpoint ?` disparait, mais `endpoint` survit dans le tableau de
       comparaison `### Interpretation : DBpedia vs Wikidata`).

    Retourne ``(found, mode)``. ``found == True`` : ne PAS emettre de
    ``LOST_SECTION`` (le predicat conclut que la substance a ete preservee
    ailleurs). ``found == False`` : emettre le finding de perte.

    Les ``mode`` de retour (``None`` quand absent) sont des chaines courtes
    stables -- utiles en sortie machine pour discriminer les strategies du
    garde par poste de verite.
    """
    if base_heading_norm in head_headings_norm:
        return True, "SUBSTANCE_FOUND_RENAMED_SECTION"
    # Passe 2 -- retrogradation `### X` -> `**X** : complement`. Le titre
    # normalise peut etre un PREFIXE d'un bold inline normalise (qui inclut
    # le complement ` : SW-3 Graph Operations`). On accepte le membership
    # direct OU prefixe (espace-separe) pour absorber les deux formes :
    # `**Prerequis**` seul et `**Prerequis** : SW-3 Graph Operations`.
    for hb in head_bold_norm:
        if hb == base_heading_norm or hb.startswith(base_heading_norm + " "):
            return True, "SUBSTANCE_FOUND_INLINE_BOLD"
    base_tokens = _significant_tokens(base_heading_norm)
    if base_tokens:
        # Au moins UN token significatif survit-il dans le head normalise ?
        head_token_set = set(re.split(r"\s+", head_text_norm))
        surviving = base_tokens & head_token_set
        if surviving:
            return True, "SUBSTANCE_FOUND_TOKEN_MATCH"
    return False, None


def _normalize_for_search(text: str) -> str:
    """Normalisation pour la recherche de substance dans le head du PR.

    Meme politique que ``_normalize_heading`` : NFKD + strip diacritiques +
    lowercase + collapse espaces + strip ponctuation terminale. Applique au
    TEXTE du head (cellules entieres, blocs bold inline, paragraphes
    complets) pour que la passe 2 (bold inline) et la passe 3 (token
    significatif) absorbent les variations de casse/accents **et** de
    ponctuation terminale (un bloc `**Prerequis** : SW-3 Graph Operations.`
    doit matcher `prerequis : sw-3 graph operations`, sans le point final).

    La ponctuation INTERNE est preservee (utile pour les bold inline :
    `**Objectifs d'apprentissage**` doit etre trouvable comme
    `objectifs d'apprentissage` apres normalisation).
    """
    if not text:
        return ""
    nfkd = unicodedata.normalize("NFKD", text)
    ascii_form = "".join(c for c in nfkd if not unicodedata.combining(c))
    lower = ascii_form.lower()
    no_terminal_punct = _TRAILING_PUNCT_RE.sub("", lower)
    return re.sub(r"\s+", " ", no_terminal_punct).strip()


def _extract_bold_inline(nb: dict) -> set[str]:
    """Blocs ``**Foo**`` du head (formes normalisees).

    Une retrogradation legitime `### Prerequis` -> `**Prerequis** : SW-3
    Graph Operations` retire le titre du plan mais laisse le bloc bold
    intact. La passe 2 de ``_substance_present_heuristic`` retrouve ce cas.
    """
    out: set[str] = set()
    full = _load_notebook_text(nb)
    for m in _BOLD_INLINE_RE.finditer(full):
        body = m.group(1).strip()
        tail = (m.group(2) or "").strip() if m.lastindex and m.lastindex >= 2 else ""
        # 1. La queue complete (`Prerequis : SW-3 Graph Operations`) -- plus
        #    discriminante que le strict titre bold.
        full_phrase = (body + (" " + tail if tail else "")).strip()
        if full_phrase:
            out.add(_normalize_for_search(full_phrase))
        # 2. Le titre bold isole (fallback si la queue est vide).
        if body:
            out.add(_normalize_for_search(body))
    return out


def _worktree_root_for(nb_path: Path) -> Path | None:
    """Trouve la racine du worktree git contenant ``nb_path``.

    Necessaire pour executer ``git show <ref>:<rel_path>`` depuis le bon
    worktree : un fichier dans ``tmp_path/...`` lors d'un test pytest n'est
    PAS dans le worktree courant (cwd) -- ``git show HEAD:<abs_path_hors>``
    echoue avec ``fatal: path ... is outside repository``. On resout le
    worktree par ``git -C <dir_of_file> rev-parse --show-toplevel``,
    puis on prend le chemin RELATIF a ce worktree.

    Retourne ``None`` si le fichier n'est dans aucun worktree (cas pathologique
    ou fichier non-committed ; les helpers en aval traitent ce cas comme
    ``unreadable`` / ``absent``).
    """
    parent = nb_path.resolve().parent
    try:
        out = subprocess.run(
            ["git", "-C", str(parent), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except (FileNotFoundError, OSError):
        return None
    if out.returncode != 0:
        return None
    root = Path(out.stdout.strip())
    try:
        rel = nb_path.resolve().relative_to(root)
    except ValueError:
        return None
    return root


def read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    """Lit le contenu d'un notebook a un ref git donne via ``git show ref:path``.

    Le ``-C <worktree_root>`` est obligatoire quand ``nb_path`` n'est pas
    dans le worktree courant (cas test pytest : ``tmp_path/...``). Cf.
    ``_worktree_root_for``.

    Cf. ``detect_md_content_loss.read_notebook_at_ref`` -- meme convention.
    """
    wt = _worktree_root_for(nb_path)
    if wt is None:
        return None
    try:
        rel = nb_path.resolve().relative_to(wt).as_posix()
    except ValueError:
        return None
    try:
        out = subprocess.run(
            ["git", "-C", str(wt), "show", f"{ref}:{rel}"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except (FileNotFoundError, OSError):
        return None
    if out.returncode != 0 or not out.stdout:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def path_exists_at_ref(nb_path: Path, ref: str) -> bool:
    """True si le chemin existe a ce ref (cf. meme justification que #8655/#8912).

    Distinction EXISTANT vs NOUVEAU : un fichier absent a la base est
    EXEMPT (rien a perdre, tout est ajout) ; un fichier PRESENT mais
    illisible est un rc=2 (fail loud preserve anti-auto-desarmement).

    Utilise ``-C <worktree_root>`` comme ``read_notebook_at_ref`` pour
    tolerer les fichiers de test sous ``tmp_path``.
    """
    wt = _worktree_root_for(nb_path)
    if wt is None:
        return False
    try:
        rel = nb_path.resolve().relative_to(wt).as_posix()
    except ValueError:
        return False
    try:
        out = subprocess.run(
            ["git", "-C", str(wt), "cat-file", "-e", f"{ref}:{rel}"],
            capture_output=True, check=False,
        )
    except (FileNotFoundError, OSError):
        return False
    return out.returncode == 0


def ref_resolves(ref: str) -> bool:
    """True si le ref git existe (``git cat-file -e <ref>``). Cf. #8655."""
    try:
        out = subprocess.run(
            ["git", "cat-file", "-e", ref],
            capture_output=True, check=False,
        )
    except (FileNotFoundError, OSError):
        return False
    return out.returncode == 0


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None) -> dict:
    """Compare le PLAN d'un notebook entre base_ref et head_ref (ou working tree).

    Cf. docstring module pour la strategie des 3 passes et la justification
    de la portee STRUCTURE_DRIFT.
    """
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    if not ref_resolves(base_ref):
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} introuvable (ref git invalide)"}

    # Notebook NOUVEAU (absent a la base) : exempt. Cf. detect_md_content_loss.scan_notebook
    # -- meme politique, distinction preservee par path_exists_at_ref.
    if not path_exists_at_ref(nb_path, base_ref):
        head_h = extract_headings(nb_head)
        # Meme jeu de cles de stats que les branches comparees : le render
        # texte de main() indexe base_md_cells/head_md_cells/cell_count_stable
        # -- leur absence faisait crasher new_file en KeyError (#15147, une
        # PR de renommages traite chaque nouveau chemin comme un new_file).
        head_md_count = sum(
            1 for c in nb_head.get("cells", []) if c.get("cell_type") == "markdown"
        )
        return {
            "notebook": str(nb_path),
            "base_ref": base_ref,
            "head_ref": head_label,
            "new_file": True,
            "findings": [],
            "stats": {
                "base_md_cells": 0,
                "head_md_cells": head_md_count,
                "cell_count_stable": False,
                "base_headings": 0,
                "head_headings": len(head_h),
                "findings_count": 0,
            },
        }

    nb_base = read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} unreadable"}

    base_h_list = extract_headings(nb_base)
    head_h_list = extract_headings(nb_head)

    # Plans normalises : ensembles de titres pour le diff. L'ordre n'importe
    # pas -- un diff de PLAN est un ENSEMBLE, pas une sequence (un reorder
    # honnete ne supprime ni n'ajoute de section ; seul l'ensemble compte).
    base_norm_set: set[str] = {_normalize_heading(t) for _, _, t in base_h_list}
    head_norm_set: set[str] = {_normalize_heading(t) for _, _, t in head_h_list}

    # STRUCTURE_DRIFT : le compte de cellules markdown differe entre base et
    # head. Signal INFORMATIF, non bloquant -- le diff de plan compare des
    # ENSEMBLES de titres puis cherche la substance par texte, aucune de ces
    # passes n'apparie des positions de cellules : une fusion/scission ne
    # peut pas y cacher une perte (un titre disparu reste absent de
    # l'ensemble head, substance comprise). La premiere redaction
    # court-circuitait ici (borne transposee de detect_md_content_loss, ou
    # la comparaison de volume PAR CELLULE exige un appariement positionnel)
    # et rougissait sur tout enrichissement AJOUTANT une cellule markdown --
    # le geste pedagogique standard du depot (FP mesures : #15403, ajout
    # pur, 0 titre perdu ; #15390). La detection de perte tourne donc
    # TOUJOURS, drift ou pas. Cf. #8655 design #1 pour l'origine de la borne.
    base_md_count = sum(1 for c in nb_base.get("cells", []) if c.get("cell_type") == "markdown")
    head_md_count = sum(1 for c in nb_head.get("cells", []) if c.get("cell_type") == "markdown")
    cell_count_stable = base_md_count == head_md_count
    findings: list[dict] = []
    if not cell_count_stable:
        findings.append({
            "kind": "STRUCTURE_DRIFT",
            "base_md_cells": base_md_count,
            "head_md_cells": head_md_count,
            "detail": (
                "le nombre de cellules markdown differe entre base et head "
                "-- signal informatif, non bloquant : le diff de plan "
                "compare des ENSEMBLES de titres et reste fiable au "
                "decalage de cellules."
            ),
        })

    # Candidats : titres normalises presents a la base, absents au head.
    candidates: list[tuple[int, str, str, int, str, str]] = []
    for idx, level, text in base_h_list:
        norm = _normalize_heading(text)
        if norm and norm not in head_norm_set:
            # Stocke l'idx source + le texte original (pour le finding lisible)
            # + le normalized pour les passes de recherche.
            candidates.append((idx, level, text, idx, text, norm))

    # Pre-extraction pour les 3 passes de recherche de substance.
    head_bold_norm = _extract_bold_inline(nb_head)
    head_text_norm = _normalize_for_search(_load_notebook_text(nb_head))

    for _idx, _lvl, original_text, base_idx, base_orig, base_norm in candidates:
        found, mode = _substance_present_heuristic(
            base_norm, head_norm_set, head_bold_norm, head_text_norm,
        )
        if found:
            findings.append({
                "kind": "SUBSTANCE_FOUND",
                "base_heading": base_orig,
                "base_heading_normalized": base_norm,
                "mode": mode,
                "base_cell_idx": base_idx,
            })
        else:
            findings.append({
                "kind": "LOST_SECTION",
                "base_heading": base_orig,
                "base_heading_normalized": base_norm,
                "base_cell_idx": base_idx,
            })

    return {
        "notebook": str(nb_path),
        "base_ref": base_ref,
        "head_ref": head_label,
        "findings": findings,
        "stats": {
            "base_md_cells": base_md_count,
            "head_md_cells": head_md_count,
            "cell_count_stable": cell_count_stable,
            "base_headings": len(base_h_list),
            "head_headings": len(head_h_list),
            "candidates_count": len(candidates),
            "substance_found_count": sum(1 for f in findings if f.get("kind") == "SUBSTANCE_FOUND"),
            "lost_section_count": sum(1 for f in findings if f.get("kind") == "LOST_SECTION"),
            "findings_count": len(findings),
        },
    }


def _parse_pr_body_markers(pr_body: str, notebook_path: Path) -> set[str]:
    """Parse les markers ``plan-loss: section assumee -- <nb> section: <titre> : <raison>``.

    Le titre est matche apres NORMALISATION (le body PR est ecrit par un humain,
    avec accents et casse variables ; on normalise pour absorber). La clef de
    justification est la forme normalisee du titre (``base_heading_normalized``
    dans le finding). Cf. `_parse_pr_body_markers` de
    ``detect_md_content_loss.py`` pour la meme politique par-cellule (#13491).

    Un marker est valide si TOUT est present : mot-cle ``plan-loss``, token
    ``section assumee``, chemin ou basename du notebook, token ``section:
    <titre>`` (le titre est tout ce qui suit ``section:`` jusqu'au `` :``
    final), et une raison non vide. Un marker malforme est inerte (ne leve
    AUCUNE suppression sur aucun finding -- comportement preserve).
    """
    if not pr_body:
        return set()
    NB_TAIL_RE = r"[^\s:]+"
    PAT = re.compile(
        r"^plan-loss\s*:\s*section\s+assum[eé]+(?:e|ée)\s*(?:--|—)\s*"
        r"(?P<nb>" + NB_TAIL_RE + r")"
        r"\s+section\s*:\s*(?P<title>.+?)"
        r"\s*:\s*(?P<reason>\S.*?)$",
        re.MULTILINE,
    )
    nb_name = notebook_path.name
    justified: set[str] = set()
    for m in PAT.finditer(pr_body):
        nb_token = m.group("nb").rstrip("/").rstrip(":")
        if nb_token != nb_name and not nb_token.endswith("/" + nb_name):
            continue
        title_raw = m.group("title").strip()
        if not title_raw:
            continue
        justified.add(_normalize_heading(title_raw))
    return justified


def _apply_body_justifications(findings: list[dict], justified_norm_titles: set[str]) -> list[dict]:
    """Supprime les findings ``LOST_SECTION`` justifies par le body, en gardant une trace.

    Trace preservee (cf. ``_apply_body_justifications`` de
    ``detect_md_content_loss.py`` -- meme politique) : un finding
    ``LOST_SECTION`` sur un titre normalise justifie est remplace par un
    finding de meme cle mais de kind ``LOST_SECTION_JUSTIFIED_BY_BODY``. La
    sortie n'est pas masquee : un auditeur en review voit ce qui s'est
    passe ; seul le verdict binaire du ``--check`` le rend vert.
    """
    if not justified_norm_titles:
        return findings
    out: list[dict] = []
    for f in findings:
        if (
            f.get("kind") == "LOST_SECTION"
            and f.get("base_heading_normalized") in justified_norm_titles
        ):
            f2 = dict(f)
            f2["kind"] = "LOST_SECTION_JUSTIFIED_BY_BODY"
            out.append(f2)
        else:
            out.append(f)
    return out


def _blocking_findings(findings: list[dict]) -> list[dict]:
    """Findings qui font rougir ``--check`` : ``LOST_SECTION`` non justifiees.

    ``SUBSTANCE_FOUND`` (perte apparente, substance retrouvee ailleurs) et
    ``STRUCTURE_DRIFT`` (signal informatif de compte de cellules -- la
    detection de perte tourne malgre lui, cf. scan_notebook) ne bloquent
    pas, pas plus que les ``LOST_SECTION_JUSTIFIED_BY_BODY``.
    """
    return [f for f in findings
            if not str(f.get("kind", "")).endswith("JUSTIFIED_BY_BODY")
            and f.get("kind") not in ("SUBSTANCE_FOUND", "STRUCTURE_DRIFT")]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("notebook", type=Path, help="Chemin vers le .ipynb")
    p.add_argument("--base", default="origin/main", help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None, help="Ref git du head (defaut working tree)")
    p.add_argument("--check", action="store_true", help="Exit 1 si perte detectee (CI)")
    p.add_argument("--json", action="store_true", help="Sortie JSON machine")
    p.add_argument(
        "--pr-body-file", type=Path, default=None,
        help="Chemin vers un fichier contenant le body de la PR. Y cherche les "
             "markers `plan-loss: section assumee -- <notebook> section: "
             "<titre> : <raison>` qui justifient un finding LOST_SECTION sur "
             "le meme couple (notebook, base_heading_normalized). Marker "
             "absent ou invalide = comportement actuel (rc=1 inchange). "
             "Defaut : la variable d'env `PLAN_LOSS_PR_BODY_FILE` si "
             "definie, sinon aucun.",
    )
    p.add_argument(
        "--pr-body", default=None,
        help="Contenu literal du body de la PR. Equivalent a `--pr-body-file` "
             "mais evite d'ecrire le body dans un fichier sur le runner. "
             "Defaut : la variable d'env `PLAN_LOSS_PR_BODY` si definie "
             "(prioritaire sur --pr-body-file / PLAN_LOSS_PR_BODY_FILE).",
    )
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"ERROR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    # Resolution du body PR (mem politique que detect_md_content_loss.main).
    pr_body: str | None = None
    if args.pr_body is not None:
        pr_body = args.pr_body
    elif env_body := os.environ.get("PLAN_LOSS_PR_BODY"):
        pr_body = env_body
    else:
        pr_body_file: Path | None = args.pr_body_file
        if pr_body_file is None:
            env_file = os.environ.get("PLAN_LOSS_PR_BODY_FILE")
            if env_file:
                pr_body_file = Path(env_file)
        if pr_body_file is not None:
            try:
                pr_body = pr_body_file.read_text(encoding="utf-8", errors="replace")
            except (OSError, UnicodeDecodeError) as e:
                print(f"ERROR: --pr-body-file illisible: {e}", file=sys.stderr)
                return 2

    result = scan_notebook(args.notebook, args.base, args.head)

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        return 2

    # Justification par-section depuis le body de la PR (port de la politique
    # #13491 au grain section plutot que cellule). Meme cle de comptage :
    # les JUSTIFIED restent dans la sortie machine (transparence) mais le
    # verdict binaire --check ignore les *_JUSTIFIED_BY_BODY.
    if pr_body is not None:
        justified = _parse_pr_body_markers(pr_body, args.notebook)
        if justified:
            result["findings"] = _apply_body_justifications(result["findings"], justified)
            result["stats"]["findings_count"] = sum(
                1 for f in result["findings"]
                if not str(f.get("kind", "")).endswith("JUSTIFIED_BY_BODY")
            )
            result["stats"]["findings_count_with_justified"] = len(result["findings"])
            result["stats"]["justified_by_body_sections"] = sorted(justified)

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        nb = result["notebook"]
        st = result["stats"]
        fins = result["findings"]
        print(f"[NOTEBOOK] {nb}")
        print(f"[BASE]     {result['base_ref']}")
        print(f"[HEAD]     {result['head_ref']}")
        if result.get("new_file"):
            print("[NEW FILE] absent a la base -> exempt de plan-loss "
                  "(rien a perdre, tout est ajout).")
        print(
            f"[STATS]    md_cells base={st['base_md_cells']} head={st['head_md_cells']} "
            f"stable={st['cell_count_stable']} | headings base={st['base_headings']} "
            f"head={st['head_headings']} | candidates={st.get('candidates_count', '-')} "
            f"substance_found={st.get('substance_found_count', '-')} "
            f"lost_section={st.get('lost_section_count', '-')} | "
            f"findings={st['findings_count']}"
        )
        if st.get("justified_by_body_sections"):
            print(f"[JUSTIFIED_BY_BODY] {len(st['justified_by_body_sections'])} section(s) "
                  f"assumee(s) par marqueur de body.")
        if fins:
            print("\n[FINDINGS]")
            for f in fins:
                if f["kind"] == "STRUCTURE_DRIFT":
                    print(f"  - {f['kind']}: base={f['base_md_cells']} -> "
                          f"head={f['head_md_cells']} cellules markdown -- {f['detail']}")
                elif f["kind"] == "SUBSTANCE_FOUND":
                    print(f"  - {f['kind']}: '{f['base_heading']}' -> {f['mode']} "
                          f"(cellule base {f['base_cell_idx']})")
                elif f["kind"] in ("LOST_SECTION", "LOST_SECTION_JUSTIFIED_BY_BODY"):
                    suffix = " -- reecriture assumee par marqueur de body" \
                        if f["kind"].endswith("JUSTIFIED_BY_BODY") else ""
                    print(f"  - {f['kind']}: '{f['base_heading']}' "
                          f"(cellule base {f['base_cell_idx']}, normalise "
                          f"'{f['base_heading_normalized']}'){suffix}")

    if args.check and result["findings"]:
        if _blocking_findings(result["findings"]):
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
