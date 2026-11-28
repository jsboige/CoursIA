"""Ratchet gate: code cells of changed notebooks must keep a minimum comment
density (issue #26782, user Concerns #26607 / #26616 du 15/11).

« le code est non commenté et tres difficile a lire. Le CI devrait le
rejeter sur ces deux bases. » Aucun organe du depot ne mesurait la densite
de commentaires (recherche ``comment_density|comment_ratio`` dans scripts/ :
0 resultat au 15/11). Mesure de premier passage sur main (``88727241266``) :
C# 331 carnets, mediane 21,5 %, p10 4,1 %, 38 sous 5 % ; Python 1456 carnets,
mediane 17,9 %, p10 7,6 %, 69 sous 5 %. Les tetes des PRs motivees : Z3-20
C# (#26613) 1,0 % ; Ataraxos 13h C# (#26616) 3,3 % ; Frontieres-05 Python
(#26607) 3,7 % -- 5 a 20 fois sous la mediane, et rare sur le stock (107
carnets sur 1787). L'incident est donc un APPORT du Marathon II, pas une
dette generale : le ratchet ne juge que le diff.

Classification par TOKENIZER, pas par regex (spec point 1) : la mesure de
l'issue etait un premier passage regex ; l'organe classe chaque ligne
physique par token -- Python via ``tokenize`` (stdlib), C# par machine a
etats consciente des chaines (``//``, ``/* */``, ``@"..."`` verbatim,
``$"..."`` interpole, echappements, litteraux char). Un ``#`` ou un ``//``
DANS une chaine ne compte pas comme commentaire. La classification des
lignes est celle posee par #26694 pour les marqueurs de stub (lignes de
commentaire seules lues, jamais la chaine voisine).

Classes de ligne (une ligne = exactement une classe) :

  CODE         porte au moins un token significatif hors commentaire
  COMMENT      porte au moins un token commentaire (ligne entiere OU fin de
               ligne -- un commentaire de fin de ligne compte, spec #26782 ;
               la ligne porte alors COMMENT meme si elle porte aussi du code)
  STRING_CONT  continuation d'une chaine multi-lignes (docstring, verbatim) :
               ni code ni commentaire -- une docstring n'est pas un ``#``
  BLANK        vide ou whitespace
  EXCLUDED     magies et directives : ``%magic``, ``!shell``, ``#r``,
               ``#!polyglot``, directives preprocesseur C#

Densite = lignes COMMENT / lignes CODE. Une ligne a commentaire de fin de
ligne compte au numerateur ET reste une ligne de code au denominateur
(un commentaire de fin de ligne compte, spec #26782) : sans cela, un carnet
dont chaque ligne porterait un trailing reduirait le denominateur a zero et
echapperait au gate par construction. Une ligne entiere commentaire
n'entre qu'au numerateur.

Le ratchet (spec point 2), bloquant, borne au diff comme ses freres
``check_output_failure_text.py`` / ``check_output_collapse.py`` :

  - carnet AJOUTE par la PR : rouge si >= 40 lignes de code ET densite < 5 %
    -- c'est le coeur de la demande user (« le CI devrait le rejeter ») ;
  - carnet MODIFIE : rouge si >= 40 lignes de code ET la densite PASSE sous
    5 % (base >= 5 % -> tete < 5 %) ;
  - le stock de main n'est JAMAIS juge par le gate : un carnet deja sous le
    seuil a la base qui y reste est signale ADVISORY (ALREADY_BELOW), pas
    rouge -- c'est la dette du plan de remediation (§I de #26782), pas celle
    de la PR. Un carnet qui retombe sous 40 lignes de code n'est pas juge.

Second axe « difficile a lire » (spec point 3), ADVISORY (mesurer avant de
bloquer), calcule sur les carnets changes :

  LONG_LINE      ligne de cellule code de plus de 120 caracteres
  LONG_BLOCK     plus de 60 lignes consecutives CODE/STRING_CONT sans un
                 seul commentaire dans la meme cellule
  ONE_LETTER     identifiant d'une lettre hors indice de boucle -- exemptes :
                 variables de ``for X in`` / ``for X, Y in`` / comprehension
                 (Python), ``for (T X =`` / ``foreach (var X in`` (C#) ;
                 heuristique ANNOUNCEE, pas une analyse semantique

Un organe de densite peut pousser au commentaire de remplissage ; les
reviewers verifient qu'un commentaire dit POURQUOI ou CE QUE REPRESENTE une
variable, pas qu'il paraphrase la ligne (spec #26782, dernier alinea).

Usage:
    python check_code_comment_density.py <base-ref> [--json]
    python check_code_comment_density.py <base-ref> --readability [--json]
    python check_code_comment_density.py --all [--json]
    python check_code_comment_density.py --self-test

Le mode ratchet resoud la base en merge-base(base, HEAD) : une branche en
retard de sa base est jugee sur son seul diff (convention #11528, reprise
de check_output_failure_text.py). Le mode ``--readability`` ne JAMAIS
gater : exit 0, findings imprimés (enregistre blocking=False).

Exit 1 (mode ratchet seul) ssi au moins un carnet change est rouge.
"""

from __future__ import annotations

import argparse
import io
import json
import re
import subprocess
import sys
import tokenize
from pathlib import Path

# Seuils de la spec #26782 (point 2 et point 3).
MIN_DENSITY = 0.05          # 5 % de lignes de commentaire
MIN_CODE_LINES = 40         # en dessous : carnet non juge
LONG_LINE_CHARS = 120       # axe lisibilite, advisory
LONG_BLOCK_LINES = 60       # axe lisibilite, advisory

# Exclusions de livraison, comme check_output_failure_text.py.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")

BS = "\\"

CODE = "CODE"
COMMENT = "COMMENT"
STRING_CONT = "STRING_CONT"
BLANK = "BLANK"
EXCLUDED = "EXCLUDED"

PY_LANGS = {"python", "python3", "ipykernel"}
CSHARP_LANGS = {"csharp", "c#", "cs"}
FSHARP_LANGS = {"fsharp", "f#", "fs"}


# ---------------------------------------------------------------------------
# Classification Python : par tokenizer stdlib.
# ---------------------------------------------------------------------------

_MAGIC_PREFIXES = ("%", "!", "?")


def _excluded_py_line(stripped: str) -> bool:
    """Ligne magie/directive Python : exclue des deux compteurs."""
    if not stripped:
        return False
    if stripped.startswith(_MAGIC_PREFIXES):
        return True
    # `#r "NuGet: ..."` (polyglot .NET), `#!csharp`, `#!shebang-like`.
    if stripped.startswith("#!") or re.match(r"^#r[\s\"']", stripped):
        return True
    return False


def classify_python(source: str, degraded: list | None = None) -> list[str]:
    """Classe chaque ligne physique d'une cellule Python par tokenizer.

    En cas d'erreur de tokenisation (source non-Python dans une cellule
    python, syntaxe exotique), repli DEGRADE sur une classification par
    ligne ; le repli s'annonce en ajoutant ``"python_tokenize"`` a la liste
    ``degraded`` fournie par l'appelant, que ``notebook_stats`` publie sous
    ``py_degraded``. Mieux vaut une mesure approchee mais SIGNALEE qu'un
    carnet invisible ou une mesure presentee comme exacte.
    """
    lines = source.splitlines()
    n = len(lines)
    classes = [BLANK] * n
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        if degraded is not None:
            degraded.append("python_tokenize")
        return _classify_python_naive(source)
    string_spans: list[tuple[int, int]] = []
    for tok in tokens:
        row = tok.start[0]
        if row > n:
            continue
        i = row - 1
        if tok.type == tokenize.COMMENT:
            classes[i] = COMMENT
        elif tok.type in (tokenize.NL, tokenize.NEWLINE, tokenize.ENDMARKER,
                          tokenize.INDENT, tokenize.DEDENT, tokenize.ENCODING):
            if classes[i] == BLANK:
                classes[i] = BLANK
        else:
            # STRING, NAME, NUMBER, OP... : ligne de code.
            if classes[i] != COMMENT:
                classes[i] = CODE
            if tok.type == tokenize.STRING and tok.end[0] > tok.start[0]:
                string_spans.append((tok.start[0], tok.end[0]))
    # Interieur d'une chaine multi-lignes : ni code ni commentaire (les
    # lignes n'ont emis aucun token propre ; on les marque explicites pour
    # ne pas les laisser BLANK par accident).
    for start, end in string_spans:
        for row in range(start + 1, min(end, n) + 1):
            i = row - 1
            if classes[i] == BLANK:
                classes[i] = STRING_CONT
    # Magies et directives, hors chaine : une ligne qui COMMENCE par `%`,
    # `!`, `?`, `#!` ou `#r ` n'est ni code ni commentaire pour la densite
    # (IPython l'exclut deja de l'execution Python). Le tokenizer produit
    # des tokens OP/NAME sur `%matplotlib` et un COMMENT sur `#!csharp` :
    # l'override porte sur toute classe sauf STRING_CONT.
    for i, line in enumerate(lines):
        if classes[i] == STRING_CONT:
            continue
        if _excluded_py_line(line.strip()):
            classes[i] = EXCLUDED
    return classes


def _split_py_code_comment(line: str) -> tuple[str, bool, str | None]:
    """Coupe une ligne en (code, a_un_commentaire, triple_ouvert).

    Un ``#`` n'ouvre un commentaire que s'il est HORS CHAINE : dans
    ``s = "a # b"`` c'est du texte. ``triple_ouvert`` rend le delimiteur
    ``\"\"\"``/``'''`` laisse ouvert en fin de ligne (docstring multi-lignes).
    """
    i, n = 0, len(line)
    quote: str | None = None
    while i < n:
        if quote is not None:
            if line[i] == "\\":
                i += 2
                continue
            if line.startswith(quote, i):
                i += len(quote)
                quote = None
                continue
            i += 1
            continue
        for triple in ('"""', "'''"):
            if line.startswith(triple, i):
                quote = triple
                i += 3
                break
        else:
            ch = line[i]
            if ch in ('"', "'"):
                quote = ch
            elif ch == "#":
                return line[:i], True, None
            i += 1
    opened = quote if quote in ('"""', "'''") else None
    return line, False, opened


def _classify_python_naive(source: str) -> list[str]:
    """Repli ligne a ligne quand ``tokenize`` echoue (mesure DEGRADEE).

    Mime les classes du tokenizer : une ligne portant un commentaire est
    COMMENT meme si du code la precede (regle de densite, cf
    ``_has_code_before_comment``) ; un ``#`` dans une chaine n'est pas un
    commentaire ; l'interieur d'une docstring est STRING_CONT, pas du code.
    """
    out: list[str] = []
    triple: str | None = None
    for line in source.splitlines():
        stripped = line.strip()
        if triple is not None:
            out.append(STRING_CONT)
            if triple in stripped:
                triple = None
            continue
        if not stripped:
            out.append(BLANK)
            continue
        if _excluded_py_line(stripped):
            out.append(EXCLUDED)
            continue
        _code, has_comment, opened = _split_py_code_comment(line)
        # La ligne d'ouverture d'une docstring porte le token chaine : le
        # tokenizer la classe CODE (test_docstring_interior...).
        out.append(COMMENT if has_comment else CODE)
        if opened is not None:
            triple = opened
    return out


# ---------------------------------------------------------------------------
# Classification C# / F# : machine a etats consciente des chaines.
# Etats portes d'une ligne a l'autre : code, block_comment (``/* */`` ou
# ``(* *)``), string (echappements ``\\``), verbatim (``@"..."``, ``""``).
# Un ``#`` DANS une chaine ne compte pas (spec point 1) ; une directive
# preprocesseur (``#region``, ``#pragma``, ``#r``, ``#!polyglot``) est
# EXCLUDED, pas commentaire.
# ---------------------------------------------------------------------------

def classify_csharp(source: str, fsharp: bool = False) -> list[str]:
    """Classification ligne par ligne, etat d'ENTREE porte entre lignes."""
    classes: list[str] = []
    state = "code"
    for line in source.splitlines():
        stripped = line.strip()
        if state in ("string", "verbatim"):
            # Interieur de chaine multi-lignes : la ligne est une
            # continuation SAUF si elle ferme la chaine ET porte du VRAI
            # code apres la fermeture -- une queue de ponctuation (`";`,
            # `");`) n'est pas du code, la compter gonflerait le
            # denominateur d'un point par chaine verbatim.
            before, closed, after, new_state = _split_close_string(line, state)
            tail_code = after.strip().strip(");, \t")
            if closed and tail_code:
                classes.append(CODE)
            else:
                classes.append(STRING_CONT)
            state = new_state
            continue
        if state == "block_comment":
            has_comment = True
            new_state = _block_close(line, fsharp)
            classes.append(COMMENT)
            state = new_state
            continue
        if stripped.startswith("#"):
            classes.append(EXCLUDED)
            continue
        has_comment, has_code, new_state, rest_is_comment = _scan_csharp_line(
            line, fsharp)
        if rest_is_comment:
            # `//` rencontre : le reste de la ligne est commentaire ; la
            # ligne est COMMENT (avec ou sans code avant).
            classes.append(COMMENT)
        elif has_comment and has_code:
            classes.append(COMMENT)
        elif has_comment:
            classes.append(COMMENT)
        elif has_code:
            classes.append(CODE)
        else:
            classes.append(BLANK)
        state = new_state
    return classes


def _block_close(line: str, fsharp: bool) -> str:
    closer = "*)" if fsharp else "*/"
    idx = line.find(closer)
    if idx < 0:
        return "block_comment"
    rest = line[idx + 2:]
    # Simplification assumee : du code peut suivre la fermeture sur la meme
    # ligne (rare en carnets) ; on rouvre l'analyse a partir de la fin.
    _, _, new_state, _ = _scan_csharp_line(rest, fsharp)
    return new_state


def _split_close_string(line: str, state: str):
    """Cherche la fermeture de chaine dans une ligne de continuation.

    Rend (avant, fermee ?, apres, etat_sortie).
    """
    i = 0
    while i < len(line):
        ch = line[i]
        if state == "verbatim" and ch == '"':
            if i + 1 < len(line) and line[i + 1] == '"':
                i += 2
                continue
            return line[:i], True, line[i + 1:], "code"
        if state == "string" and ch == "\\":
            i += 2
            continue
        if state == "string" and ch == '"':
            return line[:i], True, line[i + 1:], "code"
        i += 1
    return line, False, "", state


def _scan_csharp_line(line: str, fsharp: bool):
    """Analyse d'une ligne partant de l'etat code.

    Rend (has_comment, has_code, etat_sortie, reste_commentaire).
    """
    has_comment = False
    has_code = False
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]
        nxt = line[i + 1] if i + 1 < n else ""
        if not fsharp and ch == "/" and nxt == "/":
            return has_comment, has_code, "code", True
        if fsharp and ch == "/" and nxt == "/":
            return has_comment, has_code, "code", True
        if not fsharp and ch == "/" and nxt == "*":
            has_comment = True
            i += 2
            # La fin de ligne peut fermer le bloc.
            j = i
            closed = False
            while j < n:
                if line[j] == "*" and j + 1 < n and line[j + 1] == "/":
                    closed = True
                    break
                j += 1
            if closed:
                i = j + 2
                continue
            return has_comment, has_code, "block_comment", False
        if fsharp and ch == "(" and nxt == "*":
            has_comment = True
            i += 2
            j = i
            closed = False
            while j < n:
                if line[j] == "*" and j + 1 < n and line[j + 1] == ")":
                    closed = True
                    break
                j += 1
            if closed:
                i = j + 2
                continue
            return has_comment, has_code, "block_comment", False
        if ch == "@" and nxt == '"':
            has_code = True
            i += 2
            j = i
            closed = False
            while j < n:
                if line[j] == '"':
                    if j + 1 < n and line[j + 1] == '"':
                        j += 2
                        continue
                    closed = True
                    break
                j += 1
            if closed:
                i = j + 1
                continue
            return has_comment, has_code, "verbatim", False
        if ch == "$" and nxt == '"':
            # Chaine interpolee : la fermeture echappee suit les regles de
            # la chaine reguliere ($"{x}" -- les {{ }} sont des accolades
            # de contenu, pas des fermetures).
            has_code = True
            i += 2
            nxt_i = _consume_regular_string(line, i)
            if isinstance(nxt_i, int):
                i = nxt_i
                continue
            return has_comment, has_code, "string", False
        if ch == '"':
            has_code = True
            i += 1
            nxt_i = _consume_regular_string(line, i)
            if isinstance(nxt_i, int):
                i = nxt_i
                continue
            return has_comment, has_code, "string", False
        if ch == "'":
            has_code = True
            j = i + 1
            if j < n and line[j] == "\\":
                j += 2
            while j < n and line[j] != "'":
                j += 1
            i = j + 1 if j < n else n
            continue
        if not ch.isspace():
            has_code = True
        i += 1
    return has_comment, has_code, "code", False


def _consume_regular_string(line: str, i: int):
    """Consomme une chaine "..." a partir de i (apres l'ouvrant).

    Rend l'index APRES la fermeture, ou None si non fermee sur la ligne.
    """
    n = len(line)
    while i < n:
        if line[i] == "\\":
            i += 2
            continue
        if line[i] == '"':
            return i + 1
        i += 1
    return None


# ---------------------------------------------------------------------------
# Langue d'une cellule / d'un carnet.
# ---------------------------------------------------------------------------

def _norm(lang: str | None) -> str | None:
    if not lang:
        return None
    l = lang.strip().lower()
    if l in PY_LANGS or l.startswith("python"):
        return "python"
    if l in CSHARP_LANGS or "csharp" in l:
        return "csharp"
    if l in FSHARP_LANGS or "fsharp" in l:
        return "fsharp"
    return None


def cell_language(cell: dict, kernel_lang: str | None) -> str | None:
    """Langue d'une cellule : metadata, magie polyglot, puis kernel."""
    meta = cell.get("metadata") or {}
    lang = _norm(meta.get("language"))
    if lang:
        return lang
    src_lines = cell.get("source") or []
    first = ""
    for piece in src_lines:
        first = piece
        break
    m = re.match(r"^#!\s*(csharp|fsharp|python|pwsh)\b", first.strip().lower())
    if m:
        return _norm(m.group(1))
    return kernel_lang


def kernel_language(nb: dict) -> str | None:
    ks = (nb.get("metadata") or {}).get("kernelspec") or {}
    name = str(ks.get("name") or "").lower()
    display = str(ks.get("display_name") or "").lower()
    for blob in (name, display):
        lang = _norm(blob)
        if lang:
            return lang
        if ".net" in blob or "polyglot" in blob:
            # .NET Interactive, langue par cellule ; csharp par defaut.
            return "csharp"
    return None


# ---------------------------------------------------------------------------
# Statistiques d'un carnet.
# ---------------------------------------------------------------------------

def notebook_stats(nb: dict) -> dict:
    """Compte par langue + densite agregee du carnet."""
    klang = kernel_language(nb)
    per_lang: dict[str, dict] = {}
    long_lines = 0
    long_blocks = 0
    one_letter_hits = 0
    unknown_lang_cells = 0
    degraded_cells = 0
    for cell in nb.get("cells", []) or []:
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source") or [])
        if not source.strip():
            continue
        lang = cell_language(cell, klang)
        if lang is None:
            unknown_lang_cells += 1
            continue
        if lang == "python":
            fallbacks: list = []
            classes = classify_python(source, degraded=fallbacks)
            degraded_cells += 1 if fallbacks else 0
        else:
            classes = classify_csharp(source, fsharp=(lang == "fsharp"))
        bucket = per_lang.setdefault(
            lang, {"code": 0, "comment": 0, "cells": 0})
        bucket["cells"] += 1
        bucket["code"] += sum(1 for c in classes if c == CODE)
        bucket["comment"] += sum(1 for c in classes if c == COMMENT)
        # Trailing comments restent des lignes de code au denominateur (voir
        # docstring) : une ligne COMMENT qui ne COMMENCE pas par le marqueur
        # porte du code devant son commentaire.
        bucket["code"] += sum(
            1 for line, c in zip(source.splitlines(), classes)
            if c == COMMENT and _has_code_before_comment(line, lang))
        # Axe lisibilite (advisory) : calcule sur les memes classes.
        for line in source.splitlines():
            if len(line) > LONG_LINE_CHARS:
                long_lines += 1
        run = 0
        for c in classes:
            if c in (CODE, STRING_CONT):
                run += 1
                if run == LONG_BLOCK_LINES + 1:
                    long_blocks += 1
            elif c == COMMENT:
                run = 0
        one_letter_hits += _one_letter_count(source, lang)
    code_lines = sum(b["code"] for b in per_lang.values())
    comment_lines = sum(b["comment"] for b in per_lang.values())
    density = (comment_lines / code_lines) if code_lines else None
    return {
        "code_lines": code_lines,
        "comment_lines": comment_lines,
        "density": density,
        "per_language": per_lang,
        "unknown_language_cells": unknown_lang_cells,
        # Cellules Python mesurees par le repli (tokenize en echec) : la
        # mesure de ce carnet est approchee, et elle le DIT.
        "py_degraded": degraded_cells,
        "readability": {
            "long_lines": long_lines,
            "long_blocks": long_blocks,
            "one_letter_identifiers": one_letter_hits,
        },
    }


def _has_code_before_comment(line: str, lang: str) -> bool:
    """Une ligne classee COMMENT porte-t-elle du code devant le marqueur ?

    Proxy assume : la ligne entiere commence par le marqueur (``#``,
    ``//``, ``/*``, ``(*``) ; toute autre ligne COMMENT est un commentaire
    de fin de ligne -- le tokenizer a deja confirme le token commentaire,
    la question n'est que la presence d'un prefixe de code.
    """
    stripped = line.strip()
    if lang == "python":
        return not stripped.startswith("#")
    starters = ("//", "/*", "(*") if lang != "python" else ("#",)
    return not stripped.startswith(starters)


_LOOP_EXEMPT = re.compile(
    r"for\s+[A-Za-z_]\s*(?:,\s*[A-Za-z_]\s*)*in\b"       # python for
    r"|for\s*\(\s*[A-Za-z_][\w<>.]*\s+[A-Za-z_]\s*="      # csharp for init
    r"|foreach\s*\(\s*[\w<>.]+\s+[A-Za-z_]\s+in\b"        # csharp foreach
)

_IDENT = re.compile(r"\b[A-Za-z_]\b")


def _one_letter_count(source: str, lang: str) -> int:
    """Identifiants d'une lettre hors indices de boucle (heuristique).

    Exemptes : variables de boucle detectees par les motifs ``_LOOP_EXEMPT``
    sur la MEME cellule. Le compte restant est un signal de lisibilite,
    pas une analyse semantique -- advisory uniquement.
    """
    exempt = set(m.group(0) for m in _LOOP_EXEMPT.finditer(source))
    # Le motif capture la clause ; extraire les lettres seules.
    exempt_letters = set(re.findall(r"\b[A-Za-z_]\b", " ".join(exempt)))
    stripped = strip_comments(source, lang)
    hits = [m.group(0) for m in _IDENT.finditer(stripped)
            if m.group(0) not in exempt_letters]
    return len(hits)


def strip_comments(source: str, lang: str) -> str:
    """Source sans les commentaires (pour l'axe one-letter)."""
    if lang == "python":
        classes = classify_python(source)
    else:
        classes = classify_csharp(source, fsharp=(lang == "fsharp"))
    lines = source.splitlines()
    kept = [line for line, c in zip(lines, classes) if c != COMMENT]
    return "\n".join(kept)


# ---------------------------------------------------------------------------
# Git plumbing (convention check_output_failure_text.py).
# ---------------------------------------------------------------------------

def git(*args, cwd=None):
    try:
        out = subprocess.run(["git", "-c", "core.quotePath=false", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def resolve_base(base, cwd=None):
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


def diff_notebooks(base, head="HEAD", cwd=None):
    """Carnets changes : ``[(chemin_tete, chemin_origine)]``.

    ``--name-status -M -C`` rend ``R<score>``/``C<score>`` suivis du chemin
    d'ORIGINE puis du nouveau. ``--name-only`` ne rend que le nouveau : la
    base se lisait alors au nouveau chemin (absent a la base), le carnet
    passait pour un AJOUT et un ``git mv`` pur -- qui n'ajoute rien --
    rougissait. La base se lit desormais au chemin d'origine.
    """
    raw = git("diff", "--name-status", "-z", "-M", "-C",
              "--diff-filter=ACMR", base, head, "--", "*.ipynb", cwd=cwd)
    if raw is None:
        return []
    fields = raw.split("\0")
    pairs = []
    i = 0
    while i < len(fields):
        status = fields[i].strip()
        if not status:
            i += 1
            continue
        if status[0] in ("R", "C"):
            if i + 2 >= len(fields):
                break
            origin, target = fields[i + 1], fields[i + 2]
            i += 3
        else:
            if i + 1 >= len(fields):
                break
            origin = target = fields[i + 1]
            i += 2
        target_posix = target.strip().replace(BS, "/")
        origin_posix = origin.strip().replace(BS, "/")
        if not target_posix:
            continue
        if any(m in "/" + target_posix for m in EXCLUDE_MARKERS):
            continue
        pairs.append((target_posix, origin_posix))
    return sorted(pairs)


def changed_notebooks(base, head="HEAD", cwd=None):
    """Chemins de TETE des carnets changes (compatibilite)."""
    return [target for target, _origin in diff_notebooks(base, head, cwd=cwd)]


def all_notebooks(cwd=None):
    out = git("ls-files", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace(BS, "/")
        if posix and not any(m in "/" + posix for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def read_notebook_at(ref, path, cwd=None):
    if ref is None:
        try:
            # ``cwd`` n'est pas decoratif : sans lui la tete se lit relative
            # au cwd du PROCESSUS, pas a celui du depot mesure (un appel
            # depuis un autre repertoire rend « carnet absent »).
            file = Path(cwd) / path if cwd else Path(path)
            return json.loads(file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return None
    raw = git("show", ref + ":" + path, cwd=cwd)
    if raw is None:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


# ---------------------------------------------------------------------------
# Verdicts.
# ---------------------------------------------------------------------------

def verdict(base_stats: dict | None, head_stats: dict) -> dict:
    """Rouge ssi apport/regression de la PR (spec #26782 point 2)."""
    head_lines = head_stats["code_lines"]
    head_dens = head_stats["density"]
    if head_lines < MIN_CODE_LINES:
        return {"verdict": "NOT_JUDGED",
                "reason": f"{head_lines} lignes de code < {MIN_CODE_LINES}"}
    if head_dens is None:
        return {"verdict": "NOT_JUDGED", "reason": "aucune ligne de code"}
    if head_dens >= MIN_DENSITY:
        return {"verdict": "OK",
                "density": head_dens, "code_lines": head_lines}
    # Sous le seuil : rouge pour un AJOUT ; rouge pour une MODIFICATION qui
    # PASSE sous le seuil ; dette heritee -> advisory, jamais gate.
    if base_stats is None:
        return {"verdict": "RED", "reason": "carnet ajoute sous le seuil",
                "density": head_dens, "code_lines": head_lines}
    base_dens = base_stats["density"]
    if base_dens is None:
        # Base SANS ligne de code (carnet de prose, ou cellule code vide) :
        # c'est la PR qui introduit le code mesure. Rouge, et surtout pas
        # un formatage de None (TypeError -> exit 1 sans JSON).
        return {"verdict": "RED",
                "reason": "code introduit sous le seuil (base sans code)",
                "density": head_dens, "base_density": None,
                "code_lines": head_lines}
    if base_dens < MIN_DENSITY:
        return {"verdict": "ALREADY_BELOW",
                "reason": "stock deja sous le seuil a la base (dette §I)",
                "density": head_dens, "base_density": base_dens,
                "code_lines": head_lines}
    return {"verdict": "RED",
            "reason": "densite passee sous le seuil "
                      f"({base_dens:.1%} -> {head_dens:.1%})",
            "density": head_dens, "base_density": base_dens,
            "code_lines": head_lines}


def compare(base_ref, head_ref, paths, cwd=None):
    rows = []
    for entry in paths:
        # ``diff_notebooks`` rend (tete, origine) : la base se lit a
        # l'origine, sinon un renommage se lit comme un ajout.
        path, origin = entry if isinstance(entry, tuple) else (entry, entry)
        base_nb = read_notebook_at(base_ref, origin, cwd=cwd)
        head_nb = read_notebook_at(head_ref, path, cwd=cwd)
        if head_nb is None:
            continue
        base_stats = notebook_stats(base_nb) if base_nb is not None else None
        head_stats = notebook_stats(head_nb)
        v = verdict(base_stats, head_stats)
        rows.append({
            "notebook": path,
            "added": base_nb is None,
            "base": ({k: base_stats[k] for k in
                      ("code_lines", "comment_lines", "density")}
                     if base_stats else None),
            "head": {k: head_stats[k] for k in
                     ("code_lines", "comment_lines", "density")},
            # Cellules Python mesurees par le repli : visible en JSON comme
            # en texte, la mesure approchee se DECLARE (review #26788 pt 2).
            "py_degraded": head_stats["py_degraded"],
            "readability": head_stats["readability"],
            **v,
        })
    return rows


# ---------------------------------------------------------------------------
# Self-test (pre-controle du garde : un detecteur qui ne tire pas est
# indiscernable d'un detecteur debranche).
# ---------------------------------------------------------------------------

PY_45_UNCOMMENTED = "\n".join(
    ["import math"] +
    [f"v{i} = math.sqrt({i}) + {i} * 2" for i in range(44)]) + "\n"

PY_20_PERCENT = "\n".join(
    ["# Cellule d'illustration du seuil"] +
    [line for i in range(20) for line in
     (f"x{i} = {i}", f"y{i} = x{i} + 1", f"# etape {i} : somme cumulee",
      f"z{i} = y{i} * 2")] +
    [f"w{i} = z{i} - 3" for i in range(20)]) + "\n"

CS_45_UNCOMMENTED = "\n".join(
    ["var acc = 0.0;"] +
    [f"var v{i} = Math.Sqrt({i}) + {i} * 2;" for i in range(44)]) + "\n"


def _nb(cells: list[tuple[str, str]], kernel: str = "python3") -> dict:
    return {
        "cells": [{"cell_type": "code", "execution_count": 1,
                   "metadata": {}, "outputs": [],
                   "source": src.splitlines(True)} for _, src in cells],
        "metadata": {"kernelspec": {"name": kernel,
                                    "display_name": kernel}},
        "nbformat": 4, "nbformat_minor": 5,
    }


def self_test() -> int:
    failures = []

    def check(name: str, ok: bool, detail: str = ""):
        print(f"  {'OK  ' if ok else 'ECHEC'} {name}"
              + (f"  ({detail})" if detail and not ok else ""))
        if not ok:
            failures.append(name)

    # --- Classification unitaire -------------------------------------
    classes = classify_python('s = "a # b"\nx = 1  # fin de ligne\n'
                              '# ligne entiere\n')
    check("python: # dans une chaine n'est pas un commentaire",
          classes[0] == CODE, str(classes))
    check("python: commentaire de fin de ligne compte",
          classes[1] == COMMENT, str(classes))
    check("python: ligne entiere commentaire",
          classes[2] == COMMENT, str(classes))

    classes = classify_python('"""\ndocstring ligne interieure\n"""\n')
    check("python: interieur de docstring ni code ni commentaire",
          classes[0] == CODE and classes[1] == STRING_CONT, str(classes))

    classes = classify_python("%matplotlib inline\n!pip install x\n"
                              '#r "NuGet: X, 1.0"\n#!csharp\nz = 1\n')
    check("python: magies et directives exclues",
          classes[0] == EXCLUDED and classes[1] == EXCLUDED
          and classes[2] == EXCLUDED and classes[3] == EXCLUDED, str(classes))

    classes = classify_csharp('var s = "# pas un commentaire";\n'
                              'var t = 1; // fin de ligne\n'
                              '// ligne entiere\n')
    check("csharp: # dans une chaine n'est pas un commentaire",
          classes[0] == CODE, str(classes))
    check("csharp: commentaire de fin de ligne compte",
          classes[1] == COMMENT, str(classes))
    check("csharp: ligne entiere commentaire",
          classes[2] == COMMENT, str(classes))

    classes = classify_csharp('var q = @"verbatim\ninterieur\n";\n'
                              'var z = q.Length;\n')
    check("csharp: interieur verbatim ni code ni commentaire",
          classes[0] == CODE and classes[1] == STRING_CONT
          and classes[2] == STRING_CONT and classes[3] == CODE, str(classes))

    classes = classify_csharp('/* bloc\nsuite */ var a = 1;\n#region X\n')
    check("csharp: interieur de bloc compte comme commentaire",
          classes[0] == COMMENT and classes[1] == COMMENT, str(classes))
    check("csharp: directive preprocesseur exclue",
          classes[2] == EXCLUDED, str(classes))

    # --- Densite et verdicts ------------------------------------------
    stats = notebook_stats(_nb([("py", PY_45_UNCOMMENTED)]))
    check("densite 0 % sur 45 lignes de code",
          stats["code_lines"] >= 40 and stats["density"] == 0,
          f"code={stats['code_lines']} dens={stats['density']}")
    v = verdict(None, stats)
    check("carnet AJOUTE sous le seuil -> RED",
          v["verdict"] == "RED", str(v))

    stats = notebook_stats(_nb([("cs", CS_45_UNCOMMENTED)],
                               kernel=".net-csharp"))
    check("csharp: densite 0 % sur 45 lignes",
          stats["code_lines"] >= 40 and stats["density"] == 0,
          f"code={stats['code_lines']} dens={stats['density']} "
          f"perlang={stats['per_language']}")

    stats = notebook_stats(_nb([("py", PY_20_PERCENT)]))
    v = verdict(None, stats)
    check("controle negatif ~20 % -> OK",
          v["verdict"] == "OK" and stats["density"] >= 0.15,
          f"dens={stats['density']}")

    small = _nb([("py", "\n".join(f"x{i} = {i}" for i in range(30)) + "\n")])
    stats = notebook_stats(small)
    v = verdict(None, stats)
    check("moins de 40 lignes -> NOT_JUDGED",
          v["verdict"] == "NOT_JUDGED", str(v))

    base_stats = {"code_lines": 100, "comment_lines": 10, "density": 0.10}
    head_stats = {"code_lines": 100, "comment_lines": 2, "density": 0.02}
    v = verdict(base_stats, head_stats)
    check("modification qui passe sous le seuil -> RED",
          v["verdict"] == "RED", str(v))
    head_stats_ok = {"code_lines": 100, "comment_lines": 8, "density": 0.08}
    check("modification qui reste au-dessus -> OK",
          verdict(base_stats, head_stats_ok)["verdict"] == "OK")
    base_below = {"code_lines": 100, "comment_lines": 1, "density": 0.01}
    head_below = {"code_lines": 100, "comment_lines": 2, "density": 0.02}
    check("dette heritee sous le seuil -> ALREADY_BELOW (advisory)",
          verdict(base_below, head_below)["verdict"] == "ALREADY_BELOW")

    # --- Axe lisibilite -------------------------------------------------
    long_src = "x = 1  # " + "a" * 130 + "\n"
    stats = notebook_stats(_nb([("py", long_src)]))
    check("ligne > 120 caracteres comptee",
          stats["readability"]["long_lines"] == 1)
    block_src = "\n".join(["v = 1"] + [f"w{i} = {i}" for i in range(80)])
    stats = notebook_stats(_nb([("py", block_src)]))
    check("bloc > 60 lignes sans commentaire comptee",
          stats["readability"]["long_blocks"] >= 1,
          str(stats["readability"]))
    check("identifiant d'une lettre hors boucle compte",
          _one_letter_count("q = f(w)\nfor i in range(3):\n    pass\n",
                            "python") >= 1)
    check("indice de boucle exempt",
          _one_letter_count("for i in range(3):\n    acc = i\n",
                            "python") == 0)

    # Pas de f-string multi-lignes ici : PEP 701 (3.12+) seulement, le
    # runner CI est en 3.11 et la collection pytest y echoue (SyntaxError).
    # Le nom "verdict" designe deja une fonction de ce module : ne pas le masquer.
    selftest_msg = "PASS" if not failures else "%d ECHEC(S)" % len(failures)
    print("self-test: " + selftest_msg)
    return 1 if failures else 0


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Ratchet: densite de commentaires du code des carnets "
                    "changes (base vs PR), #26782.")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--all", action="store_true",
                    help="Sweep advisory du stock (table §I de #26782)")
    ap.add_argument("--readability", action="store_true",
                    help="Axe lisibilite seul (advisory, jamais gate)")
    ap.add_argument("--self-test", action="store_true",
                    help="Controles embarques positifs et negatifs")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.all:
        head = (git("rev-parse", "HEAD") or "?").strip()[:12]
        behind = (git("rev-list", "--count", "HEAD..origin/main")
                  or "?").strip()
        dirty = "dirty" if (git("status", "--porcelain", "--", "*.ipynb")
                            or "").strip() else "clean"
        provenance = ("tree HEAD " + head + " | " + behind
                      + " commit(s) behind origin/main | notebooks " + dirty)
        rows = []
        for path in all_notebooks():
            nb = read_notebook_at(None, path)
            if nb is None:
                continue
            s = notebook_stats(nb)
            if s["code_lines"] < MIN_CODE_LINES or s["density"] is None:
                continue
            if s["density"] < MIN_DENSITY:
                rows.append({"notebook": path,
                             "code_lines": s["code_lines"],
                             "comment_lines": s["comment_lines"],
                             "density": round(s["density"], 4),
                             "per_language": s["per_language"]})
        rows.sort(key=lambda r: r["density"])
        if args.as_json:
            print(json.dumps({"mode": "sweep", "provenance": provenance,
                              "below_threshold": len(rows),
                              "rows": rows}, indent=2, ensure_ascii=False))
        else:
            print("SWEEP §I [" + provenance + "] -- "
                  + str(len(rows)) + " carnets >= "
                  + str(MIN_CODE_LINES)
                  + " lignes de code sous "
                  + f"{MIN_DENSITY:.0%} (plan de remediation #26782)")
            for r in rows:
                print(f"  {r['density']:.1%}  "
                      f"{r['code_lines']:5d} lignes  {r['notebook']}")
        return 0

    if not args.base:
        ap.error("base ref required (or --all / --self-test)")

    base = resolve_base(args.base)
    paths = diff_notebooks(base)
    rows = compare(base, None, paths)
    if args.readability:
        findings = [(r["notebook"], r["readability"]) for r in rows
                    if any(r["readability"].values())]
        if args.as_json:
            print(json.dumps({"base_ref": args.base, "merge_base": base,
                              "changed": len(paths),
                              "advisory": "readability",
                              "rows": rows}, indent=2, ensure_ascii=False))
        else:
            print("ADVISORY lisibilite (jamais gate) -- base "
                  + str(args.base) + " -> " + base[:12] + " | "
                  + str(len(paths)) + " carnets changes")
            for path, rd in findings:
                print(f"  {path}  long_lines={rd['long_lines']} "
                      f"long_blocks={rd['long_blocks']} "
                      f"one_letter={rd['one_letter_identifiers']}")
            if not findings:
                print("  aucun finding lisibilite")
        return 0

    bad = [r for r in rows if r["verdict"] == "RED"]
    advisory = [r for r in rows if r["verdict"] == "ALREADY_BELOW"]
    if args.as_json:
        print(json.dumps({"base_ref": args.base, "merge_base": base,
                          "changed": len(paths), "red": len(bad),
                          "already_below": len(advisory),
                          "rows": rows}, indent=2, ensure_ascii=False))
    else:
        print("base " + str(args.base) + " -> merge-base " + base[:12]
              + " | " + str(len(paths)) + " carnets changes | "
              + str(len(bad)) + " rouge(s)")
        for r in rows:
            dens = (f"{r['head']['density']:.1%}"
                    if r["head"]["density"] is not None else "n/a")
            line = (f"  {r['verdict']:<13} {dens:>6} "
                    f"{r['head']['code_lines']:5d} lignes  {r['notebook']}")
            if r.get("py_degraded"):
                line += (f"  -- {r['py_degraded']} cellule(s) Python au repli "
                         "(tokenize en echec, mesure approchee)")
            if r.get("reason"):
                line += "  -- " + r["reason"]
            print(line)
        if bad:
            print("\nUn commentaire de remplissage ne suffit pas : le "
                  "reviewer verifie qu'un commentaire dit POURQUOI ou CE "
                  "QUE REPRESENTE une variable (spec #26782).")
        if advisory:
            print("\nADVISORY (dette heritee, plan §I, jamais gate) : "
                  + ", ".join(r["notebook"] for r in advisory))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
