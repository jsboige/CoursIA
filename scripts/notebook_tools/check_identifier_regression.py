#!/usr/bin/env python3
"""Detecte les regressions d'identifiants accentues dans un notebook PR (registre #2876).

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais) est contractuellement
**markdown-only STRICT** (adjudication ai-01 17/07) : un agent qui cure les
accents ne doit toucher QUE les cellules markdown. Les commentaires de code et
les litteraux stdout sont hors-scope (zone grise), et les **identifiants de
code** (noms de variables, parametres, proprietes, classes) sont une violation
**encore plus grave** : accentuer un identifiant change l'API source.

Pourtant c'est arrive trois fois en quelques cycles :
  - #7094 : `Difference` -> `Différence` (propriete anonyme LINQ C#)
  - #7143 : `for iteration:` -> `for itération:` (variable de boucle Python)
  - #7154 : `préférences =`, `def f(..., préférences: list)`, `résultat = ...`
    (5 cellules, variable + parametre + boucle Python)

Pourquoi ces PR passent les gardes existants
--------------------------------------------
- La verification NFD-normalisee accent-stripped qu'utilisent les agents est
  **aveugle par construction** a ce defect : stripper les accents de
  `préférences` rend `preferences`, donc le diff "accent-only" rapporte
  "0 mismatch" meme quand un identifiant de code a ete touche.
- `validate_pr_notebooks.py` verifie execution_count / errors / C.1 mais pas
  les identifiants ; Python 3 (PEP 3131) accepte les identifiants Unicode donc
  le notebook s'execute toujours (H.1 passe).
- `regression_scan.py` cible la sante des OUTPUTS (axe-2), pas la source.

Cet outil resserre le harnais sur cette classe de defect (mandat user
"resserrer le harnais et le comportement de review des bots", EPIC #3801) en
comparant les cellules de code d'un notebook entre une base git (defaut
origin/main) et une HEAD (defaut working tree ou origin/<branch>).

Comment ca marche
-----------------
Pour chaque cellule de code, on :
  1. supprime les chaines et commentaires (Python, C#, F#, Lisp) pour ne garder
     que les tokens structurels ;
  2. tokenise les identifiants (Unicode-aware, donc inclut les formes accentuees) ;
  3. pour chaque identifiant accentue de la HEAD, on verifie si sa forme
     desaccentuee existait comme identifiant dans la base -> **REGRESSION**
     (la PR a accentue un identifiant existant).
  4. tout identifiant accentue nouveau (forme desaccentuee absente de la base)
     est rapporte comme **SUSPECT** (plus faible : pourrait etre un ajout legitime).

L'outil lit seulement (local git : git show). Il ne touche rien.

Usage
-----
    # un notebook : working tree vs origin/main
    python check_identifier_regression.py NB.ipynb
    python check_identifier_regression.py NB.ipynb --base origin/main --head origin/fix/ma-branche
    # exit 1 si regression detectee (CI-ready)
    python check_identifier_regression.py NB.ipynb --check
    # sortie machine
    python check_identifier_regression.py NB.ipynb --json

Exit codes
----------
    0 -- aucune regression d'identifiant detectee (ou mode non --check)
    1 -- un ou plusieurs identifiants accentues en regression (--check seulement)
    2 -- erreur (notebook illisible, ref git introuvable)

Voir aussi
----------
- detect_accent_stripping.py (registre #2876, moitie DETECTION des accents perdus)
- validate_pr_notebooks.py (garde PR : execution_count, errors, C.1)
- Memoires : issue-2876-scope-boundary-markdown-vs-code-pending-adjudication
  (scope = markdown-only STRICT)
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

# Caracteres accentues FR (et leurs capitales). Un identifiant qui en contient
# au moins un est candidat a une regression d'accent.
ACCENT_CHARS = set("àâäéèêëïîôöùûüçÀÂÄÉÈÊËÏÎÔÖÙÛÜÇœŒæÆ")

# Regex unique eliminant chaines + commentaires (Python / C# / F# / Lisp).
# Ordre des alternatives important : les formes longues (triple-quoted, blocs)
# doivent venir avant les formes courtes.
_STRIP_RE = re.compile(
    r"""
      (?P<py_triple>\"\"\"[\s\S]*?\"\"\"|\'\'\'[\s\S]*?\'\'\')   # Python triple-quoted
    | (?P<cs_block>/\*[\s\S]*?\*/)                               # C#/F# /* */ bloc
    | (?P<fs_block>\(\*[\s\S]*?\*\))                             # F#/OCaml (* *) bloc
    | (?P<line_comment>\#.*?$|//.*?$|;;.*?$)                     # commentaires ligne
    | (?P<string>[@$]?[rfbFRB]{0,2}\"(?:[^\"\\]|\\.)*\"          # chaines "..."
        | [@$]?[rfbFRB]{0,2}\'(?:[^\'\\]|\\.)*\')                 # chaines '...'
    """,
    re.VERBOSE | re.MULTILINE | re.DOTALL,
)

# Identifiant Unicode-aware : lettre/underscore en tete, puis word-chars.
# \w couvre les accents en mode Unicode (defaut Python 3 sur str).
_IDENT_RE = re.compile(r"[^\W\d]\w*", re.UNICODE)


def _src_str(cell: dict) -> str:
    """source nbformat : liste de lignes OU str -> str unique."""
    s = cell.get("source", "")
    if isinstance(s, list):
        s = "".join(s)
    return s or ""


def _deaccent(token: str) -> str:
    """Forme desaccentuee (NFKD + retrait des marques combinantes)."""
    nfkd = unicodedata.normalize("NFKD", token)
    return "".join(c for c in nfkd if not unicodedata.combining(c))


def _has_accent(token: str) -> bool:
    return any(c in ACCENT_CHARS for c in token)


def _strip_preserve_lines(source: str) -> str:
    """Remplace chaines + commentaires par un bloc de memes sauts de ligne.

    Indispensable pour conserver l'alignement des numeros de ligne : un commentaire
    bloc multi-ligne (/* ... \\n ... */) ou une triple-quoted qui serait remplace
    par une espace unique decalerait tous les numeros de ligne subsequents. On
    remplace donc chaque match par exactement son compte de '\\n' (intercale de
    ; le contenu est detruit mais la structure de lignes est preservee).
    """
    return _STRIP_RE.sub(lambda m: "\n" * m.group(0).count("\n"), source)


def code_identifiers(source: str) -> set:
    """Identifiants structurels (hors chaines/commentaires) d'un source code.

    Retourne l'ensemble des formes DESACCENTUEES (pour comparaison base/head).
    Limite connue : les interpolations d'f-string (``f"{len(x)}"``) sont masquees
    comme chaines, donc un identifiant accentue dans une interpolation echappe
    (faux negatif mineur ; l'expression hors-interpolation reste couverte).
    """
    stripped = _strip_preserve_lines(source)
    return {_deaccent(m.group(0)) for m in _IDENT_RE.finditer(stripped) if m.group(0)}


def partitioned_idents(source: str):
    """Partitionne les identifiants structurels en (non_accentes, accentes).

    Formes RAW (pas desaccentuees) — sert a distinguer :
      - la base avait l'identifiant NON accente (ex ``preferences``) -> une head
        accentuee (``préférences``) est une REGRESSION ;
      - la base avait DEJA l'identifiant accente (ex ``préférences``) -> la head
        l'utilisant est un statut quo (PAS une regression introduite par la PR).
    """
    stripped = _strip_preserve_lines(source)
    unaccented, accented = set(), set()
    for m in _IDENT_RE.finditer(stripped):
        tok = m.group(0)
        (accented if _has_accent(tok) else unaccented).add(tok)
    return unaccented, accented


def accented_identifiers(source: str):
    """Yield (token_accentue, ligne, ligne_contexte) pour chaque identifiant
    structurel accentue present dans le source code."""
    stripped = _strip_preserve_lines(source)
    src_lines = source.split("\n")
    for m in _IDENT_RE.finditer(stripped):
        tok = m.group(0)
        if _has_accent(tok):
            line_no = stripped.count("\n", 0, m.start()) + 1
            ctx = src_lines[line_no - 1].strip() if 0 < line_no <= len(src_lines) else ""
            yield tok, line_no, ctx


def _git_show_notebook(ref: str, path: str):
    """Lit un notebook a une ref git (None si introuvable)."""
    r = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        capture_output=True,
    )
    if r.returncode != 0:
        return None
    try:
        return json.loads(r.stdout.decode("utf-8"))
    except Exception:
        return None


def scan(old_nb: dict, new_nb: dict):
    """Compare les cellules de code old vs new. Retourne (regressions, suspects).

    regression : (cell_index, token, old_form, line, ctx) — la PR a accentue un
                 identifiant present (desaccentue) dans la base.
    suspect    : (cell_index, token, line, ctx) — identifiant accentue nouveau
                 (forme desaccentuee absente de la base) ; signal plus faible.
    """
    # Partition globale des identifiants de TOUTES les cellules de code de la
    # base. Un identifiant accentue dans UNE cellule head dont la forme
    # desaccentuee apparait (non accentee) dans N'IMPORTE QUELLE cellule base =
    # REGRESSION (la PR a accentue un identifiant existant). Si la base avait
    # DEJA la forme accentuee, c'est un statut quo (pas une regression).
    old_unaccented, old_accented = set(), set()
    for cell in old_nb.get("cells", []):
        if cell.get("cell_type") == "code":
            u, a = partitioned_idents(_src_str(cell))
            old_unaccented |= u
            old_accented |= a

    regressions = []
    suspects = []
    for i, (o, n) in enumerate(zip(old_nb.get("cells", []), new_nb.get("cells", []))):
        if n.get("cell_type") != "code":
            continue
        for tok, line, ctx in accented_identifiers(_src_str(n)):
            deacc = _deaccent(tok)
            if deacc in old_unaccented:
                # la base avait cet identifiant non accente -> la head l'a accente
                regressions.append((i, tok, deacc, line, ctx))
            elif tok in old_accented:
                # statut quo : la base avait deja cette forme accentuee
                continue
            else:
                suspects.append((i, tok, line, ctx))
    return regressions, suspects


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("notebook", help="Chemin du notebook (.ipynb)")
    p.add_argument("--base", default="origin/main", help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None,
                   help="Ref git de la head (defaut: working tree, lu depuis le disque)")
    p.add_argument("--check", action="store_true", help="Exit 1 si regression detectee (CI-ready)")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    args = p.parse_args(argv)

    nb_path = Path(args.notebook)
    # chemin relatif repo pour git show (depuis la racine du repo)
    try:
        rel = subprocess.run(
            ["git", "ls-files", "--full-name", "--", str(nb_path)],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except subprocess.CalledProcessError:
        rel = ""
    # fallback : chemin tel quel si non tracked (notebook en cours d'ajout)
    git_path = rel or str(nb_path).replace("\\", "/")

    old_nb = _git_show_notebook(args.base, git_path)
    if old_nb is None:
        msg = f"Notebook introuvable a la base {args.base}:{git_path}"
        if args.json:
            print(json.dumps({"error": msg}, ensure_ascii=False))
        else:
            print(msg, file=sys.stderr)
        return 2

    if args.head:
        new_nb = _git_show_notebook(args.head, git_path)
        if new_nb is None:
            msg = f"Notebook introuvable a la head {args.head}:{git_path}"
            if args.json:
                print(json.dumps({"error": msg}, ensure_ascii=False))
            else:
                print(msg, file=sys.stderr)
            return 2
    else:
        if not nb_path.exists():
            print(f"Notebook introuvable sur disque: {nb_path}", file=sys.stderr)
            return 2
        new_nb = json.loads(nb_path.read_text(encoding="utf-8"))

    regressions, suspects = scan(old_nb, new_nb)

    if args.json:
        out = {
            "notebook": str(nb_path),
            "base": args.base,
            "head": args.head or "working-tree",
            "regressions": [
                {"cell": i, "token": t, "old_form": o, "line": ln, "context": c}
                for (i, t, o, ln, c) in regressions
            ],
            "suspects": [
                {"cell": i, "token": t, "line": ln, "context": c}
                for (i, t, ln, c) in suspects
            ],
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        if regressions:
            print(f"IDENTIFIER REGRESSION (x{len(regressions)}) — {nb_path}")
            for i, t, o, ln, c in regressions:
                print(f"  cell[{i}] L{ln}: {o} -> {t}   | {c[:80]}")
        else:
            print(f"OK — aucune regression d'identifiant accentue ({nb_path})")
        if suspects:
            print(f"SUSPECTS (x{len(suspects)}) — identifiants accentues nouveaux (a verifier):")
            for i, t, ln, c in suspects[:10]:
                print(f"  cell[{i}] L{ln}: {t}   | {c[:80]}")
            if len(suspects) > 10:
                print(f"  ... (+{len(suspects) - 10} autres)")

    if args.check and regressions:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
