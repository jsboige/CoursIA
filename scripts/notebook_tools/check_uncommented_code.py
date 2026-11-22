#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Organe : code de notebook non commente (lisibilite).

Demande user, verbatim, en commentaire de PR le 2026-11-15 :

    #26607 : « le code est non commente et tres difficile a lire. Le CI
              devrait le rejeter sur ces deux bases. »
    #26616 : « code non commente et tres dur a lire. Il nous faut un organe
              contre ca. »

Le user demande que le CI **rejette** cette classe, pas qu'on reformule les
PRs une a une : traitee PR par PR, la reserve meurt avec le fil et la PR
suivante du meme type la rouvre.

Ce que l'organe mesure
----------------------
Une cellule de code est SIGNALEE quand elle porte assez de code pour etre
penible a lire et **aucun** commentaire :

  * ``code_lines >= MIN_CODE_LINES`` (defaut 8) ;
  * **zero** commentaire ``#``, compte par le **tokenizer** python -- un
    ``#`` dans une chaine (couleur ``"#fff"``, motif, URL) n'est pas un
    commentaire et un comptage par ligne en fabriquerait ;
  * aucune docstring, ou une cellule **longue** (``>= LONG_CELL_LINES``,
    defaut 26) : au-dela, une docstring unique ne porte plus la lisibilite.

Le faux positif est le vrai risque -- le user le nomme lui-meme : « du code
mathematique court et lisible n'a pas besoin de commentaires ». Quatre
exemptions declarees :

  * cellule courte (< ``MIN_CODE_LINES``) ;
  * bloc d'``import`` / magics seul -- il ne s'explique pas ligne a ligne ;
  * stub d'exercice (``# TODO``, ``# Indice``, ``# Etape``) -- regle C.1 les
    veut creux ; le marqueur ne compte que sur une **ligne de commentaire** :
    un marqueur dans une chaine (« voir # Etape 3 ») n'exempte rien (reserve
    #26694 sur #26690) ;
  * cellule illisible au tokenizer : on retombe sur un comptage de lignes et
    le finding porte ``counter="fallback"`` -- jamais un zero silencieux.

Le marqueur de commentaire depend du NOYAU
------------------------------------------
Le cens du corpus l'a impose (mesure du 2026-11-15, ``main`` a
``ffdfd724e3f``) : une premiere version comptait ``#`` partout et signalait
**2703 cellules C#**, soit 66 % des cellules C# du depot -- or le C# n'a pas
de commentaire ``#``. Ce n'etaient pas des defauts de lisibilite, c'etaient
des cellules lues dans la mauvaise langue. Le compteur suit donc la famille
du noyau, lue dans ``metadata.kernelspec.language`` :

  * **Python** (defaut, y compris noyau inconnu) : tokenizer ;
  * **C#** : ``//`` et ``/* */``, chaines masquees avant comptage -- sans le
    masquage, l'URL ``"https://..."`` d'une cellule C# compterait comme un
    commentaire et blanchirait la cellule (le piège miroir du ``#`` dans une
    chaine) ;
  * **Lean** : ``--`` et ``/- -/``, chaines masquees ;
  * **Rust** (noyau evcxr, ``language: rust``) : ``//`` et ``/* */``, chaines
    brutes, echappees et caracteres masques. Sans cette famille, le noyau
    Rust tombait sur le tokenizer Python, qui lit ``//`` comme un operateur :
    une cellule commentee ressortait a 0 commentaire (mesure du 2026-11-21,
    ``Sudoku-10-CP-SAT-Rust``, cellule 11 : 4 ``//``, 0 compte).

Bornage
-------
Mode diff (``--diff <base>``, celui de la CI) : seules les cellules
**ajoutees ou modifiees** entre le merge-base et HEAD sont jugees. Sans ce
bornage, cabler l'organe rougirait d'un coup les ~950 carnets de ``main`` au
lieu de tenir la ligne sur les carnets que les PRs touchent. Les cellules
sont appariees par leur ``id`` nbformat 4.5 ; a defaut, par position -- un
carnet sans ids voit alors ses cellules suivantes comptees comme modifiees
quand une insertion decale les positions, ce qui sur-signale sans jamais
manquer un defaut.

Un carnet **renomme** sans changement de contenu n'est pas neuf : ``git diff
--name-only`` (l'attelage partage) ne rend que le nouveau chemin, et lire la
base a ce chemin rend ``None`` -- le carnet entier etait alors juge
« (carnet neuf) » (35 faux positifs sur les 21 renommages de #26420 ; 18
cellules preexistantes signalees sur le pur renommage #26381, le rouge qui a
fonde la reparation). La table nouveau->ancien (``renamed_notebooks`` :
``-M --diff-filter=R``, importee de l'organe partage) fait lire la base a
l'ANCIEN chemin du carnet renomme (correctif #26690 sur l'organe, centralise
par #26883).

Mode fichier (``--file``) : juge un carnet entier, pour l'audit hors CI.

Codes de sortie : 0 aucun defaut, 1 au moins un defaut, 2 erreur d'invocation.

Usage
-----
    python scripts/notebook_tools/check_uncommented_code.py --self-test
    python scripts/notebook_tools/check_uncommented_code.py --diff origin/main
    python scripts/notebook_tools/check_uncommented_code.py --diff origin/main --json
    python scripts/notebook_tools/check_uncommented_code.py --file <carnet>.ipynb
"""
from __future__ import annotations

import argparse
import io
import json
import re
import sys
import tokenize
from pathlib import Path

# Le meme attelage git que les organes freres : une seule implementation de
# « qu'est-ce qui a change entre le merge-base et HEAD ».
import check_output_failure_text  # module objet : delegation renamed_notebooks
from check_output_failure_text import (
    BS,
    _cell_source,
    _parse_rename_status,
    changed_notebooks,
    git,
    read_notebook_at,
    resolve_base,
)
from check_output_flood import _cell_key


def renamed_notebooks(base, head="HEAD", cwd=None):
    """{chemin a la tete: chemin a la base} pour les carnets RENOMMES.

    Delegation a l'organe partage (commande git, parseur
    ``_parse_rename_status``, filtre des cibles exclues) avec le ``git`` de
    CE module : les tests pytest #26914 stubent ``organ.git`` par
    ``monkeypatch.setattr`` -- une re-export de la fonction source
    resoudrait ``git`` dans le module source et le patch ne prendrait pas.
    """
    return check_output_failure_text.renamed_notebooks(
        base, head=head, cwd=cwd, git_fn=git)


# --------------------------------------------------------------------------
# Seuils -- ce sont eux qui portent le faux positif.
# --------------------------------------------------------------------------

#: En dessous, la cellule n'est pas jugee : trois lignes de maths n'ont pas
#: besoin d'un commentaire, et le user l'a dit explicitement.
MIN_CODE_LINES = 8

#: Au-dela, une docstring unique ne suffit plus a porter la lisibilite.
LONG_CELL_LINES = 26

#: Marqueurs de stub d'exercice (regle C.1 : un stub se laisse creux).
STUB_MARKERS = (
    "# TODO", "#TODO", "# todo",
    "# Indice", "# INDICE", "# indice",
    "# Etape", "# Étape", "# ETAPE",
)

#: Ligne qui n'appelle pas d'explication : import, magic IPython, shell.
IMPORT_LINE = re.compile(r"^\s*(?:import\s|from\s+\S+\s+import\s|[%!])")

#: Chaines C# a masquer avant de chercher ``//`` : verbatim ``@"..."`` (dont
#: les quotes se doublent), interpolee ``$"..."``, et chaines echappees.
_CS_STRING = re.compile(r'@"(?:[^"]|"")*"|\$?"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'')

#: Chaines Lean a masquer avant de chercher ``--``.
_LEAN_STRING = re.compile(r'"(?:\\.|[^"\\])*"')

#: Chaines Rust a masquer avant de chercher ``//`` : brutes ``r#"..."#`` (le
#: nombre de ``#`` ferme la chaine), echappees ``"..."`` et ``b"..."``, et
#: caracteres ``'x'`` / ``'\n'``. Une duree de vie (``'a``) n'a pas de quote
#: fermante apres un seul caractere : elle n'est pas masquee.
_RUST_STRING = re.compile(
    r'(?<![A-Za-z0-9_])b?r(#*)"[\s\S]*?"\1'
    r'|b?"(?:\\.|[^"\\])*"'
    r"|b?'(?:\\[^'\n]{1,10}|[^'\\\n])'"
)


def _line_kind(line: str) -> str:
    """'blank' | 'comment' | 'magic' | 'code' pour une ligne brute."""
    stripped = line.strip()
    if not stripped:
        return "blank"
    if stripped.startswith("#"):
        return "comment"
    if stripped[0] in "%!":
        return "magic"
    return "code"


def _token_facts(source: str) -> tuple[int, bool] | None:
    """(commentaires, docstring) lus par le tokenizer, ou None si illisible.

    None n'est pas un zero : c'est le signal qu'on ne sait pas lire la
    cellule (noyau C#, Lean, cellules non-Python). L'appelant retombe alors
    sur un comptage de lignes et le DIT.
    """
    comments = 0
    has_docstring = False
    at_statement_start = True
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            kind = tok.type
            if kind == tokenize.COMMENT:
                comments += 1
            elif kind in (tokenize.NEWLINE, tokenize.NL):
                at_statement_start = True
            elif kind in (tokenize.INDENT, tokenize.DEDENT, tokenize.ENCODING,
                          tokenize.ENDMARKER):
                continue
            else:
                if kind == tokenize.STRING and at_statement_start:
                    has_docstring = True
                at_statement_start = False
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        return None
    return comments, has_docstring


def _family(language: str) -> str:
    """'python' | 'csharp' | 'lean' | 'rust' depuis le ``language`` du kernelspec.

    Un noyau inconnu (``?``, ``ict-py313``, ``py310-gpu``) tombe sur Python :
    c'est le defaut du depot, et se tromper dans ce sens signale une cellule
    au lieu d'en blanchir une.
    """
    key = (language or "").strip().lower()
    if key.startswith(("csharp", "c#", ".net-csharp")):
        return "csharp"
    if key.startswith("lean"):
        return "lean"
    if key == "rust":
        return "rust"
    return "python"


def _marker_facts(source: str, family: str) -> tuple[int, bool]:
    """(commentaires, docstring) par marqueurs, pour un noyau non-Python.

    Les chaines sont masquees AVANT le comptage : un ``//`` dans
    ``"https://..."`` n'est pas un commentaire, et le compter blanchirait la
    cellule -- c'est le piege miroir du ``#`` dans une chaine Python.
    """
    if family == "csharp":
        masked = _CS_STRING.sub('""', source)
        line_marker, block = "//", "/*"
    elif family == "rust":
        masked = _RUST_STRING.sub('""', source)
        line_marker, block = "//", "/*"
    else:  # lean
        masked = _LEAN_STRING.sub('""', source)
        line_marker, block = "--", "/-"

    comments = sum(1 for line in masked.splitlines() if line_marker in line)
    if block in masked:
        comments += 1
    return comments, False


def analyse_cell(cell: dict, language: str = "python") -> dict | None:
    """Finding pour une cellule de code, ou None si elle est hors jugement."""
    source = _cell_source(cell)
    lines = source.splitlines()
    code_lines = sum(1 for line in lines if _line_kind(line) == "code")

    if code_lines < MIN_CODE_LINES:
        return None

    family = _family(language)
    if family == "python":
        facts = _token_facts(source)
        if facts is None:
            comments = sum(1 for line in lines if _line_kind(line) == "comment")
            has_docstring = any('"""' in line or "'''" in line for line in lines)
            counter = "fallback"
        else:
            comments, has_docstring = facts
            counter = "python"
    else:
        comments, has_docstring = _marker_facts(source, family)
        counter = family

    if comments > 0:
        return None
    if has_docstring and code_lines < LONG_CELL_LINES:
        return None
    # Marqueurs de stub lus UNIQUEMENT sur les lignes classees commentaire :
    # un marqueur dans une CHAINE (« voir # Etape 3 ») n'est pas un stub, et
    # le substring sur la source entiere exemptait a tort la cellule
    # (reserve #26694 sur #26690). Un stub en commentaire de fin de ligne
    # reste couvert : le tokenizer le compte alors comme commentaire.
    comment_only = (line for line in lines if _line_kind(line) == "comment")
    if any(marker in line for line in comment_only for marker in STUB_MARKERS):
        return None

    body = [line for line in lines if line.strip()]
    if body and all(IMPORT_LINE.match(line) for line in body):
        return None

    return {
        "code_lines": code_lines,
        "comments": comments,
        "has_docstring": has_docstring,
        "counter": counter,
    }


def _notebook_language(notebook: dict) -> str:
    """Langage du noyau, lu dans les metadonnees du carnet."""
    meta = notebook.get("metadata") or {}
    language = (meta.get("kernelspec") or {}).get("language") or ""
    if not language:
        language = (meta.get("language_info") or {}).get("name") or ""
    return language


def analyse_notebook(notebook: dict, only_keys: set[str] | None = None) -> list[dict]:
    """Findings d'un carnet, optionnellement restreints a des cles de cellule."""
    language = _notebook_language(notebook)
    findings: list[dict] = []
    for index, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        key = _cell_key(cell, index)
        if only_keys is not None and key not in only_keys:
            continue
        finding = analyse_cell(cell, language=language)
        if finding is not None:
            findings.append(dict(finding, cell=index, key=key))
    return findings


def changed_keys(base_notebook: dict | None, head_notebook: dict) -> set[str] | None:
    """Cles des cellules ajoutees ou modifiees ; None si le carnet est neuf."""
    if base_notebook is None:
        return None
    base_sources: dict[str, str] = {}
    for index, cell in enumerate(base_notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        base_sources[_cell_key(cell, index)] = _cell_source(cell)

    keys: set[str] = set()
    for index, cell in enumerate(head_notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        key = _cell_key(cell, index)
        if base_sources.get(key) != _cell_source(cell):
            keys.add(key)
    return keys


def compare(base_ref: str, paths: list[str], cwd: str | None = None,
            renames: dict[str, str] | None = None) -> list[dict]:
    """Findings par carnet, bornes aux cellules que la branche a touchees.

    ``renames`` ({chemin tete: chemin base}, cf. ``renamed_notebooks`` de
    l'organe partage) fait lire la base a l'ANCIEN chemin d'un carnet
    renomme : sans lui, le chemin de tete est absent de la base,
    ``changed_keys`` rend ``None`` et le carnet est juge entier -- du code
    preexistant signale comme neuf (angle mort corrige sur #26690, table
    centralisee dans l'organe partage par #26883 : 35 faux positifs sur les
    21 renommages de #26420, 18 cellules sur le pur renommage #26381).
    """
    renames = renames or {}
    rows: list[dict] = []
    for path in paths:
        head_notebook = read_notebook_at(None, path, cwd=cwd)
        if head_notebook is None:
            continue
        base_notebook = read_notebook_at(
            base_ref, renames.get(path, path), cwd=cwd)
        keys = changed_keys(base_notebook, head_notebook)
        findings = analyse_notebook(head_notebook, only_keys=keys)
        if findings:
            rows.append({
                "notebook": path,
                "new_notebook": base_notebook is None,
                "cells": findings,
            })
    return rows


# --------------------------------------------------------------------------
# Controles
# --------------------------------------------------------------------------

def _cell(*lines: str) -> dict:
    return {
        "cell_type": "code",
        "source": [line + "\n" for line in lines],
        "metadata": {},
        "execution_count": 1,
        "outputs": [],
    }


def _notebook(*cells: dict) -> dict:
    return {"cells": list(cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


_BODY_12 = (
    "def cout_total(commandes, prix, taxes):",
    "    total = 0.0",
    "    for commande in commandes:",
    "        ligne = commande['quantite'] * prix[commande['article']]",
    "        total = total + ligne",
    "    total = total * (1.0 + taxes)",
    "    return round(total, 2)",
    "",
    "resultat = cout_total(commandes, prix, 0.2)",
    "assert resultat > 0",
    "print(resultat)",
    "print(cout_total([], prix, 0.2))",
)


def self_test() -> int:
    """Controles positif/negatif sur des carnets synthetiques."""
    checks: list[tuple[str, bool]] = []

    # 1. POSITIF -- 12 lignes de code, aucun commentaire : signale.
    checks.append((
        "positif : 12 lignes de code sans commentaire",
        analyse_cell(_cell(*_BODY_12)) is not None,
    ))

    # 2. NEGATIF -- le meme code avec un seul commentaire : silencieux.
    commented = ("# Cout total d'une commande, taxes incluses.",) + _BODY_12
    checks.append((
        "negatif : un seul commentaire suffit a taire le finding",
        analyse_cell(_cell(*commented)) is None,
    ))

    # 3. NEGATIF -- cellule courte (maths) : hors jugement.
    checks.append((
        "negatif : cellule courte non jugee",
        analyse_cell(_cell("a = 1", "b = 2", "print(a + b)")) is None,
    ))

    # 4. NEGATIF -- bloc d'imports seul.
    imports = tuple("import module_%d" % i for i in range(10))
    checks.append((
        "negatif : bloc d'imports non juge",
        analyse_cell(_cell(*imports)) is None,
    ))

    # 5. NEGATIF -- docstring sur une cellule courte.
    documented = ('"""Somme des recompenses actualisees."""',) + _BODY_12[:7]
    checks.append((
        "negatif : docstring sur cellule courte",
        analyse_cell(_cell(*documented)) is None,
    ))

    # 5bis. POSITIF -- docstring seule sur une cellule LONGUE : signale.
    long_documented = ('"""Somme des recompenses actualisees."""',) + _BODY_12 + (
        "def autre(x):",
        "    return x * 2",
        "print(autre(3))",
        "print(autre(4))",
        "print(autre(5))",
        "print(autre(6))",
        "print(autre(7))",
        "print(autre(8))",
        "print(autre(9))",
        "print(autre(10))",
        "print(autre(11))",
        "print(autre(12))",
        "print(autre(13))",
        "print(autre(14))",
        "print(autre(15))",
        "print(autre(16))",
        "print(autre(17))",
        "print(autre(18))",
    )
    checks.append((
        "positif : docstring seule sur cellule longue",
        analyse_cell(_cell(*long_documented)) is not None,
    ))

    # 6. NEGATIF -- stub d'exercice (C.1).
    stub = ("# TODO etudiant : completer", "resultat = None") + _BODY_12
    checks.append((
        "negatif : stub d'exercice (C.1)",
        analyse_cell(_cell(*stub)) is None,
    ))

    # 6bis. POSITIF -- un marqueur de stub dans une CHAINE n'exempte pas :
    #     « voir # Etape 3 » n'est pas un stub. Le substring sur la source
    #     entiere exemptait a tort la cellule (reserve #26694).
    fake_stub = ('print("voir # Etape 3 du carnet compagnon")',) + _BODY_12
    checks.append((
        "positif : marqueur de stub dans une chaine n'exempte pas",
        analyse_cell(_cell(*fake_stub)) is not None,
    ))

    # 7. NEGATIF -- un '#' dans une CHAINE n'est pas un commentaire, donc le
    #    finding doit rester. C'est le controle du tokenizer.
    with_hash_string = ('COULEUR = "#ffffff"', "MOTIF = 'a#b'") + _BODY_12
    checks.append((
        "positif : '#' dans une chaine ne compte pas comme commentaire",
        analyse_cell(_cell(*with_hash_string)) is not None,
    ))

    # 8. BORNAGE -- une cellule inchangee n'est pas re-jugee.
    base_nb = _notebook(_cell(*_BODY_12))
    head_nb = _notebook(_cell(*_BODY_12), _cell("x = 1"))
    keys = changed_keys(base_nb, head_nb)
    checks.append((
        "bornage : cellule inchangee hors jugement",
        keys is not None and "" not in keys and analyse_notebook(head_nb, keys) == [],
    ))
    # ... et une cellule MODIFIEE l'est.
    head_changed = _notebook(_cell(*(_BODY_12 + ("print(1)",))))
    keys_changed = changed_keys(base_nb, head_changed)
    checks.append((
        "bornage : cellule modifiee jugee",
        keys_changed is not None and len(analyse_notebook(head_changed, keys_changed)) == 1,
    ))

    # 9. LANGUE -- une cellule C# commentee par `//` est silencieuse ; le meme
    #    code sans commentaire est signale. Le cens du corpus a montre que
    #    compter `#` partout signalait 2703 cellules C# sur 4092.
    cs_body = (
        "var total = 0.0;",
        "foreach (var c in commandes)",
        "{",
        "    total += c.Quantite * prix[c.Article];",
        "}",
        "total *= 1.0 + taxes;",
        "Console.WriteLine(Math.Round(total, 2));",
        "Console.WriteLine(total);",
        "Console.WriteLine(commandes.Count);",
    )
    checks.append((
        "langue : cellule C# commentee par // non signalee",
        analyse_cell(_cell("// Cout total taxes incluses.", *cs_body),
                     language="C#") is None,
    ))
    checks.append((
        "langue : cellule C# sans commentaire signalee",
        analyse_cell(_cell(*cs_body), language="C#") is not None,
    ))
    # ... et le piege miroir : une URL dans une chaine ne compte pas.
    url_cell = ('var api = "https://api.exemple.fr/v1";',) + cs_body
    url_finding = analyse_cell(_cell(*url_cell), language="C#")
    checks.append((
        "langue : '//' dans une chaine C# ne compte pas comme commentaire",
        url_finding is not None and url_finding["counter"] == "csharp",
    ))

    # 10. LANGUE -- Lean commente par `--`.
    lean_body = (
        "theorem deux_plus_deux : (2 : Nat) + 2 = 4 := by",
        "  norm_num",
        "  ring",
        "  omega",
        "  simp",
        "  rfl",
        "  decide",
        "  native_decide",
        "  trivial",
    )
    checks.append((
        "langue : cellule Lean commentee par -- non signalee",
        analyse_cell(_cell("-- Une preuve tres simple.", *lean_body),
                     language="lean4") is None,
    ))
    checks.append((
        "langue : cellule Lean sans commentaire signalee",
        analyse_cell(_cell(*lean_body), language="lean4") is not None,
    ))

    # 11. RENOMMAGE -- la table nouveau->ancien delegue a l'organe partage
    #     (commande git, parseur ``_parse_rename_status`` extrait pour les
    #     tests pytest #26914, filtre des cibles exclues). Le stub porte sur
    #     le ``git`` de CE module : la delegation passe ``git_fn``, sinon le
    #     patch ne prendrait que dans le module source.
    rename_out = (
        "R100\tdossier/ancien.ipynb\tdossier/nouveau.ipynb\n"
        "M\tun/Modifie.ipynb\n"
        "R075\tchemin" + BS + "base.ipynb\tchemin" + BS
        + "reordonne.ipynb\n"
    )
    checks.append((
        "renommage : parseur seul (R100, R075, anti-diagnostics BS)",
        _parse_rename_status(rename_out) == {
            "dossier/nouveau.ipynb": "dossier/ancien.ipynb",
            "chemin/reordonne.ipynb": "chemin/base.ipynb"},
    ))
    saved_git = git
    try:
        globals()["git"] = lambda *a, **k: rename_out
        renames = renamed_notebooks("base")
    finally:
        globals()["git"] = saved_git
    checks.append((
        "renommage : table nouveau->ancien par delegation stubable",
        renames == {"dossier/nouveau.ipynb": "dossier/ancien.ipynb",
                    "chemin/reordonne.ipynb": "chemin/base.ipynb"},
    ))

    # 12. RENOMMAGE -- un carnet renomme a cellules INTACTES n'est pas neuf :
    #     sa base existe (lue a l'ancien chemin par compare), donc keys est un
    #     ensemble VIDE, pas None, et aucune cellule n'est jugee.
    renamed_head = _notebook(_cell(*_BODY_12))
    checks.append((
        "renommage : base trouvee => cellules intactes hors jugement",
        changed_keys(_notebook(_cell(*_BODY_12)), renamed_head) == set(),
    ))

    # 12bis. CONTROLE POSITIF -- un VRAI carnet neuf rend bien None (le carnet
    #     entier reste juge, y compris apres le correctif renommage).
    checks.append((
        "renommage : carnet vraiment neuf => keys=None (juge en entier)",
        changed_keys(None, renamed_head) is None,
    ))

    failed = [name for name, ok in checks if not ok]
    for name, ok in checks:
        print(("  OK   " if ok else "  FAIL ") + name)
    print("self-test : %d/%d" % (len(checks) - len(failed), len(checks)))
    return 0 if not failed else 1


# --------------------------------------------------------------------------
# Entree
# --------------------------------------------------------------------------

def _format(row: dict) -> str:
    lines = ["FLAGGED %s%s" % (row["notebook"],
                               "  (carnet neuf)" if row["new_notebook"] else "")]
    for finding in row["cells"]:
        lines.append(
            "  cellule %d : %d lignes de code, %d commentaire(s), docstring=%s, "
            "compteur=%s"
            % (finding["cell"], finding["code_lines"], finding["comments"],
               "oui" if finding["has_docstring"] else "non", finding["counter"]))
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Signale les cellules de code sans aucun commentaire "
                    "(demande user du 2026-11-15, #26690).")
    parser.add_argument("--diff", metavar="BASE",
                        help="Juge les cellules ajoutees/modifiees depuis BASE "
                             "(resolue en merge-base avec HEAD).")
    parser.add_argument("--file", action="append", default=[],
                        metavar="CARNET",
                        help="Juge un carnet entier (repetable).")
    parser.add_argument("--self-test", action="store_true",
                        help="Controles positif/negatif, puis sortie.")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if not args.diff and not args.file:
        parser.error("--diff BASE ou --file CARNET requis (ou --self-test)")

    rows: list[dict] = []
    scope = 0
    if args.diff:
        base = resolve_base(args.diff)
        paths = changed_notebooks(base)
        renames = renamed_notebooks(base)
        scope += len(paths)
        rows.extend(compare(base, paths, renames=renames))
    for path in args.file:
        notebook = read_notebook_at(None, path)
        if notebook is None:
            parser.error("carnet illisible : " + path)
        scope += 1
        findings = analyse_notebook(notebook)
        if findings:
            rows.append({"notebook": path, "new_notebook": False,
                         "cells": findings})

    flagged = sum(len(row["cells"]) for row in rows)

    if args.as_json:
        print(json.dumps({"scope": scope, "flagged_notebooks": len(rows),
                          "flagged_cells": flagged, "rows": rows},
                         indent=2, ensure_ascii=False))
    else:
        print("%d carnet(s) dans le perimetre | %d cellule(s) signalee(s) "
              "dans %d carnet(s)" % (scope, flagged, len(rows)))
        for row in rows:
            print(_format(row))
        if rows:
            print("\nUne cellule de %d lignes ou plus sans un seul commentaire "
                  "est difficile a lire. Ajoutez des commentaires -- ou, si la "
                  "cellule est un stub d'exercice, laissez-lui son marqueur "
                  "# TODO (regle C.1)." % MIN_CODE_LINES)
    return 0 if not rows else 1


if __name__ == "__main__":
    sys.exit(main())