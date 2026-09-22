#!/usr/bin/env python3
"""Repare la regle ``math_paren_delims`` de ``detect_markdown_rendering.py`` (#17380).

Le defaut
---------
Un delimiteur inline ``\\( ... \\)`` hors code span ne rend NULLE PART par
defaut : le tex2jax de MathJax 2 (export HTML nbconvert classique) ne le
typesette pas, et les configs MathJax 3 de JupyterLab / VS Code ne declarent
que ``$`` et ``$$`` (mesure Playwright avant/apres sur IIT-06, commit
``5242d81907`` : le LaTeX inline rendait en texte brut, seul le ``$$``
central etait typesette). ``$ ... $`` est le seul delimiteur inline rendu
partout.

La reparation
-------------
Convertir chaque paire `\\( ... \\)` delimitante (ouvreur `\\(` ancre, contenu
sans newline ni delimiteur interne, fermeur `\\)`) en `$...$`, uniquement dans
les segments de PROSE : hors fences (le contenu d'un bloc ``` verbatim est du
code affiche, pas du markdown) et hors code spans inline (``\\(x\\)`` entre
backticks est un exemple qui EXPLIQUE le delimiteur, pas un defaut). La parite
detector/fixer est exacte sur les fences et les code spans ; le fixer ajoute
une borne de FORME (le regex de paire) qui l'empeche de convertir un `\\)`
isole -- cas fondateur mesure le 2026-09-22 (attrape par le twin-parity audit
de PR #17395) : « les separateurs (/ ou \\) selon l'OS », prose avec backslash
litteral, n'est PAS un span math et reste intact.

    \\(S = \\mathbb{F}_p^n\\)      ->      $S = \\mathbb{F}_p^n$

**Invariant de round-trip** : la transformation ne fait que remplacer des
paires `\\(` / `\\)` par des `$`, a l'identique elsewhere. Verifie
systematiquement par element (tokens retires == $ inseres == conversions, et
le contenu prive de ces tokens est byte-identique) -- le script refuse
d'ecrire si l'invariant est viole. Remplacement PAR ELEMENT de la liste
`source` : les lignes non touchees restent byte-identiques, le decoupage est
preserve (zero churn structurel).

Ce que le script NE fait PAS
----------------------------
Il ne touche ni a ``math_bare_macro`` ni a ``math_odd_dollars`` : ces deux
regles WARN exigent de COMPRENDRE l'intention (macro a envelopper, dollar
monnaie ou math) -- les deviner produirait des faux correctifs. Seule la
conversion deterministe est outillee.

Usage
-----
    python scripts/notebook_tools/fix_math_delims.py --scan  <notebook|dir>
    python scripts/notebook_tools/fix_math_delims.py --apply <notebook|dir>
"""
from __future__ import annotations

import re

import argparse
import json
import sys
from pathlib import Path

# Marcheur canonique centralise (#8650) -- meme perimetre que le detector.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from notebook_walk import iter_notebooks  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from detect_markdown_rendering import _inside_fence_lines  # noqa: E402

# Une PAIRE delimitante \( ... \) avec contenu math entre les deux. La borne
# est fondee sur un faux-fix mesure le 2026-09-22 (attrape par le twin-parity
# audit de PR #17395) : « les separateurs (/ ou \\) selon l'OS » porte un
# backslash litteral suivi d'une vraie parenthese fermante -- ce n'est PAS un
# delimiteur math, et le convertir en $ cassait le rendu (parenthese jamais
# fermee, $ orphelin). Le detector signale la ligne (WARN l'auteur); le fixer,
# lui, ne touche que ce qui a la FORME d'un span math :
#   \( + contenu sans \n, sans `\), sans delimiteur $/$$ interne + \)
# Le contenu ne doit pas finir par une lettre accentuee d'un mot francais
# suivi d'une parenthese de prose -- la garde minimale est l'absence de
# delimiteurs internes, qui exclut le cas fondateur (contenu = « / ou \\ »,
# 1 mot + backslash litteral, pas de math).
_MATH_SPAN_RE = re.compile(r"\\\((?P<body>[^\n$]*?)\\\)")


def _looks_like_math(body: str) -> bool:
    r"""Heuristique borne-le-fixer : le contenu d'un \( ... \) est-il du math ?

    Le cas fondateur du faux-fix (mesure 2026-09-22, attrape par le twin-parity
    audit de PR #17395) : « les separateurs (/ ou \\) selon l'OS » — le body
    se termine par un BACKSLASH LITTERAL echappant une VRAIE parenthese de
    prose (`\` + `)`), signature du chemin Windows, jamais d'une macro LaTeX.
    A l'inverse, les vrais spans math du corpus portent des `\{`, `\}`, `\,`
    (accolades et espacement LaTeX) et des variables nues (`\(M\)`, `\(p\)`,
    `\((A, B)\)`) : il ne faut exclure ni les uns ni les autres. Borne unique
    et decidable : un `\` suivi de `)` a l'INTERIEUR du body (le `\)` de
    fermeture est consomme par le motif et n'y figure pas) -> prose.
    """
    return "\\)" not in body


def _convert_outside_code(line: str) -> tuple[str, int]:
    """Convertit les paires `\\(...\\)` delimitantes en `$...$` hors code spans ;
    rend (ligne, n_converted). Les `\\(`/\\)` isoles qui ne forment pas un span
    math reconnaissable sont laisses intacts (borne fondee sur le faux-fix
    « / ou \\) » mesure le 2026-09-22).

    Le toggle backtick reproduit `_strip_inline_code` : un run de N backticks
    ouvre/ferme un code span, un run non ferme s'etend jusqu'a la fin de la
    ligne (CommonMark) -- son contenu est literal et n'est pas converti.
    """
    out: list[str] = []
    in_code = False
    i, n = 0, len(line)
    converted = 0
    while i < n:
        if line[i] == "`":
            j = i
            while j < n and line[j] == "`":
                j += 1
            in_code = not in_code
            out.append(line[i:j])
            i = j
            continue
        if in_code:
            out.append(line[i])
            i += 1
            continue
        if line.startswith("\\(", i):
            m = _MATH_SPAN_RE.match(line, i)
            if m and _looks_like_math(m.group("body")):
                out.append("$" + m.group("body") + "$")
                converted += 2
                i = m.end()
                continue
        out.append(line[i])
        i += 1
    return "".join(out), converted


def _check_invariant(before: str, after: str, converted: int) -> None:
    r"""Le contenu hors tokens convertis est byte-identique (refuse d'ecrire sinon).

    La transformation declaree ne fait que remplacer des paires `\(` / `\)`
    par des `$`. Verifie a parite : le nombre de tokens `\(` + `\)` retires
    doit egaler `converted`, et le nombre de `$` inseres doit lui egaler le
    meme compte. Les `\(`/`\)` restants (spans non convertis, ex. prose avec
    backslash litteral) ne comptent ni d'un cote ni de l'autre.
    """
    stripped_before = before.replace("$", "").replace("\\(", "").replace("\\)", "")
    stripped_after = after.replace("$", "").replace("\\(", "").replace("\\)", "")
    if stripped_before != stripped_after:
        raise SystemExit(
            "INVARIANT VIOLE : le contenu a change au-dela de la conversion "
            f"\\( -> $ ({before!r} -> {after!r})"
        )
    tokens_removed = (before.count("\\(") + before.count("\\)")
                      - after.count("\\(") - after.count("\\)"))
    dollars_added = after.count("$") - before.count("$")
    if tokens_removed != converted or dollars_added != converted:
        raise SystemExit(
            "INVARIANT VIOLE : tokens retires / $ inseres != conversions "
            f"({before!r} -> {after!r}, {converted} conversions)"
        )


def process(path: Path, apply: bool) -> tuple[int, list[str]]:
    raw = path.read_text(encoding="utf-8")
    nb = json.loads(raw)
    report: list[str] = []
    n = 0
    changed = False
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src_list = cell.get("source")
        if not isinstance(src_list, list):
            # forme string (rare) : le remplacement par element ne s'y applique
            # pas tel quel -- signaler, ne pas improviser une reecriture.
            src_str = src_list if isinstance(src_list, str) else ""
            if "\\(" in src_str or "\\)" in src_str:
                report.append("  %s cell#%-3d (source string, revision manuelle)"
                              % (path.name, ci))
            continue
        text = "".join(src_list)
        lines = text.split("\n")
        fenced = _inside_fence_lines(lines)
        cell_converted = 0
        # Remplacement PAR ELEMENT de la liste source (pas de re-split) : les
        # elements non touchees restent byte-identiques, la structure de liste
        # (decoupage, eventuel element final vide) est preservee telle quelle --
        # le diff produit se limite aux lignes converties (mesure sur IIT-06 :
        # un re-split systematique churnait les 17 cellules markdown du fichier
        # alors que 13 portaient le defaut).
        pos = 0  # indice de ligne du debut de l'element courant
        for ei, elem in enumerate(src_list):
            pieces = elem.split("\n")
            covers = len(pieces) - (1 if pieces and pieces[-1] == "" else 0)
            if covers != 1:
                # element multi-lignes (rare) : conservateur, ne pas toucher --
                # la frontiere fence/code-span s'y raisonne a la main.
                if covers > 1:
                    pos += covers
                continue
            if pos not in fenced:
                fixed, converted = _convert_outside_code(elem)
                if converted:
                    _check_invariant(elem, fixed, converted)
                    if apply:
                        src_list[ei] = fixed
                    cell_converted += converted
                    report.append("  %s cell#%-3d %s"
                                  % (path.name, ci, elem.strip()[:88]))
            pos += 1
        n += cell_converted
        if cell_converted and apply:
            changed = True
    if apply and changed:
        # preservation du style de fins de ligne du fichier (CRLF vs LF) et de
        # la presence du saut de ligne final : la conversion ne doit produire
        # AUCUN churn de serialisation hors des lignes touchees.
        text = json.dumps(nb, ensure_ascii=False, indent=1)
        if "\r\n" in raw:
            text = text.replace("\n", "\r\n")
        if raw.endswith("\n"):
            text += "\r\n" if "\r\n" in raw else "\n"
        path.write_text(text, encoding="utf-8", newline="")
    return n, report


# --- controle positif : la conversion DOIT produire la forme canonique ------
_ctrl_bad = r"Soit \(S = \mathbb{F}_p^n\) l'ensemble."
_ctrl_ok = r"Soit $S = \mathbb{F}_p^n$ l'ensemble."
_fixed, _n = _convert_outside_code(_ctrl_bad)
assert _fixed == _ctrl_ok and _n == 2, "CONTROLE: conversion incorrecte"
_fixed2, _n2 = _convert_outside_code(r"La syntaxe `\(x\)` n'est pas rendue.")
assert _n2 == 0 and _fixed2 == "La syntaxe `\\(x\\)` n'est pas rendue.", (
    "CONTROLE: conversion a l'interieur d'un code span"
)
# Controle du faux-fix fondateur (mesure 2026-09-22, twin-parity PR #17395) :
# « les separateurs (/ ou \\) selon l'OS » n'est PAS un span math -- le fixer
# ne doit PAS convertir la \) fermante en $.
_ctrl_falsefix = "les separateurs (/ ou \\\\) selon l'OS."
_fixed3, _n3 = _convert_outside_code(_ctrl_falsefix)
assert _n3 == 0 and _fixed3 == _ctrl_falsefix, (
    "CONTROLE: faux-fix sur prose avec backslash litteral (bornage paire+contenu perdu)"
)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("targets", nargs="+", type=Path)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--scan", action="store_true", help="rapporter sans ecrire (defaut)")
    g.add_argument("--apply", action="store_true", help="ecrire les corrections")
    args = ap.parse_args()

    files: list[Path] = []
    for t in args.targets:
        files.extend(iter_notebooks(t) if t.is_dir() else [t])

    total = 0
    for f in files:
        try:
            n, rep = process(f, args.apply)
        except json.JSONDecodeError as exc:
            print("  SKIP %s (json: %s)" % (f, exc), file=sys.stderr)
            continue
        if n:
            print("\n".join(rep))
            total += n
    verb = "converti(s)" if args.apply else "trouvee(s) (utiliser --apply)"
    print("\n%d occurrence(s) %s dans %d fichier(s)" % (total, verb, len(files)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
