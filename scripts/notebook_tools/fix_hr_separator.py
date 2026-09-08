#!/usr/bin/env python3
"""Convertit les separateurs horizontaux `---` en `***` dans les cellules markdown.

Pourquoi
--------
Une ligne `---` seule ouvre un bloc de metadonnees YAML au sens Pandoc
(`yaml_metadata_block`), referme par un `---` ou `...` ulterieur. Dans un
notebook, un `---` ecrit comme separateur horizontal en debut de cellule ouvre
un tel bloc ; la prose et les titres des cellules suivantes sont alors lus
comme des paires cle/valeur -> `YAMLException` -> `quarto render` echoue.
Comme Quarto s'arrete au PREMIER echec, un seul notebook fait tomber tout le
site (incident #11451, 2026-08-17).

`***` rend exactement le meme `<hr>` en markdown et n'a aucune semantique YAML.
C'est la conversion appliquee ici.

Ce que l'outil NE touche PAS
----------------------------
- les `---` a l'interieur d'un bloc de code (``` ou ~~~) ;
- les `---` qui SOULIGNENT du texte : un `---` colle a une ligne non vide est
  un titre setext H2, pas un separateur — le convertir changerait le rendu ;
- un VRAI bloc de frontmatter en tete de notebook (cellule 0 commencant par
  `---` dont le contenu parse en mapping YAML) : Quarto s'en sert
  legitimement pour le titre, l'auteur, les options de rendu.

Distinction avec `detect_markdown_rendering.py`
-----------------------------------------------
Ce dernier vise les defauts de rendu VISUEL (bloc surdimensionne a l'ouverture)
cellule par cellule. Le present outil vise l'echec de BUILD Quarto, qui est
CROSS-CELLULE par nature (le `---` ouvrant et le `---` fermant sont dans deux
cellules differentes). Les deux populations se recouvrent sans coincider.

Usage
-----
    python scripts/notebook_tools/fix_hr_separator.py --check MyIA.AI.Notebooks/GameTheory
    python scripts/notebook_tools/fix_hr_separator.py --apply MyIA.AI.Notebooks/GameTheory

Sortie : 0 si rien a convertir (--check) ou conversion faite (--apply),
1 si des separateurs restent a convertir (--check), 2 en cas d'erreur.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

FENCE_RE = re.compile(r"^(`{3,}|~{3,})")
HR = "---"
REPLACEMENT = "***"


def _lines(source) -> list[str]:
    """Rend les lignes d'une source de cellule, quel que soit son encodage nbformat."""
    if isinstance(source, list):
        return "".join(source).split("\n")
    return (source or "").split("\n")


def _is_real_frontmatter(lines: list[str]) -> bool:
    """Vrai si la cellule EST un bloc de frontmatter YAML legitime.

    Forme : premiere ligne `---`, une ligne `---`/`...` de fermeture plus bas,
    et un contenu qui ressemble a des paires cle/valeur (au moins une ligne
    `cle: valeur` et aucune ligne de prose evidente). On reste volontairement
    grossier : en cas de doute on considere que c'en est un et on ne touche pas.
    """
    if not lines or lines[0].strip() != HR:
        return False
    close = None
    for i in range(1, len(lines)):
        if lines[i].strip() in (HR, "..."):
            close = i
            break
    if close is None:
        return False
    body = [x for x in lines[1:close] if x.strip()]
    if not body:
        return False
    return any(re.match(r"^[A-Za-z_][A-Za-z0-9_.-]*\s*:", x) for x in body)


def convert_cell(source, is_first_cell: bool) -> tuple[object, int]:
    """Rend (nouvelle_source, nb_conversions) pour une source de cellule markdown."""
    lines = _lines(source)
    if is_first_cell and _is_real_frontmatter(lines):
        return source, 0

    in_fence = False
    changed = 0
    out: list[str] = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if FENCE_RE.match(stripped):
            in_fence = not in_fence
            out.append(line)
            continue
        if in_fence or stripped != HR:
            out.append(line)
            continue
        prev = lines[i - 1].strip() if i > 0 else ""
        if prev != "":
            out.append(line)  # soulignement setext : ne pas toucher
            continue
        out.append(line.replace(HR, REPLACEMENT, 1))
        changed += 1

    if not changed:
        return source, 0

    text = "\n".join(out)
    if isinstance(source, list):
        parts = text.split("\n")
        return [p + "\n" for p in parts[:-1]] + ([parts[-1]] if parts[-1] else []), changed
    return text, changed


def _raw_decode(text: str, i: int):
    """Decode un token JSON (string, nombre, bool, null) via le decodeur standard."""
    return json.JSONDecoder().raw_decode(text, i)


def _parse_spans(text: str):
    """Parse la JSON du notebook et enregistre les offsets bytes de chaque string literal.

    Retourne ``(nb, literal_spans)`` ou ``literal_spans`` est une liste de tuples
    ``(start, end, decoded, path)`` : ``start``/``end`` sont les offsets bytes du
    literal dans ``text``, ``decoded`` sa valeur decodee, ``path`` son chemin JSON
    (ex. ``("cells", 3, "source", 1)`` pour l'element 1 de la source de la cellule 3).
    """
    literal_spans = []

    def skip(i):
        while i < len(text) and text[i] in " \t\r\n":
            i += 1
        return i

    def parse(i, path):
        i = skip(i)
        c = text[i]
        if c == '"':
            val, end = _raw_decode(text, i)
            literal_spans.append((i, end, val, path))
            return val, end
        if c == "{":
            i += 1
            obj = {}
            while True:
                i = skip(i)
                if text[i] == "}":
                    i += 1
                    break
                k, i = parse(i, path)
                i = skip(i)
                if text[i] == ":":
                    i += 1
                v, i = parse(i, path + (k,))
                obj[k] = v
                i = skip(i)
                if text[i] == ",":
                    i += 1
            return obj, i
        if c == "[":
            i += 1
            arr = []
            idx = 0
            while True:
                i = skip(i)
                if text[i] == "]":
                    i += 1
                    break
                v, i = parse(i, path + (idx,))
                arr.append(v)
                idx += 1
                i = skip(i)
                if text[i] == ",":
                    i += 1
            return arr, i
        val, end = _raw_decode(text, i)
        return val, end

    nb, _ = parse(0, ())
    return nb, literal_spans


def _literal_offset_map(lit: str, decoded: str) -> list[int]:
    """Map index de char decode -> offset byte dans ``lit`` (le literal, guillemets inclus).

    ``lit`` est la tranche brute ``text[start:end]`` du literal JSON ; ``decoded`` sa
    valeur decodee. Retourne une liste de longueur ``len(decoded)`` : le k-ième élément
    est l'offset byte (dans ``lit``) du k-ième caractère décodé. Les paires de
    surrogates (``\\uD800\\uDC00``) comptent pour un seul caractère décodé.
    """
    inner = lit[1:-1]
    out = []
    ri = 0
    di = 0
    n = len(inner)
    while ri < n and di < len(decoded):
        out.append(ri + 1)  # +1 : guillemet ouvrant
        ch = inner[ri]
        if ch == "\\":
            c2 = inner[ri + 1] if ri + 1 < n else ""
            if c2 == "u":
                j = ri + 2
                hexs = inner[j:j + 4]
                cp = int(hexs, 16) if hexs else -1
                ri = j + 4
                if 0xD800 <= cp <= 0xDBFF and ri + 6 <= n and inner[ri:ri + 2] == "\\u":
                    ri += 6  # paire de surrogates : un seul char décodé
            else:
                ri += 2
        else:
            ri += 1
        di += 1
    return out


def _source_spans_by_cell(literal_spans: list) -> dict:
    """Regroupe les spans de source par index de cellule, pour les cellules markdown."""
    by_cell = {}
    for (s, e, d, p) in literal_spans:
        if len(p) >= 3 and p[0] == "cells" and p[2] == "source":
            by_cell.setdefault(p[1], []).append((s, e, d))
    return by_cell


def _cell_edits(raw: str, old_src, new_src, spans: list):
    """Calcule les edits bytes ``(start, end, replacement)`` pour une cellule.

    Compare la source decodee aplatie avant/après conversion et ne retient que les
    positions exactes ou ``---`` devient ``***``. Retourne ``None`` si la longueur
    ne se réconcilie pas (extraction impossible), sinon la liste des edits.
    """
    if not spans:
        return None
    flat_chars = []
    raw_offsets = []
    for (s, e, d) in spans:
        lit = raw[s:e]
        offs = _literal_offset_map(lit, d)
        flat_chars.append(d)
        raw_offsets.extend(s + o for o in offs)
    flat_old = "".join(flat_chars)
    flat_new = "".join(new_src) if isinstance(new_src, list) else new_src
    if len(flat_new) != len(flat_old) or len(raw_offsets) != len(flat_old):
        return None

    edits = []
    i = 0
    while i <= len(flat_old) - 3:
        if flat_old[i:i + 3] == HR and flat_new[i:i + 3] == REPLACEMENT:
            edits.append((raw_offsets[i], raw_offsets[i] + 3, REPLACEMENT))
            i += 3
        else:
            i += 1
    return edits


def _count_conversions(nb) -> int:
    """Nombre de separateurs convertibles, sans ecrire (reutilise convert_cell)."""
    total = 0
    seen_markdown = False
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        first = not seen_markdown
        seen_markdown = True
        _, n = convert_cell(cell.get("source"), first)
        total += n
    return total


def _apply_byte_preserving(raw: str, nb, expected_total: int):
    """Applique les conversions de facon byte-preserving.

    Ne modifie que les fragments de source markdown eligibles ; tout le reste du
    fichier (code, outputs, execution_count, metadata, nbsp interne des chaines
    HTML) est preserve octet par octet. Retourne le nouveau texte, ou ``None`` si
    le nombre de mutations texte ne se reconcilie pas avec ``expected_total``.
    """
    _, literal_spans = _parse_spans(raw)
    cells = nb.get("cells", [])
    by_cell = _source_spans_by_cell(literal_spans)

    edits = []
    seen_markdown = False
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        first = not seen_markdown
        seen_markdown = True
        old_src = cell.get("source")
        new_src, n = convert_cell(old_src, first)
        if not n:
            continue
        spans = by_cell.get(i)
        cell_edits = _cell_edits(raw, old_src, new_src, spans)
        if cell_edits is None or len(cell_edits) != n:
            return None
        edits.extend(cell_edits)

    if len(edits) != expected_total:
        return None

    # Chaque mutation doit porter sur un vrai separateur `---` dans le texte brut,
    # sans quoi la substitution ecrirait des octets hors cible (echouer sans ecrire).
    edits.sort(key=lambda e: e[0], reverse=True)
    for (s, e, repl) in edits:
        if raw[s:e] != HR:
            return None
        raw = raw[:s] + repl + raw[e:]
    return raw


def process(path: Path, apply: bool) -> int:
    """Rend le nombre de separateurs convertis (ou convertibles si apply=False).

    ``apply=True`` ecrit de facon byte-preserving : seule la source markdown
    eligible change ; code, outputs, metadata et whitespace interne restent
    intactes. Lève ``RuntimeError`` (rien n'est ecrit) si le nombre de mutations
    texte ne se reconcilie pas avec le nombre de conversions calcule.
    """
    # Lecture/ecriture en MODE BINAIRE : le mode texte de Windows convertirtait
    # les fins de ligne LF/CRLF, ce qui casserait la preservation byte-a-byte.
    # decode/encode utf-8 sans traduction de newline : les octets hors cible
    # restent exactement ceux du fichier d'entree.
    try:
        raw_bytes = path.read_bytes()
    except OSError as exc:
        print(f"ILLISIBLE {path}: {exc}", file=sys.stderr)
        return 0
    try:
        raw = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        print(f"ILLISIBLE {path}: {exc}", file=sys.stderr)
        return 0
    try:
        nb = json.loads(raw)
    except ValueError as exc:
        print(f"ILLISIBLE {path}: {exc}", file=sys.stderr)
        return 0

    total = _count_conversions(nb)
    if not total:
        return 0
    if not apply:
        return total

    new_raw = _apply_byte_preserving(raw, nb, total)
    if new_raw is None:
        raise RuntimeError(
            f"reconciliation ECHOUE sur {path} : {total} conversion(s) calculee(s) "
            f"mais mutations textuelles non reconciliees — rien n'a ete ecrit"
        )
    path.write_bytes(new_raw.encode("utf-8"))
    return total


def iter_notebooks(targets: list[str]):
    for t in targets:
        p = Path(t)
        if p.is_dir():
            for nb in sorted(p.rglob("*.ipynb")):
                s = str(nb).replace("\\", "/")
                if "/.ipynb_checkpoints/" in s or s.endswith("_output.ipynb"):
                    continue
                yield nb
        elif p.suffix == ".ipynb":
            yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="ne rien ecrire, compter")
    mode.add_argument("--apply", action="store_true", help="ecrire les conversions")
    ap.add_argument("targets", nargs="+", help="fichiers .ipynb ou repertoires")
    args = ap.parse_args(argv)

    files = 0
    seps = 0
    for nb in iter_notebooks(args.targets):
        try:
            n = process(nb, apply=args.apply)
        except RuntimeError as exc:
            print(f"ECHEC {nb}: {exc}", file=sys.stderr)
            return 2
        if n:
            files += 1
            seps += n
            verbe = "converti" if args.apply else "a convertir"
            print(f"  {nb.as_posix()} : {n} separateur(s) {verbe}")

    verbe = "convertis" if args.apply else "a convertir"
    print(f"{seps} separateur(s) {verbe} dans {files} notebook(s)")
    if args.check and seps:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
