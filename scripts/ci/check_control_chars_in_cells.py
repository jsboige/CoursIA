#!/usr/bin/env python3
"""check_control_chars_in_cells.py - garde caracteres de controle dans les sources de cellules.

Source : issue #18048. Un outil d'ecriture qui interprete les echappements
Python transforme ``\\a``, ``\\b``, ``\\f`` ou ``\\v`` d'une source de cellule
en caractere de controle (BEL, backspace, VT, FF). Le JSON reste valide (les
controles y sont echappes ``\\u0007`` / ``\\b`` / ``\\f``), le notebook
s'execute, aucun organe ne rougissait -- mais le rendu est casse : LaTeX
illisible, regex affichee fausse.

Temoins fondateurs (les deux du body de #18048, en test dans
scripts/tests/test_check_control_chars_in_cells.py) :
  - tete f19ca6ff91 de la PR #17919 (MGS-01-Introduction, cellule 10
    markdown) : 3x U+0007 dans ``$\\sigma <BEL>pprox 12$`` (intention :
    ``\\approx``) ;
  - main, auditer-la-conformite-visuelle.ipynb cellule 18 (markdown) :
    U+0008 dans ``un `<BS>` apres les six chiffres`` (intention : la
    frontiere ``\\b`` d'une regex).

Garde : sur le diff d'une PR, refuse toute source de cellule AJOUTEE ou
MODIFIEE contenant U+0007, U+0008, U+000B ou U+000C. Le stock herite ne
rougit pas : une cellule dont la source, controle compris, est presente a
l'identique dans la base est exempee (le garde porte sur le delta, pas sur
la dette). Un notebook du diff illisible en JSON mais portant un octet de
controle BRUT est aussi un constat (l'outil a ecrit l'octet tel quel cette
fois-ci, et aucun lecteur JSON strict ne l'acceptera).

Verdict :
  exit 0 = aucune source ajoutee/modifiee ne porte de caractere de controle
  exit 1 = au moins un constat (nomme la cellule, propose l'echappement)
  exit 2 = incident d'entree (git en echec, notebook du diff illisible SANS
           controle brut) -- neutre au check-run via warn_rc=(2,) :
           un depot sans verdict reste un depot sans garde, mais on
           n'accuse pas une PR sur une mesure qui n'a pas eu lieu

Usage :
  python scripts/ci/check_control_chars_in_cells.py --diff origin/main...HEAD
  python scripts/ci/check_control_chars_in_cells.py --self
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

# Les 4 echappements Python sans equivalent visible : le caractere de
# controle obtenu -> l'echappement PROBABLE que l'auteur voulait ecrire
# (texte litteral backslash + lettre).
CONTROL_CHARS: dict[int, str] = {0x07: "\\a", 0x08: "\\b", 0x0B: "\\v", 0x0C: "\\f"}
CHAR_NAMES: dict[int, str] = {0x07: "BEL", 0x08: "BS", 0x0B: "VT", 0x0C: "FF"}

EXCERPT_RADIUS = 30


def cell_sources(nb: dict) -> list[dict]:
    """Sources de cellules decodees d'un notebook charge.

    Le champ ``source`` peut etre une liste de lignes (nbformat standard)
    ou une chaine (variantes d'outils) ; les deux sont normalisees.
    """
    cells = []
    for i, cell in enumerate(nb.get("cells", [])):
        raw = cell.get("source", "")
        if isinstance(raw, list):
            raw = "".join(raw)
        cells.append({
            "index": i,
            "type": cell.get("cell_type", "?"),
            "source": raw,
        })
    return cells


def compare_cells(head_cells: list[dict], base_cells: list[dict]) -> list[dict]:
    """Constats sur les cellules ajoutees ou modifiees entre base et head.

    Une source presente A L'IDENTIQUE dans la base (meme deplacee ou
    reindexee) est du stock, pas du delta : jamais de constat dessus.
    """
    base_stock = [c["source"] for c in base_cells]
    findings: list[dict] = []
    for cell in head_cells:
        present = sorted({ord(cp) for cp in cell["source"] if ord(cp) in CONTROL_CHARS})
        if not present:
            continue
        if cell["source"] in base_stock:
            base_stock.remove(cell["source"])
            continue
        first = cell["source"].index(chr(present[0]))
        excerpt = cell["source"][max(0, first - EXCERPT_RADIUS):first + EXCERPT_RADIUS]
        findings.append({
            "cell_index": cell["index"],
            "cell_type": cell["type"],
            "chars": present,
            "excerpt": excerpt,
        })
    return findings


def scan_raw_control_bytes(blob: bytes) -> list[int]:
    """Octets de controle PRESENTS BRUTS dans le fichier (JSON invalide)."""
    return sorted({b for b in blob if b in CONTROL_CHARS})


def excerpt_around(blob: bytes, byte: int) -> str:
    i = blob.find(bytes([byte]))
    window = blob[max(0, i - EXCERPT_RADIUS):i + EXCERPT_RADIUS]
    return repr(window.decode("utf-8", errors="replace"))


def run_git(args: list[str]) -> bytes:
    out = subprocess.run(args, capture_output=True)
    if out.returncode != 0:
        sys.stderr.write(f"git {args[:2]} en echec: {out.stderr.decode(errors='replace')}\n")
        sys.exit(2)
    return out.stdout


def changed_notebooks(base_ref: str) -> list[str]:
    out = run_git([
        "git", "diff", "--name-only", "-z", "--diff-filter=ACMR",
        f"{base_ref}...HEAD", "--", "*.ipynb",
    ])
    return [p for p in out.decode("utf-8").split("\0") if p]


def base_rev_of(range_spec: str) -> str:
    """Rev de base d'un spec de range git (a...b ou a..b -> a)."""
    return range_spec.split("...")[0].split("..")[0]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--diff", metavar="RANGE",
                      help="range git a scanner (ex : origin/main...HEAD)")
    mode.add_argument("--self", action="store_true",
                      help="scanner l'arbre de travail contre HEAD")
    args = parser.parse_args(argv)

    # --self compare l'arbre de travail contre HEAD (deux points) ; --diff
    # compare le merge-base de la base a HEAD (trois points, forme du
    # registre : {base_ref}...HEAD).
    if args.self:
        base_ref = "HEAD"
        out = run_git([
            "git", "diff", "--name-only", "-z", "--diff-filter=ACMR",
            "HEAD", "--", "*.ipynb",
        ])
        paths = [p for p in out.decode("utf-8").split("\0") if p]
    else:
        base_ref = base_rev_of(args.diff)
        paths = changed_notebooks(base_ref)

    if not paths:
        print(f"[control-chars] 0 notebook dans le diff contre {base_ref} : rien a scanner")
        return 0

    findings: list[str] = []
    incidents: list[str] = []
    for path in paths:
        disk = Path(path)
        if not disk.exists():
            continue  # supprime dans l'arbre : hors scope (filtre ACMR du range)
        blob = disk.read_bytes()
        try:
            head_nb = json.loads(blob.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            raw = scan_raw_control_bytes(blob)
            if raw:
                for b in raw:
                    findings.append(
                        f"constat: {path} : octet de controle BRUT U+{b:04X} "
                        f"({CHAR_NAMES[b]}) -- le fichier n'est meme pas un JSON "
                        f"valide ; echappement probable : `{CONTROL_CHARS[b]}` "
                        f"(backslash + lettre). Extrait: {excerpt_around(blob, b)}")
            else:
                incidents.append(f"{path} : JSON illisible sans octet de controle")
            continue

        # Rev de base sans le fichier = notebook AJOUTE : base vide. On
        # sonde d'abord l'existence (cat-file -e, chemin POSIX tel que
        # rendu par git diff -z) au lieu de laisser git show echouer.
        probe = subprocess.run(
            ["git", "cat-file", "-e", f"{base_ref}:{path}"], capture_output=True)
        if probe.returncode != 0:
            base_cells: list[dict] = []
        else:
            base_blob = run_git(["git", "show", f"{base_ref}:{path}"])
            try:
                base_nb = json.loads(base_blob.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError):
                sys.stderr.write(f"{path} : base illisible a {base_ref}\n")
                return 2
            base_cells = cell_sources(base_nb)

        for f in compare_cells(cell_sources(head_nb), base_cells):
            chars = ", ".join(
                f"U+{cp:04X} ({CHAR_NAMES[cp]}) -> `{CONTROL_CHARS[cp]}`"
                for cp in f["chars"])
            findings.append(
                f"constat: {path} cellule {f['cell_index']} ({f['cell_type']}) : "
                f"caractere(s) de controle {chars} (echappement probable : "
                f"backslash + lettre, a ecrire en texte litteral). "
                f"Extrait: {f['excerpt']!r}")

    for line in findings:
        print(line)
    if findings:
        print(f"[control-chars] {len(findings)} constat(s) sur {len(paths)} notebook(s) du diff")
        return 1
    if incidents:
        for line in incidents:
            sys.stderr.write(f"incident: {line}\n")
        return 2
    print(f"[control-chars] 0 constat sur {len(paths)} notebook(s) du diff")
    return 0


if __name__ == "__main__":
    sys.exit(main())
