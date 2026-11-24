#!/usr/bin/env python3
"""Genere la table « Statut de maturite » du README de la serie Lean.

Defaut mesure (#17545) : la table etait une copie manuelle completement
derivee. Sur 18 lignes echantillonnees, la colonne « Cellules » ne matchait
`cells_total` que 5 fois et `cells_code` que 5 fois -- elle ne suivait aucune
unite stable. 15 carnets documentes dans la table de description (dont
Lean-33) en etaient absents, 5 lignes orphelines referenceaient des carnets
descendus en sous-series sous leur nom d'avant gradation, et la colonne
« Solutions » melangeait des comptes (0/2/3) et des mots (Oui/Non/-) sans
marqueur mecanique dans les carnets (les solutions y sont de la prose,
« Solution proposee par ... », jamais un heading).

La table generee est l'**image de la table de description** : une ligne par
carnet_linked, dans l'ordre de lecture du README, avec deux colonnes
mesurees --

  - « Cellules (code) » : nombre de cellules `code` du carnet. C'est l'unite
    que la prose du README utilise deja (« 17 cellules code », « 11 cellules
    code ») et que le catalogue publie (`cells_code`).
  - « Exercices » : nombre de headings markdown `##..#### Exercice ...`.
    C'est la structure qu'un lecteur compte en parcourant le carnet ; c'est
    aussi le marqueur le plus proche des valeurs declarees (10/11 des « 3 »
    declares matchent ce compte, contre aucun marqueur TODO).

La colonne « Statut » reste editoriale : le generateur la preserve
verbatim pour les ids existants et pose `**NOUVEAU** (kernel ...)`, kernel
mesure, pour les ids qu'il ajoute. La colonne « Solutions » est retiree :
aucun marqueur mecanique ne la fonde (voir docstring ci-dessus) et ses
valeurs mixtes n'avaient pas de semantique stable.

Les lignes orphelines (ids absents de la table de description) sont
retirees : les carnets qu'elles referenceent sont descendus en sous-series
(KNOTS, GALOIS, ANALYSE, Langlands) et chacun vit dans le README de sa
sous-serie -- c'est la ou sa maturite est documentee.

Usage :
    python scripts/lean/lean_series_maturity.py --check   # rc 0/1/2
    python scripts/lean/lean_series_maturity.py --write   # regenere la table

Codes de sortie (contrat de `check_lean_derived_pages.py`) :
    0 = table conforme ;
    1 = divergence (regenerer par `--write`) ;
    2 = mesure impossible (un carnet_linked est illisible) -- rien n'est
        ecrit, la page sur disque reste intacte.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PAGE = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "README.md"

UNMEASURABLE_RC = 2

SECTION_HEADING = "## Statut de maturité"
TABLE_HEADER = "| # | Notebook | Cellules (code) | Exercices | Statut |"
TABLE_SEPARATOR = "|---|----------|-----------------|-----------|--------|"

# Identifiant de ligne : numerique (16, 16b) ou prefixe de sous-serie
# (GOL-07, KNOTS-03, ANALYSE-14, MIMO-04, GROTH-02, GALOIS-01).
# Suffixe lettre jusqu'a z : la serie a passe g (13h, renumerotation #26536).
_ID = r"(?:[A-Z]+-)?\d{1,2}[a-z]?"

# Ligne de la table de description : | 16b | [Nom](chemin.ipynb) ... |
# La cellule peut porter PLUSIEURS liens (ANALYSE-09 y cite son jumeau _en) :
# on prend le premier lien qui n'est pas un artefact d'execution
# (`*_output.ipynb`), jamais la ligne entiere pour un artefact en tete.
DESC_ROW = re.compile(r"^\| (%s) \| (.*)$" % _ID)
LINK = re.compile(r"\[([^\]]+)\]\(([^)]+\.ipynb)\)")

# Ligne de la table de maturite existante : | 16b | Nom | ... | statut |
MAT_ROW = re.compile(r"^\| (%s) \|" % _ID)

# Heading d'exercice dans une cellule markdown : ## a #### « Exercice ... ».
EXERCICE_HEADING = re.compile(r"^#{2,4}\s*Exercice\b", re.MULTILINE)


@dataclass(frozen=True)
class Notebook:
    """Un carnet_linked par la table de description, avec sa mesure."""

    ident: str
    name: str
    rel_path: str
    cells_code: int
    exercises: int
    kernel: str

    def row(self, statut: str) -> str:
        return "| %s | [%s](%s) | %d | %d | %s |" % (
            self.ident, self.name, self.rel_path, self.cells_code,
            self.exercises, statut)


def _measure(ident: str, name: str, rel_path: str) -> Notebook:
    """Mesure un carnet. Leve FileNotFoundError/OSError/JSONDecodeError."""
    path = PAGE.parent / rel_path
    nb = json.loads(path.read_text(encoding="utf-8"))
    cells = nb.get("cells", [])
    cells_code = sum(1 for c in cells if c.get("cell_type") == "code")
    md_text = "\n".join(
        "".join(c.get("source", [])) for c in cells
        if c.get("cell_type") == "markdown")
    exercises = len(EXERCICE_HEADING.findall(md_text))
    kernelspec = nb.get("metadata", {}).get("kernelspec", {})
    kernel = kernelspec.get("name", "inconnu")
    return Notebook(ident, name, rel_path, cells_code, exercises, kernel)


def parse_description(lines: list[str]) -> list[tuple[str, str, str]]:
    """Les (id, nom, chemin) lies par la table de description, en ordre.

    Ne lit que ce qui PRECEDE la section « Statut de maturite » : la table
    regeneree a la meme forme de ligne (| id | [nom](chemin) | ...) et se
    re-parserait elle-meme, doublant l'image a chaque passage.
    """
    cutoff = len(lines)
    for i, line in enumerate(lines):
        if line.strip() == SECTION_HEADING:
            cutoff = i
            break
    out: list[tuple[str, str, str]] = []
    for line in lines[:cutoff]:
        m = DESC_ROW.match(line)
        if not m:
            continue
        ident, cell = m.group(1), m.group(2)
        for name, path in LINK.findall(cell):
            if path.endswith("_output.ipynb"):
                continue  # artefact d'execution, pas un carnet de la serie
            out.append((ident, name, path))
            break
    return out


def parse_statuts(lines: list[str]) -> dict[str, str]:
    """Les statuts editoriaux de la table de maturite actuelle, par id."""
    statuts: dict[str, str] = {}
    for line in lines:
        m = MAT_ROW.match(line)
        if not m or line.startswith(TABLE_SEPARATOR):
            continue
        parts = [p.strip() for p in line.split("|")]
        # ['', id, nom, cellules, exercices, [solutions,] statut, '']
        if len(parts) >= 6:
            statuts[m.group(1)] = parts[-2]
    return statuts


def _section_bounds(lines: list[str]) -> tuple[int, int]:
    """(debut, fin) de la table de maturite : premiere ligne d'en-tete
    apres le heading de section, et premiere ligne non-table apres le corps.
    Leve ValueError si la section ou la table est introuvable."""
    try:
        start = next(i for i, l in enumerate(lines)
                     if l.strip() == SECTION_HEADING)
    except StopIteration:
        raise ValueError("section %r introuvable" % SECTION_HEADING)
    header_idx = next(i for i in range(start + 1, len(lines))
                      if lines[i].startswith("|"))
    end = header_idx + 1
    while end < len(lines) and lines[end].startswith("|"):
        end += 1
    return header_idx, end


def build_table(readme_lines: list[str]) -> tuple[list[str], dict[str, list[str]]]:
    """La table attendue + le rapport (ajouts, retraits, statuts herites).

    Leve FileNotFoundError/OSError/ValueError si la mesure est impossible.
    """
    desc = parse_description(readme_lines)
    if not desc:
        raise ValueError("table de description vide ou introuvable")
    header_idx, end = _section_bounds(readme_lines)
    statuts = parse_statuts(readme_lines[header_idx:end])

    rows: list[str] = []
    report: dict[str, list[str]] = {"ajouts": [], "retraits": []}
    for ident, name, rel_path in desc:
        nb = _measure(ident, name, rel_path)
        if ident in statuts:
            statut = statuts[ident]
        else:
            statut = "**NOUVEAU** (kernel `%s`)" % nb.kernel
            report["ajouts"].append("%s %s" % (ident, name))
        rows.append(nb.row(statut))

    for ident in statuts:
        if ident not in {d[0] for d in desc}:
            report["retraits"].append(ident)
    return [TABLE_HEADER, TABLE_SEPARATOR] + rows, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true",
                      help="rend 1 si la table diverge, 0 sinon")
    mode.add_argument("--write", action="store_true",
                      help="regenere la table sur disque")
    args = parser.parse_args(argv)

    lines = PAGE.read_text(encoding="utf-8").splitlines()
    try:
        expected, report = build_table(lines)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print("UNMEASURABLE: %s" % exc)
        return UNMEASURABLE_RC

    header_idx, end = _section_bounds(lines)
    current = lines[header_idx:end]

    if report["ajouts"]:
        print("ajouts: %s" % ", ".join(report["ajouts"]))
    if report["retraits"]:
        print("retraits (sous-series, voir leur README): %s"
              % ", ".join(report["retraits"]))

    if args.check:
        if current == expected:
            print("OK: table de maturite = image de la table de description"
                  " (%d carnets)." % (len(expected) - 2))
            return 0
        print("DIVERGENTE: %d lignes attendues vs %d sur disque."
              % (len(expected), len(current)))
        for i, (a, b) in enumerate(zip(current, expected)):
            if a != b:
                print("  sur disque : %s" % a)
                print("  attendu    : %s" % b)
        return 1

    if current == expected:
        print("deja conforme, rien a ecrire")
        return 0

    new_lines = lines[:header_idx] + expected + lines[end:]
    PAGE.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
    try:
        where = str(PAGE.relative_to(REPO_ROOT))
    except ValueError:
        where = str(PAGE)  # page hors depot (tests) : chemin absolu
    print("ecrit : %s (%d carnets)" % (where, len(expected) - 2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
