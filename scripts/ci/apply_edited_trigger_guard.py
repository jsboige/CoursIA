#!/usr/bin/env python3
"""Garde de retrigger `edited` -- une fournee homogene sur la population qui ecoute `edited`.

Contexte (#25510, tranche T-C/2). Un workflow qui ecoute `pull_request: edited`
rejoue a chaque edition du titre, du body ou de la **base** de la PR. Pour la
majorite de la population, le verdict ne depend d'aucun de ces trois axes :
l'edition est un **rejeu inutile** (source des « premieres tentatives
redondantes » mesurees par `scripts/ci/measure_redundant_runs.py`). Pour une
minorite, le verdict depend de la base (le filtre `paths:` est evalue sur le
diff base-relative : un retarget peut faire matcher un workflow qui ne
matchait pas) ou du body.

Ce que fait ce fixer, sur chaque workflow de la population :

1. **le garde de job** : le job ne s'execute que si l'evenement n'est pas une
   edition, ou si l'edition a change la base (et le body, pour les workflows
   dont le verdict en depend). La forme :

       (expression existante) && (github.event.action != 'edited' || github.event.changes.base != null)

   **Les parentheses sont obligatoires, des deux cotes** : dans les expressions
   GitHub, `&&` lie plus fort que `||`. Sans parentheses, `A || B && G` se lit
   `A || (B && G)` -- le garde serait contourné par le premier terme d'une
   disjonction existante (cas reel : les workflows de garde, dont la condition
   est `head.repo.full_name == null || ...`) ; et `X && G1 || G2` se lit
   `(X && G1) || G2` -- le garde serait alors contourne par `G2`.

2. **la cle de groupe de concurrence** : la concurrence s'evalue AVANT le
   `if:` du job, donc une edition de titre dans le meme groupe annulerait le
   run REEL en cours. Les editions qui ne changent ni la base ni le body
   recoivent donc une cle de groupe distincte (suffixe conditionnel) : elles ne
   se concurrencent ni avec le run reel, ni entre elles.

Ce que ce fixer ne fait PAS : il ne touche pas aux types du declencheur
(`edited` reste ecoute -- c'est la forme retenue, et c'est ce que verifie
`scripts/ci/list_edited_trigger_workflows.py`), pas aux noms de jobs, et pas
aux workflows dont le verdict depend du **titre** (GitHub n'expose pas
`changes.title` : une edition de titre ne peut pas etre distinguee d'une
edition de body, donc un verdict titre-dépendant doit toujours rejouer).

Le job qui saute emet un check-run `skipped` du meme nom : c'est pourquoi le
repli du fold (`scripts/pr_gate.py::dedupe_latest`) ne remplace jamais un
verdict reel anterieur par un `skipped` (tranche T-C/1). Le seul check **requis**
sur `main` est `PR gate`, produit par `pr-gate.yml` -- qui n'ecoute pas
`edited` et que ce fixer ne touche donc pas.

Usage :
    python scripts/ci/apply_edited_trigger_guard.py            # simulation
    python scripts/ci/apply_edited_trigger_guard.py --apply    # ecrit
    python scripts/ci/apply_edited_trigger_guard.py --check    # verifie

Les editions sont faites par **edition textuelle** (jamais par round-trip
YAML) : ces workflows sont riches en commentaires, et un round-trip les
detruirait.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import list_edited_trigger_workflows as census  # noqa: E402

GUARD_BASE = "github.event.action != 'edited' || github.event.changes.base != null"
GUARD_BODY = GUARD_BASE + " || github.event.changes.body != null"

#: Exclusions nominatives : workflows du census que le fixer ne doit pas
#: toucher. Vide a ce jour. `notebook-latex-control-chars.yml` y figurait tant
#: que la tranche T-A/2 etait ouverte ; elle est mergee, le declencheur
#: `pull_request` du workflow est retire, et il sort du census de lui-meme.
#: Une entree ne se justifie que pour un workflow qui ecoute ENCORE `edited`.
EXCLUDED: set[str] = set()


class Unsupported(Exception):
    """Une forme d'`if:` que l'edition textuelle ne sait pas traiter."""


def guard_for(depends_on: list[str]) -> str:
    """Le garde, selon l'axe dont depend le verdict du workflow."""
    return GUARD_BODY if "body" in depends_on else GUARD_BASE


def separator_for(depends_on: list[str]) -> str:
    """Le suffixe de groupe de concurrence, selon le meme axe.

    Expression GitHub : le suffixe n'est non vide que pour une edition qui ne
    change ni la base ni le body -- donc une edition de titre ne partage pas
    le groupe du run reel et ne l'annule pas, et une edition qui change la
    base (retarget) le partage et l'annule comme un run normal.
    """
    cond = "github.event.action == 'edited' && github.event.changes.base == null"
    if "body" in depends_on:
        cond += " && github.event.changes.body == null"
    return "${{ " + cond + " && 'meta-edit' || '' }}"


def _split_comment(value: str) -> tuple[str, str]:
    """Separe la valeur de son commentaire de fin (un `#` hors quotes)."""
    value = value.strip()
    quote = ""
    for index, char in enumerate(value):
        if quote:
            if char == quote:
                quote = ""
            continue
        if char in "'\"":
            quote = char
            continue
        if char == "#" and (index == 0 or value[index - 1].isspace()):
            return value[:index].rstrip(), "  " + value[index:].strip()
    return value.rstrip(), ""


def _job_ranges(lines: list[str]) -> list[tuple[str, int, int]]:
    """(nom, debut, fin) de chaque job du bloc `jobs:`."""
    start = None
    for index, line in enumerate(lines):
        if line.rstrip() == "jobs:":
            start = index + 1
            break
    if start is None:
        return []
    ranges: list[tuple[str, int, int]] = []
    index = start
    while index < len(lines):
        line = lines[index]
        if not line.strip() or line.lstrip().startswith("#"):
            index += 1
            continue
        if not line.startswith("  ") or line.startswith("   "):
            break
        name = line.strip().rstrip(":")
        end = index + 1
        while end < len(lines):
            candidate = lines[end]
            if not candidate.strip() or candidate.lstrip().startswith("#"):
                end += 1
                continue
            if candidate.startswith("    "):
                end += 1
                continue
            break
        ranges.append((name, index, end))
        index = end
    return ranges


def _guard_job(lines: list[str], start: int, end: int, guard: str) -> bool:
    """Pose le garde sur UN job (bloc [start, end)). Retourne True si change."""
    target = None
    for index in range(start + 1, end):
        if lines[index].startswith("    if:"):
            target = index
            break
    if target is None:
        # Le `if:` est insere apres le `name:` du job quand il y en a un
        # (l'ordre des cles d'une mappe YAML est libre, mais le `name:` en
        # tete est la forme lisible du depot).
        insert_at = start + 1
        for index in range(start + 1, min(end, start + 12)):
            if lines[index].startswith("    name:"):
                insert_at = index + 1
                break
        lines.insert(insert_at, f"    if: ({guard})")
        return True
    value = lines[target][len("    if:"):]
    expression, comment = _split_comment(value)
    if expression.startswith("${{") or expression.startswith("|") \
            or expression.startswith(">"):
        raise Unsupported(
            f"forme d'if: non geree (job a la ligne {start + 1}) : "
            f"{expression[:60]}"
        )
    if f"({guard})" in expression:
        return False
    lines[target] = ("    if: (" + expression + ") && (" + guard + ")" + comment)
    return True


def apply_guard(text: str, guard: str) -> tuple[str, int]:
    """Pose le garde sur tous les jobs du workflow. Retourne (texte, nb)."""
    lines = text.split("\n")
    changed = 0
    # Les jobs sont traites a l'ENVERS : l'insertion d'un `if:` decale les
    # index des jobs suivants.
    for _name, start, end in reversed(_job_ranges(lines)):
        if _guard_job(lines, start, end, guard):
            changed += 1
    return "\n".join(lines), changed


def _concurrency_blocks(lines: list[str]) -> list[tuple[int, str]]:
    """(index de la ligne `concurrency:`, indent) pour chaque bloc.

    Un bloc au niveau du workflow est a l'indent 0, un bloc au niveau d'un
    job est a l'indent 6. Les deux portent un risque d'annulation : le
    groupe est evalue avant le `if:` du job.
    """
    blocks: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        if line.rstrip() != "concurrency:":
            continue
        indent = len(line) - len(line.lstrip())
        if indent in (0, 6):
            blocks.append((index, " " * indent))
    return blocks


def apply_group(text: str, separator: str) -> tuple[str, int]:
    """Donne aux editions sans changement de base une cle de groupe distincte."""
    lines = text.split("\n")
    changed = 0
    for index, indent in _concurrency_blocks(lines):
        group_indent = indent + "  "
        for offset in range(index + 1, min(index + 8, len(lines))):
            candidate = lines[offset]
            if not candidate.strip() or candidate.lstrip().startswith("#"):
                continue
            if not candidate.startswith(group_indent):
                break
            if candidate.strip().startswith("group:"):
                value = candidate.split("group:", 1)[1].strip()
                if separator in value:
                    break
                lines[offset] = f"{group_indent}group: {value}-{separator}"
                changed += 1
                break
    return "\n".join(lines), changed


def has_group_separator(text: str) -> bool:
    return "meta-edit" in text


def has_concurrency(text: str) -> bool:
    """Le workflow porte-t-il un bloc `concurrency:` (workflow ou job) ?

    Sans bloc, il n'y a pas d'annulation a separer : le controle de
    coherence ne doit pas exiger un separateur la ou il n'y a rien a
    separer.
    """
    return bool(_concurrency_blocks(text.split("\n")))


def guard_present(text: str, guard: str) -> bool:
    """Le garde est-il present sur TOUS les jobs du workflow ?"""
    lines = text.split("\n")
    ranges = _job_ranges(lines)
    if not ranges:
        return False
    for _name, start, end in ranges:
        found = False
        for index in range(start + 1, end):
            if lines[index].startswith("    if:"):
                found = f"({guard})" in lines[index]
                break
        if not found:
            return False
    return True


def population(root: Path) -> list[dict]:
    """La population a traiter : ceux dont le verdict ne depend pas du titre."""
    rows = []
    for row in census.survey(root):
        rel = row["workflow"]
        if rel in EXCLUDED:
            continue
        # Un verdict titre-dépendant doit toujours rejouer : GitHub n'expose
        # pas `changes.title`.
        if "title" in row["depends_on"]:
            continue
        rows.append(row)
    return rows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--apply", action="store_true",
                        help="ecrire les fichiers (sans ce drapeau : simulation)")
    parser.add_argument("--check", action="store_true",
                        help="verifier seulement (exit 1 si un workflow manque)")
    args = parser.parse_args(argv)

    root = args.root.resolve()
    rows = population(root)
    problems: list[str] = []
    total_jobs = 0
    for row in rows:
        rel = row["workflow"]
        path = root / rel
        text = path.read_text(encoding="utf-8")
        guard = guard_for(row["depends_on"])
        separator = separator_for(row["depends_on"])
        if args.check:
            if not guard_present(text, guard):
                problems.append(f"{rel}: garde absent sur un job au moins")
            if not has_group_separator(text) and has_concurrency(text):
                problems.append(f"{rel}: cle de groupe non separee")
            continue
        try:
            new_text, changed = apply_guard(text, guard)
            new_text, group_changed = apply_group(new_text, separator)
        except Unsupported as exc:
            problems.append(f"{rel}: {exc}")
            continue
        total_jobs += changed
        print(f"[edited-guard] {rel}: {changed} job(s) garde(s), "
              f"{group_changed} groupe(s) separe(s) "
              f"({', '.join(row['depends_on']) or '-'})")
        if args.apply and new_text != text:
            path.write_text(new_text, encoding="utf-8", newline="")
    if problems:
        for problem in problems:
            print(f"[edited-guard] PROBLEME {problem}", file=sys.stderr)
    if args.check:
        if problems:
            return 1
        print(f"[edited-guard] OK -- {len(rows)} workflow(s) de population")
        return 0
    print(f"[edited-guard] {len(rows)} workflow(s) de population, "
          f"{total_jobs} job(s) a garder"
          f"{'' if args.apply else ' (simulation)'}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
