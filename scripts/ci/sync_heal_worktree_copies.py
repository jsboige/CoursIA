#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Regenere les copies inline du soin d'arbre chaud (#23512).

Le soin d'arbre chaud (`Restore the warm work tree before the sparse checkout`)
est porte par 26 workflows du pool persistant, sous la forme d'un bloc shell
inline. La source unique est `.github/actions/heal-worktree/heal_worktree.sh`
(le corps sous son marqueur) ; les copies inline en sont byte-identiques, ce
que verifie `scripts/tests/test_heal_worktree_action.py`.

Ce que la duplication rendait couteux : corriger le bloc demandait 26 editions
synchrones a la main. Ce script retire la main de l'edition : on modifie le
script source, on lance le generateur, et les 26 copies sont regenerees.

Il ne decide rien de la forme de l'appel. L'action composite existe, mais
l'appel `uses: jsboige/CoursIA/.github/actions/heal-worktree@main` force
GitHub a telecharger l'archive codeload du depot ENTIER a l'etape « Set up
job » (~3,5 Go, mesure dans #23574) et l'action locale `uses: ./...` est
impossible a cet endroit (l'etape court AVANT `actions/checkout`, donc
`.github/actions/` n'est pas dans l'espace de travail). Les copies inline
restent donc en place ; c'est ce generateur qui porte l'objectif de source
unique.

Usage :

    python scripts/ci/sync_heal_worktree_copies.py            # regenere
    python scripts/ci/sync_heal_worktree_copies.py --check    # exit 1 si desync

Le mode `--check` est le mode CI : il n'ecrit rien et sort en erreur si une
copie a derive du script source.
"""

from __future__ import annotations

import argparse
import io
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / ".github" / "actions" / "heal-worktree" / "heal_worktree.sh"
WORKFLOWS = ROOT / ".github" / "workflows"

STEP_NAME = "Restore the warm work tree before the sparse checkout"
MARKER = "# --- corps extrait : byte-identique au bloc des workflows (#23287) ---"
INDENT = " " * 10

STEP_RE = re.compile(
    r"^      - name: " + re.escape(STEP_NAME) + r"\n        run: \|\n", re.MULTILINE
)


class Desync(ValueError):
    """Un workflow porte une occurrence du bloc que le generateur ne sait pas regeneree."""


def script_body() -> list[str]:
    """Corps du script source : les lignes apres le marqueur."""
    text = SCRIPT.read_text(encoding="utf-8")
    if MARKER not in text:
        raise Desync("le marqueur de corps a disparu du script source : %s" % SCRIPT)
    return text.split(MARKER + "\n", 1)[1].splitlines()


def _blocks(text: str) -> list[tuple[int, int, list[str]]]:
    """Occurrences du bloc dans un workflow.

    Rend pour chacune le couple (debut, fin) du corps dans le texte et les
    lignes du corps, dedentees de l'indentation du workflow.
    """
    found = []
    for match in STEP_RE.finditer(text):
        tail = text[match.end():]
        stop = tail.find("\n      - ")
        end = match.end() + (stop if stop >= 0 else len(tail))
        raw = text[match.end():end].splitlines()
        body = []
        for line in raw:
            if not line:
                body.append("")
            elif line.startswith(INDENT):
                body.append(line[len(INDENT):])
            else:
                raise Desync(
                    "ligne du bloc sans indentation attendue (%r) : %r" % (INDENT, line[:40])
                )
        found.append((match.end(), end, body))
    return found


def sync_text(text: str, body: list[str]) -> tuple[str, int]:
    """Rend le texte regenere et le nombre d'occurrences reecrites."""
    rendered = "\n".join((INDENT + line) if line else "" for line in body)
    out = []
    cursor = 0
    count = 0
    for start, end, current in _blocks(text):
        if current == body:
            continue
        out.append(text[cursor:start])
        out.append(rendered)
        cursor = end
        count += 1
    out.append(text[cursor:])
    return "".join(out), count


def sync_file(path: Path, body: list[str]) -> int:
    """Regenere un workflow. Rend le nombre d'occurrences reecrites.

    Le texte est **normalise avant** la synchronisation. Sans cela, le
    generateur est un no-op silencieux sur un checkout CRLF -- c'est-a-dire
    sur tous les postes Windows de la flotte (`core.autocrlf=true`) : le
    fichier porte `run: |\r\n`, que `STEP_RE` (qui exige `\n`) ne
    reconnait pas, donc `_blocks()` rend 0 occurrence, rien n'est ecrit, et
    `main()` annonce pourtant « regenere ».

    Les fins de ligne du fichier sont rendues a l'ecriture : le generateur
    ne touche qu'au corps du bloc.
    """
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    text = raw.decode("utf-8").replace("\r\n", "\n")
    new_text, count = sync_text(text, body)
    if count and new_text != text:
        if newline == "\r\n":
            new_text = new_text.replace("\r\n", "\n").replace("\n", "\r\n")
        path.write_bytes(new_text.encode("utf-8"))
    return count


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Regenere les copies inline du soin d'arbre chaud depuis sa source unique."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="ne rien ecrire ; exit 1 si une copie a derive du script source",
    )
    args = parser.parse_args(argv)

    body = script_body()
    changed = []
    carriers = 0
    for path in sorted(WORKFLOWS.glob("*.yml")):
        text = path.read_text(encoding="utf-8")
        occurrences = _blocks(text)
        if occurrences:
            carriers += 1
        new_text, count = sync_text(text, body)
        if count and new_text != text:
            changed.append((path.name, count))

    if not changed:
        print("[heal-worktree] %d workflow(s) portent le bloc -- toutes les copies sont a jour"
              % carriers)
        return 0

    for name, count in changed:
        print("[heal-worktree] %s : %d bloc(s) a regenerer" % (name, count))
    if args.check:
        print("[heal-worktree] DESYNC : %d workflow(s) a regenerer (mode --check : rien n'a ete ecrit)"
              % len(changed))
        return 1
    for name, count in changed:
        path = WORKFLOWS / name
        written = sync_file(path, body)
        if written != count:
            raise Desync(
                "%s : %d bloc(s) detecte(s) mais %d ecrit(s) -- le generateur a "
                "echoue en silence, rien n'a ete regenere" % (name, count, written)
            )
        print("[heal-worktree] %s : regenere (%d bloc(s) ecrit(s))" % (name, written))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Desync as exc:
        print("[heal-worktree] ERREUR : %s" % exc, file=sys.stderr)
        sys.exit(2)
