#!/usr/bin/env python3
"""Mesure la forme des READMEs de séries de notebooks, sans rien modifier.

Usage: python scripts/notebook_tools/check_readme_series_form.py --base-ref
       origin/main [--paths <README.md|dossier> ...] [--json]

V1 compte les trois marqueurs de forme (au moins deux requis). V2 signale
une ligne de palier lettré dans « Parcours principal » ou des paliers
lettrés absents de « Approfondissements ». --base-ref est obligatoire : le
code de sortie ne sanctionne que les violations ajoutées depuis cette base.

La doctrine #3973 autorise explicitement un palier lettré **en lien court
dans la dernière colonne** de la table du parcours (« Pour approfondir »).
V2 ne signale donc que les lettres hors de cette forme : une ligne dont la
première cellule est un numéro lettré, ou un lien lettré dans une colonne
autre que la dernière. Compter toute ligne contenant un lien lettré
signalait la forme conforme comme un défaut (9 fichiers sur 9, mesuré le
2026-11-12 sur `origin/main`).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NOTEBOOKS = ROOT / "MyIA.AI.Notebooks"
MARKERS = (
    ("colonne_Ce_qu_on_y_apprend", re.compile(r"\|[^\n]*Ce qu'on y apprend[^\n]*\|", re.I)),
    ("section_Comment_lire_ce_README", re.compile(r"^#{1,6}\s+Comment lire ce README\b", re.I | re.M)),
    ("section_Approfondissements", re.compile(r"^#{1,6}\s+Approfondissements\b", re.I | re.M)),
)
LETTER = re.compile(r"^\|\s*\d+[a-z]\s*\|", re.I)
LETTER_LINK = re.compile(r"\[\s*\d{1,2}[a-z](?:\s+[^]]*)?\s*\]", re.I)
NUMBERED = re.compile(r"^\|\s*\d+[a-z]?\s*\|")


def _table_rows(text: str, heading: str) -> list[str]:
    lines = text.splitlines()
    active = False
    depth = 0
    rows: list[str] = []
    heading_re = re.compile(rf"^(#{{1,6}})\s+{re.escape(heading)}\b", re.I)
    for line in lines:
        if not active:
            match = heading_re.match(line)
            if match:
                active = True
                depth = len(match.group(1))
            continue
        match = re.match(r"^(#{1,6})\s+", line)
        if match and len(match.group(1)) <= depth:
            break
        if line.lstrip().startswith("|") and not re.match(r"^\|\s*[-: ]+\|", line):
            rows.append(line)
    return rows


def _cells(row: str) -> list[str]:
    """Découpe une ligne de tableau Markdown en cellules, pipes échappés respectés."""
    body = row.strip()
    if body.startswith("|"):
        body = body[1:]
    if body.endswith("|"):
        body = body[:-1]
    return re.split(r"(?<!\\)\|", body)


def _section_text(text: str, heading: str) -> str:
    """Corps d'une section, prose ET tableaux, jusqu'au titre de niveau égal ou supérieur.

    `_table_rows` ne rend que les lignes de tableau ; la contrepartie de la
    doctrine #3973 se lit dans toute la section — un palier traité en prose
    est traité.
    """
    heading_re = re.compile(rf"^(#{{1,6}})\s+{re.escape(heading)}\b", re.I)
    out: list[str] = []
    depth = 0
    active = False
    for line in text.splitlines():
        if not active:
            match = heading_re.match(line)
            if match:
                active = True
                depth = len(match.group(1))
            continue
        match = re.match(r"^(#{1,6})\s+", line)
        if match and len(match.group(1)) <= depth:
            break
        out.append(line)
    return "\n".join(out)


def _last_column_allows_letters(main_rows: list[str]) -> bool:
    """La dernière colonne n'exempte que si son en-tête annonce l'approfondissement.

    Sans cette garde, une table `| # | Notebook |` où le palier lettré est
    présenté comme le carnet de l'étape bénéficiait de l'exemption réservée à
    la colonne « Pour approfondir ».
    """
    if not main_rows:
        return False
    header = _cells(main_rows[0])
    if len(header) < 2:
        return False
    return "approfondir" in header[-1].lower()


def _last_column_letters(main_rows: list[str]) -> list[str]:
    """Paliers cités en lien court dans la dernière colonne (forme autorisée)."""
    if not _last_column_allows_letters(main_rows):
        return []
    letters: list[str] = []
    for row in main_rows:
        cells = _cells(row)
        if len(cells) < 2:
            continue
        for match in LETTER_LINK.finditer(cells[-1]):
            token = re.match(r"\[\s*(\d{1,2}[a-z])", match.group(0), re.I)
            if token:
                letters.append(token.group(1).lower())
    return letters


def _letter_is_covered(letter: str, section: str) -> bool:
    """Le palier est traité par la section : lien court ou numéro nu."""
    return re.search(
        rf"\[\s*{re.escape(letter)}\b|(?<![\w]){re.escape(letter)}(?![\w])",
        section, re.I) is not None


def _main_path_violations(main_rows: list[str]) -> list[str]:
    """Lignes du parcours principal portant une lettre hors de la forme autorisée.

    Forme autorisée par la doctrine #3973 : un palier lettré peut être cité
    en **lien court dans la dernière colonne** (« Pour approfondir »). Une
    lettre ailleurs est un défaut : en première cellule, c'est un palier
    déguisé en étape du parcours ; dans une colonne intermédiaire, c'est un
    palier présenté comme une étape.
    """
    allow_last = _last_column_allows_letters(main_rows)
    bad: list[str] = []
    for row in main_rows:
        if LETTER.match(row):
            bad.append(row)
            continue
        cells = _cells(row)
        if len(cells) < 2:
            if LETTER_LINK.search(row):
                bad.append(row)
            continue
        # L'exemption de la dernière colonne est conditionnelle à son en-tête.
        scope = cells[:-1] if allow_last else cells
        if LETTER_LINK.search("|".join(scope)):
            bad.append(row)
    return bad


def inspect_text(path: str, text: str) -> dict:
    found = [name for name, pattern in MARKERS if pattern.search(text)]
    missing = [name for name, _ in MARKERS if name not in found]
    main_rows = _table_rows(text, "Parcours principal")
    approfond_rows = _table_rows(text, "Approfondissements")
    bad_main = _main_path_violations(main_rows)
    letters_below = [row for row in approfond_rows if LETTER.match(row)]
    extra = []
    if bad_main:
        extra.append("lettres_dans_parcours_principal")
        if not any(LETTER.match(row) or LETTER_LINK.search(row) for row in approfond_rows):
            extra.append("lettres_absentes_d_Approfondissements")
    # Forme autorisée : un lien lettré en dernière colonne reste soumis à la
    # contrepartie de la doctrine #3973 — le palier qu'il cite doit être traité
    # par la section « Approfondissements » (lien court ou numéro, prose
    # comprise). Sans ce contrôle, la forme autorisée échappait entièrement à
    # la vérification que son exemption a précisément pour but de rendre due.
    section = _section_text(text, "Approfondissements")
    uncovered = [x for x in _last_column_letters(main_rows)
                 if not _letter_is_covered(x, section)]
    if uncovered and "lettres_absentes_d_Approfondissements" not in extra:
        extra.append("lettres_absentes_d_Approfondissements")
    v2 = bool(bad_main) or bool(uncovered)
    return {"path": path, "conforming": len(found) >= 2 and not v2,
            "missing": missing, "extra": extra}


def _git(*args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=ROOT, text=True,
                          encoding="utf-8", errors="replace", capture_output=True)
    if proc.returncode:
        raise ValueError(proc.stderr.strip() or f"git {' '.join(args)} a échoué")
    return proc.stdout


def _read_at(ref: str, rel: str) -> str | None:
    proc = subprocess.run(["git", "show", f"{ref}:{rel}"], cwd=ROOT,
                          text=True, encoding="utf-8", errors="replace", capture_output=True)
    return proc.stdout if proc.returncode == 0 else None


def _series_at(ref: str | None, worktree: bool = False) -> dict[str, dict]:
    if worktree:
        files = sorted(NOTEBOOKS.rglob("*.ipynb"))
        grouped: dict[str, int] = {}
        for p in files:
            folder = p.parent.relative_to(ROOT).as_posix()
            grouped[folder] = grouped.get(folder, 0) + 1
        result = {}
        for folder, count in grouped.items():
            if count < 2 or not (ROOT / folder / "README.md").is_file():
                continue
            p = ROOT / folder / "README.md"
            result[folder + "/README.md"] = inspect_text(folder + "/README.md", p.read_text(encoding="utf-8"))
        return result
    assert ref
    paths = _git("-c", "core.quotepath=false", "ls-tree", "-r", "--name-only", ref, "--", "MyIA.AI.Notebooks").splitlines()
    counts: dict[str, int] = {}
    for path in paths:
        if path.endswith(".ipynb"):
            folder = path.rsplit("/", 1)[0]
            counts[folder] = counts.get(folder, 0) + 1
    result = {}
    for folder, count in counts.items():
        if count >= 2 and folder + "/README.md" in paths:
            path = folder + "/README.md"
            text = _read_at(ref, path)
            result[path] = inspect_text(path, text or "")
    return result


def _delta(base_ref: str, head_ref: str | None, scope: list[str] | None = None) -> list[dict]:
    # Compare violation details for changed series only; untouched backlog is inert.
    head = _series_at(head_ref) if head_ref else _series_at(None, worktree=True)
    base = _series_at(base_ref)
    diff_args = (base_ref, head_ref) if head_ref else (base_ref,)
    changed = set(_git("diff", "--name-only", *diff_args, "--", "MyIA.AI.Notebooks").splitlines())
    rename_map: dict[str, str] = {}
    for line in _git("diff", "--find-renames", "--name-status", *diff_args,
                     "--", "MyIA.AI.Notebooks").splitlines():
        parts = line.split("\t")
        if len(parts) == 3 and parts[0].startswith("R") and parts[1].endswith("/README.md"):
            rename_map[parts[1]] = parts[2]
    if rename_map:
        base = {rename_map.get(path, path): value for path, value in base.items()}
    affected = {p for p in set(base) | set(head)
                if p in changed or p.rsplit("/", 1)[0] in {x.rsplit("/", 1)[0] for x in changed}}
    if scope:
        affected = {path for path in affected if _in_scope(path, scope)}
    findings = []
    for path in sorted(affected):
        before, after = base.get(path), head.get(path)
        if not after:
            continue
        if after["conforming"]:
            continue
        prior = set(before["missing"] + before["extra"]) if before else set()
        current = set(after["missing"] + after["extra"])
        introduced = current - prior
        if introduced:
            finding = dict(after)
            finding["introduced"] = sorted(introduced)
            findings.append(finding)
    return findings


def _in_scope(path: str, scope: list[str]) -> bool:
    for raw in scope:
        p = Path(raw)
        item = (p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()).rstrip("/")
        if path == item or path.startswith(item + "/"):
            return True
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paths", nargs="+", help="README.md / dossiers à inspecter")
    parser.add_argument("--json", action="store_true", help="Sortie JSON")
    parser.add_argument("--base-ref", required=True, help="Référence Git de base pour le mode delta obligatoire")
    parser.add_argument("--head-ref", help="Référence Git de tête (défaut: worktree courant)")
    args = parser.parse_args(argv)
    try:
        if args.paths and args.head_ref:
            results = [item for path, item in _series_at(args.head_ref).items()
                       if _in_scope(path, args.paths)]
        elif args.paths:
            results = []
            for raw in args.paths:
                p = Path(raw)
                if not p.is_absolute():
                    p = ROOT / p
                if p.is_dir():
                    folders = sorted({n.parent for n in p.rglob("*.ipynb")})
                    results.extend(inspect_text((folder / "README.md").relative_to(ROOT).as_posix(),
                                                (folder / "README.md").read_text(encoding="utf-8") if (folder / "README.md").is_file() else "")
                                   for folder in folders if len(list(folder.glob("*.ipynb"))) >= 2 and (folder / "README.md").is_file())
                else:
                    results.append(inspect_text(p.relative_to(ROOT).as_posix(), p.read_text(encoding="utf-8")))
        else:
            results = list(_series_at(args.head_ref, worktree=not args.head_ref).values())
        findings = _delta(args.base_ref, args.head_ref, args.paths)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({"results": results, "delta": findings}, ensure_ascii=False, indent=2))
    else:
        for item in sorted(results, key=lambda x: x["path"]):
            print(f"{'OK' if item['conforming'] else 'NON CONFORME'} {item['path']}"
                  + (f" — manquants: {', '.join(item['missing'])}" if item["missing"] else "")
                  + (f" — écarts V2: {', '.join(item['extra'])}" if item["extra"] else ""))
        print(f"Séries: {len(results)} ; conformes: {sum(x['conforming'] for x in results)} ; non conformes: {sum(not x['conforming'] for x in results)}")
        print(f"Dégradations dans la PR: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
