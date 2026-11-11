#!/usr/bin/env python3
"""Mesure la forme des READMEs de séries de notebooks, sans rien modifier.

Usage: python scripts/notebook_tools/check_readme_series_form.py --base-ref
       origin/main [--paths <README.md|dossier> ...] [--json]

V1 compte les trois marqueurs de forme (au moins deux requis). V2 signale
une ligne de palier lettré dans « Parcours principal » ou des paliers
lettrés absents de « Approfondissements ». --base-ref est obligatoire : le
code de sortie ne sanctionne que les violations ajoutées depuis cette base.
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


def inspect_text(path: str, text: str) -> dict:
    found = [name for name, pattern in MARKERS if pattern.search(text)]
    missing = [name for name, _ in MARKERS if name not in found]
    main_rows = _table_rows(text, "Parcours principal")
    approfond_rows = _table_rows(text, "Approfondissements")
    bad_main = [row for row in main_rows if LETTER.match(row) or LETTER_LINK.search(row)]
    letters_below = [row for row in approfond_rows if LETTER.match(row)]
    v2 = bool(bad_main)
    extra = []
    if bad_main:
        extra.append("lettres_dans_parcours_principal")
        if not any(LETTER.match(row) or LETTER_LINK.search(row) for row in approfond_rows):
            extra.append("lettres_absentes_d_Approfondissements")
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
