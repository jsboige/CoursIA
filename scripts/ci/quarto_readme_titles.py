#!/usr/bin/env python3
"""Titres temporaires des README de la liste Quarto, sans modifier les sources livrées."""
from __future__ import annotations

import argparse
import base64
import html
import json
import re
import sys
from pathlib import Path


def readmes(root: Path, config: Path | None = None) -> list[Path]:
    text = (config or root / '_quarto.yml').read_text(encoding='utf-8')
    match = re.search(r'(?ms)^  render:\s*\n(.*?)(?=^  [\w-]+:|^\w|\Z)', text)
    if not match:
        raise ValueError('liste project.render absente')
    paths = []
    for line in match.group(1).splitlines():
        # Le générateur écrit des chemins entre guillemets doubles ; une
        # apostrophe à l'intérieur fait partie du nom, pas du délimiteur.
        item = re.match(r'^\s+-\s+"([^"\r\n]+)"\s*$', line)
        if not item and re.match(r'^\s+-\s+', line) and 'README.md' in line:
            raise ValueError(f'entrée README non reconnue : {line}')
        if item and item[1].endswith('README.md'):
            p = Path(item[1])
            if p.is_absolute() or '..' in p.parts or not (root / p).is_file():
                raise ValueError(f'README invalide : {p}')
            paths.append(p)
    if not paths or len(set(paths)) != len(paths):
        raise ValueError('liste README vide ou dupliquée')
    return paths


def frontmatter(text: str) -> tuple[str | None, int]:
    if not re.match(r'^---[ \t]*\r?\n', text):
        return None, 0
    end = re.search(r'(?m)^---[ \t]*\r?$', text[text.index('\n') + 1:])
    if not end:
        raise ValueError('front matter non terminé')
    start = text.index('\n') + 1
    return text[start:start + end.start()], start


def explicit(text: str) -> str | None:
    fm, _ = frontmatter(text)
    if fm is None:
        return None
    entries = re.findall(r'''(?m)^(?:pagetitle|"pagetitle"|'pagetitle')[ \t]*:[ \t]*([^\r\n]*)\r?$''', fm)
    if not entries:
        return None
    if len(entries) != 1:
        raise ValueError('plusieurs pagetitle')
    value = entries[0].strip()
    if not value or value.startswith('#'):
        raise ValueError('pagetitle vide')
    if value.startswith('"'):
        value = json.loads(value)
    elif value.startswith("'"):
        if not re.fullmatch(r"'(?:[^']|'')*'", value):
            raise ValueError('pagetitle YAML mal formé')
        value = value[1:-1].replace("''", "'")
    elif re.search(r'[#\[\]{}]|:[ \t]|^([|>]|null$|~$|true$|false$)', value, re.I):
        raise ValueError('pagetitle YAML non pris en charge')
    if not isinstance(value, str) or not value.strip():
        raise ValueError('pagetitle vide')
    return value.strip()


def derived(text: str, path: Path) -> str:
    fm, start = frontmatter(text)
    if fm is not None:
        text = text[start + len(fm):]
    fenced = None
    for line in text.splitlines():
        fence = re.match(r'^\s*(`{3,}|~{3,})', line)
        if fence:
            if fenced is None:
                fenced = fence[1][0]
            elif fence[1][0] == fenced:
                fenced = None
            continue
        if fenced:
            continue
        m = re.match(r'^ {0,3}#\s+(.+?)\s*#*\s*$', line)
        if m:
            title = re.sub(r'!?\[([^]]+)\]\([^)]*\)', r'\1', m[1])
            title = re.sub(r'<[^>]*>|[`*_~]', '', title)
            title = html.unescape(title).strip()
            if title:
                return title
    return path.as_posix() if path != Path('README.md') else 'Accueil'


def plan(root: Path, paths: list[Path]) -> dict[Path, str]:
    texts = {p: (root / p).read_text(encoding='utf-8-sig') for p in paths}
    existing = {p: explicit(t) for p, t in texts.items()}
    titles = {p: existing[p] or derived(t, p) for p, t in texts.items()}
    groups = {}
    for p, title in titles.items():
        groups.setdefault(title.casefold(), []).append(p)
    for group in groups.values():
        if len(group) > 1:
            for p in group:
                if existing[p] is None:
                    titles[p] += f' ({p.as_posix()})'
    validate(titles)
    return titles


def validate(titles: dict[Path, str | None]) -> None:
    seen = {}
    for p, value in titles.items():
        if not value or not value.strip():
            raise ValueError(f'titre absent : {p}')
        key = value.strip().casefold()
        if key in seen:
            raise ValueError(f'titre dupliqué : {seen[key]} et {p}')
        seen[key] = p


def apply(root: Path, backup: Path, config: Path | None = None) -> None:
    if backup.exists():
        raise ValueError('sauvegarde déjà présente ; restaurer avant apply')
    paths = readmes(root, config)
    titles = plan(root, paths)
    changes = {}
    for p in paths:
        data = (root / p).read_bytes()
        text = data.decode('utf-8-sig')
        if explicit(text) is not None:
            continue
        fm, start = frontmatter(text)
        entry = 'pagetitle: ' + json.dumps(titles[p], ensure_ascii=False) + '\n'
        updated = text[:start] + entry + text[start:] if fm is not None else '---\n' + entry + '---\n\n' + text
        changes[str(p)] = {'original': base64.b64encode(data).decode(), 'updated': base64.b64encode(updated.encode()).decode()}
    backup.write_text(json.dumps(changes), encoding='utf-8')
    for name, item in changes.items():
        (root / name).write_bytes(base64.b64decode(item['updated']))
    check(root, config)
    print(f'{len(paths)} README vérifiés, {len(changes)} titres temporaires')


def check(root: Path, config: Path | None = None) -> None:
    paths = readmes(root, config)
    validate({p: explicit((root / p).read_text(encoding='utf-8-sig')) for p in paths})
    print(f'{len(paths)} titres présents et distincts')


def restore(root: Path, backup: Path) -> None:
    if not backup.exists():
        raise ValueError('sauvegarde absente')
    changes = json.loads(backup.read_text(encoding='utf-8'))
    for name, item in changes.items():
        path = root / name
        if path.read_bytes() not in (base64.b64decode(item['updated']), base64.b64decode(item['original'])):
            raise ValueError(f'source modifiée depuis apply : {name}')
    for name, item in changes.items():
        (root / name).write_bytes(base64.b64decode(item['original']))
    backup.unlink()
    print(f'{len(changes)} README restaurés')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('apply', 'check', 'restore'))
    parser.add_argument('--root', type=Path, default=Path('.'))
    parser.add_argument('--backup', type=Path, default=Path('/tmp/quarto-readme-titles.json'))
    parser.add_argument('--config', type=Path)
    args = parser.parse_args()
    try:
        if args.action == 'apply':
            apply(args.root, args.backup, args.config)
        elif args.action == 'check':
            check(args.root, args.config)
        else:
            restore(args.root, args.backup)
    except (ValueError, OSError, json.JSONDecodeError) as exc:
        print(f'erreur : {exc}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
