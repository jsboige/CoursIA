#!/usr/bin/env python3
"""
check_dataset_registry.py — Vérificateur cohérence registre datasets.

Issue #8055 tranche 2 — DATASET_REGISTRY.md + check_dataset_registry.py.

But : pour chaque entrée du registre, recalculer le SHA256 sur disque et signaler
    - DRIFT (SHA256 a changé depuis l'inventaire)
    - MISSING (chemin absent du repo)
    - CARD_REQUIRED (catégorie sensible sans DATASET_CARD associée)
    - OK (tout est conforme)

Litmus anti-LIGHT : ce script EXTRACT, il ne DÉCIDE pas. Le verdict final
= revue humaine/agent compétent. Cf docs/notebook-metadata/DATASET_REGISTRY.md.

Usage :
  python scripts/audit/check_dataset_registry.py [--repo-root <path>] [--out <file.yml>]

Sortie YAML manuelle :
  global_status: OK | DRIFT | MISSING | CARD_REQUIRED | UNKNOWN
  total_entries: <int>
  ok_count / ok_truncated_count / drift_count / missing_count / card_required_count / unknown_count
  findings:
    - chemin: <path>
      expected_sha256_prefix: <hex>
      actual_sha256_prefix: <hex>
      size_bytes_expected: <int>
      size_bytes_actual: <int>
      severity: CRITICAL | MAJOR | MINOR
      detail: <str>
"""

import argparse
import hashlib
import re
import sys
from pathlib import Path


# === Patterns de parsing du registre ===

# Format ligne : `| `<chemin>` | <taille> B | `<sha256_prefix>`… | <licence> | <catégorie> | ... |`
# Stratégie : split par `|` puis strip + dé-backticks + validation colonne par colonne.
# (Plus robuste qu'un regex complexe multi-groupes, tolère `**sensible**` et autres
#  caractères markdown dans les colonnes usage/card.)
SHA256_RE = re.compile(r'^[0-9a-f]{15,64}[…\.]*$')


def sha256_file(path: Path) -> str:
    """SHA256 hex d'un fichier, lu par chunks (mémoire constante)."""
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def parse_registry(registry_path: Path) -> list:
    """Parse les lignes du tableau markdown en entrées structurées.

    Stratégie : split `|` puis strip + dé-backticks. On exige les 5 premières
    colonnes (chemin, taille, sha256, licence, catégorie) ; les colonnes
    usage/card sont optionnelles et ignorées ici.
    """
    if not registry_path.exists():
        return []
    entries = []
    for line in registry_path.read_text(encoding='utf-8').splitlines():
        if not line.lstrip().startswith('|'):
            continue
        cols = [c.strip().strip('`').strip() for c in line.split('|')]
        cols = [c for c in cols if c != '']
        if len(cols) < 5:
            continue
        chemin, taille_raw, sha256_short, licence, categorie = cols[:5]
        try:
            taille = int(taille_raw.replace(' ', '').replace(' ', ''))
        except ValueError:
            continue
        if not SHA256_RE.match(sha256_short):
            continue
        entries.append({
            'chemin': chemin.strip(),
            'taille': taille,
            'sha256_short': sha256_short.strip(),
            'licence': licence.strip(),
            'categorie': categorie.strip(),
        })
    return entries


def is_sha256_complete(short: str) -> bool:
    """SHA256 complet = 64 chars hex."""
    return len(short) == 64 and all(c in '0123456789abcdef' for c in short)


def check_entry(entry: dict, repo_root: Path) -> dict:
    """Audit une entrée du registre."""
    full_path = repo_root / entry['chemin']
    finding = {
        'chemin': entry['chemin'],
        'expected_sha256': entry['sha256_short'],
        'size_bytes_expected': entry['taille'],
        'severity': None,
        'detail': None,
    }

    if not full_path.exists():
        finding.update({
            'status': 'MISSING',
            'severity': 'CRITICAL',
            'detail': f'Chemin {entry["chemin"]} absent du repo',
        })
        return finding

    actual_sha256 = sha256_file(full_path)
    actual_size = full_path.stat().st_size

    finding['actual_sha256'] = actual_sha256
    finding['size_bytes_actual'] = actual_size

    # Vérifier taille (warning si mismatch)
    if actual_size != entry['taille']:
        finding['size_warning'] = (
            f'Taille actuelle {actual_size} B != taille déclarée {entry["taille"]} B'
        )

    # Vérifier SHA256 (préfixe tronqué accepté)
    sha = entry['sha256_short']
    if sha.endswith('…') or sha.endswith('...'):
        prefix = sha.rstrip('…').rstrip('.')
        if actual_sha256.startswith(prefix):
            finding.update({'status': 'OK_TRUNCATED', 'severity': None})
        else:
            finding.update({
                'status': 'DRIFT',
                'severity': 'MAJOR',
                'detail': f'Préfixe SHA256 {prefix} ne correspond pas à {actual_sha256[:16]}...',
            })
    elif is_sha256_complete(sha):
        if actual_sha256 == sha:
            finding.update({'status': 'OK', 'severity': None})
        else:
            finding.update({
                'status': 'DRIFT',
                'severity': 'MAJOR',
                'detail': f'SHA256 actuel {actual_sha256[:16]}... != déclaré {sha[:16]}...',
            })
    else:
        finding.update({
            'status': 'UNKNOWN',
            'severity': 'MINOR',
            'detail': f'Format SHA256 non reconnu : {sha}',
        })

    # Vérifier CARD_REQUIRED pour catégorie sensible
    if entry['categorie'] == '**sensible**':
        card_path = repo_root / 'docs' / 'notebook-metadata' / 'DATASET_CARD.md'
        if not card_path.exists():
            finding.update({
                'status': 'CARD_REQUIRED',
                'severity': 'CRITICAL',
                'detail': 'Catégorie sensible mais DATASET_CARD.md absent',
            })
        else:
            card_text = card_path.read_text(encoding='utf-8')
            # Matching sémantique : le chemin complet OU juste la portion relative
            # après `MyIA.AI.Notebooks/` (le DATASET_CARD utilise souvent le
            # chemin raccourci dans ses titres `### `)
            chemin_complet = entry['chemin']
            chemin_relatif = (
                chemin_complet.split('MyIA.AI.Notebooks/', 1)[-1]
                if 'MyIA.AI.Notebooks/' in chemin_complet
                else chemin_complet
            )
            if chemin_complet not in card_text and chemin_relatif not in card_text:
                finding.update({
                    'status': 'CARD_REQUIRED',
                    'severity': 'MAJOR',
                    'detail': f'Catégorie sensible mais {chemin_complet} non documenté dans DATASET_CARD.md',
                })

    return finding


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, default=Path('.'),
                        help='Racine du repo (default: cwd)')
    parser.add_argument('--registry', type=Path,
                        default=Path('docs/notebook-metadata/DATASET_REGISTRY.md'),
                        help='Chemin du registre (default: docs/notebook-metadata/DATASET_REGISTRY.md)')
    parser.add_argument('--out', type=Path,
                        help='Fichier YAML de sortie (default: stdout)')
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    registry_path = args.registry if args.registry.is_absolute() else repo_root / args.registry

    if not registry_path.exists():
        print(f"ERROR: registre {registry_path} introuvable", file=sys.stderr)
        return 1

    entries = parse_registry(registry_path)
    if not entries:
        print(f"ERROR: aucune entrée parsée depuis {registry_path}", file=sys.stderr)
        return 1

    findings = [check_entry(e, repo_root) for e in entries]

    # Status global
    statuses = [f.get('status', 'UNKNOWN') for f in findings]
    if 'CARD_REQUIRED' in statuses:
        global_status = 'CARD_REQUIRED'
    elif 'MISSING' in statuses:
        global_status = 'MISSING'
    elif 'DRIFT' in statuses:
        global_status = 'DRIFT'
    elif 'UNKNOWN' in statuses:
        global_status = 'UNKNOWN'
    else:
        global_status = 'OK'

    # Sortie YAML manuelle
    lines = [
        f"global_status: {global_status}",
        f"total_entries: {len(entries)}",
        f"ok_count: {sum(1 for s in statuses if s == 'OK')}",
        f"ok_truncated_count: {sum(1 for s in statuses if s == 'OK_TRUNCATED')}",
        f"drift_count: {sum(1 for s in statuses if s == 'DRIFT')}",
        f"missing_count: {sum(1 for s in statuses if s == 'MISSING')}",
        f"card_required_count: {sum(1 for s in statuses if s == 'CARD_REQUIRED')}",
        f"unknown_count: {sum(1 for s in statuses if s == 'UNKNOWN')}",
        "findings:",
    ]
    for f in findings:
        lines.append(f"  - chemin: {f['chemin']!r}")
        lines.append(f"    status: {f.get('status', 'UNKNOWN')}")
        lines.append(f"    expected_sha256_prefix: {f['expected_sha256'][:16]!r}")
        if 'actual_sha256' in f:
            lines.append(f"    actual_sha256_prefix: {f['actual_sha256'][:16]!r}")
        lines.append(f"    size_bytes_expected: {f['size_bytes_expected']}")
        if 'size_bytes_actual' in f:
            lines.append(f"    size_bytes_actual: {f['size_bytes_actual']}")
        if f.get('severity'):
            lines.append(f"    severity: {f['severity']}")
        if f.get('detail'):
            lines.append(f"    detail: {f['detail']!r}")
        if f.get('size_warning'):
            lines.append(f"    size_warning: {f['size_warning']!r}")

    output = '\n'.join(lines)
    if args.out:
        args.out.write_text(output, encoding='utf-8')
        print(f"Audit écrit: {args.out}")
    else:
        print(output)

    # Exit code : 0 si OK ou OK_TRUNCATED uniquement, 1 sinon
    if global_status in ('OK', 'OK_TRUNCATED'):
        return 0
    return 1


if __name__ == '__main__':
    sys.exit(main())
