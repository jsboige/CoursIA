#!/usr/bin/env python3
"""
check_cost_metadata.py — Vérificateur cohérence frontmatter `cost:`.

Issue #8056 (P1) — matrice coût/ressource par notebook.

But : extraire pour un notebook :
  - Le bloc YAML `cost:` de la cellule 0 (markdown frontmatter)
  - Les usages réels : appels API, .cuda(), HF_TOKEN, QuantBook, etc.
  - Signaler les :
      (1) gpu_required: false mais cellule code lance torch.cuda / tensorflow GPU
      (2) api_usd_est: 0.0 mais cellule appelle openai.ChatCompletion / anthropic / mistral
      (3) external_account: none mais cellule demande HF_TOKEN / OPENAI_API_KEY
      (4) free_alternative pointe vers un notebook inexistant
      (5) Notebook QC sans qc_cloud validator
      (6) Notebook GPU sans sk_visual validator

Litmus anti-LIGHT : ce script EXTRACT, il ne DÉCIDE pas. Le verdict final
= revue humaine/agent compétent. Cf docs/notebook-metadata/cost-matrix.md.

Usage :
  python scripts/audit/check_cost_metadata.py <notebook>.ipynb [--out <fichier.yml>]
"""

import argparse
import re
import sys
from pathlib import Path

import nbformat
import yaml


# === Patterns de détection ===

# Cellule code GPU
GPU_PATTERNS = [
    r'\.cuda\(\)',
    r'\.to\("cuda"\)',
    r'torch\.cuda\.',
    r'tensorflow\.gpu',
    r'with\s+tf\.device\(["\']/gpu',
]

# API payantes (litmus 2 : api_usd_est = 0 mais cellule appelle API)
API_PATTERNS = {
    'openai': r'openai\.ChatCompletion|openai\.Image|openai\.Audio|from openai',
    'anthropic': r'anthropic\.|from anthropic|claude',
    'mistral': r'mistralai|from mistral',
    'google': r'google\.generativeai|gemini',
    'replicate': r'replicate\.',
    'hf_inference_api': r'huggingface_hub\.InferenceClient',
}

# Tokens requis (litmus 3 : external_account=none mais cellule demande token)
TOKEN_PATTERNS = {
    'hf': r'os\.getenv\(["\']HF_TOKEN|os\.environ\[["\']HF_TOKEN',
    'openai': r'os\.getenv\(["\']OPENAI_API_KEY',
    'anthropic': r'os\.getenv\(["\']ANTHROPIC_API_KEY',
    'qc': r'os\.getenv\(["\']QC_USER|os\.getenv\(["\']QC_API_TOKEN',
    'comfyui': r'os\.getenv\(["\']COMFYUI',
}


def parse_cost_frontmatter(cell_source: str) -> dict:
    """Parse le bloc YAML `--- ... ---` en cellule 0 markdown."""
    # Pattern : début de cellule = `---`, lignes YAML, `---` final
    pattern = r'^---\s*\n(.*?)\n---\s*\n'
    match = re.match(pattern, cell_source, re.DOTALL)
    if not match:
        return {}
    try:
        return yaml.safe_load(match.group(1)) or {}
    except yaml.YAMLError:
        return {}


def detect_gpu_usage(code_source: str) -> bool:
    """Litmus 1 : cellule code utilise GPU."""
    for pattern in GPU_PATTERNS:
        if re.search(pattern, code_source):
            return True
    return False


def detect_api_usage(code_source: str) -> list:
    """Litmus 2 : cellule code appelle API payante."""
    found = []
    for provider, pattern in API_PATTERNS.items():
        if re.search(pattern, code_source, re.IGNORECASE):
            found.append(provider)
    return found


def detect_token_usage(code_source: str) -> list:
    """Litmus 3 : cellule code lit token externe."""
    found = []
    for provider, pattern in TOKEN_PATTERNS.items():
        if re.search(pattern, code_source):
            found.append(provider)
    return found


def detect_quantbook_usage(code_source: str) -> bool:
    """Litmus 5 : QC notebook utilise QuantBook."""
    return bool(re.search(r'QuantBook\(\)|self\.QuantBook', code_source))


def check_notebook(notebook_path: Path, repo_root: Path) -> dict:
    """Audit complet d'un notebook."""
    with notebook_path.open('r', encoding='utf-8') as f:
        nb = nbformat.read(f, as_version=4)

    findings = []
    cost_meta = {}
    code_cells_source = []

    # Extraction frontmatter cellule 0 markdown
    if nb.cells and nb.cells[0].get('cell_type') == 'markdown':
        source = nb.cells[0].get('source', '')
        if isinstance(source, list):
            source = ''.join(source)
        cost_meta = parse_cost_frontmatter(source).get('cost', {})

    # Agrégation cellules code
    for idx, cell in enumerate(nb.cells):
        if cell.get('cell_type') != 'code':
            continue
        source = cell.get('source', '')
        if isinstance(source, list):
            source = ''.join(source)
        code_cells_source.append((idx, source))

    # Litmus 1 : GPU_required: false mais GPU usage
    uses_gpu = any(detect_gpu_usage(src) for _, src in code_cells_source)
    if uses_gpu and not cost_meta.get('gpu_required', False):
        findings.append({
            'pattern': 'gpu_used_but_not_declared',
            'detail': 'Cellule code utilise GPU (.cuda(), torch.cuda) mais cost.gpu_required: false',
            'severity': 'MAJOR',
        })

    # Litmus 2 : api_usd_est: 0 mais API usage
    api_used = set()
    for _, src in code_cells_source:
        api_used.update(detect_api_usage(src))
    if api_used and cost_meta.get('api_usd_est', 0.0) == 0.0:
        for provider in api_used:
            findings.append({
                'pattern': 'api_used_but_cost_zero',
                'detail': f'Cellule code appelle {provider} mais cost.api_usd_est: 0.0',
                'severity': 'CRITICAL',
            })

    # Litmus 3 : external_account: none mais token usage
    tokens_required = set()
    for _, src in code_cells_source:
        tokens_required.update(detect_token_usage(src))
    declared_account = cost_meta.get('external_account', 'none')
    if tokens_required and declared_account == 'none':
        for provider in tokens_required:
            findings.append({
                'pattern': 'token_required_but_no_account',
                'detail': f'Cellule code lit token {provider} mais cost.external_account: none',
                'severity': 'MAJOR',
            })

    # Litmus 4 : free_alternative pointe vers un notebook inexistant
    free_alt = cost_meta.get('free_alternative')
    if free_alt:
        # free_alt est un path relatif du repo
        alt_path = repo_root / free_alt
        if not alt_path.exists():
            findings.append({
                'pattern': 'free_alternative_missing',
                'detail': f'cost.free_alternative pointe vers {free_alt} mais fichier absent',
                'severity': 'MAJOR',
            })

    # Litmus 5 : QC notebook sans qc_cloud validator
    uses_qc = any(detect_quantbook_usage(src) for _, src in code_cells_source)
    validator = cost_meta.get('validator', 'manual')
    if uses_qc and validator != 'qc_cloud':
        findings.append({
            'pattern': 'qc_notebook_no_validator',
            'detail': 'Notebook QuantConnect (QuantBook) mais cost.validator != qc_cloud',
            'severity': 'MAJOR',
        })

    # Litmus 6 : GPU sans sk_visual validator (cf #5780 sweep)
    if cost_meta.get('gpu_required', False) and validator not in ('sk_visual', 'papermill'):
        findings.append({
            'pattern': 'gpu_no_visual_validator',
            'detail': 'Notebook GPU sans sk_visual validator (cf sweep #5780)',
            'severity': 'MINOR',
        })

    return {
        'notebook': str(notebook_path),
        'cost_meta_found': bool(cost_meta),
        'cost_meta': cost_meta,
        'uses_gpu': uses_gpu,
        'api_used': sorted(api_used),
        'tokens_required': sorted(tokens_required),
        'uses_quantbook': uses_qc,
        'findings': findings,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('notebook', type=Path, help='Chemin du .ipynb à auditer')
    parser.add_argument('--out', type=Path, help='Fichier YAML de sortie (default: stdout)')
    parser.add_argument('--repo-root', type=Path, default=Path('.'),
                        help='Racine du repo (pour résoudre free_alternative)')
    args = parser.parse_args()

    if not args.notebook.exists():
        print(f"ERROR: notebook {args.notebook} introuvable", file=sys.stderr)
        return 1

    try:
        result = check_notebook(args.notebook, args.repo_root)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    # Sortie YAML
    lines = [
        f"notebook: {result['notebook']}",
        f"cost_meta_found: {result['cost_meta_found']}",
        f"uses_gpu: {result['uses_gpu']}",
        f"api_used: {result['api_used']}",
        f"tokens_required: {result['tokens_required']}",
        f"uses_quantbook: {result['uses_quantbook']}",
        "cost_meta:",
    ]
    for k, v in (result['cost_meta'] or {}).items():
        lines.append(f"  {k}: {v!r}")
    lines.append("findings:")
    for f in result['findings']:
        lines.append(f"  - pattern: {f['pattern']}")
        lines.append(f"    severity: {f['severity']}")
        lines.append(f"    detail: {f['detail']!r}")

    output = '\n'.join(lines)
    if args.out:
        args.out.write_text(output, encoding='utf-8')
        print(f"Audit écrit: {args.out}")
    else:
        print(output)
    return 0


if __name__ == '__main__':
    sys.exit(main())
