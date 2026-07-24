#!/usr/bin/env python3
"""
extract_claims_vs_outputs.py — Audit sémantique cell-par-cell.

Issue #8052 (P0) — protocole d'échantillonnage sémantique cross-famille.

But : extraire pour un notebook :
  - Les claims numériques/qualitatifs du MARKDOWN (titres, conclusions, interprétations)
  - Les outputs réels des cellules CODE
  - Signaler les :
      (1) Mismatch : claim numérique markdown qui n'apparaît pas dans les outputs
      (2) Fallback silencieux : try/except ImportError broad qui réassigne à trivial
      (3) Verdict markdown positif alors que warnings/erreurs dans les outputs
      (4) Outil SOTA mentionné dans markdown mais pas importé dans les cells code
      (5) Cohérence pédagogique (cf exercise-example-labeling.md)

Usage :
  python scripts/audit/extract_claims_vs_outputs.py <notebook>.ipynb [--out <fichier.yml>]

Litmus anti-LIGHT : ce script EXTRACT, il ne DÉCIDE pas. Le verdict final = revue
humaine/agent compétent dans le domaine. Cf docs/audit/sampling-protocol.md.
"""

import argparse
import json
import re
import sys
from pathlib import Path

import nbformat


# === Patterns de détection ===

# Claims numériques : "95%", "1234", "3.14", "100k", "10⁵"
CLAIM_NUMERIC_RE = re.compile(
    r'\b(?:\d{1,3}(?:[,.\s]\d{3})*(?:[.,]\d+)?|\d+(?:\.\d+)?)\s*(?:%|k|M|ms|s|min|h)?\b'
)

# Fallback silencieux : try: ... except ImportError: ...
FALLBACK_RE = re.compile(
    r'(try:\s*\n[\s\S]*?except[^:]*:\s*\n[\s\S]*?(?:pass|return [^\n]*\n|\w+\s*=\s*[A-Za-z][^\n]*\n))',
    re.MULTILINE
)

# Verdict positif : "Conclusion", "Synthèse", "Verdict"
VERDICT_HEADER_RE = re.compile(
    r'^#+\s*(?:Conclusion|Synthèse|Verdict|Résultat|Summary)\b',
    re.IGNORECASE | re.MULTILINE
)

# Outil SOTA mentionné dans markdown (multi-language: Python + .NET Interactive + Lean)
# Note : utiliser la classe [.] pour matcher un point littéral sans backslash escape,
# sinon SyntaxWarning sous Python 3.12+.
SOTA_TOOLS = [
    # Python PPL / ML
    'pyphi', 'pymc', 'numpyro', 'stan', 'scikit-learn', 'sklearn',
    'xgboost', 'lightgbm', 'catboost', 'tensorflow', 'pytorch',
    'transformers', 'tenseal', 'concrete-ml', 'pyfhel', 'paillier',
    # .NET Interactive / Infer.NET — alias regroupés via SOTA_ALIASES ci-dessous
    'infer[.]net', 'microsoft[.]ml[.]probabilistic', 'msinfer', 'minfer',
    # Solveurs CSP / SMT
    'z3', 'cplex', 'gurobi', 'ortools', 'cp-sat', 'cpsat',
    # Visualisation (SOTA ad hoc)
    'plotly', 'matplotlib', 'seaborn', 'pyviz',
    # Argumentum / Tweety / SW
    'tweety', 'socialchoice', 'kop', 'sweety',
    # Lean 4
    'mathlib',
    # GenAI services
    'qwen', 'claude', 'gpt-4', 'mistral', 'lumen',
    # Agents / Frameworks
    'netlogo', 'autogen', 'langgraph',
]


# Fix A — anti-bruit (cf #8052 pilote C# c.848) : un nombre sur une ligne de header
# markdown ("# Search-11", "## Étape 3", "### Section 10") est un numéro de
# section/titre, pas un claim pédagogique. Sur les notebooks .NET (titres riches en
# numéros de série/section), ce bruit explosait à 100+ "numeric_claim_not_in_outputs"
# MAJOR qui masquaient les vrais findings. On ne coupe QUE les entiers nus (1-3 digits,
# sans unité) sur headers — un claim à unité ("95%", "40×") sur un titre est préservé.
HEADER_BARE_INT_RE = re.compile(r'^\d{1,3}$')


def _on_header_line(cell_source: str, start: int) -> bool:
    """True si le match débutant à `start` est sur une ligne markdown commençant par '#'."""
    line_start = cell_source.rfind('\n', 0, start) + 1
    return cell_source[line_start:].lstrip().startswith('#')


def extract_markdown_claims(cell_source: str) -> dict:
    """Extrait les claims numériques/qualitatifs d'une cellule markdown."""
    claims = []
    for match in CLAIM_NUMERIC_RE.finditer(cell_source):
        value = match.group(0).strip()
        # Fix A : ignore les entiers nus (1-3 digits) sur les lignes de header markdown
        # — numéros de section/titre ("# Search-11", "## Étape 3"), pas des claims.
        # SAUF si l'entier est immédiatement suivi d'une unité dans le source ("%","×",
        # "x","°") : "### Précision : 95%" est un vrai claim (le % échappe au \b du regex
        # et n'est pas dans la valeur extraite, on le détecte donc via le char qui suit).
        if HEADER_BARE_INT_RE.match(value) and _on_header_line(cell_source, match.start()):
            trailing = cell_source[match.end():match.end() + 2]
            if not re.match(r'^\s*[%×x°]', trailing):
                continue
        claims.append({
            'value': value,
            'span': match.span(),
        })
    has_verdict_header = bool(VERDICT_HEADER_RE.search(cell_source))
    has_positive_verdict = bool(re.search(
        r'(?:succès|réussi|opérationnel|valide|true|✓|✔|✅|positif)',
        cell_source,
        re.IGNORECASE
    ))
    return {
        'numeric_claims': claims,
        'has_verdict_header': has_verdict_header,
        'has_positive_verdict': has_positive_verdict,
        'mentioned_sota_tools': [
            tool for tool in SOTA_TOOLS
            if re.search(rf'\b{re.escape(tool)}\b', cell_source, re.IGNORECASE)
            or re.search(rf'\b{SOTA_ALIASES.get(tool, re.escape(tool))}\b', cell_source, re.IGNORECASE)
        ],
    }


def extract_code_outputs(cell: dict) -> dict:
    """Extrait les sorties réelles d'une cellule code (texte + erreur)."""
    outputs = cell.get('outputs', [])
    text_chunks = []
    has_error = False
    has_warning = False
    numeric_values_found = set()

    for out in outputs:
        if out.get('output_type') == 'stream':
            text = out.get('text', '')
            if isinstance(text, list):
                text = ''.join(text)
            text_chunks.append(text)
            if out.get('name') == 'stderr':
                if 'error' in text.lower() or 'traceback' in text.lower():
                    has_error = True
                elif 'warning' in text.lower():
                    has_warning = True
        elif out.get('output_type') == 'error':
            has_error = True
            text_chunks.append(f"ERROR: {out.get('ename', '')} {out.get('evalue', '')}")
        elif out.get('output_type') in ('execute_result', 'display_data'):
            data = out.get('data', {})
            for mime, content in data.items():
                if mime == 'text/plain':
                    if isinstance(content, list):
                        content = ''.join(content)
                    text_chunks.append(content)
                    # Extract numbers from text
                    for match in CLAIM_NUMERIC_RE.finditer(content):
                        numeric_values_found.add(match.group(0).strip())

    return {
        'text': '\n'.join(text_chunks),
        'has_error': has_error,
        'has_warning': has_warning,
        'numeric_values': sorted(numeric_values_found),
    }


def detect_fallback_silent(code_source: str) -> list:
    """Détecte les try/except ImportError broad swallows."""
    findings = []
    for match in FALLBACK_RE.finditer(code_source):
        except_line = match.group(0).split('except')[1].split('\n')[0]
        if 'ImportError' in except_line or 'Exception' in except_line:
            findings.append({
                'pattern': 'silent_fallback',
                'snippet': match.group(0)[:200],
                'severity': 'CRITICAL' if 'pass' in match.group(0) else 'MAJOR',
            })
    return findings


# === Aliases SOTA — plusieurs noms pour le même moteur ===
# Permet de dire "infer.net" (md) ↔ "Microsoft.ML.Probabilistic" (nuget) = match.
# Utilise la classe [.] pour matcher un point littéral, sans backslash escape.
SOTA_ALIASES = {
    'infer[.]net': '(?:infer[.]net|msinfer|minfer|microsoft[.]ml[.]probabilistic)',
    'microsoft[.]ml[.]probabilistic': '(?:microsoft[.]ml[.]probabilistic|msinfer|minfer|infer[.]net)',
    'msinfer': '(?:msinfer|minfer|microsoft[.]ml[.]probabilistic|infer[.]net)',
    'minfer': '(?:minfer|msinfer|microsoft[.]ml[.]probabilistic|infer[.]net)',
}

# Nom canonique lisible pour reporting (clé = SOTA_TOOLS token interne, valeur = nom affiché)
SOTA_CANONICAL_NAME = {
    'infer[.]net': 'Infer.NET',
    'microsoft[.]ml[.]probabilistic': 'Microsoft.ML.Probabilistic',
    'msinfer': 'Infer.NET',
    'minfer': 'Infer.NET',
}


def canonical_name(tool: str) -> str:
    """Nom canonique affichable (ex: 'infer[.]net' -> 'Infer.NET')."""
    return SOTA_CANONICAL_NAME.get(tool, tool)


def audit_notebook(notebook_path: Path) -> dict:
    """Audit complet d'un notebook."""
    with notebook_path.open('r', encoding='utf-8') as f:
        nb = nbformat.read(f, as_version=4)

    findings = []
    all_numeric_claims = []
    all_numeric_outputs = set()
    sota_tools_imports = set()
    sota_tools_mentioned = set()

    # Fix B — anti-bruit (cf #8052 pilote C# c.848) : sur un notebook .NET Interactive,
    # les outils de visualisation Python (matplotlib, seaborn, pyviz) ne sont PAS
    # pertinents — un .ipynb C#/.NET utilise Plotly/XPlot. Le markdown cite souvent
    # l'équivalent Python à titre pédagogique comparatif ("en Python on aurait utilisé
    # matplotlib"), ce que le litmus 4 signalait à tort comme "SOTA mentionné non
    # importé". On les exclut donc du litmus 4 sur kernel .NET.
    DOTNET_PYTHON_VIZ = {'matplotlib', 'seaborn', 'pyviz'}
    ks_name = (nb.get('metadata', {}) or {}).get('kernelspec', {}) or {}
    ks_name = (ks_name.get('name', '') or '').lower()
    is_dotnet = any(k in ks_name for k in ('.net', 'csharp', 'fsharp', 'polyglot'))
    if not is_dotnet:
        # Heuristique de secours : cellules code .NET Interactive (#r nuget / using
        # Microsoft. / magic #!csharp). Évite un .ipynb mal étiqueté kernelspec.
        for c in nb.cells:
            if c.get('cell_type') != 'code':
                continue
            src = c.get('source', '')
            if isinstance(src, list):
                src = ''.join(src)
            if re.search(r'#r\s+"[^"]*nuget|using\s+Microsoft\.|#!\s*(?:csharp|fsharp|pwsh)', src, re.IGNORECASE):
                is_dotnet = True
                break

    for idx, cell in enumerate(nb.cells):
        cell_type = cell.get('cell_type', '')
        source = cell.get('source', '')
        if isinstance(source, list):
            source = ''.join(source)

        if cell_type == 'markdown':
            claims = extract_markdown_claims(source)
            all_numeric_claims.extend([
                {'cell_idx': idx, **c} for c in claims['numeric_claims']
            ])
            sota_tools_mentioned.update(claims['mentioned_sota_tools'])

        elif cell_type == 'code':
            # Detect imports for SOTA tools actually used (multi-language: Python import/from,
            # .NET Interactive #r nuget:/using, Lean import, C# using/var, Markdown code-fence load)
            for tool in SOTA_TOOLS:
                # Token matchable = tool literal OU un de ses aliases (ex: infer[.]net ↔ microsoft[.]ml[.]probabilistic)
                token_matchable = SOTA_ALIASES.get(tool, re.escape(tool))
                patterns = [
                    rf'(?:^|\n)\s*(?:from|import)\s+[\w.]*(?:{token_matchable})',  # Python
                    rf'#r\s+"[^"]*(?:{token_matchable})',                            # .NET Interactive nuget:
                    rf'using\s+[\w.]*(?:{token_matchable})',                         # C# using directive
                    rf'(?:^|\n)\s*import\s+[\w.]*(?:{token_matchable})',             # Lean / generic
                    rf'#load\s+"[^"]*(?:{token_matchable})',                         # .NET Interactive load directive
                ]
                for pat in patterns:
                    if re.search(pat, source, re.IGNORECASE):
                        sota_tools_imports.add(tool)
                        break

            # Fallback silent detection
            findings.extend([
                {'cell_idx': idx, **f} for f in detect_fallback_silent(source)
            ])

            # Outputs
            outputs = extract_code_outputs(cell)
            all_numeric_outputs.update(outputs['numeric_values'])

            # Litmus 3 : verdict positif markdown + error dans outputs
            if outputs['has_error']:
                # Mark for later matching against markdown claims
                findings.append({
                    'cell_idx': idx,
                    'pattern': 'output_has_error',
                    'snippet': outputs['text'][:200],
                    'severity': 'INFO',
                })

    # Litmus 1 : claim numérique markdown qui n'apparaît pas dans outputs
    matched = unmatched = 0
    for claim in all_numeric_claims:
        # Substring match (claim peut être avec unités)
        if any(claim['value'] in num or num in claim['value']
               for num in all_numeric_outputs):
            matched += 1
        else:
            unmatched += 1
            findings.append({
                'cell_idx': claim['cell_idx'],
                'pattern': 'numeric_claim_not_in_outputs',
                'claim_value': claim['value'],
                'severity': 'MAJOR',  # MAJOR = claim exagéré possible
            })

    # Litmus 4 : SOTA tool mentionné mais pas importé (canonicalisé pour reporting)
    # On déduplique au niveau canonique AVANT la soustraction (sinon 4 tokens internes
    # mappent au même nom affiché 'Infer.NET' et faussent le comptage).
    mentioned_canon = {canonical_name(t) for t in sota_tools_mentioned}
    if is_dotnet:
        # Fix B : viz Python non pertinente en .NET (cf commentaire en tête de fonction)
        mentioned_canon -= DOTNET_PYTHON_VIZ
    imported_canon = {canonical_name(t) for t in sota_tools_imports}
    mentioned_not_imported_canon = mentioned_canon - imported_canon
    for tool_canon in mentioned_not_imported_canon:
        findings.append({
            'pattern': 'sota_mentioned_not_imported',
            'tool': tool_canon,
            'severity': 'MAJOR',  # MAJOR = fallback silencieux probable
        })

    return {
        'notebook': str(notebook_path),
        'numeric_claims_total': len(all_numeric_claims),
        'numeric_claims_matched': matched,
        'numeric_claims_unmatched': unmatched,
        'sota_tools_mentioned': sorted({canonical_name(t) for t in sota_tools_mentioned}),
        'sota_tools_imported': sorted({canonical_name(t) for t in sota_tools_imports}),
        'sota_tools_mentioned_not_imported': sorted(mentioned_not_imported_canon),
        'findings': findings,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('notebook', type=Path, help='Chemin du .ipynb à auditer')
    parser.add_argument('--out', type=Path, help='Fichier YAML de sortie (default: stdout)')
    args = parser.parse_args()

    if not args.notebook.exists():
        print(f"ERROR: notebook {args.notebook} introuvable", file=sys.stderr)
        return 1

    try:
        result = audit_notebook(args.notebook)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    # Sortie YAML manuelle (pas de PyYAML dep pour rester léger)
    lines = [
        f"notebook: {result['notebook']}",
        f"numeric_claims_total: {result['numeric_claims_total']}",
        f"numeric_claims_matched: {result['numeric_claims_matched']}",
        f"numeric_claims_unmatched: {result['numeric_claims_unmatched']}",
        f"sota_tools_mentioned: {result['sota_tools_mentioned']}",
        f"sota_tools_imported: {result['sota_tools_imported']}",
        f"sota_tools_mentioned_not_imported: {result['sota_tools_mentioned_not_imported']}",
        "findings:",
    ]
    for f in result['findings']:
        snippet_or_value = f.get('snippet', f.get('claim_value', f.get('tool', '?')))
        lines.append(f"  - pattern: {f['pattern']}")
        lines.append(f"    severity: {f['severity']}")
        lines.append(f"    detail: {snippet_or_value!r}")
        if 'cell_idx' in f:
            lines.append(f"    cell_idx: {f['cell_idx']}")

    output = '\n'.join(lines)
    if args.out:
        args.out.write_text(output, encoding='utf-8')
        print(f"Audit écrit: {args.out}")
    else:
        print(output)
    return 0


if __name__ == '__main__':
    sys.exit(main())
