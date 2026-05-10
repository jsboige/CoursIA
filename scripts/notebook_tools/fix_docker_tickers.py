"""Replace unavailable tickers in quantbook notebooks with Docker-available ones.

Available in Docker: AAPL, GOOGL, GOOG, SPY, QQQ, IWM, USO, BAC
"""
import json
import re
import sys
from pathlib import Path

AVAILABLE = {'AAPL', 'GOOGL', 'GOOG', 'SPY', 'QQQ', 'IWM', 'USO', 'BAC'}

# Mapping: unavailable -> best available proxy
TICKER_MAP = {
    'MSFT': 'QQQ',
    'TLT': 'IWM',
    'GLD': 'USO',
    'SHY': 'SPY',
    'XLF': 'BAC',
    'XLE': 'USO',
    'XLK': 'QQQ',
    'XLP': 'SPY',
    'XLY': 'QQQ',
    'XLV': 'BAC',
    'XLU': 'IWM',
    'XLI': 'IWM',
    'XLRE': 'SPY',
    'XLB': 'IWM',
    'NVDA': 'AAPL',
    'AMD': 'GOOGL',
    'ORCL': 'GOOGL',
    'CSCO': 'BAC',
    'QCOM': 'AAPL',
    'AMZN': 'GOOGL',
    'INTC': 'BAC',
    'TSLA': 'AAPL',
    'META': 'GOOGL',
    'NFLX': 'GOOGL',
    'DIS': 'AAPL',
    'BA': 'IWM',
    'CAT': 'IWM',
    'GE': 'IWM',
    'V': 'BAC',
    'MA': 'BAC',
    'JPM': 'BAC',
    'WFC': 'BAC',
    'GS': 'BAC',
    'JNJ': 'SPY',
    'PFE': 'SPY',
    'UNH': 'SPY',
    'WMT': 'SPY',
    'HD': 'QQQ',
    'MCD': 'SPY',
    'NKE': 'QQQ',
    'KO': 'SPY',
    'PEP': 'SPY',
    'PG': 'SPY',
    'SVXY': 'QQQ',  # short vol → tech
    'SPVXSTR': 'SPY',  # VIX related
    'DIA': 'SPY',
    'SLV': 'USO',
}

def fix_notebook(nb_path: Path) -> dict:
    try:
        nb = json.loads(nb_path.read_text(encoding='utf-8'))
    except Exception as e:
        return {'path': str(nb_path), 'error': f'JSON_ERROR: {e}', 'changes': 0}

    total_changes = 0
    for cell in nb['cells']:
        if cell['cell_type'] != 'code':
            continue
        src = cell['source']
        if isinstance(src, list):
            src = ''.join(src)

        new_src = src
        for old_t, new_t in TICKER_MAP.items():
            if old_t not in AVAILABLE:
                # Replace in single-quoted strings: 'MSFT' -> 'QQQ'
                new_src = re.sub(rf"'{old_t}'", f"'{new_t}'", new_src)
                # Replace in double-quoted strings: "MSFT" -> "QQQ"
                new_src = re.sub(rf'"{old_t}"', f'"{new_t}"', new_src)

        if new_src != src:
            if isinstance(cell['source'], list):
                cell['source'] = new_src.split('\n')
                cell['source'] = [line + '\n' for line in cell['source'][:-1]] + [cell['source'][-1]]
            else:
                cell['source'] = new_src
            total_changes += 1

    if total_changes > 0:
        nb_path.write_text(json.dumps(nb, indent=1, ensure_ascii=False), encoding='utf-8')

    return {'path': nb_path.name, 'changes': total_changes}


def main():
    targets_dir = Path('MyIA.AI.Notebooks/QuantConnect/projects')
    notebooks = sorted(targets_dir.glob('*/quantbook.ipynb'))
    print(f'Found {len(notebooks)} quantbook notebooks')

    total_changed = 0
    for nb in notebooks:
        r = fix_notebook(nb)
        if r['changes'] > 0:
            print(f"  {r['path']}: {r['changes']} cells fixed")
            total_changed += 1

    print(f'\nTotal: {total_changed}/{len(notebooks)} notebooks modified')


if __name__ == '__main__':
    main()
