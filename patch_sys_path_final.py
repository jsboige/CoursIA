"""Patch 03-3: strip all existing injection blocks (any form), inject clean one."""
import json
from pathlib import Path

NB = Path('MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-3-Performance-Optimization.ipynb')
nb = json.load(NB.open(encoding='utf-8'))

CLEAN_INJECTION = [
    "# === Pre-amble: ensure user-site-packages is on sys.path for diffusers ===",
    "import sys, os",
    "from pathlib import Path as _P",
    "_user_site = _P(os.environ.get('APPDATA', r'C:\\Users\\jsboi\\AppData\\Roaming')) / 'Python' / 'Python313' / 'site-packages'",
    "_user_site_str = str(_user_site)",
    "if _user_site_str not in sys.path:",
    "    sys.path.insert(0, _user_site_str)",
    "# =======================================================================",
    "",
]

# Detect any line that's part of an injection block (start marker, sys.path manip, path construction)
INJECTION_LINE_SUBSTRINGS = [
    "Pre-amble: ensure user-site-packages",
    "Force diffusers path injection (user-site-packages)",
    "Force sys.path to include user-site-packages",
    "user_site = os.environ.get",
    "user_site = _P(",
    "_user_site = _P(",
    "_user_site = os.environ",
    "_user_site_str = str(",
    "sys.path.insert(0, _user_site_str)",
    "sys.path.insert(0, user_site)",
    "if user_site not in sys.path:",
    "if _user_site_str not in sys.path:",
    "from pathlib import Path as _P",
    "==== Pre-amble:",  # safety
    "===========Pre-amble",  # safety
    "==========Pre-amble",  # safety
    "from pathlib import Path",
]

# Separator decoration lines (longer)
def is_decoration(line):
    s = line.strip()
    if s.startswith('# ===') or s.startswith('# ====') or s.startswith('# ====='):
        return True
    return False

for i in [4, 55]:
    c = nb['cells'][i]
    src_list = list(c['source'])
    # Drop any line that looks like an injection fragment
    cleaned = []
    for line in src_list:
        if any(sub in line for sub in INJECTION_LINE_SUBSTRINGS):
            continue
        if is_decoration(line) and len(cleaned) == 0:
            # Drop leading decoration
            continue
        if is_decoration(line) and len(cleaned) > 0 and cleaned[-1].strip() == '':
            # Drop decoration followed by blank (end of old injection block)
            # Actually we want to KEEP leading decoration that belongs to original cell
            # So we only drop if line directly follows an injection fragment
            # Check context: drop if previous non-blank was injection
            cleaned.pop()
            continue
        cleaned.append(line)
    # Strip leading blanks
    while cleaned and cleaned[0].strip() == '':
        cleaned.pop(0)
    # Prepend clean injection
    c['source'] = CLEAN_INJECTION + cleaned
    print(f"Cell {i}: {len(src_list)} -> {len(c['source'])} lines")

NB.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
print(f"Saved {NB.name}")
