"""Patch 04-3: inject sys.path for diffusers (user-site-packages)."""
import json
from pathlib import Path

NB = Path('MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-3-Production-Integration.ipynb')
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

# Find first code cell that imports diffusers (cell 13 = our new patched cell)
TARGET_CELL = None
for i, c in enumerate(nb['cells']):
    src = ''.join(c.get('source', []))
    if 'from diffusers import StableDiffusionPipeline' in src:
        TARGET_CELL = i
        break

if TARGET_CELL is None:
    print("ERROR: no diffusers import cell found")
    raise SystemExit(1)

c = nb['cells'][TARGET_CELL]
if not any('Pre-amble: ensure user-site-packages' in line for line in c['source']):
    c['source'] = CLEAN_INJECTION + c['source']
    print(f"Cell {TARGET_CELL}: prepended sys.path injection ({len(c['source'])} lines)")
else:
    print(f"Cell {TARGET_CELL}: already patched (idempotent)")

NB.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
print(f"Saved {NB.name}")
