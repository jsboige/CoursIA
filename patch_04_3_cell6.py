"""Patch 04-3 cell 6 to handle missing aiohttp/openai gracefully."""
import json
from pathlib import Path

NB = Path('MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-3-Production-Integration.ipynb')
nb = json.load(NB.open(encoding='utf-8'))

c = nb['cells'][6]
src_lines = c['source']

# Find line numbers
aiohttp_idx = None
openai_idx = None
log_level_idx = None
log_level_basicConfig_idx = None

for i, line in enumerate(src_lines):
    if line.strip() == 'import asyncio' or line.strip() == 'import aiohttp':
        if aiohttp_idx is None:
            aiohttp_idx = i
    if line.strip().startswith('from openai import'):
        openai_idx = i
    if 'log_level' in line and '.upper()' in line and 'getattr' in line:
        log_level_basicConfig_idx = i

print(f'aiohttp block starts at line {aiohttp_idx}')
print(f'openai import at line {openai_idx}')
print(f'logging.basicConfig with log_level at line {log_level_basicConfig_idx}')

# Wrap imports in try/except
# Original lines from aiohttp_idx to (openai_idx + 2) approximately
if aiohttp_idx and openai_idx:
    new_lines = []
    new_lines.append("# === Pre-amble: ensure user-site-packages is on sys.path for diffusers ===")
    new_lines.append("import sys, os")
    new_lines.append("from pathlib import Path as _P")
    new_lines.append("_user_site = _P(os.environ.get('APPDATA', r'C:\\Users\\jsboi\\AppData\\Roaming')) / 'Python' / 'Python313' / 'site-packages'")
    new_lines.append("_user_site_str = str(_user_site)")
    new_lines.append("if _user_site_str not in sys.path:")
    new_lines.append("    sys.path.insert(0, _user_site_str)")
    new_lines.append("# =======================================================================")
    new_lines.append("")
    new_lines.append("# === PATCH #12961: graceful import for optional deps (aiohttp, openai) ===")
    new_lines.append("try:")
    for i in range(aiohttp_idx, openai_idx):
        new_lines.append("    " + src_lines[i].lstrip())
    new_lines.append("except ImportError as e:")
    new_lines.append("    print(f'⚠️ Optional deps missing: {e}')")
    new_lines.append("    # RECOVERABLE-USER-HAND: openai API requires API key + libs")
    new_lines.append("    aiohttp = None")
    new_lines.append("    AsyncOpenAI = None")
    new_lines.append("    OpenAI = None")
    new_lines.append("# =======================================================================")

    # Replace original lines from aiohttp_idx to openai_idx-1 with new_lines
    src_lines = src_lines[:aiohttp_idx] + new_lines + src_lines[openai_idx:]

# Fix logging.basicConfig using log_level that may not be defined
# Replace getattr(logging, log_level.upper(), logging.INFO) with safe version
src_lines = [line.replace(
    "level=getattr(logging, log_level.upper(), logging.INFO)",
    "level=logging.INFO  # PATCH #12961: log_level undefined → default INFO"
) for line in src_lines]

c['source'] = src_lines
NB.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
print(f"\nPatched 04-3 cell 6 ({len(src_lines)} lines)")
print(f"New first 15 lines of cell 6:")
for i, line in enumerate(src_lines[:25]):
    print(f" [{i}] {line}")
