"""Scan SC-15 for f-string issues causing SyntaxError in Python 3.11+."""
import json, re

path = r'MyIA.AI.Notebooks/SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs.ipynb'
with open(path, 'r', encoding='utf-8') as f:
    nb = json.load(f)

print(f"Total cells: {len(nb['cells'])}")
issues = []

for i, cell in enumerate(nb['cells']):
    if cell.get('cell_type') != 'code':
        continue
    src = ''.join(cell['source'])

    # Pattern: f-string containing backslash (illegal in Python 3.12+)
    # f"...\" or f'...\'
    # Also: f-string with nested quotes issues
    for j, line in enumerate(cell['source']):
        line_text = line.rstrip()

        # Check f-string with backslash escapes
        # Python 3.12 forbids backslash in f-string expressions
        # But the issue is likely f"...\"..." where \ is inside f-string

        # Simple check: f" or f' with content that has \n \t \\ etc inside braces
        # Actually the most common issue is f-string with = sign and complex expressions
        # Let's just find all f-strings
        if re.search(r"""f['"]""", line_text):
            # Check for backslash inside f-string expression
            matches = re.finditer(r"""f(['"])(.*?)\1""", line_text)
            for m in matches:
                content = m.group(2)
                if '\\' in content and '{' in content:
                    issues.append((i, j, line_text[:120]))
                    print(f"  CELL[{i}] LINE[{j}]: {line_text[:120]}")

if not issues:
    print("\nNo obvious f-string backslash issues found.")
    print("\nAll f-string lines:")
    for i, cell in enumerate(nb['cells']):
        if cell.get('cell_type') != 'code':
            continue
        for j, line in enumerate(cell['source']):
            if re.search(r"""f['"]""", line.rstrip()):
                print(f"  CELL[{i}] LINE[{j}]: {line.rstrip()[:120]}")
