"""Convert print(CONTRACT) cells to compile_and_deploy() + interaction cells.

Pattern detection:
- Find code cells containing `CONTRACT = '''...'''; print(CONTRACT)` or similar
- Replace print() with compile_and_deploy()
- Add interaction cells after deployment

This is a semi-automatic process: it modifies the print to deploy but the
interaction code needs to be specific to each contract.
"""
import json
import os
import re

SC_BASE = "d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts"

def source_text(cell):
    """Get cell source as single string."""
    src = cell.get('source', '')
    if isinstance(src, list):
        return ''.join(src)
    return src

def make_source_list(text):
    """Convert text to LIST format source."""
    lines = text.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return result

def transform_print_cell(cell):
    """Transform a print(CONTRACT) cell into compile_and_deploy.

    Returns (modified_cell, was_transformed)
    """
    text = source_text(cell)

    # Pattern: VAR_NAME = '''...solidity...''' followed by print(VAR_NAME)
    # We keep the contract definition but replace print with compile_and_deploy

    # Check if this is a contract definition + print cell
    has_solidity = 'pragma solidity' in text
    has_print = 'print(' in text
    has_contract_var = re.search(r'(\w+)\s*=\s*[\'"]{3}', text) is not None

    if not (has_solidity and has_print and has_contract_var):
        return cell, False

    # Find the variable name
    match = re.search(r'(\w+)\s*=\s*[\'"]{3}', text)
    var_name = match.group(1)

    # Find contract name in the Solidity code
    contract_match = re.search(r'contract\s+(\w+)', text)
    contract_name = contract_match.group(1) if contract_match else "Unknown"

    # Check if constructor has parameters
    constructor_match = re.search(r'constructor\s*\((.*?)\)', text)
    has_constructor_params = constructor_match and constructor_match.group(1).strip()

    # Replace print() lines with compile_and_deploy
    new_lines = []
    for line in text.split('\n'):
        # Remove print lines
        if re.match(r'\s*print\s*\(', line):
            continue
        # Remove standalone header prints
        if line.strip().startswith('print(') and var_name not in line:
            continue
        new_lines.append(line)

    # Add deployment at the end
    instance_name = contract_name.lower()
    if has_constructor_params:
        new_lines.append(f"")
        new_lines.append(f"# Deployer (ajuster les arguments du constructeur si necessaire)")
        new_lines.append(f"# {instance_name}, receipt = compile_and_deploy(w3, {var_name}, deployer)")
        new_lines.append(f"# print(f\"Deploye a: {{{instance_name}.address}}\")")
    else:
        new_lines.append(f"")
        new_lines.append(f"# Compilation et deploiement reel sur anvil")
        new_lines.append(f"{instance_name}, receipt = compile_and_deploy(w3, {var_name}, deployer)")

    cell['source'] = make_source_list('\n'.join(new_lines))
    return cell, True

# Process notebooks
notebooks = [
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-1-Solidity-Basics.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-2-Functions-State.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-3-Inheritance.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-4-Errors-Events.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-5-Token-Standards.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-6-DeFi-Primitives.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-7-DAO-Governance.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-8-Account-Abstraction.ipynb"),
]

total_transformed = 0
for nb_path in notebooks:
    basename = os.path.basename(nb_path)
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    transformed = 0
    for cell in nb['cells']:
        if cell.get('cell_type') != 'code':
            continue
        cell, was_transformed = transform_print_cell(cell)
        if was_transformed:
            transformed += 1

    if transformed > 0:
        with open(nb_path, 'w', encoding='utf-8', newline='\n') as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write('\n')
        print(f"  {basename}: {transformed} cells converted (print -> deploy)")
        total_transformed += transformed
    else:
        print(f"  {basename}: no print-contract cells found")

print(f"\nTotal: {total_transformed} cells converted across {len(notebooks)} notebooks")
