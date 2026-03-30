"""Update navigation links in all 27 SmartContracts notebooks."""
import json, os, re

SC_BASE = "d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts"

# Ordered list of all notebooks with their paths relative to SC_BASE
NOTEBOOKS = [
    ("00-Foundations", "SC-0-Cypherpunk-Origins"),
    ("00-Foundations", "SC-1-Setup-Foundry"),
    ("00-Foundations", "SC-2-Setup-Web3py"),
    ("01-Solidity-Foundation", "SC-3-Solidity-Basics"),
    ("01-Solidity-Foundation", "SC-4-Functions-State"),
    ("01-Solidity-Foundation", "SC-5-Inheritance"),
    ("01-Solidity-Foundation", "SC-6-Errors-Events"),
    ("02-Solidity-Advanced", "SC-7-Token-Standards"),
    ("02-Solidity-Advanced", "SC-8-DeFi-Primitives"),
    ("02-Solidity-Advanced", "SC-9-DAO-Governance"),
    ("02-Solidity-Advanced", "SC-10-Account-Abstraction"),
    ("02-Solidity-Advanced", "SC-11-LLM-Assisted"),
    ("03-Foundry-Testing", "SC-12-Foundry-Testing"),
    ("03-Foundry-Testing", "SC-13-Fuzz-Invariants"),
    ("03-Foundry-Testing", "SC-14-Formal-Verification"),
    ("04-Privacy-Cryptography", "SC-15-Zero-Knowledge-Proofs"),
    ("04-Privacy-Cryptography", "SC-16-Homomorphic-Encryption"),
    ("04-Privacy-Cryptography", "SC-17-E2E-Verifiable-Voting"),
    ("05-Alternative-Chains", "SC-18-Vyper"),
    ("05-Alternative-Chains", "SC-19-Ripple-XRP"),
    ("05-Alternative-Chains", "SC-20-Bitcoin-Scripting"),
    ("05-Alternative-Chains", "SC-21-Move-Sui"),
    ("05-Alternative-Chains", "SC-22-Solana-Anchor"),
    ("06-Real-World", "SC-23-Cross-Chain"),
    ("06-Real-World", "SC-24-Testnet-Deploy"),
    ("06-Real-World", "SC-25-Mainnet-Deploy"),
    ("06-Real-World", "SC-26-Final-Project"),
]

# Human-readable short names
SHORT_NAMES = {
    "SC-0-Cypherpunk-Origins": "Cypherpunk Origins",
    "SC-1-Setup-Foundry": "Setup Foundry",
    "SC-2-Setup-Web3py": "Setup Web3py",
    "SC-3-Solidity-Basics": "Solidity Basics",
    "SC-4-Functions-State": "Functions & State",
    "SC-5-Inheritance": "Inheritance",
    "SC-6-Errors-Events": "Errors & Events",
    "SC-7-Token-Standards": "Token Standards",
    "SC-8-DeFi-Primitives": "DeFi Primitives",
    "SC-9-DAO-Governance": "DAO Governance",
    "SC-10-Account-Abstraction": "Account Abstraction",
    "SC-11-LLM-Assisted": "LLM Assisted",
    "SC-12-Foundry-Testing": "Foundry Testing",
    "SC-13-Fuzz-Invariants": "Fuzz & Invariants",
    "SC-14-Formal-Verification": "Formal Verification",
    "SC-15-Zero-Knowledge-Proofs": "Zero-Knowledge Proofs",
    "SC-16-Homomorphic-Encryption": "Homomorphic Encryption",
    "SC-17-E2E-Verifiable-Voting": "E2E Verifiable Voting",
    "SC-18-Vyper": "Vyper",
    "SC-19-Ripple-XRP": "Ripple XRP",
    "SC-20-Bitcoin-Scripting": "Bitcoin Scripting",
    "SC-21-Move-Sui": "Move & Sui",
    "SC-22-Solana-Anchor": "Solana & Anchor",
    "SC-23-Cross-Chain": "Cross-Chain",
    "SC-24-Testnet-Deploy": "Testnet Deploy",
    "SC-25-Mainnet-Deploy": "Mainnet Deploy",
    "SC-26-Final-Project": "Final Project",
}


def relative_path(from_dir, to_dir, to_name):
    """Compute relative path from one notebook directory to another."""
    if from_dir == to_dir:
        return f"{to_name}.ipynb"
    else:
        return f"../{to_dir}/{to_name}.ipynb"


def make_nav_line(idx):
    """Create navigation markdown line for notebook at index idx."""
    parts = []
    if idx > 0:
        prev_dir, prev_name = NOTEBOOKS[idx - 1]
        cur_dir = NOTEBOOKS[idx][0]
        prev_path = relative_path(cur_dir, prev_dir, prev_name)
        prev_short = SHORT_NAMES[prev_name]
        parts.append(f"[<< {prev_short}]({prev_path})")

    if idx < len(NOTEBOOKS) - 1:
        next_dir, next_name = NOTEBOOKS[idx + 1]
        cur_dir = NOTEBOOKS[idx][0]
        next_path = relative_path(cur_dir, next_dir, next_name)
        next_short = SHORT_NAMES[next_name]
        parts.append(f"[{next_short} >>]({next_path})")

    return " | ".join(parts)


def source_text(cell):
    src = cell.get('source', '')
    if isinstance(src, list):
        return ''.join(src)
    return src


def make_source_list(text):
    lines = text.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return result


def is_nav_cell(cell, text=None):
    """Check if a cell is a navigation cell (contains << or >> links)."""
    if cell.get('cell_type') != 'markdown':
        return False
    if text is None:
        text = source_text(cell)
    # Navigation cells have patterns like [<< ...] or [... >>]
    return bool(re.search(r'\[<<\s', text) or re.search(r'\s>>\]', text))


def update_notebook_nav(nb_path, nav_line, notebook_name):
    """Update navigation in a notebook. Returns True if modified."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    modified = False

    # Strategy: find existing nav cells (typically first and last markdown cells)
    # and replace their content with the new nav line.

    # Check first few cells for nav
    header_nav_found = False
    for i in range(min(3, len(cells))):
        text = source_text(cells[i])
        if is_nav_cell(cells[i], text):
            # Update the nav line within this cell
            # The nav line might be part of a larger header cell
            lines = text.split('\n')
            new_lines = []
            nav_replaced = False
            for line in lines:
                if re.search(r'\[<<\s', line) or re.search(r'\s>>\]', line):
                    if not nav_replaced:
                        new_lines.append(nav_line)
                        nav_replaced = True
                    # Skip additional nav lines
                else:
                    new_lines.append(line)
            if not nav_replaced:
                new_lines.insert(1, '')
                new_lines.insert(2, nav_line)
            cells[i]['source'] = make_source_list('\n'.join(new_lines))
            header_nav_found = True
            modified = True
            break

    # If no nav in header, check if the title cell (first cell) has the nav
    if not header_nav_found and cells and cells[0].get('cell_type') == 'markdown':
        text = source_text(cells[0])
        if text.startswith('# SC-') or text.startswith('# '):
            # Add nav after title
            lines = text.split('\n')
            # Insert nav after the first heading line
            heading_end = 0
            for j, line in enumerate(lines):
                if line.startswith('# '):
                    heading_end = j + 1
                    break
            # Insert blank line + nav
            lines.insert(heading_end, '')
            lines.insert(heading_end + 1, nav_line)
            cells[0]['source'] = make_source_list('\n'.join(lines))
            modified = True

    # Check last few cells for footer nav
    footer_nav_found = False
    for i in range(max(0, len(cells) - 3), len(cells)):
        text = source_text(cells[i])
        if is_nav_cell(cells[i], text):
            # Replace footer nav
            lines = text.split('\n')
            new_lines = []
            nav_replaced = False
            for line in lines:
                if re.search(r'\[<<\s', line) or re.search(r'\s>>\]', line):
                    if not nav_replaced:
                        new_lines.append(nav_line)
                        nav_replaced = True
                else:
                    new_lines.append(line)
            cells[i]['source'] = make_source_list('\n'.join(new_lines))
            footer_nav_found = True
            modified = True
            break

    # If no footer nav, add one at the end
    if not footer_nav_found:
        footer_cell = {
            "cell_type": "markdown",
            "metadata": {},
            "source": make_source_list(f"---\n\n{nav_line}")
        }
        cells.append(footer_cell)
        modified = True

    # Fix any STRING format cells while we're at it
    for cell in cells:
        src = cell.get('source', '')
        if isinstance(src, str):
            cell['source'] = make_source_list(src)
            modified = True

    if modified:
        with open(nb_path, 'w', encoding='utf-8', newline='\n') as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write('\n')

    return modified


# Process all notebooks
total_modified = 0
for idx, (nb_dir, nb_name) in enumerate(NOTEBOOKS):
    nb_path = os.path.join(SC_BASE, nb_dir, f"{nb_name}.ipynb")
    nav_line = make_nav_line(idx)

    if not os.path.exists(nb_path):
        print(f"  SKIP (not found): {nb_name}")
        continue

    modified = update_notebook_nav(nb_path, nav_line, nb_name)
    if modified:
        print(f"  {nb_name}: nav updated")
        total_modified += 1
    else:
        print(f"  {nb_name}: no changes")

print(f"\nDone. {total_modified}/{len(NOTEBOOKS)} notebooks updated.")
