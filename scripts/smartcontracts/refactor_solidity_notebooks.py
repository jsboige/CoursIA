"""Refactor Solidity notebooks: add web3.py setup cell and update navigation.

This script adds a web3.py/anvil connection cell at the top of each Solidity notebook,
and updates navigation to reflect the new numbering scheme.

Phase 1: Add connection cells + update nav (this script)
Phase 2: Replace individual print() cells with compile/deploy (manual, per-notebook)
"""
import json
import os

SC_BASE = "d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts"

# Web3.py setup cell to insert after header
SETUP_SOURCE = [
    "# Connection a anvil (blockchain locale Foundry)\n",
    "# Prerequis: anvil en cours d'execution dans un terminal\n",
    "from web3 import Web3\n",
    "import solcx\n",
    "\n",
    "SOLC_VERSION = \"0.8.28\"\n",
    "ANVIL_URL = \"http://127.0.0.1:8545\"\n",
    "\n",
    "# Connexion\n",
    "w3 = Web3(Web3.HTTPProvider(ANVIL_URL))\n",
    "assert w3.is_connected(), f\"Impossible de se connecter a {ANVIL_URL}. Lancez 'anvil' dans un terminal.\"\n",
    "\n",
    "# Installer solc si necessaire\n",
    "installed = [str(v) for v in solcx.get_installed_solc_versions()]\n",
    "if SOLC_VERSION not in installed:\n",
    "    solcx.install_solc(SOLC_VERSION)\n",
    "solcx.set_solc_version(SOLC_VERSION)\n",
    "\n",
    "deployer = w3.eth.accounts[0]\n",
    "print(f\"Connecte a anvil (chain {w3.eth.chain_id}), deployer: {deployer[:10]}...\")\n",
    "\n",
    "\n",
    "def compile_and_deploy(w3, source_code, deployer, *constructor_args):\n",
    "    \"\"\"Compiler et deployer un contrat Solidity.\"\"\"\n",
    "    compiled = solcx.compile_source(\n",
    "        source_code, output_values=[\"abi\", \"bin\"], solc_version=SOLC_VERSION\n",
    "    )\n",
    "    contract_id, contract_interface = compiled.popitem()\n",
    "    Contract = w3.eth.contract(\n",
    "        abi=contract_interface[\"abi\"], bytecode=contract_interface[\"bin\"]\n",
    "    )\n",
    "    tx_hash = Contract.constructor(*constructor_args).transact({\"from\": deployer})\n",
    "    receipt = w3.eth.wait_for_transaction_receipt(tx_hash)\n",
    "    instance = w3.eth.contract(\n",
    "        address=receipt.contractAddress, abi=contract_interface[\"abi\"]\n",
    "    )\n",
    "    print(f\"Deploye: {contract_id.split(':')[-1]} a {receipt.contractAddress}\")\n",
    "    return instance, receipt\n",
]

SETUP_CELL = {
    "cell_type": "code",
    "id": "web3-setup",
    "metadata": {},
    "source": SETUP_SOURCE,
    "outputs": [],
    "execution_count": None,
}

SETUP_INTRO = {
    "cell_type": "markdown",
    "id": "web3-setup-intro",
    "metadata": {},
    "source": [
        "---\n",
        "\n",
        "## 0. Connexion a la blockchain locale\n",
        "\n",
        "Tous les contrats de ce notebook sont **compiles et deployes reellement** sur anvil.\n",
        "Lancez `anvil` dans un terminal avant d'executer les cellules.\n",
    ],
}

# Navigation mapping: old -> new
NAV_UPDATES = {
    # SC-1 -> SC-3
    "SC-1-Solidity-Basics.ipynb": {
        "old_title": "SC-1-Solidity-Basics",
        "new_title": "SC-3-Solidity-Basics",
        "old_nav": "[<< Setup](../00-Environment/SC-0-Setup.ipynb)",
        "new_nav": "[<< Setup Web3py](../00-Foundations/SC-2-Setup-Web3py.ipynb)",
        "old_next": "[Functions >>](SC-2-Functions-State.ipynb)",
        "new_next": "[Functions >>](SC-4-Functions-State.ipynb)",
    },
}

def fix_source_format(source):
    """Ensure source is LIST format."""
    if isinstance(source, str):
        lines = source.split('\n')
        result = []
        for i, line in enumerate(lines):
            if i < len(lines) - 1:
                result.append(line + '\n')
            elif line:
                result.append(line)
        return result
    elif isinstance(source, list) and len(source) == 1 and '\n' in source[0]:
        text = source[0]
        lines = text.split('\n')
        result = []
        for i, line in enumerate(lines):
            if i < len(lines) - 1:
                result.append(line + '\n')
            elif line:
                result.append(line)
        return result
    return source

def add_setup_cells(nb):
    """Insert web3.py setup cells after the header cell."""
    # Find first markdown cell (header)
    insert_idx = 1  # after header
    nb['cells'].insert(insert_idx, SETUP_INTRO)
    nb['cells'].insert(insert_idx + 1, SETUP_CELL)
    return nb

def fix_all_sources(nb):
    """Fix all cells to LIST format."""
    fixed = 0
    for cell in nb['cells']:
        old = cell['source']
        cell['source'] = fix_source_format(cell['source'])
        if cell['source'] != old:
            fixed += 1
    return fixed

# Process each notebook
notebooks_to_process = [
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-1-Solidity-Basics.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-2-Functions-State.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-3-Inheritance.ipynb"),
    os.path.join(SC_BASE, "01-Solidity-Foundation", "SC-4-Errors-Events.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-5-Token-Standards.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-6-DeFi-Primitives.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-7-DAO-Governance.ipynb"),
    os.path.join(SC_BASE, "02-Solidity-Advanced", "SC-8-Account-Abstraction.ipynb"),
]

for nb_path in notebooks_to_process:
    basename = os.path.basename(nb_path)
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Check if setup cell already exists
    has_setup = any(
        cell.get('id') == 'web3-setup' for cell in nb['cells']
    )

    if not has_setup:
        add_setup_cells(nb)
        print(f"  + Setup cells added to {basename}")
    else:
        print(f"  = Setup cells already in {basename}")

    # Fix source format
    fixed = fix_all_sources(nb)
    if fixed:
        print(f"    Fixed {fixed} STRING format cells")

    with open(nb_path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        f.write('\n')

print(f"\nDone. {len(notebooks_to_process)} notebooks processed.")
print("Next step: manually convert print() cells to compile_and_deploy() in each notebook.")
