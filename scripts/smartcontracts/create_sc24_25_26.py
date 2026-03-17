"""Create SC-24, SC-25, SC-26 notebooks for 06-Real-World."""
import json, os

SC_BASE = "d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/06-Real-World"

def md(source):
    lines = source.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return {"cell_type": "markdown", "metadata": {}, "source": result}

def code(source):
    lines = source.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return {"cell_type": "code", "metadata": {}, "source": result, "outputs": [], "execution_count": None}

def make_nb(cells):
    return {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
            "language_info": {"name": "python", "version": "3.10.0"}
        },
        "cells": cells
    }

# ============================================================
# SC-24: Testnet Deploy
# ============================================================
sc24_cells = [
    md("# SC-24 : Deploiement sur Testnets\n\n"
       "[<< Cross-Chain](SC-23-Cross-Chain.ipynb) | [Mainnet Deploy >>](SC-25-Mainnet-Deploy.ipynb)\n\n"
       "**Duree estimee : 50 min**\n\n"
       "Dans ce notebook, nous deploierons de vrais contrats sur les testnets publics :\n"
       "- **Sepolia** (Ethereum testnet) via Alchemy/Infura\n"
       "- **XRP Testnet** via xrpl-py\n\n"
       "Les testnets sont des reseaux publics gratuits qui simulent le comportement du mainnet."),

    md("---\n\n## 0. Prerequis\n\n"
       "- Cle API **Alchemy** ou **Infura** (gratuit)\n"
       "- **MetaMask** ou wallet Ethereum pour recevoir du testnet ETH\n"
       "- Faucet Sepolia : [Google Cloud Faucet](https://cloud.google.com/application/web3/faucet/ethereum/sepolia) ou [Alchemy Faucet](https://sepoliafaucet.com/)\n"
       "- Python : `pip install web3 py-solc-x xrpl-py python-dotenv`"),

    code('# Configuration\n'
         'import os\n'
         'from dotenv import load_dotenv\n'
         '\n'
         'load_dotenv()  # Charge .env si present\n'
         '\n'
         '# Sepolia via Alchemy (remplacez par votre cle)\n'
         'SEPOLIA_RPC = os.getenv("SEPOLIA_RPC", "https://eth-sepolia.g.alchemy.com/v2/YOUR_KEY")\n'
         'PRIVATE_KEY = os.getenv("DEPLOYER_PRIVATE_KEY", "")  # Cle privee du deployer\n'
         '\n'
         '# Verification\n'
         'if "YOUR_KEY" in SEPOLIA_RPC:\n'
         '    print("ATTENTION: Configurez SEPOLIA_RPC dans votre .env")\n'
         '    print("  1. Creez un compte sur https://www.alchemy.com/")\n'
         '    print("  2. Creez une app Sepolia")\n'
         '    print("  3. Copiez l\'URL RPC dans .env")\n'
         'else:\n'
         '    print(f"RPC configure: {SEPOLIA_RPC[:40]}...")'),

    md("---\n\n## 1. Connexion a Sepolia\n\n"
       "Contrairement a anvil (blockchain locale), Sepolia est un reseau public.\n"
       "Les transactions prennent ~12 secondes (temps de bloc reel)."),

    code('from web3 import Web3\n'
         'import solcx\n'
         '\n'
         '# Connexion\n'
         'w3 = Web3(Web3.HTTPProvider(SEPOLIA_RPC))\n'
         '\n'
         'if w3.is_connected():\n'
         '    chain_id = w3.eth.chain_id\n'
         '    block = w3.eth.block_number\n'
         '    print(f"Connecte a Sepolia (chain_id={chain_id})")\n'
         '    print(f"Bloc actuel: {block:,}")\n'
         '    print(f"Gas price: {w3.from_wei(w3.eth.gas_price, \'gwei\'):.2f} gwei")\n'
         'else:\n'
         '    print("Impossible de se connecter. Verifiez votre cle API.")'),

    md("---\n\n## 2. Preparation du deployer\n\n"
       "Sur un testnet, vous avez besoin d'un compte avec du testnet ETH.\n"
       "Utilisez un faucet pour obtenir du Sepolia ETH gratuitement."),

    code('from eth_account import Account\n'
         '\n'
         'if PRIVATE_KEY:\n'
         '    account = Account.from_key(PRIVATE_KEY)\n'
         '    balance = w3.eth.get_balance(account.address)\n'
         '    print(f"Deployer: {account.address}")\n'
         '    print(f"Balance: {w3.from_wei(balance, \'ether\'):.4f} ETH")\n'
         '    if balance == 0:\n'
         '        print("\\nBalance nulle! Obtenez du Sepolia ETH via un faucet:")\n'
         '        print(f"  https://cloud.google.com/application/web3/faucet/ethereum/sepolia")\n'
         '        print(f"  Adresse a alimenter: {account.address}")\n'
         'else:\n'
         '    print("Pas de cle privee configuree.")\n'
         '    print("Pour generer un nouveau wallet de test:")\n'
         '    print("  account = Account.create()")\n'
         '    print("  print(account.address, account.key.hex())")'),

    md("---\n\n## 3. Deploiement d'un contrat sur Sepolia\n\n"
       "Nous deploierons un contrat SimpleStorage - le meme que dans SC-3, mais cette fois sur un vrai reseau public."),

    code('SIMPLE_STORAGE = """\n'
         '// SPDX-License-Identifier: MIT\n'
         'pragma solidity ^0.8.28;\n'
         '\n'
         'contract SimpleStorage {\n'
         '    uint256 public storedValue;\n'
         '    address public owner;\n'
         '    \n'
         '    event ValueChanged(uint256 oldValue, uint256 newValue, address changedBy);\n'
         '    \n'
         '    constructor(uint256 _initialValue) {\n'
         '        storedValue = _initialValue;\n'
         '        owner = msg.sender;\n'
         '    }\n'
         '    \n'
         '    function set(uint256 _value) external {\n'
         '        uint256 old = storedValue;\n'
         '        storedValue = _value;\n'
         '        emit ValueChanged(old, _value, msg.sender);\n'
         '    }\n'
         '    \n'
         '    function get() external view returns (uint256) {\n'
         '        return storedValue;\n'
         '    }\n'
         '}\n'
         '"""\n'
         '\n'
         '# Compiler\n'
         'SOLC_VERSION = "0.8.28"\n'
         'installed = [str(v) for v in solcx.get_installed_solc_versions()]\n'
         'if SOLC_VERSION not in installed:\n'
         '    solcx.install_solc(SOLC_VERSION)\n'
         'solcx.set_solc_version(SOLC_VERSION)\n'
         '\n'
         'compiled = solcx.compile_source(\n'
         '    SIMPLE_STORAGE, output_values=["abi", "bin"], solc_version=SOLC_VERSION\n'
         ')\n'
         'contract_id, contract_interface = compiled.popitem()\n'
         'print(f"Contrat compile: {contract_id}")\n'
         'print(f"Bytecode: {len(contract_interface[\'bin\'])} caracteres")\n'
         'print(f"ABI: {len(contract_interface[\'abi\'])} fonctions/events")'),

    code('# Deploiement sur Sepolia (necessite du testnet ETH)\n'
         'if PRIVATE_KEY and w3.is_connected():\n'
         '    Contract = w3.eth.contract(\n'
         '        abi=contract_interface["abi"],\n'
         '        bytecode=contract_interface["bin"]\n'
         '    )\n'
         '    \n'
         '    # Construire la transaction\n'
         '    nonce = w3.eth.get_transaction_count(account.address)\n'
         '    tx = Contract.constructor(42).build_transaction({\n'
         '        "from": account.address,\n'
         '        "nonce": nonce,\n'
         '        "gas": 500000,\n'
         '        "gasPrice": w3.eth.gas_price,\n'
         '        "chainId": 11155111,  # Sepolia\n'
         '    })\n'
         '    \n'
         '    # Signer et envoyer\n'
         '    signed_tx = w3.eth.account.sign_transaction(tx, PRIVATE_KEY)\n'
         '    tx_hash = w3.eth.send_raw_transaction(signed_tx.raw_transaction)\n'
         '    print(f"Transaction envoyee: {tx_hash.hex()}")\n'
         '    print(f"Explorer: https://sepolia.etherscan.io/tx/{tx_hash.hex()}")\n'
         '    \n'
         '    # Attendre confirmation (~12s)\n'
         '    print("Attente de confirmation...")\n'
         '    receipt = w3.eth.wait_for_transaction_receipt(tx_hash, timeout=120)\n'
         '    print(f"Deploye a: {receipt.contractAddress}")\n'
         '    print(f"Gas utilise: {receipt.gasUsed:,}")\n'
         '    print(f"Explorer: https://sepolia.etherscan.io/address/{receipt.contractAddress}")\n'
         'else:\n'
         '    print("Deploiement non disponible (cle manquante ou pas de connexion)")'),

    md("---\n\n## 4. Interaction avec le contrat deploye\n\n"
       "Une fois deploye, le contrat est permanent et accessible par tous."),

    code('# Interagir avec le contrat sur Sepolia\n'
         'if PRIVATE_KEY and w3.is_connected() and \'receipt\' in dir():\n'
         '    contract = w3.eth.contract(\n'
         '        address=receipt.contractAddress,\n'
         '        abi=contract_interface["abi"]\n'
         '    )\n'
         '    \n'
         '    # Lecture (gratuite, pas de gas)\n'
         '    value = contract.functions.get().call()\n'
         '    owner = contract.functions.owner().call()\n'
         '    print(f"Valeur actuelle: {value}")\n'
         '    print(f"Owner: {owner}")\n'
         '    \n'
         '    # Ecriture (coute du gas)\n'
         '    tx = contract.functions.set(100).build_transaction({\n'
         '        "from": account.address,\n'
         '        "nonce": w3.eth.get_transaction_count(account.address),\n'
         '        "gas": 100000,\n'
         '        "gasPrice": w3.eth.gas_price,\n'
         '        "chainId": 11155111,\n'
         '    })\n'
         '    signed = w3.eth.account.sign_transaction(tx, PRIVATE_KEY)\n'
         '    tx_hash = w3.eth.send_raw_transaction(signed.raw_transaction)\n'
         '    receipt2 = w3.eth.wait_for_transaction_receipt(tx_hash)\n'
         '    \n'
         '    new_value = contract.functions.get().call()\n'
         '    print(f"Nouvelle valeur: {new_value}")\n'
         '    print(f"Transaction: https://sepolia.etherscan.io/tx/{tx_hash.hex()}")\n'
         'else:\n'
         '    print("Interaction non disponible")'),

    md("---\n\n## 5. Deploiement XRP Testnet\n\n"
       "Le XRP Ledger a son propre testnet avec un faucet integre."),

    code('import xrpl\n'
         'from xrpl.clients import JsonRpcClient\n'
         'from xrpl.wallet import generate_faucet_wallet\n'
         'from xrpl.models.transactions import Payment\n'
         'from xrpl.transaction import submit_and_wait\n'
         'from xrpl.utils import xrp_to_drops\n'
         '\n'
         '# Connexion au testnet XRP\n'
         'client = JsonRpcClient("https://s.altnet.rippletest.net:51234")\n'
         '\n'
         'try:\n'
         '    # Generer un wallet finance par le faucet (gratuit, ~10s)\n'
         '    print("Generation d\'un wallet testnet (faucet)...")\n'
         '    wallet = generate_faucet_wallet(client, debug=True)\n'
         '    print(f"Adresse: {wallet.address}")\n'
         '    print(f"Balance: ~1000 XRP (testnet)")\n'
         '    \n'
         '    # Creer un deuxieme wallet pour tester un paiement\n'
         '    print("\\nGeneration d\'un second wallet...")\n'
         '    wallet2 = generate_faucet_wallet(client)\n'
         '    print(f"Destinataire: {wallet2.address}")\n'
         'except Exception as e:\n'
         '    print(f"Erreur: {e}")\n'
         '    print("Le faucet XRP testnet peut etre temporairement indisponible")'),

    code('# Envoyer un paiement XRP sur testnet\n'
         'try:\n'
         '    payment = Payment(\n'
         '        account=wallet.address,\n'
         '        amount=xrp_to_drops(25),  # 25 XRP\n'
         '        destination=wallet2.address,\n'
         '    )\n'
         '    \n'
         '    print("Envoi de 25 XRP...")\n'
         '    response = submit_and_wait(payment, client, wallet)\n'
         '    result = response.result\n'
         '    \n'
         '    print(f"Status: {result[\'meta\'][\'TransactionResult\']}")\n'
         '    print(f"Hash: {result[\'hash\']}")\n'
         '    print(f"Explorer: https://testnet.xrpl.org/transactions/{result[\'hash\']}")\n'
         '    \n'
         '    # Verifier les balances\n'
         '    balance1 = xrpl.account.get_balance(wallet.address, client)\n'
         '    balance2 = xrpl.account.get_balance(wallet2.address, client)\n'
         '    print(f"\\nBalance expediteur: {int(balance1)/1_000_000:.2f} XRP")\n'
         '    print(f"Balance destinataire: {int(balance2)/1_000_000:.2f} XRP")\n'
         'except Exception as e:\n'
         '    print(f"Erreur: {e}")'),

    md("---\n\n## 6. Comparaison Testnet vs Mainnet\n\n"
       "| Aspect | Anvil (local) | Sepolia (testnet) | Mainnet |\n"
       "|--------|--------------|-------------------|----------|\n"
       "| **Cout** | Gratuit | Gratuit (faucet) | Reel ($$$) |\n"
       "| **Vitesse** | Instantane | ~12s (bloc) | ~12s (bloc) |\n"
       "| **Persistance** | Reset a chaque redemarrage | Permanent | Permanent |\n"
       "| **Acces** | localhost | Public | Public |\n"
       "| **Usage** | Dev/debug | Test d'integration | Production |\n\n"
       "### Bonnes pratiques\n"
       "1. **Developper sur anvil** (SC-3 a SC-12)\n"
       "2. **Tester sur testnet** (ce notebook)\n"
       "3. **Deployer sur mainnet** seulement quand tout est verifie (SC-25)"),

    md("---\n\n## Exercice\n\n"
       "Deployez un contrat ERC-20 (SC-7) sur Sepolia et effectuez un transfer reel entre deux adresses.\n"
       "Verifiez le resultat sur Etherscan."),

    code('# Exercice : Deploy ERC-20 sur Sepolia\n'
         '# 1. Reprendre le contrat SimpleToken de SC-7\n'
         '# 2. Le compiler avec py-solc-x\n'
         '# 3. Le deployer sur Sepolia\n'
         '# 4. Effectuer un transfer()\n'
         '# 5. Verifier sur https://sepolia.etherscan.io/\n'
         '\n'
         'raise NotImplementedError("Completez cet exercice")'),

    md("---\n\n[<< Cross-Chain](SC-23-Cross-Chain.ipynb) | [Mainnet Deploy >>](SC-25-Mainnet-Deploy.ipynb)"),
]

# ============================================================
# SC-25: Mainnet Deploy
# ============================================================
sc25_cells = [
    md("# SC-25 : Deploiement Mainnet (L2)\n\n"
       "[<< Testnet Deploy](SC-24-Testnet-Deploy.ipynb) | [Final Project >>](SC-26-Final-Project.ipynb)\n\n"
       "**Duree estimee : 40 min**\n\n"
       "Deploiement sur un vrai reseau L2 (Base ou Polygon) avec du gas reel.\n\n"
       "> **Cout estime : ~0.01-0.50$ en ETH** sur Base/Polygon (beaucoup moins cher que Ethereum L1)"),

    md("---\n\n## 0. Pourquoi un L2 ?\n\n"
       "| Reseau | Gas moyen (deploy simple) | Temps de confirmation |\n"
       "|--------|--------------------------|----------------------|\n"
       "| Ethereum L1 | ~$5-50 | ~12s |\n"
       "| Base (L2) | ~$0.01-0.10 | ~2s |\n"
       "| Polygon PoS | ~$0.01-0.05 | ~2s |\n"
       "| Arbitrum (L2) | ~$0.05-0.50 | ~1s |\n\n"
       "Les L2 heritent de la securite d'Ethereum tout en etant beaucoup moins chers."),

    md("---\n\n## 1. Configuration Base (L2 de Coinbase)"),

    code('import os\n'
         'from dotenv import load_dotenv\n'
         'from web3 import Web3\n'
         'import solcx\n'
         '\n'
         'load_dotenv()\n'
         '\n'
         '# Base mainnet\n'
         'BASE_RPC = os.getenv("BASE_RPC", "https://mainnet.base.org")\n'
         'PRIVATE_KEY = os.getenv("DEPLOYER_PRIVATE_KEY", "")\n'
         '\n'
         'w3 = Web3(Web3.HTTPProvider(BASE_RPC))\n'
         '\n'
         'if w3.is_connected():\n'
         '    chain_id = w3.eth.chain_id  # 8453 pour Base\n'
         '    gas_price = w3.eth.gas_price\n'
         '    print(f"Connecte a Base (chain_id={chain_id})")\n'
         '    print(f"Gas price: {w3.from_wei(gas_price, \'gwei\'):.4f} gwei")\n'
         '    print(f"Bloc: {w3.eth.block_number:,}")\n'
         'else:\n'
         '    print("Connexion echouee. Base RPC public peut etre lent.")\n'
         '    print("Alternative: utilisez Alchemy/Infura avec une cle API Base")'),

    md("---\n\n## 2. Estimation du cout\n\n"
       "Avant de deployer, estimons le cout en ETH et en USD."),

    code('from eth_account import Account\n'
         '\n'
         'if PRIVATE_KEY and w3.is_connected():\n'
         '    account = Account.from_key(PRIVATE_KEY)\n'
         '    balance = w3.eth.get_balance(account.address)\n'
         '    balance_eth = w3.from_wei(balance, \'ether\')\n'
         '    \n'
         '    # Estimation du cout de deploiement\n'
         '    estimated_gas = 300000  # Gas typique pour un contrat simple\n'
         '    gas_price = w3.eth.gas_price\n'
         '    estimated_cost = estimated_gas * gas_price\n'
         '    cost_eth = w3.from_wei(estimated_cost, \'ether\')\n'
         '    \n'
         '    print(f"Deployer: {account.address}")\n'
         '    print(f"Balance: {balance_eth:.6f} ETH")\n'
         '    print(f"\\nEstimation deploiement:")\n'
         '    print(f"  Gas estime: {estimated_gas:,}")\n'
         '    print(f"  Gas price: {w3.from_wei(gas_price, \'gwei\'):.4f} gwei")\n'
         '    print(f"  Cout estime: {cost_eth:.6f} ETH")\n'
         '    print(f"  (~${float(cost_eth) * 2500:.2f} a $2500/ETH)")\n'
         '    \n'
         '    if balance < estimated_cost:\n'
         '        print(f"\\nBalance insuffisante. Envoyez du ETH sur Base a:")\n'
         '        print(f"  {account.address}")\n'
         'else:\n'
         '    print("Configurez DEPLOYER_PRIVATE_KEY dans .env")'),

    md("---\n\n## 3. Deploiement sur Base\n\n"
       "Le processus est identique a Sepolia, seul le chain_id change."),

    code('STORAGE_CONTRACT = """\n'
         '// SPDX-License-Identifier: MIT\n'
         'pragma solidity ^0.8.28;\n'
         '\n'
         '/// @title SimpleStorage - Premier contrat deploye sur mainnet\n'
         '/// @notice Stocke une valeur avec historique des modifications\n'
         'contract SimpleStorage {\n'
         '    uint256 public value;\n'
         '    address public owner;\n'
         '    uint256 public updateCount;\n'
         '    \n'
         '    event Updated(uint256 indexed newValue, address indexed by, uint256 count);\n'
         '    \n'
         '    constructor(uint256 _initial) {\n'
         '        value = _initial;\n'
         '        owner = msg.sender;\n'
         '    }\n'
         '    \n'
         '    function set(uint256 _v) external {\n'
         '        value = _v;\n'
         '        updateCount++;\n'
         '        emit Updated(_v, msg.sender, updateCount);\n'
         '    }\n'
         '}\n'
         '"""\n'
         '\n'
         '# Compiler\n'
         'SOLC_VERSION = "0.8.28"\n'
         'installed = [str(v) for v in solcx.get_installed_solc_versions()]\n'
         'if SOLC_VERSION not in installed:\n'
         '    solcx.install_solc(SOLC_VERSION)\n'
         'solcx.set_solc_version(SOLC_VERSION)\n'
         '\n'
         'compiled = solcx.compile_source(\n'
         '    STORAGE_CONTRACT, output_values=["abi", "bin"], solc_version=SOLC_VERSION\n'
         ')\n'
         'cid, ci = compiled.popitem()\n'
         'print(f"Compile: {cid}, bytecode={len(ci[\'bin\'])} chars")'),

    code('# Deploy sur Base mainnet\n'
         'if PRIVATE_KEY and w3.is_connected():\n'
         '    Contract = w3.eth.contract(abi=ci["abi"], bytecode=ci["bin"])\n'
         '    \n'
         '    nonce = w3.eth.get_transaction_count(account.address)\n'
         '    tx = Contract.constructor(42).build_transaction({\n'
         '        "from": account.address,\n'
         '        "nonce": nonce,\n'
         '        "gas": 500000,\n'
         '        "gasPrice": w3.eth.gas_price,\n'
         '        "chainId": w3.eth.chain_id,\n'
         '    })\n'
         '    \n'
         '    # POINT DE NON-RETOUR: cette transaction coute du vrai ETH\n'
         '    print("Deploiement en cours (gas reel)...")\n'
         '    signed = w3.eth.account.sign_transaction(tx, PRIVATE_KEY)\n'
         '    tx_hash = w3.eth.send_raw_transaction(signed.raw_transaction)\n'
         '    print(f"TX: {tx_hash.hex()}")\n'
         '    \n'
         '    receipt = w3.eth.wait_for_transaction_receipt(tx_hash, timeout=60)\n'
         '    actual_cost = receipt.gasUsed * receipt.effectiveGasPrice\n'
         '    \n'
         '    print(f"\\nDeploye a: {receipt.contractAddress}")\n'
         '    print(f"Gas utilise: {receipt.gasUsed:,}")\n'
         '    print(f"Cout reel: {w3.from_wei(actual_cost, \'ether\'):.6f} ETH")\n'
         '    print(f"Explorer: https://basescan.org/address/{receipt.contractAddress}")\n'
         'else:\n'
         '    print("Deploiement non disponible (cle/connexion manquante)")'),

    md("---\n\n## 4. Verification sur l'explorateur\n\n"
       "Apres deploiement, votre contrat est:\n"
       "- **Permanent** : il existera tant que Base existera\n"
       "- **Public** : n'importe qui peut lire le code et interagir\n"
       "- **Immuable** : le code ne peut plus etre modifie\n\n"
       "Vous pouvez verifier le contrat sur [BaseScan](https://basescan.org/) pour que d'autres puissent lire le code source."),

    md("---\n\n## 5. Securite mainnet\n\n"
       "### Checklist avant deploiement mainnet\n\n"
       "1. **Audit du code** : Tous les tests passent (SC-12 a SC-14)\n"
       "2. **Testnet d'abord** : Deploye et teste sur Sepolia (SC-24)\n"
       "3. **Gestion des cles** : Jamais de cle privee en clair dans le code\n"
       "4. **Gas estimation** : Verifier le cout avant de signer\n"
       "5. **Proxy pattern** : Si le contrat doit etre evolutif, utiliser un proxy\n"
       "6. **Multi-sig** : Pour les fonds importants, utiliser un wallet multi-signature\n\n"
       "### Erreurs communes\n"
       "- Deployer avec une cle de test sur mainnet\n"
       "- Oublier de verifier le code sur l'explorateur\n"
       "- Ne pas tester sur testnet avant mainnet"),

    md("---\n\n## Exercice\n\n"
       "Deployez un token ERC-20 minimal sur Base (ou Polygon).\n"
       "Estimez le cout avant deploiement, puis comparez avec le cout reel."),

    code('# Exercice : Deploy ERC-20 sur L2 mainnet\n'
         '# 1. Reprendre le contrat de SC-7\n'
         '# 2. Estimer le gas\n'
         '# 3. Deployer\n'
         '# 4. Verifier sur BaseScan/PolygonScan\n'
         '# 5. Comparer cout estime vs reel\n'
         '\n'
         'raise NotImplementedError("Completez cet exercice")'),

    md("---\n\n[<< Testnet Deploy](SC-24-Testnet-Deploy.ipynb) | [Final Project >>](SC-26-Final-Project.ipynb)"),
]

# ============================================================
# SC-26: Final Project
# ============================================================
sc26_cells = [
    md("# SC-26 : Projet Final - DApp Complete\n\n"
       "[<< Mainnet Deploy](SC-25-Mainnet-Deploy.ipynb)\n\n"
       "**Duree estimee : 90 min**\n\n"
       "Ce projet capstone integre toutes les competences acquises dans la serie :\n"
       "- Cryptographie fondamentale (SC-0)\n"
       "- Solidity et deploiement (SC-3 a SC-14)\n"
       "- Cryptographie avancee (SC-15 a SC-17)\n"
       "- Multi-chain (SC-18 a SC-23)\n"
       "- Deploiement reel (SC-24 a SC-25)"),

    md("---\n\n## Sujet : Systeme de Vote Decentralise\n\n"
       "Construire un systeme de vote complet avec :\n"
       "1. **Smart contract** Solidity pour la gouvernance (SC-9)\n"
       "2. **Chiffrement** des votes avec Paillier (SC-16, SC-17)\n"
       "3. **Preuve ZKP** de validite du bulletin (SC-15)\n"
       "4. **Deploiement** sur testnet (SC-24)\n"
       "5. **Tests** avec Foundry (SC-12)\n\n"
       "### Architecture\n\n"
       "```\n"
       "[Electeur] --> [Chiffre vote (Paillier)] --> [Prouve validite (ZKP)]\n"
       "     |                                            |\n"
       "     v                                            v\n"
       "[Smart Contract: enregistre bulletin chiffre + preuve]\n"
       "     |                                            |\n"
       "     v                                            v\n"
       "[Decompte homomorphique] --> [Dechiffrement resultat]\n"
       "     |                                            |\n"
       "     v                                            v\n"
       "[Verification publique: tout le monde peut verifier]\n"
       "```"),

    md("---\n\n## Partie 1 : Smart Contract de Vote (Solidity)\n\n"
       "Ecrivez un contrat `VotingSystem` qui :\n"
       "- Enregistre les electeurs autorises\n"
       "- Accepte des bulletins chiffres\n"
       "- Stocke les preuves de validite\n"
       "- Permet le decompte final"),

    code('# Partie 1: Contrat Solidity\n'
         '# Utilisez compile_and_deploy() de SC-2\n'
         '\n'
         'from web3 import Web3\n'
         'import solcx\n'
         '\n'
         'VOTING_CONTRACT = """\n'
         '// SPDX-License-Identifier: MIT\n'
         'pragma solidity ^0.8.28;\n'
         '\n'
         'contract VotingSystem {\n'
         '    // TODO: Definir la structure du systeme de vote\n'
         '    // - Liste des electeurs autorises\n'
         '    // - Mapping des bulletins chiffres (bytes)\n'
         '    // - Phase de vote (enum: Registration, Voting, Tallying, Ended)\n'
         '    // - Fonction registerVoter(address)\n'
         '    // - Fonction submitBallot(bytes calldata encryptedBallot, bytes calldata proof)\n'
         '    // - Fonction tally() qui declenche le decompte\n'
         '    // - Events pour chaque action\n'
         '    \n'
         '    // Indices:\n'
         '    // - enum Phase { Registration, Voting, Tallying, Ended }\n'
         '    // - mapping(address => bool) public registeredVoters;\n'
         '    // - mapping(address => bytes) public encryptedBallots;\n'
         '    // - modifier onlyPhase(Phase _phase)\n'
         '}\n'
         '"""\n'
         '\n'
         'print("Completez le contrat VotingSystem ci-dessus")\n'
         'print("Inspirez-vous de SC-9 (DAO Governance) et SC-17 (E2E Voting)")'),

    md("---\n\n## Partie 2 : Chiffrement des votes (Python)\n\n"
       "Utilisez Paillier (SC-16) pour chiffrer les votes cote client."),

    code('# Partie 2: Chiffrement Paillier\n'
         'from phe import paillier\n'
         '\n'
         '# TODO: Implementer le chiffrement des votes\n'
         '# 1. Generer les cles Paillier\n'
         '# 2. Definir les candidats\n'
         '# 3. Chiffrer un vote (1 pour le candidat choisi, 0 pour les autres)\n'
         '# 4. Verifier que l\'addition homomorphique fonctionne\n'
         '\n'
         '# Indice: voir SC-16 et SC-17 pour le pattern\n'
         '# public_key, private_key = paillier.generate_paillier_keypair()\n'
         '# encrypted_vote = [public_key.encrypt(1), public_key.encrypt(0), public_key.encrypt(0)]\n'
         '\n'
         'raise NotImplementedError("Implementez le chiffrement des votes")'),

    md("---\n\n## Partie 3 : Preuve de validite (ZKP)\n\n"
       "Chaque electeur doit prouver que son bulletin est valide sans reveler son vote."),

    code('# Partie 3: Preuve ZKP simplifiee\n'
         'import hashlib\n'
         'import secrets\n'
         '\n'
         '# TODO: Implementer une preuve que le bulletin chiffre contient\n'
         '# exactement un 1 et le reste des 0\n'
         '# \n'
         '# Approche simplifiee (commitment scheme):\n'
         '# 1. L\'electeur genere un nonce r\n'
         '# 2. Commitment = hash(vote || r)\n'
         '# 3. La preuve montre que sum(votes) == 1 sans reveler les votes individuels\n'
         '#\n'
         '# Voir SC-15 pour les protocoles Sigma et SC-17 pour l\'application au vote\n'
         '\n'
         'raise NotImplementedError("Implementez la preuve de validite")'),

    md("---\n\n## Partie 4 : Integration et deploiement\n\n"
       "Assemblez les 3 parties et deployez sur anvil (local) puis sur Sepolia (testnet)."),

    code('# Partie 4: Integration complete\n'
         '\n'
         '# TODO:\n'
         '# 1. Deployer VotingSystem sur anvil\n'
         '# 2. Enregistrer 3 electeurs\n'
         '# 3. Chaque electeur chiffre et soumet son vote\n'
         '# 4. Effectuer le decompte homomorphique\n'
         '# 5. Verifier les resultats\n'
         '# 6. (Bonus) Deployer sur Sepolia\n'
         '\n'
         '# Workflow:\n'
         '# ANVIL_URL = "http://127.0.0.1:8545"\n'
         '# w3 = Web3(Web3.HTTPProvider(ANVIL_URL))\n'
         '# contract, receipt = compile_and_deploy(w3, VOTING_CONTRACT, deployer)\n'
         '# ... enregistrer, voter, decompter\n'
         '\n'
         'raise NotImplementedError("Assemblez et deployez le systeme complet")'),

    md("---\n\n## Partie 5 : Tests Foundry (Bonus)\n\n"
       "Ecrivez des tests Foundry pour le contrat VotingSystem."),

    code('# Partie 5: Tests Foundry\n'
         '\n'
         'VOTING_TEST = """\n'
         '// SPDX-License-Identifier: MIT\n'
         'pragma solidity ^0.8.28;\n'
         '\n'
         'import "forge-std/Test.sol";\n'
         '// import "../src/VotingSystem.sol";\n'
         '\n'
         '// TODO: Ecrivez les tests pour VotingSystem\n'
         '// - test_RegisterVoter()\n'
         '// - test_SubmitBallot()\n'
         '// - test_OnlyRegisteredCanVote()\n'
         '// - test_CannotVoteTwice()\n'
         '// - test_Tally()\n'
         '// - test_PhaseTransitions()\n'
         '\n'
         '// Utilisez les cheatcodes de SC-12:\n'
         '// - vm.prank(voter) pour simuler un electeur\n'
         '// - vm.expectRevert() pour les cas d\'erreur\n'
         '// - vm.warp() si vous avez des deadlines\n'
         '"""\n'
         '\n'
         'print("Squelette de test Foundry pour VotingSystem")\n'
         'print(VOTING_TEST)\n'
         'print("\\nPour executer: forge test -vvv")'),

    md("---\n\n## Criteres d'evaluation\n\n"
       "| Critere | Points | Description |\n"
       "|---------|--------|-------------|\n"
       "| Smart Contract | 30% | Contrat compile, deploye, fonctionnel |\n"
       "| Chiffrement | 25% | Votes chiffres, decompte homomorphique correct |\n"
       "| ZKP | 20% | Preuve de validite du bulletin |\n"
       "| Deploiement | 15% | Fonctionne sur anvil + testnet |\n"
       "| Tests | 10% | Au moins 3 tests Foundry qui passent |\n\n"
       "### Bonus\n"
       "- Vote sur mainnet L2 (+5%)\n"
       "- Interface web basique (+5%)\n"
       "- Multi-candidats (>2) (+5%)\n"
       "- Verification publique complete (+5%)"),

    md("---\n\n## Ressources\n\n"
       "- [SC-0 : Fondamentaux crypto](../00-Foundations/SC-0-Cypherpunk-Origins.ipynb)\n"
       "- [SC-9 : DAO Governance](../02-Solidity-Advanced/SC-9-DAO-Governance.ipynb)\n"
       "- [SC-12 : Foundry Testing](../03-Foundry-Testing/SC-12-Foundry-Testing.ipynb)\n"
       "- [SC-15 : Zero-Knowledge Proofs](../04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs.ipynb)\n"
       "- [SC-16 : Homomorphic Encryption](../04-Privacy-Cryptography/SC-16-Homomorphic-Encryption.ipynb)\n"
       "- [SC-17 : E2E Verifiable Voting](../04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb)\n"
       "- [OpenZeppelin Contracts](https://docs.openzeppelin.com/contracts/)\n"
       "- [Foundry Book](https://book.getfoundry.sh/)\n\n"
       "---\n\n"
       "[<< Mainnet Deploy](SC-25-Mainnet-Deploy.ipynb)"),
]

# Write all three notebooks
for name, cells in [
    ("SC-24-Testnet-Deploy.ipynb", sc24_cells),
    ("SC-25-Mainnet-Deploy.ipynb", sc25_cells),
    ("SC-26-Final-Project.ipynb", sc26_cells),
]:
    nb = make_nb(cells)
    path = os.path.join(SC_BASE, name)
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        f.write('\n')
    print(f"Created {name}: {len(cells)} cells")

print("\nDone. 3 Real-World notebooks created.")
