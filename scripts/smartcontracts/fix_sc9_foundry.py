"""Fix SC-9: purge exposed solutions + replace fake outputs."""
import json

path = "d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-9-Foundry-Basics.ipynb"
with open(path, 'r', encoding='utf-8') as f:
    nb = json.load(f)

def make_list(text):
    lines = text.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return result

cells_by_id = {c['id']: (i, c) for i, c in enumerate(nb['cells'])}

# 1. Fix cell-3: fake version -> real check
_, cell3 = cells_by_id['cell-3']
cell3['source'] = make_list(
    '# Verification reelle de Foundry\n'
    'import subprocess\n'
    '\n'
    'def check_tool(name):\n'
    '    try:\n'
    '        result = subprocess.run([name, "--version"], capture_output=True, text=True, timeout=10)\n'
    '        if result.returncode == 0:\n'
    '            return True, result.stdout.strip()\n'
    '        return False, result.stderr.strip()\n'
    '    except FileNotFoundError:\n'
    '        return False, "Non installe"\n'
    '    except Exception as e:\n'
    '        return False, str(e)\n'
    '\n'
    'print("Verification des outils Foundry:")\n'
    'print("-" * 50)\n'
    'all_ok = True\n'
    'for tool in ["forge", "cast", "anvil"]:\n'
    '    ok, info = check_tool(tool)\n'
    '    status = "OK" if ok else "MANQUANT"\n'
    '    print(f"  {tool}: {status}")\n'
    '    if ok:\n'
    '        print(f"    {info}")\n'
    '    all_ok = all_ok and ok\n'
    'print("-" * 50)\n'
    'if all_ok:\n'
    '    print("Tous les outils sont installes !")\n'
    'else:\n'
    '    print("Installez Foundry: curl -L https://foundry.paradigm.xyz | bash && foundryup")'
)
cell3['outputs'] = []
print("  Fixed cell-3: real Foundry version check")

# 2. Fix cell-12: fake test output -> explanation
_, cell12 = cells_by_id['cell-12']
cell12['source'] = make_list(
    '# Pour executer forge test, il faut un projet Foundry initialise.\n'
    '# Voici la sortie attendue lorsque les tests passent.\n'
    'try:\n'
    '    result = subprocess.run(["forge", "--version"], capture_output=True, text=True, timeout=10)\n'
    '    if result.returncode == 0:\n'
    '        print(f"forge disponible: {result.stdout.strip()}")\n'
    '        print()\n'
    '        print("Pour executer les tests :")\n'
    '        print("  mkdir test-project && cd test-project")\n'
    '        print("  forge init")\n'
    '        print("  # Copiez les contrats ci-dessus dans src/ et test/")\n'
    '        print("  forge test -vvv")\n'
    '    else:\n'
    '        print("forge non disponible")\n'
    'except FileNotFoundError:\n'
    '    print("forge non installe - sortie attendue :")\n'
    '    print()\n'
    '    print("  [PASS] test_Decrement() (gas: ~28000)")\n'
    '    print("  [PASS] test_InitialState() (gas: ~5000)")\n'
    '    print("  [PASS] test_Increment() (gas: ~23000)")\n'
    '    print("  [PASS] test_SetNumber() (gas: ~24000)")\n'
    '    print("  Test result: ok. 4 passed; 0 failed")'
)
cell12['outputs'] = []
print("  Fixed cell-12: real forge check or expected output")

# 3. PURGE cell-29: Vault solution -> skeleton
_, cell29 = cells_by_id['cell-29']
cell29['source'] = make_list(
    '# Exercice : Ecrivez les tests pour SimpleVault\n'
    '# Utilisez les cheatcodes de ce notebook\n'
    '\n'
    'VAULT_TEST_SKELETON = """\n'
    '// SPDX-License-Identifier: MIT\n'
    'pragma solidity ^0.8.30;\n'
    '\n'
    'import "forge-std/Test.sol";\n'
    'import "../src/SimpleVault.sol";\n'
    '\n'
    'contract SimpleVaultTest is Test {\n'
    '    SimpleVault public vault;\n'
    '    address public alice = address(0x1);\n'
    '    address public bob = address(0x2);\n'
    '\n'
    '    function setUp() public {\n'
    '        vault = new SimpleVault();\n'
    '        // TODO: Donner des ETH a Alice et Bob avec vm.deal\n'
    '    }\n'
    '\n'
    '    function test_Deposit() public {\n'
    '        // TODO: Tester le depot (vm.prank, deposit, assertEq)\n'
    '    }\n'
    '\n'
    '    function test_DepositFailsWithZero() public {\n'
    '        // TODO: Tester que deposer 0 revert (vm.expectRevert)\n'
    '    }\n'
    '\n'
    '    function test_Withdraw() public {\n'
    '        // TODO: Deposer puis retirer, verifier les soldes\n'
    '    }\n'
    '\n'
    '    function test_WithdrawFailsWithInsufficientBalance() public {\n'
    '        // TODO: Tester que retirer plus que le solde revert\n'
    '    }\n'
    '}\n'
    '"""\n'
    '\n'
    'print("Squelette du test SimpleVault.t.sol :")\n'
    'print(VAULT_TEST_SKELETON)\n'
    'print("Indices :")\n'
    'print("  - vm.deal(alice, 10 ether) pour donner des ETH")\n'
    'print("  - vm.prank(alice) pour simuler un appel depuis Alice")\n'
    'print("  - vault.deposit{value: 1 ether}() pour deposer")\n'
    'print("  - vm.expectRevert(bytes(\\"message\\")) avant un revert attendu")'
)
cell29['outputs'] = []
print("  PURGED cell-29: Vault test solution -> exercise skeleton")

# 4. PURGE cell-32: Timelock solution -> skeleton
_, cell32 = cells_by_id['cell-32']
cell32['source'] = make_list(
    '# Exercice : Ecrivez les tests pour Timelock\n'
    '# Vous devrez utiliser vm.warp() ou skip() pour le temps\n'
    '\n'
    'TIMELOCK_TEST_SKELETON = """\n'
    '// SPDX-License-Identifier: MIT\n'
    'pragma solidity ^0.8.30;\n'
    '\n'
    'import "forge-std/Test.sol";\n'
    'import "../src/Timelock.sol";\n'
    '\n'
    'contract TimelockTest is Test {\n'
    '    Timelock public timelock;\n'
    '    address public alice = address(0x1);\n'
    '\n'
    '    function setUp() public {\n'
    '        timelock = new Timelock();\n'
    '        // TODO: Donner des ETH a Alice\n'
    '    }\n'
    '\n'
    '    function test_Lock() public {\n'
    '        // TODO: Verrouiller des ETH, verifier lockTime et lockedAmount\n'
    '    }\n'
    '\n'
    '    function test_CannotUnlockBeforeTime() public {\n'
    '        // TODO: Verrouiller puis tenter de debloquer immediatement\n'
    '        // Doit revert avec "Still locked"\n'
    '    }\n'
    '\n'
    '    function test_CanUnlockAfterTime() public {\n'
    '        // TODO: Verrouiller, avancer le temps avec skip(1 days + 1),\n'
    '        // puis debloquer et verifier les soldes\n'
    '    }\n'
    '}\n'
    '"""\n'
    '\n'
    'print("Squelette du test Timelock.t.sol :")\n'
    'print(TIMELOCK_TEST_SKELETON)\n'
    'print("Indices :")\n'
    'print("  - skip(1 days + 1) pour avancer le temps")\n'
    'print("  - vm.warp(timestamp) pour aller a un moment precis")\n'
    'print("  - timelock.lockTime(alice) pour le temps de deblocage")'
)
cell32['outputs'] = []
print("  PURGED cell-32: Timelock test solution -> exercise skeleton")

# Fix all STRING format
fixed = 0
for cell in nb['cells']:
    src = cell.get('source', '')
    if isinstance(src, str):
        cell['source'] = make_list(src)
        fixed += 1

with open(path, 'w', encoding='utf-8', newline='\n') as f:
    json.dump(nb, f, ensure_ascii=False, indent=1)
    f.write('\n')

print(f"\nDone. Fixed {fixed} STRING cells. SC-9 cleaned up.")
