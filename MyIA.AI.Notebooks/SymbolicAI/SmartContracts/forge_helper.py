"""Helper to compile Solidity with external imports via Foundry (WSL on Windows).

Usage in notebooks:
    from forge_helper import forge_compile, forge_compile_and_deploy

    # Compile only
    abi, bytecode = forge_compile(source_code, "MyContract")

    # Compile and deploy on anvil
    instance, receipt = forge_compile_and_deploy(w3, source_code, "MyContract", deployer)
"""

import json
import os
import platform
import subprocess
import tempfile
from pathlib import Path


# Path to the Foundry project with OZ and AA dependencies
FOUNDRY_DIR = Path(__file__).parent / "foundry-lib"


def _run_forge(source_code: str, contract_name: str) -> dict:
    """Write source to foundry-lib/src, run forge build, return artifact JSON."""
    src_file = FOUNDRY_DIR / "src" / f"{contract_name}.sol"
    src_file.write_text(source_code, encoding="utf-8")

    try:
        foundry_path = str(FOUNDRY_DIR).replace("\\", "/")

        if platform.system() == "Windows":
            # Convert to WSL path
            drive = foundry_path[0].lower()
            wsl_path = f"/mnt/{drive}/{foundry_path[3:]}"
            cmd = [
                "wsl", "-d", "Ubuntu", "--", "bash", "-c",
                f'export PATH="$HOME/.foundry/bin:$PATH" && '
                f'cd "{wsl_path}" && forge build --force --silent 2>&1'
            ]
        else:
            cmd = ["bash", "-c", f'cd "{foundry_path}" && forge build --force --silent']

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

        # Read the artifact
        # Forge creates out/<filename>/<ContractName>.json
        artifact_path = FOUNDRY_DIR / "out" / f"{contract_name}.sol" / f"{contract_name}.json"
        if not artifact_path.exists():
            # Try to find the artifact by listing the output directory
            out_dir = FOUNDRY_DIR / "out" / f"{contract_name}.sol"
            if out_dir.exists():
                jsons = list(out_dir.glob("*.json"))
                if jsons:
                    artifact_path = jsons[0]
                else:
                    raise FileNotFoundError(
                        f"No artifacts in {out_dir}. Forge output: {result.stdout}{result.stderr}"
                    )
            else:
                raise FileNotFoundError(
                    f"Build failed. Forge output: {result.stdout}{result.stderr}"
                )

        with open(artifact_path, encoding="utf-8") as f:
            return json.load(f)

    finally:
        # Clean up the temp source file
        if src_file.exists():
            src_file.unlink()


def forge_compile(source_code: str, contract_name: str) -> tuple:
    """Compile Solidity source with Foundry (supports @openzeppelin, @account-abstraction).

    Args:
        source_code: Full Solidity source code
        contract_name: Name of the contract to extract (must match contract name in source)

    Returns:
        (abi, bytecode) tuple
    """
    artifact = _run_forge(source_code, contract_name)
    abi = artifact["abi"]
    bytecode = artifact["bytecode"]["object"]
    return abi, bytecode


def forge_compile_and_deploy(w3, source_code: str, contract_name: str,
                              deployer, *constructor_args) -> tuple:
    """Compile with Foundry and deploy on the connected chain.

    Args:
        w3: Web3 instance (connected to anvil or other)
        source_code: Full Solidity source code
        contract_name: Name of the contract to extract
        deployer: Address to deploy from
        *constructor_args: Arguments for the constructor

    Returns:
        (contract_instance, receipt) tuple
    """
    abi, bytecode = forge_compile(source_code, contract_name)
    Contract = w3.eth.contract(abi=abi, bytecode=bytecode)
    tx_hash = Contract.constructor(*constructor_args).transact({"from": deployer})
    receipt = w3.eth.wait_for_transaction_receipt(tx_hash)
    instance = w3.eth.contract(address=receipt.contractAddress, abi=abi)
    print(f"Deploye: {contract_name} a {receipt.contractAddress}")
    return instance, receipt
