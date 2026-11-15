"""test_sc11_local_path.py — temoin du chemin local (Ollama) de SC-11.

Ce que le carnet `SC-11-LLM-Assisted-Python.ipynb` montre en section 7 : un
contrat genere par un modele local, compile par `solc`, affiche tel quel. Le
carnet ne deploie ni n'appelle ce contrat — la compilation est le seul controle
deterministe applique sur ce chemin.

Ce temoin ferme la boucle : il compile **le texte exact de la sortie commitee**
(il n'est pas reecrit a la main), le deploie sur PyEVM, puis appelle `store`
et `retrieve`. Mesure attendue, et donc verifiee par ce fichier : `store(5)`
n'ecrit pas le nombre 5, il ecrase le message par les 32 octets de
`abi.encodePacked(uint256)` (31 octets nuls puis 0x05), et `retrieve()` ne rend
plus « Hello, World! ».

Ce n'est donc pas un carnet casse : c'est un carnet qui presente une
demonstration de compilation comme une demonstration de fonctionnement. La
lecture de la section 7 le dit desormais explicitement.

Le temoin n'exige **ni serveur Ollama ni cle d'API** : il ne depend que du
contrat deja commite et de la toolchain Solidity locale.

Lancer depuis le dossier de la serie :

    python -m pytest test_sc11_local_path.py -q

ou, pour le rapport lisible :

    python test_sc11_local_path.py
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

SERIES_ROOT = Path(__file__).resolve().parent
NOTEBOOK = SERIES_ROOT / "02-Solidity-Advanced" / "SC-11-LLM-Assisted-Python.ipynb"

# Balise affichee par la cellule de demonstration locale, juste avant le
# contrat : c'est l'ancre qui selectionne le bon code et la bonne sortie.
LOCAL_DEMO_BANNER = "Contrat généré par Ollama et compilé avec solc :"

SOLIDITY_MIN = (0, 8, 20)


# --------------------------------------------------------------------------
# Extraction du contrat depuis la sortie commitee
# --------------------------------------------------------------------------


def _cell_source(cell) -> str:
    source = cell.get("source", "")
    return "".join(source) if isinstance(source, list) else source


def _output_text(cell) -> str:
    chunks: list[str] = []
    for output in cell.get("outputs", []):
        text = output.get("text")
        if isinstance(text, list):
            chunks.extend(text)
        elif isinstance(text, str):
            chunks.append(text)
        data = output.get("data", {}).get("text/plain")
        if isinstance(data, list):
            chunks.extend(data)
        elif isinstance(data, str):
            chunks.append(data)
    return "".join(chunks)


def contract_from_committed_output() -> str:
    """Retourne le source Solidity affiche par la demonstration locale."""
    notebook = json.loads(NOTEBOOK.read_text(encoding="utf-8"))
    for cell in notebook["cells"]:
        if cell.get("cell_type") != "code":
            continue
        if LOCAL_DEMO_BANNER not in _cell_source(cell):
            continue
        text = _output_text(cell)
        if LOCAL_DEMO_BANNER not in text:
            continue
        body = text.split(LOCAL_DEMO_BANNER, 1)[1].strip()
        assert "contract HelloWorld" in body, (
            "la sortie locale ne contient pas le contrat attendu : "
            "le carnet a change, ce temoin doit etre relu"
        )
        return body
    raise AssertionError(
        "aucune sortie commitee ne porte la demonstration locale : "
        "le carnet a change, ce temoin doit etre relu"
    )


# --------------------------------------------------------------------------
# Toolchain
# --------------------------------------------------------------------------


def _as_tuple(version) -> tuple[int, ...]:
    parts = tuple(int(part) for part in str(version).split(".") if part.isdigit())
    return parts + (0,) * (3 - len(parts))


def _solc_version() -> str:
    solcx = pytest.importorskip("solcx")
    installed = [
        version
        for version in solcx.get_installed_solc_versions()
        if _as_tuple(version) >= SOLIDITY_MIN
    ]
    if not installed:
        try:
            solcx.install_solc("0.8.20")
        except Exception as exc:  # pragma: no cover - dependance reseau
            pytest.skip(f"solc >= 0.8.20 indisponible : {exc}")
        installed = [
            version
            for version in solcx.get_installed_solc_versions()
            if _as_tuple(version) >= SOLIDITY_MIN
        ]
    if not installed:
        pytest.skip("solc >= 0.8.20 absent : `solcx.install_solc('0.8.20')`")
    return str(min(installed))


def _compile(source: str):
    solcx = pytest.importorskip("solcx")
    solcx.set_solc_version(_solc_version())
    compiled = solcx.compile_source(source, output_values=["abi", "bin"])
    if "contracts" in compiled:
        compiled = list(compiled["contracts"].values())[0]
    else:
        compiled = list(compiled.values())[0]
    return compiled["abi"], compiled["bin"]


def _selector(signature: str) -> bytes:
    from eth_utils import keccak

    return keccak(text=signature)[:4]


def _decode_string(raw: str) -> bytes:
    """Decode une valeur de retour `string` ABI-encodee."""
    data = bytes.fromhex(raw.removeprefix("0x"))
    length = int.from_bytes(data[32:64], "big")
    return data[64 : 64 + length]


# --------------------------------------------------------------------------
# Mesures
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def deployed_contract():
    pytest.importorskip("eth_tester")
    from eth_tester import EthereumTester, PyEVMBackend

    source = contract_from_committed_output()
    abi, bytecode = _compile(source)
    assert bytecode, "la compilation ne produit aucun bytecode"

    tester = EthereumTester(PyEVMBackend())
    account = tester.get_accounts()[0]
    tx_hash = tester.send_transaction(
        {"from": account, "gas": 6_000_000, "data": bytecode}
    )
    receipt = tester.get_transaction_receipt(tx_hash)
    assert receipt["status"] == 1, "le deploiement echoue"
    return {
        "tester": tester,
        "account": account,
        "address": receipt["contract_address"],
        "abi": abi,
        "bytecode": bytecode,
    }


def test_le_contrat_local_se_compile(deployed_contract):
    """Le contrat affiche par le chemin local compile : la preuve est reelle."""
    assert deployed_contract["bytecode"]
    assert len(deployed_contract["bytecode"]) > 0


def test_store_uint256_ecrase_le_message_par_32_octets(deployed_contract):
    """`store(uint256)` n'ecrit pas le nombre : il ecrase le message par 32 octets.

    C'est le defaut que la compilation seule ne peut pas voir, et que le carnet
    doit donc nommer dans sa lecture de la sortie.
    """
    tester = deployed_contract["tester"]
    account = deployed_contract["account"]
    address = deployed_contract["address"]

    before = _decode_string(
        tester.call({"from": account, "to": address, "data": "0x" + _selector("retrieve()").hex()})
    )
    assert before == b"Hello, World!"

    data = _selector("store(uint256)") + (5).to_bytes(32, "big")
    tx_hash = tester.send_transaction(
        {"from": account, "to": address, "data": "0x" + data.hex(), "gas": 200_000}
    )
    receipt = tester.get_transaction_receipt(tx_hash)
    assert receipt["status"] == 1, "l'ecriture reussit : le defaut est silencieux"

    after = _decode_string(
        tester.call({"from": account, "to": address, "data": "0x" + _selector("retrieve()").hex()})
    )
    assert after != b"Hello, World!", "le message initial a ete ecrase"
    assert len(after) == 32, "le message vaut les 32 octets de l'entier"
    assert after == b"\x00" * 31 + b"\x05", "la valeur stockee est le blob encodes"


def _rapport() -> int:
    source = contract_from_committed_output()
    print("=== contrat extrait de la sortie commitee ===")
    print(source)
    abi, bytecode = _compile(source)
    print(f"=== compilation OK : {len(bytecode)} octets de bytecode ===")

    from eth_tester import EthereumTester, PyEVMBackend

    tester = EthereumTester(PyEVMBackend())
    account = tester.get_accounts()[0]
    tx_hash = tester.send_transaction(
        {"from": account, "gas": 6_000_000, "data": bytecode}
    )
    receipt = tester.get_transaction_receipt(tx_hash)
    address = receipt["contract_address"]
    print(f"=== deploiement OK : {address} ===")

    before = _decode_string(
        tester.call({"from": account, "to": address, "data": "0x" + _selector("retrieve()").hex()})
    )
    data = _selector("store(uint256)") + (5).to_bytes(32, "big")
    store_tx = tester.send_transaction(
        {"from": account, "to": address, "data": "0x" + data.hex(), "gas": 200_000}
    )
    status = tester.get_transaction_receipt(store_tx)["status"]
    after = _decode_string(
        tester.call({"from": account, "to": address, "data": "0x" + _selector("retrieve()").hex()})
    )
    print(f"retrieve() avant store(5) : {before!r}")
    print(f"store(5) -> status {status} (succes : le defaut est silencieux)")
    print(f"retrieve() apres store(5) : {after!r} ({len(after)} octets)")
    print("VERDICT : le message initial est ecrase par les 32 octets de l'entier")
    return 0


if __name__ == "__main__":
    raise SystemExit(_rapport())
