"""test_web3_tx.py — tests de l'organe `web3_tx` et garde statique de la serie.

Deux familles de tests :

1. **comportement** de `transact_and_wait` sur un faux Web3 (aucun anvil, aucun
   web3 installe : les dependances de ce fichier sont la bibliotheque standard) ;
2. **garde statique** : aucun carnet de la serie SmartContracts n'appelle
   `.transact()` directement. C'est cette assertion qui empeche la classe de
   revenir par un nouveau carnet, et c'est elle qui rend l'organe utile au-dela
   du nettoyage ponctuel (cf docstring de `web3_tx.py`).

Lancer depuis le dossier de la serie :

    python -m pytest test_web3_tx.py -q
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from web3_tx import TransactionReverted, transact_and_wait

SERIES_ROOT = Path(__file__).resolve().parent

# Carnets de la serie ou l'appel direct a `.transact()` a ete remplace par
# l'organe. Les carnets non listes ici ne sont pas (encore) contraints : la
# garde s'elargit a mesure que la conversion avance, elle ne se referme jamais.
#
# SC-07 n'y figure pas encore : la PR #22877 (ouverte) y a pose un helper local
# `transact_and_wait` avant que cet organe existe. Les deux ne peuvent pas
# cohabiter sur la meme branche ; SC-07 rejoint cette liste quand #22877 est
# mergee, en remplacant son helper local par l'import. Tant qu'il n'y figure
# pas, la garde ne dit rien de lui — elle ne l'exempte pas, elle ne le voit pas.
GUARDED_NOTEBOOKS = [
    "01-Solidity-Foundation/SC-03-Solidity-Basics-Python.ipynb",
    "01-Solidity-Foundation/SC-04-Functions-State-Python.ipynb",
    "01-Solidity-Foundation/SC-05-Inheritance-Python.ipynb",
    "02-Solidity-Advanced/SC-08-DeFi-Primitives-Python.ipynb",
]


# --------------------------------------------------------------------------
# Faux Web3 : enregistre l'ordre des appels, ce qui est exactement ce que le
# defaut fondeur (lire avant le minage) viole.
# --------------------------------------------------------------------------


class FakeEth:
    def __init__(self, receipt):
        self._receipt = receipt
        self.waited = []

    def wait_for_transaction_receipt(self, tx_hash):
        self.waited.append(tx_hash)
        return self._receipt


class FakeW3:
    def __init__(self, receipt):
        self.eth = FakeEth(receipt)


class FakeFn:
    def __init__(self, tx_hash="0xdeadbeef"):
        self.tx_hash = tx_hash
        self.calls = []

    def transact(self, tx_params):
        self.calls.append(tx_params)
        return self.tx_hash


# --------------------------------------------------------------------------
# Comportement
# --------------------------------------------------------------------------


def test_attend_le_receipt_et_le_rend():
    """L'organe rend le receipt, pas le hash, et l'attente a bien eu lieu."""
    receipt = {"status": 1, "gasUsed": 21000, "transactionHash": "0xdeadbeef"}
    w3 = FakeW3(receipt)
    fn = FakeFn()

    got = transact_and_wait(w3, fn, "0x" + "11" * 20)

    assert got is receipt
    assert w3.eth.waited == ["0xdeadbeef"], "wait_for_transaction_receipt non appele"
    assert fn.calls[0]["from"] == "0x" + "11" * 20


def test_les_kwargs_de_transaction_passent():
    """`value=` et consorts doivent atteindre `transact`, pas etre avales."""
    w3 = FakeW3({"status": 1})
    fn = FakeFn()

    transact_and_wait(w3, fn, "0xsender", value=10**18, gas=100000)

    assert fn.calls == [{"from": "0xsender", "value": 10**18, "gas": 100000}]


def test_sender_prioritaire_sur_un_from_dans_les_kwargs():
    """Un `from` passe en kwarg ne doit pas ecraser le sender nomme."""
    w3 = FakeW3({"status": 1})
    fn = FakeFn()

    transact_and_wait(w3, fn, "0xsender", **{"from": "0xINTRUS"})

    assert fn.calls[0]["from"] == "0xsender"


def test_receipt_sans_status_ne_leve_pas():
    """Un receipt muet (cas des fakes de carnets) n'est pas un echec."""
    receipt = {"gasUsed": 21000}
    w3 = FakeW3(receipt)

    assert transact_and_wait(w3, FakeFn(), "0xsender") is receipt


def test_status_zero_leve_TransactionReverted():
    """Minee ET echouee : la meme classe de mensonge, on refuse de continuer."""
    w3 = FakeW3({"status": 0})

    with pytest.raises(TransactionReverted):
        transact_and_wait(w3, FakeFn(), "0xsender")


def test_receipt_non_indexable_ne_leve_pas():
    """Un objet receipt sans `__getitem__` reste acceptable."""
    w3 = FakeW3(object())

    transact_and_wait(w3, FakeFn(), "0xsender")


# --------------------------------------------------------------------------
# Garde statique : aucun `.transact()` direct dans les carnets convertis
# --------------------------------------------------------------------------


def _code_sources(path: Path):
    """Rend (index, source) des cellules de code, commentaires retires."""
    nb = json.loads(path.read_text(encoding="utf-8"))
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        lines = []
        for line in "".join(cell.get("source", [])).splitlines():
            stripped = line.split("#", 1)[0]
            lines.append(stripped)
        yield i, "\n".join(lines)


@pytest.mark.parametrize("relpath", GUARDED_NOTEBOOKS)
def test_carnet_sans_transact_direct(relpath):
    """Chaque carnet converti doit passer par l'organe, pas par `.transact()`."""
    path = SERIES_ROOT / relpath
    if not path.exists():
        pytest.skip(f"{relpath} absent de ce checkout")

    hits = [(i, s) for i, s in _code_sources(path) if ".transact(" in s]
    assert not hits, (
        f"{relpath} : {len(hits)} appel(s) direct(s) a .transact() "
        f"(cellules {[i for i, _ in hits]}) — utiliser transact_and_wait()"
    )


@pytest.mark.parametrize("relpath", GUARDED_NOTEBOOKS)
def test_carnet_importe_l_organe(relpath):
    """Le carnet doit importer l'organe, sinon la garde precedente est vide."""
    path = SERIES_ROOT / relpath
    if not path.exists():
        pytest.skip(f"{relpath} absent de ce checkout")

    imports = [
        s for _, s in _code_sources(path) if "from web3_tx import" in s
    ]
    assert imports, f"{relpath} : aucun `from web3_tx import ...`"


def test_tout_importateur_de_l_organe_est_garde():
    """La liste ne peut pas se refermer : tout carnet qui importe l'organe
    doit figurer dans GUARDED_NOTEBOOKS, sinon sa conversion echapperait a
    test_carnet_sans_transact_direct (retirer une entree ferait passer la
    garde au vert sans qu'aucun test ne rougisse).
    """
    importateurs = []
    for path in SERIES_ROOT.rglob("*.ipynb"):
        rel = path.relative_to(SERIES_ROOT).as_posix()
        if any("from web3_tx import" in s for _, s in _code_sources(path)):
            importateurs.append(rel)
    manquants = sorted(set(importateurs) - set(GUARDED_NOTEBOOKS))
    assert not manquants, (
        f"carnets important web3_tx absents de GUARDED_NOTEBOOKS : {manquants} "
        "— la garde ne les couvre plus, les ajouter a la liste"
    )
