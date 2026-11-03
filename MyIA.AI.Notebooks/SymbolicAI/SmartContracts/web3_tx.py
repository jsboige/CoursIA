"""web3_tx.py — envoyer une transaction web3 ET attendre son minage.

Usage dans les carnets de la serie SmartContracts :

    import sys
    from pathlib import Path

    for _parent in [Path.cwd(), *Path.cwd().parents]:
        if (_parent / "web3_tx.py").exists():
            if str(_parent) not in sys.path:
                sys.path.insert(0, str(_parent))
            break
    from web3_tx import transact_and_wait

    receipt = transact_and_wait(w3, erc20.functions.transfer(to, 1000), deployer)
    receipt = transact_and_wait(w3, pay.functions.deposit(), deployer, value=one_eth)
    print(receipt["gasUsed"])

Pourquoi cet organe existe
--------------------------

Sous anvil, `.transact()` rend la main des que la transaction est **acceptee dans
le mempool**, pas quand elle est minee. Une cellule qui lit l'etat juste apres
-- `balanceOf`, `counter`, `owner`, `allowance`, `totalSupply` -- peut donc
afficher la valeur d'AVANT la transaction : la sortie committee se contredit
elle-meme, sans qu'aucune cellule n'ait leve d'erreur.

Instance fondatrice, mesuree sur piece (contre-audit #17073, PR #22877) : la
cellule 7 de `SC-07-Token-Standards-Python.ipynb` affichait, dans le meme
output,

    Apres transfer(1000 SIM) : receiver = 0 SIM
    Apres approve(500) + transferFrom(200) : receiver = 1200 SIM
    allowance restante = 300 SIM

Trois nombres qui ne peuvent pas etre vrais ensemble : le `0` etait l'etat
d'avant le transfert. L'ancienne execution de juin masquait la course par sa
lenteur ; une machine plus rapide l'a revelee.

Le defaut est une **classe**, pas une instance : il ne se voit que quand la
machine est assez rapide pour lire trop tot, et il se propage a chaque nouveau
carnet qui ecrit `x.functions.f(...).transact(...)` suivi d'une lecture. D'ou un
organe importe plutot qu'une ligne recopiee : la garde statique
`test_web3_tx.py` refuse qu'un `.transact()` direct reapparaisse dans les
carnets de la serie.

Ce qui n'est PAS fait ici, et pourquoi
--------------------------------------

Aucun reessai, aucun timeout personnalise : `wait_for_transaction_receipt` a
deja son `timeout`, et un reessai sur une transaction qui a echoue minerait
deux fois. Le seul ajout au-dela de l'attente est le controle de
`receipt["status"]`, parce qu'une transaction minee avec `status == 0` est
exactement la meme classe de mensonge : le code continue comme si l'ecriture
avait eu lieu.
"""

from __future__ import annotations


class TransactionReverted(RuntimeError):
    """La transaction a ete minee mais a echoue (`status != 1`)."""


def transact_and_wait(w3, fn, sender, **tx_kwargs):
    """Envoyer une transaction, attendre son minage, rendre son receipt.

    Parametres
    ----------
    w3 :
        L'instance Web3 de la cellule (aucun import web3 ici : le module reste
        importable sans web3 installe).
    fn :
        L'appel de fonction non lie, par exemple
        `erc20.functions.transfer(receiver, 1000)` — surtout pas deja appele
        avec `.transact(...)`.
    sender :
        L'adresse qui signe, placee dans `from`. Prioritaire : un `from`
        passe dans `tx_kwargs` est ecrase par `sender`, ne comptez pas sur lui.
    **tx_kwargs :
        Les autres cles de transaction (`value`, `gas`, `gasPrice`, ...).
        Une cle `from` ici est ignoree au profit de `sender`.

    Retour
    ------
    Le receipt (`w3.eth.wait_for_transaction_receipt`), pas le hash : c'est le
    receipt qui porte `status`, `gasUsed` et les evenements. Le hash reste
    accessible par `receipt["transactionHash"]`.

    Leve
    ----
    `TransactionReverted` si la transaction est minee avec `status != 1`. Un
    revert detecte a l'estimation de gas leve avant, depuis `transact`, comme
    avant : les cellules qui attendent un revert gardent leur `try/except`.
    """
    # `sender` en dernier : prioritaire sur un eventuel `from` passe dans
    # `tx_kwargs` (contrat du test test_sender_prioritaire_sur_un_from_dans_les_kwargs).
    tx_hash = fn.transact({**tx_kwargs, "from": sender})
    receipt = w3.eth.wait_for_transaction_receipt(tx_hash)
    try:
        status = receipt["status"]
    except (TypeError, KeyError):
        status = None
    if status is not None and status != 1:
        raise TransactionReverted(
            f"Transaction minee mais echouee (status={status}) : {tx_hash!r}"
        )
    return receipt
