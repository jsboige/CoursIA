# 00-Foundations - Origines Cypherpunk et Environnement

**Navigation** : [Sommaire de la serie](../README.md) | [SC-3 Solidity Basics >>](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)

La sous-serie d'ouverture des SmartContracts (SC-0 a SC-2) pose les deux socles sur lesquels toute la serie reposera : le **pourquoi** (les primitives cryptographiques qui font qu'une blockchain tient) et le **comment** (l'environnement de developpement). On commence par remonter aux origines cypherpunk -- hachage, arbres de Merkle, preuve de travail, signatures, tables de hachage distribuees -- pour comprendre *pourquoi* une chaine est immuable et resistante a la falsification. On installe ensuite **Foundry** (`forge`, `cast`, `anvil`), la trousse a outils de reference, puis on connecte **web3.py** + **py-solc-x** a `anvil` pour compiler, deployer et appeler un premier contrat Solidity entierement depuis Python.

A l'issue de cette phase (~2h10), l'environnement est operationnel et le pattern de compilation/deploiement depuis Python -- reutilise dans tous les notebooks suivants -- est en place. Les notebooks suivants supposent cet environnement installe : Foundry sur le PATH, `web3`/`py-solc-x` disponibles, `anvil` capable de lancer une blockchain locale.

---

## Notebooks

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 0 | [SC-0-Cypherpunk-Origins](SC-0-Cypherpunk-Origins.ipynb) | ~60 min | Mouvement cypherpunk, primitives cryptographiques (hash, signatures, PoW), mini-blockchain Python, arbre de Merkle, DHT/Kademlia |
| 1 | [SC-1-Setup-Foundry](SC-1-Setup-Foundry.ipynb) | ~30 min | Installation Foundry (forge/cast/anvil), verification Solidity, premier projet, compilation + test d'un contrat simple |
| 2 | [SC-2-Setup-Web3py](SC-2-Setup-Web3py.ipynb) | ~40 min | web3.py + py-solc-x, connexion a anvil, compiler/deployer/appeler un contrat depuis Python, pattern reutilisable |

---

## Objectifs d'apprentissage

A l'issue de cette sous-serie, vous serez capable de :

1. **Expliquer** les primitives cryptographiques fondatrices (hachage, Merkle, PoW, signatures) et leur role dans l'immutabilite d'une blockchain
2. **Installer** l'environnement de developpement complet (Foundry + web3.py + py-solc-x)
3. **Compiler, deployer et appeler** un contrat Solidity depuis Python via anvil
4. **Etablir** le pattern de deploiement reutilisable pour les notebooks suivants

---

## Prerequis

| Notebook | Prerequis |
|----------|-----------|
| SC-0 Cypherpunk Origins | Python 3.10+ (`hashlib` stdlib), `pycryptodome` pour les signatures ; aucune connaissance blockchain prealable |
| SC-1 Setup Foundry | Python 3.10+, curl ou PowerShell, Git |
| SC-2 Setup Web3py | SC-1 complete (anvil installe), Python 3.10+, `pip install web3 py-solc-x` |

---

## Remarques pedagogiques

- **SC-0** travaille les primitives **from scratch en Python** : aucune blockchain externe n'est requise. La mini-blockchain et l'arbre de Merkle sont construits a la main pour rendre la theorie tangible.
- **SC-1 / SC-2** sont des notebooks de *setup* : ils installent et verifient l'environnement. Les outputs committes documentent honnetement ce qui s'execute (Foundry installe, anvil lance, contrat compile+deploye) -- ils ne contiennent pas d'erreurs volontaires et s'executent de bout en bout une fois les dependances presentes.
- Le pattern `compile -> deploy -> call` etabli en SC-2 est celui repris dans toute la serie (01-Solidity-Foundation et au-dela) : c'est la fondation technique autant que conceptuelle.

---

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte et parcours global de la serie |
| [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) | Suite immediate | SC-3 Solidity Basics demarre apres SC-2 |

## Navigation

[<- Sommaire SmartContracts](../README.md) | [SC-3 Solidity Basics ->](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)
