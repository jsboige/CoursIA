# Smart Contracts - Des Cypherpunks aux Blockchains Modernes

Serie de notebooks educatifs couvrant les fondements cryptographiques, le developpement Solidity, les tests, la cryptographie avancee (ZKP, HE, vote verifiable), et les blockchains alternatives.

## Vue d'Ensemble

| Metrique | Valeur |
|----------|--------|
| **Notebooks** | 27 (SC-0 a SC-26) |
| **Duree totale** | ~22 heures |
| **Niveau** | Debutant a Avance |
| **Prerequis** | Python 3.10+, programmation de base |

## Structure

```
SmartContracts/
├── 00-Foundations/              # Histoire + Setup (3 notebooks)
├── 01-Solidity-Foundation/     # Fondements Solidity (4 notebooks)
├── 02-Solidity-Advanced/       # Solidity avance (5 notebooks)
├── 03-Foundry-Testing/         # Tests et securite (3 notebooks)
├── 04-Privacy-Cryptography/    # ZKP, HE, Vote E2E (3 notebooks)
├── 05-Alternative-Chains/      # Vyper, XRP, Bitcoin, Move, Solana (5 notebooks)
├── 06-Real-World/              # Cross-chain, deploy testnet/mainnet (4 notebooks)
└── requirements.txt            # Dependances Python
```

## Progression

### Partie 0 : Fondations et Histoire (~2h10)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 0 | [SC-0-Cypherpunk-Origins](00-Foundations/SC-0-Cypherpunk-Origins.ipynb) | 60 min | Hash, Merkle, PoW, signatures, DHT - code executable |
| 1 | [SC-1-Setup-Foundry](00-Foundations/SC-1-Setup-Foundry.ipynb) | 30 min | Installation Foundry (forge, cast, anvil) |
| 2 | [SC-2-Setup-Web3py](00-Foundations/SC-2-Setup-Web3py.ipynb) | 40 min | web3.py + py-solcx + compile/deploy reel |

**Objectifs** : Comprendre les origines Cypherpunk, installer l'environnement, deployer un premier contrat

### Partie 1 : Solidity Fondements (~2h30)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 3 | [SC-3-Solidity-Basics](01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb) | 40 min | Types, variables, structure |
| 4 | [SC-4-Functions-State](01-Solidity-Foundation/SC-4-Functions-State.ipynb) | 45 min | Fonctions, modifiers, storage |
| 5 | [SC-5-Inheritance](01-Solidity-Foundation/SC-5-Inheritance.ipynb) | 35 min | Heritage, interfaces |
| 6 | [SC-6-Errors-Events](01-Solidity-Foundation/SC-6-Errors-Events.ipynb) | 30 min | Erreurs, events |

**Objectifs** : Maitriser les bases de Solidity avec deploiement reel sur anvil

### Partie 2 : Solidity Avance (~4h30)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 7 | [SC-7-Token-Standards](02-Solidity-Advanced/SC-7-Token-Standards.ipynb) | 50 min | ERC-20, ERC-721, ERC-1155 |
| 8 | [SC-8-DeFi-Primitives](02-Solidity-Advanced/SC-8-DeFi-Primitives.ipynb) | 55 min | AMM, lending, oracles |
| 9 | [SC-9-DAO-Governance](02-Solidity-Advanced/SC-9-DAO-Governance.ipynb) | 45 min | Votes, gouvernance on-chain |
| 10 | [SC-10-Account-Abstraction](02-Solidity-Advanced/SC-10-Account-Abstraction.ipynb) | 50 min | ERC-4337 |
| 11 | [SC-11-LLM-Assisted](02-Solidity-Advanced/SC-11-LLM-Assisted.ipynb) | 45 min | LLM pour smart contracts |

**Objectifs** : Protocoles DeFi, gouvernance, ERC-4337, LLM-assisted

### Partie 3 : Testing (~2h15)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 12 | [SC-12-Foundry-Testing](03-Foundry-Testing/SC-12-Foundry-Testing.ipynb) | 45 min | Tests unitaires, cheatcodes |
| 13 | [SC-13-Fuzz-Invariants](03-Foundry-Testing/SC-13-Fuzz-Invariants.ipynb) | 40 min | Fuzz testing, invariants |
| 14 | [SC-14-Formal-Verification](03-Foundry-Testing/SC-14-Formal-Verification.ipynb) | 50 min | Verification formelle |

**Objectifs** : Tests Solidity, fuzzing, verification formelle

### Partie 4 : Cryptographie et Vie Privee (~3h)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 15 | [SC-15-Zero-Knowledge-Proofs](04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs.ipynb) | 60 min | Schnorr, Fiat-Shamir, Sigma protocols |
| 16 | [SC-16-Homomorphic-Encryption](04-Privacy-Cryptography/SC-16-Homomorphic-Encryption.ipynb) | 50 min | Paillier, CKKS/TenSEAL, Shamir |
| 17 | [SC-17-E2E-Verifiable-Voting](04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb) | 70 min | Vote anonyme verifiable, ElectionGuard |

**Objectifs** : ZKP from scratch, chiffrement homomorphique, vote E2E verifiable

### Partie 5 : Blockchains Alternatives (~4h)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 18 | [SC-18-Vyper](05-Alternative-Chains/SC-18-Vyper.ipynb) | 45 min | Smart contracts Python-like |
| 19 | [SC-19-Ripple-XRP](05-Alternative-Chains/SC-19-Ripple-XRP.ipynb) | 50 min | xrpl-py, testnet, trust lines |
| 20 | [SC-20-Bitcoin-Scripting](05-Alternative-Chains/SC-20-Bitcoin-Scripting.ipynb) | 50 min | UTXO, Script, python-bitcoinlib |
| 21 | [SC-21-Move-Sui](05-Alternative-Chains/SC-21-Move-Sui.ipynb) | 50 min | Move, modele objet Sui |
| 22 | [SC-22-Solana-Anchor](05-Alternative-Chains/SC-22-Solana-Anchor.ipynb) | 55 min | Solana, Anchor framework |

**Objectifs** : Vyper, XRP, Bitcoin scripting, Move, Solana

### Partie 6 : Real-World (~3h45)

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 23 | [SC-23-Cross-Chain](06-Real-World/SC-23-Cross-Chain.ipynb) | 45 min | Bridges, interoperabilite |
| 24 | [SC-24-Testnet-Deploy](06-Real-World/SC-24-Testnet-Deploy.ipynb) | 50 min | Deploy Sepolia + XRP testnet |
| 25 | [SC-25-Mainnet-Deploy](06-Real-World/SC-25-Mainnet-Deploy.ipynb) | 40 min | Deploy L2 (Base/Polygon) |
| 26 | [SC-26-Final-Project](06-Real-World/SC-26-Final-Project.ipynb) | 90 min | Projet capstone complet |

**Objectifs** : Deploiement reel, testnets, mainnet, projet integre

## Technologies

| Technologie | Usage | Installation |
|-------------|-------|--------------|
| **Foundry** | Dev + tests Ethereum | `curl -L https://foundry.paradigm.xyz \| bash` |
| **web3.py** | Interaction Python | `pip install web3` |
| **py-solc-x** | Compilation Solidity | `pip install py-solc-x` |
| **pycryptodome** | Crypto primitives | `pip install pycryptodome` |
| **phe** | Chiffrement Paillier | `pip install phe` |
| **xrpl-py** | Protocole Ripple | `pip install xrpl-py` |
| **vyper** | Smart contracts Python-like | `pip install vyper` |
| **python-bitcoinlib** | Bitcoin scripting | `pip install python-bitcoinlib` |

## Demarrage Rapide

```bash
# 1. Installer les dependances Python
pip install -r requirements.txt

# 2. Installer Foundry
curl -L https://foundry.paradigm.xyz | bash
foundryup

# 3. Lancer anvil (blockchain locale)
anvil  # dans un terminal separe

# 4. Commencer par SC-0-Cypherpunk-Origins
```

## Ressources Externes

- [Foundry Book](https://book.getfoundry.sh/)
- [Solidity Docs](https://docs.soliditylang.org/)
- [web3.py Docs](https://web3py.readthedocs.io/)
- [OpenZeppelin Contracts](https://docs.openzeppelin.com/contracts/)
- [ElectionGuard](https://www.electionguard.vote/)
- [XRP Ledger Docs](https://xrpl.org/docs.html)

---

*Serie creee pour CoursIA (EPITA IA Symbolique) - Issue #129*
