# Smart Contracts - Développement Multi-Plateformes

Série de notebooks éducatifs pour apprendre le développement de smart contracts, de Solidity aux blockchains multi-chain.

## Vue d'Ensemble

| Métrique | Valeur |
|----------|--------|
| **Notebooks** | 17 |
| **Durée totale** | ~13 heures |
| **Niveau** | Débutant à Avancé |
| **Prérequis** | Python 3.10+, programmation de base |

## Structure

```
SmartContracts/
├── 00-Environment/           # Configuration (1 notebook)
├── 01-Solidity-Foundation/   # Fondements Solidity (4 notebooks)
├── 02-Solidity-Advanced/     # Solidity avancé (5 notebooks)
├── 03-Foundry-Testing/       # Tests et sécurité (3 notebooks)
├── 04-Multi-Chain/           # Multi-chain (3 notebooks)
└── 05-Capstone/              # Projet final (1 notebook)
```

## Progression

### Partie 0: Environnement (30 min)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 0 | [SC-0-Setup](00-Environment/SC-0-Setup.ipynb) | 30 min | [ ] |

**Objectifs**: Installer Foundry, configurer l'environnement de développement

### Partie 1: Solidity Fondements (~2h50)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 1 | [SC-1-Solidity-Basics](01-Solidity-Foundation/SC-1-Solidity-Basics.ipynb) | 40 min | [ ] |
| 2 | [SC-2-Functions-State](01-Solidity-Foundation/SC-2-Functions-State.ipynb) | 45 min | [ ] |
| 3 | [SC-3-Inheritance](01-Solidity-Foundation/SC-3-Inheritance.ipynb) | 35 min | [ ] |
| 4 | [SC-4-Errors-Events](01-Solidity-Foundation/SC-4-Errors-Events.ipynb) | 30 min | [ ] |

**Objectifs**: Maîtriser les bases de Solidity (types, fonctions, héritage)

### Partie 2: Solidity Avancé (~4h30)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 5 | [SC-5-Token-Standards](02-Solidity-Advanced/SC-5-Token-Standards.ipynb) | 50 min | [ ] |
| 6 | [SC-6-DeFi-Primitives](02-Solidity-Advanced/SC-6-DeFi-Primitives.ipynb) | 55 min | [ ] |
| 7 | [SC-7-DAO-Governance](02-Solidity-Advanced/SC-7-DAO-Governance.ipynb) | 45 min | [ ] |
| 8 | [SC-8-Account-Abstraction](02-Solidity-Advanced/SC-8-Account-Abstraction.ipynb) | 50 min | [ ] |
| 8b | [SC-8b-LLM-Assisted](02-Solidity-Advanced/SC-8b-LLM-Assisted.ipynb) | 45 min | [ ] |

**Objectifs**: Implémenter des protocoles DeFi, gouvernance, ERC-4337

### Partie 3: Foundry Testing (~2h15)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 9 | [SC-9-Foundry-Basics](03-Foundry-Testing/SC-9-Foundry-Basics.ipynb) | 45 min | [ ] |
| 10 | [SC-10-Fuzz-Testing](03-Foundry-Testing/SC-10-Fuzz-Testing.ipynb) | 40 min | [ ] |
| 11 | [SC-11-Formal-Verification](03-Foundry-Testing/SC-11-Formal-Verification.ipynb) | 50 min | [ ] |

**Objectifs**: Tests unitaires, fuzzing, vérification formelle

### Partie 4: Multi-Chain (~2h30)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 12 | [SC-12-Move-Sui](04-Multi-Chain/SC-12-Move-Sui.ipynb) | 50 min | [ ] |
| 13 | [SC-13-Solana-Anchor](04-Multi-Chain/SC-13-Solana-Anchor.ipynb) | 55 min | [ ] |
| 14 | [SC-14-Cross-Chain](04-Multi-Chain/SC-14-Cross-Chain.ipynb) | 45 min | [ ] |

**Objectifs**: Développement sur Sui (Move), Solana (Anchor), cross-chain

### Partie 5: Capstone (1h30)

| # | Notebook | Durée | Status |
|---|----------|-------|--------|
| 15 | [SC-15-Final-Project](05-Capstone/SC-15-Final-Project.ipynb) | 90 min | [ ] |

**Objectifs**: Projet complet (Token + Staking + Governance)

## Technologies

| Technologie | Usage | Installation |
|-------------|-------|--------------|
| **Foundry** | Dev Ethereum | `curl -L https://foundry.paradigm.xyz \| bash` |
| **Solidity** | Smart contracts | Inclus dans Foundry |
| **Sui CLI** | Dev Move | `cargo install --locked --git https://github.com/MystenLabs/sui sui` |
| **Anchor** | Dev Solana | `cargo install --git https://github.com/coral-xyz/anchor anchor-cli` |
| **Certora** | Vérification formelle | Via site Certora |

## Prérequis

### Logiciels

- Python 3.10+
- Git
- curl (Windows: via Git Bash ou WSL)

### Connaissances

- Programmation de base (variables, fonctions, POO)
- Notions de cryptographie (utile mais non requis)

## Démarrage Rapide

```bash
# 1. Installer Foundry
curl -L https://foundry.paradigm.xyz | bash
foundryup

# 2. Vérifier l'installation
forge --version
cast --version
anvil --version

# 3. Créer un projet test
mkdir my-project && cd my-project
forge init

# 4. Compiler et tester
forge build
forge test
```

## Ressources Externes

- [Foundry Book](https://book.getfoundry.sh/)
- [Solidity Docs](https://docs.soliditylang.org/)
- [Sui Documentation](https://docs.sui.io/)
- [Anchor Book](https://book.anchor-lang.com/)
- [OpenZeppelin Contracts](https://docs.openzeppelin.com/contracts/)

---

*Série créée pour CoursIA - Formation Intelligence Artificielle*
