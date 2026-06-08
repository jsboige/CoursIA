# Smart Contracts - Des Cypherpunks aux Blockchains Modernes

<!-- CATALOG-STATUS
series: SymbolicAI-SmartContracts
pedagogical_count: 27
breakdown: SmartContracts=27
maturity: PRODUCTION=27
-->

Serie de notebooks educatifs couvrant les fondements cryptographiques, le developpement Solidity, les tests, la cryptographie avancee (ZKP, HE, vote verifiable), et les blockchains alternatives.

Un smart contract est un programme qui s'execute tout seul sur une blockchain : une fois deploye, son code fait foi, transfere de la valeur et applique des regles sans intermediaire ni possibilite de revenir en arriere. C'est ce qui fait sa puissance — des ecosystemes entiers (DeFi, NFT, DAO) reposent dessus — et son danger : un bug n'est pas un patch a pousser le lendemain, c'est une faille immuable qui peut couter des millions (le hack de The DAO en 2016, les exploits de ponts cross-chain). D'ou le poids accorde dans cette serie aux **tests, au fuzzing et a la verification formelle** autant qu'au developpement.

Le parcours suit le fil annonce par le titre : on part des **primitives cryptographiques** des cypherpunks (hachage, arbres de Merkle, preuve de travail, signatures) pour comprendre *pourquoi* une blockchain tient, puis on construit en **Solidity** (types, heritage, standards ERC, DeFi, gouvernance), on **securise** (Foundry, invariants, verification formelle), on explore la **cryptographie pour la vie privee** (ZKP, chiffrement homomorphique, vote verifiable de bout en bout), avant d'elargir aux **chaines alternatives** (Vyper, XRP, Bitcoin Script, Move/Sui, Solana) et au **deploiement reel** sur testnet puis mainnet. L'objectif final n'est pas seulement de savoir ecrire un contrat, mais de savoir le rendre digne de confiance.

---

**27 notebooks** | **Kernel Python 3** | **~22 heures**

**A qui s'adresse cette serie** : developpeurs Solidity, ingenieurs DeFi, specialistes security/blockchain, etudiants en IA symbolique interesses par la verification formelle. Un niveau intermediaire en programmation est recommande — les bases de Python sont suffisantes, mais les concepts blockchain/cryptographie sont introduits progressivement.

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Construire** des smart contracts Solidity fonctionnels (types, fonctions, heritage, standards ERC)
2. **Deployer** et interagir avec des contrats sur des blockchains reelles (Anvil, Sepolia, XRP testnet)
3. **Tester** rigoureusement (unit tests, fuzzing, invariants) avec Foundry
4. **Vérifier** formellement la correction de contrats (SMT solvers, Certora)
5. **Implementer** des primitives cryptographiques from scratch (ZKP, chiffrement homomorphique, signatures)
6. **Explorer** les blockchains alternatives (Vyper, XRP, Bitcoin Script, Move/Sui, Solana)
7. **Déployer** en production sur testnet et mainnet

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 27 (SC-0 a SC-26) |
| Duree totale | ~22 heures |
| Langage | Python (kernel Jupyter) |
| Kernels | Python 3 |
| Outils | Foundry (forge/cast/anvil), web3.py, py-solcx |
| Cryptographie | pycryptodome, phe, TenSEAL |
| Niveaux | Debutant a Avance (Parties 0-6) |

## Parcours d'apprentissage

### Phase 1 : Fondations (~2h10)

Les notebooks 0-2 posent les bases historiques et techniques. Le notebook 0 explore les primitives cryptographiques qui fondent la blockchain (hash, arbres de Merkle, preuve de travail, signatures, DHT). Le notebook 1 installe Foundry — forge, cast, anvil — l'outil de developpement principal. Le notebook 2 configure web3.py + py-solcx pour compiler et deployer des contrats Solidity reellement sur Anvil (blockchain locale). A l'issue de cette phase, vous avez un environnement fonctionnel et deployez votre premier contrat.

### Phase 2 : Solidity Fondements (~2h30)

Les notebooks 3-6 couvrent les bases de Solidity : types et variables (SC-3), fonctions et état (SC-4), heritage et interfaces (SC-5), erreurs et events (SC-6). Chaque notebook inclut un deploiement reel sur Anvil. Cette phase vise la maitrise du langage de base — pas de code Solidity ne peut etre ecrit sans ces fondamentaux.

### Phase 3 : Solidity Avance (~4h30)

Les notebooks 7-11 abordent les standards token (ERC-20, ERC-721, ERC-1155), les primitives DeFi (AMM, lending, oracles), la gouvernance DAO, l'account abstraction (ERC-4337), et l'assistance LLM pour les smart contracts. C'est le coeur technique de la serie — chaque concept est illustré par un contrat deployable.

### Phase 4 : Testing et Securite (~2h15)

Les notebooks 12-14 traitent de la securite : tests unitaires Foundry (SC-12), fuzz testing et invariants (SC-13), verification formelle (SC-14). Cette phase est cruciale — un smart contract non teste est un contrat non deploable en production. La verification formelle (SMT solvers, Certora) represente le pont vers la preuve mathématique de correction.

### Phase 5 : Cryptographie et Vie Privee (~3h)

Les notebooks 15-17 construisent des primitives cryptographiques from scratch : preuves a connaissance nulle (Schnorr, Fiat-Shamir, sigma protocols), chiffrement homomorphique (Paillier, CKKS/TenSEAL), et un systeme de vote verifiable de bout en bout (ElectionGuard). Cette partie est la plus theorique mais la plus puissante — elle montre comment proteger la vie privee sur des blockchains transparentes.

### Phase 6 : Blockchains Alternatives (~4h)

Les notebooks 18-22 explorent cinq blockchains non-EVM : Vyper (smart contracts Python-like), XRP Ledger (xrpl-py, trust lines), Bitcoin Script (UTXO model), Move/Sui (modele objet), et Solana avec le framework Anchor. Chaque notebook est autonome et illustre un paradigme de programmation different.

### Phase 7 : Deploiement Reel (~3h45)

Les notebooks 23-26 couvrent l'interoperabilite cross-chain, le deploiement sur testnet (Sepolia + XRP testnet), le deploiement mainnet (L2 Base/Polygon), et le projet capstone integre. C'est la phase de transition vers le monde reel — tout le travail precedent sert a construire, tester et deployer un projet complet.

## Parcours alternatives

### Parcours Solidity intensif (~8h)

Se concentrer sur les phases 1-3 + phase 4 (testing) : SC-0, SC-1-2, SC-3 a SC-6, SC-7 a SC-11, SC-12-14. Idéal pour developpeurs souhaitant maitriser rapidement le developpement Ethereum.

### Parcours Cryptographie (~3h)

Les notebooks 15-17 : ZKP, chiffrement homomorphique, vote verifiable. Prerequis : notions de base en algèbre et probabilites. Pas necessaire de passer par les phases 1-4 (les primitives sont introduites in-context).

### Parcours Blockchains alternatives (~4h)

Les notebooks 18-22 : Vyper, XRP, Bitcoin, Move, Solana. Chaque notebook est autonome — l'ordre n'est pas critique. Utile pour comprendre les paradigmes non-EVM.

### Parcours Security-first (~7h)

Fondations (SC-0-2) + Solidity basique (SC-3-6) + Testing avancé (SC-12-14) + Verification formelle (SC-14). Pour developpeurs souhaitant se specialiser en smart contract auditing.

## Quel parcours choisir ?

| Objectif | Parcours recommande | Duree |
|----------|-------------------|-------|
| Decouvrir la blockchain | SC-0 → SC-1 → SC-2 → SC-3 | 3h |
| Devenir developpeur Solidity | Parcours Solidity intensif | 8h |
| Specialiser en security | Parcours Security-first | 7h |
| Cryptographie avancee | Parcours Cryptographie | 3h |
| Explorer les chains non-EVM | Parcours alternatives | 4h |
| De deployer en production | Parcours complet + SC-23-26 | 22h |
| Comprendre DeFi | SC-7-8-9 | 2h30 |
| Gouvernance DAO | SC-9-10-17 | 2h |

## Structure

```text
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

## Parcours recommande

```
  Partie 0 (Fondations)
      │
      ▼
  Partie 1 (Solidity Fondements)
      │
      ▼
  Partie 2 (Solidity Avance) ───────┐
      │                             │
      ▼                             │
  Partie 3 (Testing) ───────────────┤
      │                             │
      ▼                             │
  Partie 4 (Cryptographie) ─────────┤
      │                             │
      ▼                             │
  Partie 5 (Alternatives) ──────────┤  (chaque notebook est autonome)
      │                             │
      ▼                             │
  Partie 6 (Real-World) ────────────┘
      │
      ▼
  SC-26 (Projet capstone)
```

**Objectifs par partie** :

| Partie | Objectif principal | Livrable attendu |
|--------|-------------------|------------------|
| 0 | Installer l'environnement + comprendre les bases | Anvil en marche + 1er contrat deploye |
| 1 | Maitriser le langage Solidity | Contrats types, fonctions, heritage fonctionnels |
| 2 | Construire des protocoles DeFi complets | Token ERC-20 + AMM + DAO deployes |
| 3 | Tester et verifier un contrat | Suite de tests, fuzzing, verification formelle |
| 4 | Cacher des donnees sur blockchain publique | ZKP + chiffrement homomorphique fonctionnels |
| 5 | Comprendre les architectures alternatives | Contracts deployes sur Vyper/XRP/Bitcoin/Move/Solana |
| 6 | Deployer en production | Contrat sur testnet/mainnet + projet capstone |

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

## Concepts cles

| Concept | Description | Notebooks |
|---------|-------------|-----------|
| **Smart Contract** | Programme autonome sur blockchain, code = loi | Partout (SC-3+) |
| **EVM** | Machine virtuelle Ethereum : stack-based, bytecode | SC-1, SC-3, SC-23-26 |
| **Gas** | Mecanisme de tarification du calcul | SC-3, SC-4 |
| **Storage / Memory / Calldata** | Three tiers de donnees Solidity | SC-3, SC-4 |
| **Inheritance & Interfaces** | Heritage multiple, abstract contracts | SC-5 |
| **ERC Standards** | ERC-20 (fungible), ERC-721 (NFT), ERC-1155 (multi), ERC-4337 (AA) | SC-7, SC-10 |
| **AMM** | Automated Market Maker — uniswap V2/V3 model | SC-8 |
| **Oracle** | Pont de donnees externes vers on-chain | SC-8 |
| **Fuzz Testing** | Testing avec generateur d'inputs aleatoires | SC-13 |
| **Formal Verification** | Preuve mathématique de correction (SMT, Certora) | SC-14 |
| **Zero-Knowledge Proof** | Prouver sans reveler (Schnorr, Fiat-Shamir) | SC-15 |
| **Homomorphic Encryption** | Calculer sur donnees chiffrées (Paillier, CKKS) | SC-16 |
| **Vote E2E Verifiable** | Secret + verifiable + comptable automatiquement | SC-17 |
| **UTXO Model** | Modele transactionel de Bitcoin (non account-based) | SC-20 |
| **Move Language** | Language de smart contracts a objets (Sui) | SC-21 |
| **Cross-Chain Bridge** | Interoperabilite entre blockchains | SC-23 |
| **Account Abstraction** | ERC-4337 : wallets sans cle privee traditionnelle | SC-10 |

## Outils couverts

| Outil | Type | Usage principal | Installation |
|-------|------|----------------|--------------|
| **Foundry (forge)** | Framework dev | Compilation, tests, deploiement Solidity | `curl -L https://foundry.paradigm.xyz | bash` |
| **anvil** | Node Ethereum local | Blockchain locale pour dev | Inclus dans Foundry |
| **cast** | CLI Ethereum | Lect/écriture sur chaines | Inclus dans Foundry |
| **web3.py** | Bibliotheque Python | Interaction avec EVM | `pip install web3` |
| **py-solcx** | Compilateur Solidity | Compilation Solidity pour Python | `pip install py-solcx` |
| **pycryptodome** | Bibliotheque crypto | Hash, signatures, AES, Merkle | `pip install pycryptodome` |
| **phe** | Chiffrement homomorphique | Paillier (additif) | `pip install phe` |
| **xrpl-py** | Client Ripple | Connexion XRP Ledger | `pip install xrpl-py` |
| **vyper** | Compilateur Vyper | Smart contracts Python-like | `pip install vyper` |
| **python-bitcoinlib** | Bibliotheque Bitcoin | Manipulation UTXO/Script | `pip install python-bitcoinlib` |
| **TenSEAL** | Homomorphic encryption | CKKS (multiplicatif) sur tensors | `pip install tensile` |

## Prerequis

### Niveau en programmation attendu

Cette serie suppose un **niveau intermediaire en programmation** :

| Competence | Utilite dans la serie | Niveau requis |
|------------|---------------------|---------------|
| **Python de base** (fonctions, classes, modules) | Tous les notebooks (kernel Jupyter) | Intermédiaire |
| **Lignes de commande** (bash, git) | Setup (SC-1), testing (SC-12-14) | Intermédiaire |
| **Concepts d'API / HTTP** | Interaction web3.py (SC-2, SC-24) | Elementaire |
| **Structures de donnees** (tables de hachage, listes) | Algorithmes crypto (SC-0, SC-15) | Intermédiaire |
| **Notions de base en probabilites** | ZKP (SC-15), HE (SC-16) | Elementaire |
| **Notions de base en algèbre** | Cryptographie (SC-0, SC-15-16) | Elementaire |

**Pas necessaire en pre-requis** : Solidity (enseigne dans la serie), cryptography avancee (introduite in-context), connaissance des blockchains (introduite SC-0).

### Setup technique

Toutes les dependances sont decrites dans `requirements.txt` et les scripts de setup `scripts/`. Un environnement Python 3.10+ est requis. Foundry est installe via le script d'installation inclut.

```bash
# Installation des dependances Python
pip install -r requirements.txt

# Verification
python setup_env.py --check
```

## Demarrage Rapide

### macOS / Linux (natif)

```bash
# Setup complet en une commande (Foundry + Python + kernel Jupyter)
bash scripts/setup.sh

# Ou via l'orchestrateur Python
python setup_env.py --setup

# Lancer anvil (blockchain locale)
python setup_env.py --start-anvil
# ou directement: anvil

# Ouvrir les notebooks et selectionner le kernel "Python (SmartContracts + Foundry)"
```

### Windows (via WSL)

```bash
# Depuis PowerShell, lance le setup dans WSL Ubuntu
wsl -d Ubuntu -- bash /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup.sh

# Ou alternative en 2 etapes (WSL puis PowerShell)
# Etape 1: dans WSL Ubuntu
bash scripts/setup_wsl_smartcontracts.sh
# Etape 2: dans PowerShell
.\scripts\setup_wsl_kernel.ps1

# Lancer anvil
python setup_env.py --start-anvil
```

### Verifier l'installation

```bash
python setup_env.py --check
```

## Ressources Externes

### References academiques

| Reference | Couverture |
|-----------|------------|
| Nakamoto, "Bitcoin: A Peer-to-Peer Electronic Cash System" (2008) | SC-0, SC-20 |
| Buterin, "Ethereum White Paper" (2014) | Fondements Ethereum, SC-1 a SC-10 |
| Wood, "Ethereum: A Secure Decentralised Generalised Transaction Ledger" (2014) | EVM, gas, SC-5 |
| Ben-Sasson et al., "Scalable Zero Knowledge with No Trusted Setup" (2019) | SC-15 ZK proofs |
| Gentry, "Fully Homomorphic Encryption Using Ideal Lattices" (2009) | SC-16 HE |
| Appel, "Verification of a Cryptographic Primitive: SHA-256" (2015) | SC-14 Formal verification |
| Daian et al., "Flash Boys 2.0: Frontrunning in Decentralized Exchanges" (2020) | SC-8 DeFi |
| Atzei, Bartoletti & Cimoli, "A Survey of Attacks on Ethereum Smart Contracts" (2017) | SC-12, SC-14 |

### Ressources en ligne

- [Foundry Book](https://book.getfoundry.sh/)
- [Solidity Docs](https://docs.soliditylang.org/)
- [web3.py Docs](https://web3py.readthedocs.io/)
- [OpenZeppelin Contracts](https://docs.openzeppelin.com/contracts/)
- [ElectionGuard](https://www.electionguard.vote/)
- [XRP Ledger Docs](https://xrpl.org/docs.html)

## Cross-series Bridges

| Serie | Lien | Connection |
| ------- | ------ | ----------- |
| [Lean](../Lean/README.md) | Formal verification | Les SMT solvers (SC-14) et les preuves Lean 4 sont deux facettes de la meme verite -- la correction mathématique |
| [GameTheory](../../GameTheory/README.md) | Voting & DAO | SC-9 (DAO) et SC-17 (vote E2E) sont des instances de theorie du choix social (Arrow, Sen) |
| [Probas](../../Probas/README.md) | Decision & Risk | Minimax Regret (PyMC-19) s'applique aux smart contracts pour la gestion des incertitudes on-chain |
| [SymbolicAI/SemanticWeb](../SemanticWeb/README.md) | Ontologies & Verification | Les ontologies peuvent formaliser les proprietes de contrats pour verification formelle |
| [SymbolicAI/Tweety](../Tweety/README.md) | Non-monotonic reasoning | Le raisonnement non-monotone s'applique a la governance DAO (propositions retractables) |
| [GenAI/Texte](../../GenAI/Texte/README.md) | LLM-assisted | SC-11 applique le meme paradigme d'assistance LLM que la serie GenAI Texte |

## Connections cross-series

### SmartContracts et Lean (Verification Formelle)

Les techniques de verification formelle presentees dans cette serie (SC-14, fuzzing SC-13) complementent les methodes de preuve formelle de la serie Lean :

- **SC-14 Formal Verification** (Certora, SMTChecker) vs. **Lean 4** : deux approches de la meme idee -- prouver mathematiquement la correction d'un programme. Les SMT solvers (Z3, CVC5) sont automatiques mais bornes ; Lean est interactif mais expressif ( Curry-Howard, types dependants).
- **SC-11 LLM-Assisted Contracts** : le meme paradigme d'assistance LLM que les notebooks [Lean-7/8/9](../Lean/), applique a la generation de smart contracts.

### SmartContracts et Theorie des Jeux (GameTheory)

Les mecanismes de vote et de gouvernance on-chain (SC-9, SC-17) sont des instances concretes des resultats formels de la serie GameTheory :

- **SC-9 DAO Governance** : les systemes de vote on-chain sont soumis aux memes limitations que le **theoreme d'Arrow** (formalise dans `social_choice_lean/Arrow.lean`, 0 sorry).
- **SC-17 E2E Verifiable Voting** : les proprietes des systemes de vote (Banks sets, monotonicite STV) sont etudiees formellement dans `social_choice_lean/Voting.lean`. Le chiffrement homomorphique (SC-16) et les ZKP (SC-15) sont les briques cryptographiques qui rendent le vote E2E possible.

### Lecture transversale

[La mer qui monte](../../../docs/grothendieckian-lens.md) : une grille de lecture grothendieckienne du depot (changement de representation, certification A/B/C).

## FAQ / Troubleshooting

### 1. Foundry non detecte ou `forge: command not found`

**Symptome** : Les notebooks SC-1/SC-12 echouent avec `forge not found` ou `anvil not found`.

**Solutions** :

```bash
# Installer Foundry (macOS/Linux)
curl -L https://foundry.paradigm.xyz | bash
foundryup

# Verifier l'installation
forge --version
anvil --version

# Si deja installe mais non dans le PATH
export PATH="$HOME/.foundry/bin:$PATH"
# Ajouter au ~/.bashrc ou ~/.zshrc pour persistance
```

Sur **Windows**, Foundry s'execute via WSL. Verifier que les notebooks utilisent le bon kernel Python configuré pour WSL :

```bash
# Dans WSL
which forge && which anvil
```

### 2. `py-solcx` : erreur de compilation Solidity

**Symptome** : `solcx` retourne une erreur de compilation ou "solc binary not found".

**Cause** : `py-solcx` telecharge le compilateur `solc` a la premiere utilisation. Si le telechargement echoue (proxy, pare-feu), la compilation echoue.

**Solution** :

```python
import solcx
# Forcer l'installation d'une version specifique
solcx.install_solc("0.8.20")
# Verifier les versions disponibles
print(solcx.get_installed_solc_versions())
# Utiliser une version installee
solcx.set_solc_version("0.8.20")
```

Si le telechargement est bloque, telecharger manuellement le binaire depuis [github.com/ethereum/solidity/releases](https://github.com/ethereum/solidity/releases) et le placer dans le repertoire indique par `solcx.get_solcx_install_folder()`.

### 3. Anvil ne demarre pas ou port 8545 deja pris

**Symptome** : `ConnectionRefusedError` lors des deploiements dans les notebooks SC-2/SC-3+.

**Diagnostic** :

```bash
# Verifier si Anvil tourne deja
ps aux | grep anvil    # macOS/Linux
tasklist | findstr anvil  # Windows/WSL

# Verifier si le port 8545 est occupe
lsof -i :8545          # macOS/Linux
netstat -ano | findstr 8545  # Windows
```

**Solutions** :

```bash
# Tuer un processus Anvil existant
pkill anvil

# Ou utiliser un port different
anvil --port 8546
# Adapter les notebooks: w3 = Web3(Web3.HTTPProvider("http://127.0.0.1:8546"))
```

### 4. Erreurs `web3.py` : "insufficient funds" ou "nonce too low"

**Symptome** : Les transactions echouent lors du deploiement dans les notebooks.

**Causes et solutions** :

| Erreur | Cause | Solution |
| ------ | ----- | -------- |
| `insufficient funds` | Compte Anvil non finance | Redemarrer Anvil (les comptes sont reinitialises) ou utiliser `anvil --accounts 10 --balance 10000` |
| `nonce too low` | Transaction envoyee avec un nonce deja utilise | Appeler `w3.eth.get_transaction_count(address)` pour obtenir le nonce courant |
| `replacement fee too low` | Remplacement de transaction avec gas insuffisant | Augmenter `gasPrice` de 10% minimum |
| `execution reverted` | Erreur dans le contrat Solidity | Verifier les `require()` et les conditions dans le code Solidity |

**Astuce** : Les comptes Anvil par defaut ont 10000 ETH chacun. Si les fonds semblent manquants, redemarrer Anvil pour reinitialiser l'etat.

### 5. Erreurs d'import des bibliotheques cryptographiques

**Symptome** : `ImportError` pour `Crypto`, `phe`, `tensile` ou `xrpl`.

**Cause** : Dependances non installees ou conflit de nom de package.

**Solutions** :

```bash
# pycryptodome (attention: pas pycrypto qui est obsolete)
pip uninstall pycrypto   # si installe par erreur
pip install pycryptodome

# TenSEAL (chiffrement homomorphique, SC-16)
pip install tenseal       # nom du package = tenseal, PAS tensile

# Paillier (SC-16)
pip install phe

# XRP (SC-19)
pip install xrpl-py
```

**Conflit connu** : si `import Crypto` echoue alors que `pycryptodome` est installe, verifier que `pycrypto` n'est pas installe en parallele (il ecrase le namespace). Desinstaller `pycrypto` et reinstalle `pycryptodome`.

### 6. WSL : scripts de setup inaccessible ou permission denied

**Symptome** : Les scripts `setup.sh` ou `setup_wsl_smartcontracts.sh` echouent sur Windows.

**Solutions** :

```bash
# Verifier que WSL Ubuntu est installe
wsl --list --verbose

# Donner les permissions d'execution
wsl -d Ubuntu -- chmod +x /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup.sh

# Executer le setup
wsl -d Ubuntu -- bash /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup.sh
```

Si le chemin contient des espaces, encapsuler dans des guillemets. Alternative : cloner le depot directement dans WSL (`~/CoursIA/`) plutot que d'utiliser `/mnt/c/`.

---

*Serie creee pour CoursIA - Issue #129*
