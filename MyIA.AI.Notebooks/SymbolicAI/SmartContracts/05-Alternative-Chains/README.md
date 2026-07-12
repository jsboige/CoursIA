# 05-Alternative-Chains - Au-dela d'Ethereum : Vyper, XRP, Bitcoin, Move et Solana

**Navigation** : [Sommaire de la série](../README.md) | [<< SC-17 E2E Vérifiable Voting](../04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb) | [SC-23 Cross-Chain >>](../06-Real-World/SC-23-Cross-Chain.ipynb)

Cette cinquieme sous-série (SC-18 a SC-22) élargit le horizon au-dela de la EVM Ethereum : **Vyper** (le Solidity « sécurisé par design »), le **XRP Ledger** (consensus UNL, trust lines, DEX), **Bitcoin Script** (le langage a pile de Bitcoin et son modèle UTXO), **Move/Sui** (la programmation orientée ressources), et **Solana/Anchor** (Rust, PDAs, CPIs). Chaque notebook confronte le modèle mental Ethereum a un paradigme différent. La signature pédagogique de cette sous-série est particulière : plusieurs langages (Vyper, Bitcoin Script, Move, Rust) y sont présentes comme chaînes de caractères pour illustration, avec des sorties documentées honnêtement selon que le CLI correspondant est installe ou non.

---

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 18 | [SC-18-Vyper](SC-18-Vyper.ipynb) | 45 min | Philosophie Vyper vs Solidity, syntaxe, contrats de stockage et token, déploiement web3.py |
| 19 | [SC-19-Ripple-XRP](SC-19-Ripple-XRP.ipynb) | 45 min | XRP Ledger, consensus UNL, comptes/transactions `xrpl-py`, trust lines, DEX, payment channels, Hooks |
| 20 | [SC-20-Bitcoin-Scripting](SC-20-Bitcoin-Scripting.ipynb) | 50 min | Modèle UTXO, Bitcoin Script (langage a pile), mini-interpréteur Python, multisig, timelock, P2SH |
| 21 | [SC-21-Move-Sui](SC-21-Move-Sui.ipynb) | 40 min | Langage Move, modèle objet de Sui, module Move, abilities (key/store/copy/drop) |
| 22 | [SC-22-Solana-Anchor](SC-22-Solana-Anchor.ipynb) | 45 min | Architecture Solana, framework Anchor (Rust), PDAs, CPIs |

**Total** : 5 notebooks, ~3h45.

---

## Parcours d'apprentissage

### Étape 1 : Vyper, le Solidity sécurisé (SC-18, 45 min)

La **philosophie de conception** de Vyper : volontairement restrictif (pas d'héritage, pas d'inline assembly) pour reduire la surface d'attaque. Syntaxe des types de base, fonctions et decorateurs, ecriture d'un contrat de stockage et d'un token, déploiement via web3.py, et comparaison Vyper/Solidity sur des exemples equivalents.

### Étape 2 : XRP Ledger (SC-19, 45 min)

L'**architecture du XRP Ledger** et son consensus **UNL** (Unique Node List). Manipulation des comptes et transactions via `xrpl-py`, exploration des **trust lines**, **offers** et du **DEX integre**, découverte des **payment channels** pour les micropaiements, et des **Hooks** comme equivalent smart contract du XRPL.

### Étape 3 : Bitcoin et son langage a pile (SC-20, 50 min)

Le **modèle UTXO** de Bitcoin (vs le modèle Account d'Ethereum), **Bitcoin Script** comme langage a pile non-Turing-complet, implémentation d'un **mini-interpréteur Bitcoin Script** en Python, construction et signature manuelle de transactions, et scripts avancés (**multisig**, **timelock**, **P2SH**).

### Étape 4 : Move et Sui (SC-21, 40 min)

Le langage **Move** (ne chez Meta/Diem) et sa programmation **orientée ressources**. Le **modèle objet** de Sui, création d'un module Move simple, et utilisation des **abilities** (`key`, `store`, `copy`, `drop`) qui controlent la linearite et la copie des ressources.

### Étape 5 : Solana et Anchor (SC-22, 45 min)

L'**architecture Solana** (accounts, programs) et le framework **Anchor** (Rust). Création de **PDAs** (Program Derived Addresses) deterministes et implémentation de **CPIs** (Cross-Program Invocations).

---

## Prérequis

### Par notebook

| Notebook | Fondations requises | Dépendances |
|----------|---------------------|-------------|
| SC-18 Vyper | Solidity basics (SC-3..6) ; web3.py | Vyper compiler (`pip install vyper`), web3 |
| SC-19 Ripple-XRP | Python ; notions de consensus blockchain | `xrpl-py` ; connexion internet (Testnet XRP) |
| SC-20 Bitcoin-Scripting | Python ; arithmetique modulaire | `hashlib` (stdlib), `python-bitcoinlib` (optionnel) |
| SC-21 Move-Sui | SC-3..6 complètes (concepts) ; notions de programmation orientée ressources | Sui CLI (Move compiler) |
| SC-22 Solana-Anchor | SC-3..6 complètes (concepts) ; notions de base Rust | Solana CLI, Anchor framework, Rust toolchain |

### Configuration requise

- **Python 3.10+** pour les cellules d'orchestration de tous les notebooks.
- **SC-18** : `pip install vyper web3` ; anvil (Foundry) pour le déploiement local.
- **SC-19** : `pip install xrpl-py` ; acces au Testnet XRP (faucet).
- **SC-20** : `pip install python-bitcoinlib` (optionnel) ; le mini-interpréteur tourne en stdlib.
- **SC-21** : Sui CLI (installe via cargo ou binaire) ; le compilateur Move.
- **SC-22** : Solana CLI + Anchor (`cargo install anchor-cli`) + Rust toolchain.
- Sans ces CLI installes, les notebooks s'affranchissent proprement (sorties documentées comme illustration, audit #3164).

---

## Ponts inter-séries

| Série | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte, parcours global, glossaire |
| [04-Privacy-Cryptography](../04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs.ipynb) | Predecesseur | SC-15..17 (ZKP, chiffrement homomorphe, vote vérifiable) |
| [06-Real-World](../06-Real-World/SC-23-Cross-Chain.ipynb) | Suite | SC-23..26 (cross-chain, déploiement public, capstone) |

---

## Points de vigilance (CLI multiples)

- **Signature pédagogique multi-langage** : Vyper, Bitcoin Script, Move et Rust sont présentes comme chaînes de caractères dans les cellules Python, avec les sorties correspondantes documentées. Avec le CLI installe, ces opérations se reproduisent ; sans lui, elles servent d'illustration honnêtement disclosee (audit #3164 : SC-18 Vyper mode demo, SC-19 XRP setup-connect disclosed, SC-21 Move/Sui CLI non invoque, echos byte-identiques).
- **SC-19 XRP** : la connexion au Testnet peut echouer dans certains environnements (`asyncio.run() from running loop`) ; le notebook le documenté honnêtement et bascule sur une simulation conceptuelle disclosed.
- **SC-20 Bitcoin** : l'arithmetique (balances, tailles de script, timelocks) est exacte et vérifiable dans les outputs committes.
- **SC-22 Solana** : les PDAs (Bump 255, determinisme) sont calcules réellement via le SDK Solana Python ; la partie Anchor/Rust requiere le toolchain complet.
- **Audit #3164** : cette sous-série a ete auditee FIDELE (0 finding stricto sensu) — les replis sont honnêtement documentés, pas masques.

---

## Ressources

- **Vyper Documentation** (Vyper Team) -- philosophie, syntaxe, differences avec Solidity. docs.vyperlang.org.
- **XRP Ledger Documentation** (Ripple) -- consensus UNL, trust lines, DEX, Hooks. xrpl.org.
- **Bitcoin Developer Documentation** (Bitcoin Core) -- UTXO model, Bitcoin Script, opcodes. developer.bitcoin.org.
- **Move Book** (Diem/Meta, 2019 ; Sui) -- programmation orientée ressources, abilities. move-language.github.io/move.
- **Solana Documentation** + **Anchor Book** (Solana Labs / Anchor) -- accounts, PDAs, CPIs. docs.solana.com, book.anchor-lang.com.
- Voir aussi les références transversales dans le [README parent de la série](../README.md).

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette cinquième sous-série élargit le horizon **au-delà de la EVM Ethereum**. L'arc pédagogique confronte le modèle mental Ethereum à **cinq paradigmes différents**, chacun révélant un choix de conception qu'Ethereum avait présenté comme allant de soi :

- **Vyper** (SC-18) — le Solidity « sécurisé par conception » : volontairement restrictif (pas d'héritage, pas d'inline assembly) pour réduire la surface d'attaque. La conception du langage *comme* mesure de sécurité.
- **Le XRP Ledger** (SC-19) — un consensus sans minage (UNL, Unique Node List), des trust lines, un DEX intégré, des payment channels et des Hooks. Une blockchain pensée pour les paiements, pas le calcul général.
- **Bitcoin et son langage à pile** (SC-20) — le **modèle UTXO** (vs le modèle Account d'Ethereum), **Bitcoin Script** comme langage à pile non-Turing-complet, un mini-interpréteur en Python, et les scripts avancés (multisig, timelock, P2SH). La simplicité délibérée comme sécurité.
- **Move et Sui** (SC-21) — la programmation **orientée ressources** (née chez Meta/Diem), le modèle objet de Sui, et les abilities (`key`/`store`/`copy`/`drop`) qui contrôlent la linéarité et la copie.
- **Solana et Anchor** (SC-22) — une architecture haute performance en Rust, les **PDAs** (Program Derived Addresses) déterministes, et les **CPIs** (Cross-Program Invocations).

La signature pédagogique est multi-langage (Vyper, Bitcoin Script, Move, Rust présentés comme chaînes de caractères), avec des sorties documentées honnêtement selon que le CLI correspondant est installé.

### Prochaines étapes

- **Le déploiement réel** : la suite est [06-Real-World](../06-Real-World/README.md) (SC-23 à SC-26), qui confronte ces modèles à des réseaux publics (testnets, mainnets L2) et les assemble dans un capstone.
- **Revenir sur Ethereum** : après avoir vu UTXO, ressources et paradigmes alternatifs, relire [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) — le modèle Account/EVM apparaît alors comme *un* choix, non *le* choix.
- **La série dans son ensemble** : le [sommaire SmartContracts](../README.md) cartographie les sept sous-séries — celle-ci est le décentrement comparatif.

### Le fil rouge

Les chaînes alternatives proposent un changement de regard sur la blockchain : ne plus la voir comme une technologie unique (la EVM), mais comme un **espace de conception** où chaque axe — compte vs UTXO, Turing-complet vs langage à pile, objet vs ressource, minage vs consensus par quorum — est un compromis entre expressivité, sécurité et performance. Comprendre Vyper, XRP, Bitcoin, Move et Solana, c'est comprendre qu'il n'existe pas de « bonne » blockchain dans l'absolu, mais une famille de modèles dont Ethereum n'est qu'un point — et que le choix du paradigme dépend du compromis qu'on est prêt à accepter.
