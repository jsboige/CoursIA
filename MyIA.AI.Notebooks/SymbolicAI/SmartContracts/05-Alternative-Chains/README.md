# 05-Alternative-Chains — Au-delà d'Ethereum : Vyper, XRP, Bitcoin, Move et Solana

[← 04 — Privacy & Cryptography](../04-Privacy-Cryptography/README.md) | [↑ SmartContracts](../README.md) | [06 — Real World →](../06-Real-World/README.md)

## Ouverture — ce que cette partie enseigne (Licence)

Cette cinquième sous-série élargit l'horizon au-delà de la EVM Ethereum : **Vyper** (le Solidity « sécurisé par design »), le **XRP Ledger** (consensus UNL, trust lines, DEX), **Bitcoin Script** (le langage à pile et son modèle UTXO), **Move/Sui** (la programmation orientée ressources), et **Solana/Anchor** (Rust, PDAs, CPIs). Chaque notebook confronte le modèle mental Ethereum à un paradigme différent.

**Signature pédagogique multi-langage.** Plusieurs langages (Vyper, Bitcoin Script, Move, Rust) y sont présentés comme chaînes de caractères pour illustration, avec des sorties documentées **honnêtement** selon que le CLI correspondant est installé ou non (audit #3164 : les replis sont disclose, jamais masqués). Avec le CLI installé, ces opérations se reproduisent.

**À qui elle s'adresse.** Un lecteur ayant terminé les parties précédentes (concepts Solidity SC-3..6 supposés) et curieux des autres modèles de chaîne. Les prérequis exacts, CLI par CLI, sont en [Installation](#installation).

Le décompte des carnets de cette sous-série est tenu par le [catalogue des cours](../../../../COURSE_CATALOG.generated.md), régénéré automatiquement.

## Comment lire ce README (Licence)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous élargissez vos modèles mentaux** : suivez la table du parcours principal, de haut en bas — chaque notebook est un paradigme autonome.
- **Vous creusez un palier** : cette partie n'en porte aucun (voir [Approfondissements](#approfondissements-licence)).
- **Vous cherchez la recherche en cours** : le déploiement réel sur réseaux publics (testnets, mainnets L2) et le capstone sont en [06-Real-World](../06-Real-World/README.md).

## Parcours principal (Licence)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 18 | [SC-18-Vyper-Python](SC-18-Vyper-Python.ipynb) | La philosophie Vyper : volontairement restrictif (pas d'héritage, pas d'inline assembly) pour réduire la surface d'attaque — la conception du langage *comme* mesure de sécurité. Syntaxe, contrat de stockage, token, déploiement web3.py, comparaison Vyper/Solidity | Licence | — |
| 19 | [SC-19-Ripple-XRP-Python](SC-19-Ripple-XRP-Python.ipynb) | Le XRP Ledger et son consensus **UNL** : comptes et transactions via `xrpl-py`, trust lines, offers et DEX intégré, payment channels pour les micropaiements, Hooks comme équivalent smart contract | Licence | — |
| 20 | [SC-20-Bitcoin-Scripting-Python](SC-20-Bitcoin-Scripting-Python.ipynb) | Le **modèle UTXO** (vs le modèle Account d'Ethereum) et **Bitcoin Script**, langage à pile non-Turing-complet : mini-interpréteur Python, construction et signature manuelles de transactions, scripts avancés (multisig, timelock, P2SH) | Licence | — |
| 21 | [SC-21-Move-Sui-Python](SC-21-Move-Sui-Python.ipynb) | La programmation **orientée ressources** de Move (née chez Meta/Diem) et le modèle objet de Sui : module Move simple, abilities (`key`, `store`, `copy`, `drop`) qui contrôlent la linéarité et la copie | Licence | — |
| 22 | [SC-22-Solana-Anchor-Python](SC-22-Solana-Anchor-Python.ipynb) | L'architecture haute performance Solana et le framework **Anchor** (Rust) : PDAs (Program Derived Addresses) déterministes — calculés réellement via le SDK Python — et CPIs (Cross-Program Invocations) | Licence | — |

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Comparer** les modèles de chaîne : compte vs UTXO, Turing-complet vs langage à pile, objet vs ressource, minage vs consensus par quorum ;
2. **Lire et écrire** des scripts Bitcoin simples via un interpréteur compris de l'intérieur ;
3. **Choisir** un paradigme selon le compromis expressivité/sécurité/performance qu'on accepte.

## Approfondissements (Licence)

Cette partie **ne porte aucun approfondissement lettré** : ses notebooks sont cinq paradigmes parallèles, chacun autonome, sans variante qui se détacherait d'un numéro porteur. Rien n'est perdu ici — il n'y a rien à replier.

## Sous-séries (Licence)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [SmartContracts](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Prérequis d'entrée** : concepts Solidity SC-3..6 ; notions de consensus blockchain et d'arithmétique modulaire selon le notebook.
- **Python 3.10+** orchestre tous les notebooks :
  - **SC-18** : `pip install vyper web3` ; `anvil` (Foundry) pour le déploiement local ;
  - **SC-19** : `pip install xrpl-py` ; accès au Testnet XRP (faucet). La connexion peut échouer dans certains environnements (`asyncio.run() from running loop`) : le notebook le documente honnêtement et bascule sur une simulation conceptuelle disclose ;
  - **SC-20** : le mini-interpréteur tourne en stdlib (`hashlib`) ; `pip install python-bitcoinlib` optionnel ;
  - **SC-21** : Sui CLI (Move compiler) ;
  - **SC-22** : Solana CLI + Anchor (`cargo install anchor-cli`) + toolchain Rust.
- **Sans ces CLI installés**, les notebooks s'affranchissent proprement : sorties documentées comme illustration, replis disclose (audit #3164).

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Cette partie n'en consomme aucune. Le lake de la série (`erc20_lean`) vit en [02-Solidity-Advanced](../02-Solidity-Advanced/README.md) ; l'inventaire des modules vit dans le README parent, il n'est pas recopié ici.

**Le fil de recherche.** Ne plus voir la blockchain comme une technologie unique (la EVM), mais comme un **espace de conception** où chaque axe — compte vs UTXO, Turing-complet vs langage à pile, objet vs ressource, minage vs consensus par quorum — est un compromis entre expressivité, sécurité et performance. Il n'existe pas de « bonne » blockchain dans l'absolu, mais une famille de modèles dont Ethereum n'est qu'un point. Après avoir vu UTXO, ressources et paradigmes alternatifs, relire [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) : le modèle Account/EVM apparaît alors comme *un* choix, non *le* choix.

## Ressources

- [SmartContracts — README de la série](../README.md) : le parcours global, les parties suivantes, l'inventaire Lean.
- [06 — Real World](../06-Real-World/README.md) : la suite — réseaux publics et capstone.
- **Vyper Documentation** (Vyper Team) — philosophie, syntaxe : docs.vyperlang.org.
- **XRP Ledger Documentation** (Ripple) — consensus UNL, trust lines, DEX, Hooks : xrpl.org.
- **Bitcoin Developer Documentation** (Bitcoin Core) — UTXO, Bitcoin Script, opcodes : developer.bitcoin.org.
- **Move Book** (Diem/Meta, 2019 ; Sui) — programmation orientée ressources, abilities : move-language.github.io/move.
- **Solana Documentation** + **Anchor Book** (Solana Labs / Anchor) — accounts, PDAs, CPIs : docs.solana.com, book.anchor-lang.com.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
