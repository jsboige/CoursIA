# 00-Foundations — Origines Cypherpunk et Environnement

[↑ SmartContracts](../README.md) | [01 — Solidity Fondations →](../01-Solidity-Foundation/README.md)

## Ouverture — ce que cette partie enseigne (Découverte)

Cette sous-série d'ouverture pose les deux socles sur lesquels toute la série reposera : le **pourquoi** (les primitives cryptographiques qui font qu'une blockchain tient) et le **comment** (l'environnement de développement). On remonte d'abord aux origines cypherpunk — hachage, arbres de Merkle, preuve de travail, signatures, tables de hachage distribuées — pour comprendre *pourquoi* une chaîne est immuable et résistante à la falsification. On installe ensuite **Foundry** (`forge`, `cast`, `anvil`), la trousse à outils de référence, puis on connecte **web3.py** + **py-solc-x** à `anvil` pour compiler, déployer et appeler un premier contrat Solidity entièrement depuis Python.

Le pattern de compilation/déploiement depuis Python établi ici est réutilisé dans tous les notebooks suivants ; les parties ultérieures supposent cet environnement opérationnel (Foundry sur le PATH, `web3`/`py-solc-x` disponibles, `anvil` capable de lancer une blockchain locale).

**À qui elle s'adresse.** Un lecteur qui sait programmer en Python et qui n'a jamais écrit de smart contract. Aucune connaissance blockchain n'est supposée : les primitives cryptographiques sont reconstruites à la main avant d'être utilisées. Les prérequis exacts sont en [Installation](#installation).

Le décompte des carnets de cette sous-série est tenu par le [catalogue des cours](../../../../COURSE_CATALOG.generated.md), régénéré automatiquement.

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez les smart contracts** : suivez la table du parcours principal, de haut en bas.
- **Vous creusez un palier** : le premier palier lettré de la série est [Autour de 02](#autour-de-02--le-bac-à-sable-institutionnel) ; les paliers se multiplient à partir de la partie suivante.
- **Vous cherchez la recherche en cours** : allez à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche) — cette partie ne consomme aucune formalisation Lean ; le lake de la série vit dans la partie avancée.

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 0 | [SC-00-Cypherpunk-Origins-Python](SC-00-Cypherpunk-Origins-Python.ipynb) | Mouvement cypherpunk et primitives cryptographiques reconstruites *from scratch* : hachage, arbre de Merkle, preuve de travail, signatures, DHT/Kademlia — puis mini-blockchain Python pour voir l'immutabilité à l'œuvre | Découverte | — |
| 1 | [SC-01-Setup-Foundry-Python](SC-01-Setup-Foundry-Python.ipynb) | Installation de Foundry (`forge`, `cast`, `anvil`), vérification Solidity, premier projet, compilation et test d'un contrat simple | Découverte | — |
| 2 | [SC-02-Setup-Web3py-Python](SC-02-Setup-Web3py-Python.ipynb) | web3.py + py-solc-x : connexion à `anvil`, compiler/déployer/appeler un contrat depuis Python — le pattern réutilisé dans toute la série | Découverte | [Bac à sable institutionnel](SC-02b-Bac-ASable-Institutionnel-Python.ipynb) |

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Expliquer** les primitives cryptographiques fondatrices (hachage, Merkle, PoW, signatures) et leur rôle dans l'immuabilité d'une blockchain ;
2. **Installer** l'environnement de développement complet (Foundry + web3.py + py-solc-x) ;
3. **Compiler, déployer et appeler** un contrat Solidity depuis Python via `anvil` ;
4. **Établir** le pattern de déploiement réutilisable pour les notebooks suivants ;
5. **Simuler** une délibération multi-acteurs rejouable (journal d'événements pandas, empreinte SHA-256, échec institutionnel licite) via le compagnon lettré.

## Approfondissements (Découverte)

### Autour de 02 — le bac à sable institutionnel

[SC-02b](SC-02b-Bac-ASable-Institutionnel-Python.ipynb) retourne le point de vue du pattern `compile -> deploy -> call` : au lieu d'un compte unique qui joue tous les rôles, trois acteurs à clés BIP44 délibèrent par contrat (`Deliberation` : quorum, anti-double-vote, clôture en blocs), avec journal d'événements pandas et rejouabilité par mnemonic — jusqu'à la démonstration qu'une institution peut produire un résultat litigieux **sans violer aucune règle**. Prérequis en plus : SC-2 complété (le pattern compile-deploy-call), `pandas`.

## Sous-séries (Découverte)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [SmartContracts](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Python 3.10+** : `hashlib` (stdlib) pour SC-0 ; `pycryptodome` pour les signatures.
- **Foundry** (`forge`, `cast`, `anvil`) : installé par SC-1 (curl ou PowerShell), requis sur le PATH pour toute la suite.
- **web3.py + py-solc-x** : `pip install web3 py-solc-x` — requis à partir de SC-2.
- **pandas** : requis uniquement par le compagnon [SC-2b](SC-02b-Bac-ASable-Institutionnel-Python.ipynb).
- **Git** : pour l'installation de Foundry.

Les notebooks de *setup* documentent honnêtement ce qui s'exécute (Foundry installé, `anvil` lancé, contrat compilé et déployé) — ils s'exécutent de bout en bout une fois les dépendances présentes, sans erreur volontaire.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Cette partie ne consomme aucune formalisation Lean : les primitives cypherpunk y sont reconstruites en Python, pas prouvées. Le lake de la série, `erc20_lean`, formalise l'ERC-20 et n'est convoqué qu'en [02-Solidity-Advanced](../02-Solidity-Advanced/README.md) ; l'inventaire des modules vit dans le README parent, il n'est pas recopié ici.

**Le fil de recherche.** Le changement de regard proposé par l'ouverture : ne plus voir les smart contracts comme du « code sur une blockchain » magique, mais comme la **composition de primitives cryptographiques dont l'immuabilité est mathématiquement fondée**, manipulées via un environnement d'outils reproductible. SC-0 mérite d'être repris après avoir écrit des contrats en Solidity — la théorie du hachage et de Merkle prend tout son sens quand on manipule `keccak256` et le stockage d'un contrat.

## Ressources

- [SmartContracts — README de la série](../README.md) : le parcours global, les parties suivantes, l'inventaire Lean.
- [01 — Solidity Fondations](../01-Solidity-Foundation/README.md) : la suite immédiate, qui exploite l'environnement désormais opérationnel.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
