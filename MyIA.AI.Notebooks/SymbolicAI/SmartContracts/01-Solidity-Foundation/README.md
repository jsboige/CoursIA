# 01-Solidity-Foundation — Fondements du langage Solidity

[← 00-Foundations](../00-Foundations/README.md) | [↑ SmartContracts](../README.md) | [02 — Solidity Avancé →](../02-Solidity-Advanced/README.md)

## Ouverture — ce que cette partie enseigne (Licence)

Cette première sous-série de code Solidity pose les fondamentaux du langage : structure d'un contrat, types et variables, fonctions et état (data locations, visibilité, modifiers), héritage et interfaces, puis erreurs et events. Aucune ligne de Solidity sérieuse ne s'écrit sans ces piliers. Chaque concept est illustré par un contrat compilé et déployé **réellement** sur `anvil` (le nœud local de test fourni par Foundry) — pas de simulation : les adresses et les receipts dans les outputs sont authentiques, et le pattern `compile -> deploy -> call` hérité de [SC-2](../00-Foundations/SC-02-Setup-Web3py-Python.ipynb) est celui repris dans toute la suite.

**À qui elle s'adresse.** Un lecteur ayant terminé [00-Foundations](../00-Foundations/README.md) (environnement Foundry + web3.py opérationnel) et qui écrit ses premiers contrats. Aucune expérience Solidity préalable n'est supposée ; les prérequis exacts sont en [Installation](#installation).

Le décompte des carnets de cette sous-série est tenu par le [catalogue des cours](../../../../COURSE_CATALOG.generated.md), régénéré automatiquement.

## Comment lire ce README (Licence)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous apprenez Solidity** : suivez la table du parcours principal, de haut en bas — chaque notebook suppose les précédents.
- **Vous creusez un palier** : cette partie n'en porte aucun (voir [Approfondissements](#approfondissements-licence)) ; les paliers lettrés commencent à la partie suivante, avec les compagnons ERC-20.
- **Vous cherchez la recherche en cours** : allez à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche) — les formalisations Lean de la série vivent dans la partie avancée.

## Parcours principal (Licence)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 3 | [SC-03-Solidity-Basics-Python](SC-03-Solidity-Basics-Python.ipynb) | Structure minimale d'un contrat, types valeur (`uint`, `address`, `bool`, `bytes`), variables d'état vs locales, conversions explicites — premier déploiement réel sur `anvil` | Découverte | — |
| 4 | [SC-04-Functions-State-Python](SC-04-Functions-State-Python.ipynb) | Le cœur du langage : les trois data locations (`storage`, `memory`, `calldata`) et leur coût en gas, la visibilité (`public`/`external`/`internal`/`private`), les modifiers d'accès (`view`, `pure`, `payable`) | Licence | — |
| 5 | [SC-05-Inheritance-Python](SC-05-Inheritance-Python.ipynb) | Héritage simple et multiple via `is`, interfaces pour l'abstraction, contrats `abstract` et `override` — la préparation directe aux standards ERC de la partie suivante | Licence | — |
| 6 | [SC-06-Errors-Events-Python](SC-06-Errors-Events-Python.ipynb) | `require` (conditions d'entrée, gas rembourseé), `revert` (erreurs complexes), `assert` (invariants internes), custom errors économes en gas depuis 0.8.4, et les events pour le logging hors-chaîne | Licence | — |

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Écrire** la structure d'un contrat Solidity avec les bons types et les bonnes conversions ;
2. **Choisir** la data location et la visibilité adaptées — et mesurer leur coût en gas ;
3. **Composer** par héritage et interfaces, en préparant les standards ERC ;
4. **Signaler** erreurs et événements proprement (`require`/`revert`/`assert`, custom errors, events).

## Approfondissements (Licence)

Cette partie **ne porte aucun approfondissement lettré** : c'est le socle continu du langage, chaque notebook suppose les précédents et aucun ne se détache comme variante d'un numéro porteur. Les paliers lettrés de la série commencent à la partie suivante — les compagnons ERC-20 de SC-7 — et rien n'est perdu ici : il n'y a rien à replier.

## Sous-séries (Licence)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [SmartContracts](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Prérequis d'entrée** : [00-Foundations](../00-Foundations/README.md) complété — Foundry installé, `web3`/`py-solc-x` disponibles, pattern compile-deploy-call en main.
- **Python 3.10+** avec `pip install web3 py-solc-x`.
- **`anvil` sur le PATH et lancé** avant l'exécution : chaque notebook se connecte à un nœud local. Sans `anvil` actif, les cellules de déploiement échouent en `ConnectionRefusedError`.
- **`py-solc-x` télécharge le compilateur** au premier appel (`solcx.install_solc`) ; le versioning se fait via `foundry-lib/` au niveau de la série.
- Aucune clé API, aucun faucet, aucun ETH réel : tout tourne sur le nœud local `anvil`.

Les outputs committés proviennent d'exécutions réelles sur `anvil` : adresses de contrat, gas utilisés et receipts sont authentiques — sans erreur volontaire.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Cette partie ne consomme aucune formalisation Lean. Le lake de la série, `erc20_lean`, formalise l'ERC-20 et n'est convoqué qu'en [02-Solidity-Advanced](../02-Solidity-Advanced/README.md) ; l'inventaire des modules vit dans le README parent, il n'est pas recopié ici.

**Le fil de recherche.** Le changement de regard proposé par les fondations du langage : ne plus écrire du code qui « tourne », mais du code qui **coûte** (chaque instruction a un prix en gas) et qui est **observable** (chaque état est public sur la chaîne). Si la théorie du gas et des data locations reste abstraite, reprenez [SC-00](../00-Foundations/SC-00-Cypherpunk-Origins-Python.ipynb) — comprendre *pourquoi* une blockchain fait payer chaque opération éclaire le modèle économique de la EVM.

## Ressources

- [SmartContracts — README de la série](../README.md) : le parcours global, les parties suivantes, l'inventaire Lean.
- [00-Foundations](../00-Foundations/README.md) : l'environnement que cette partie suppose.
- [02 — Solidity Avancé](../02-Solidity-Advanced/README.md) : la suite immédiate — ERC-20/721/1155, DeFi, DAO, account abstraction, assistance LLM.
- **Foundry Book** (Foundry contributors) — `anvil`, `forge`, `cast` : book.getfoundry.sh.
- **Solidity Documentation officielle** (Ethereum Foundation) — types, data locations, héritage, errors/events : docs.soliditylang.org.
- Wood, G. (2014) — *Ethereum: A Secure Decentralised Generalised Transaction Ledger* (Yellow Paper) : EVM, gas, modèle d'exécution.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
