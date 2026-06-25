# 01-Solidity-Foundation - Fondements du langage Solidity

**Navigation** : [Sommaire de la serie](../README.md) | [<< SC-2 Setup Web3py](../00-Foundations/SC-2-Setup-Web3py.ipynb) | [SC-7 Token Standards >>](../02-Solidity-Advanced/SC-7-Token-Standards.ipynb)

Cette premiere sous-serie de code Solidity (SC-3 a SC-6) pose les fondamentaux du langage : structure d'un contrat, types et variables, fonctions et etat (data locations, visibilite, modifiers), heritage et interfaces, puis erreurs et events. Aucune ligne de Solidity serieuse ne peut etre ecrite sans ces quatres notebooks. Chaque concept est illustre par un contrat compile et deploye reellement sur `anvil` (le noeud local de test fourni par Foundry) -- pas de simulation, les adresses et les receipts dans les outputs sont authentiques.

---

## Notebooks

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 3 | [SC-3-Solidity-Basics](SC-3-Solidity-Basics.ipynb) | 40 min | Structure de contrat, types valeur, variables d'etat, conversions |
| 4 | [SC-4-Functions-State](SC-4-Functions-State.ipynb) | 45 min | Data locations (storage/memory/calldata), visibilite, modifiers (view/pure/payable) |
| 5 | [SC-5-Inheritance](SC-5-Inheritance.ipynb) | 35 min | Heritage simple et multiple, interfaces, abstract/override |
| 6 | [SC-6-Errors-Events](SC-6-Errors-Events.ipynb) | 30 min | `require`/`revert`/`assert`, custom errors (0.8.4+), events |

**Total** : 4 notebooks, ~2h30.

---

## Parcours d'apprentissage

### Etape 1 : Syntaxe et types (SC-3, 40 min)

On commence par la structure minimale d'un contrat, les types valeur (uint, address, bool, bytes), les variables d'etat vs locales, et les conversions explicites. Premier deploiement sur `anvil`.

### Etape 2 : Fonctions et etat (SC-4, 45 min)

Le coeur de la programmation Solidity : les trois **data locations** (storage, memory, calldata) et leur cout en gas, la visibilite (public/external/internal/private), et les modifiers qui restreignent l'acces (`view`, `pure`, `payable`).

### Etape 3 : Heritage et abstraction (SC-5, 35 min)

Solidity supporte l'heritage multiple avec le mot-cle `is`, les interfaces pour l'abstraction, et les contrats `abstract`. Cette etape prepare directement aux standards ERC de la sous-serie suivante (02-Solidity-Advanced).

### Etape 4 : Erreurs et observabilite (SC-6, 30 min)

`require` (conditions d'entree, gas rembourse), `revert` (erreurs complexes), `assert` (invariants internes), les custom errors economes en gas depuis 0.8.4, et les events pour le logging hors-chain.

---

## Prerequis

### Par notebook

| Notebook | Fondations requises | Dependances |
|----------|---------------------|-------------|
| SC-3 Solidity-Basics | [SC-2 Setup Web3py](../00-Foundations/SC-2-Setup-Web3py.ipynb) | `web3`, `py-solc-x` |
| SC-4 Functions-State | SC-3 complete | idem |
| SC-5 Inheritance | SC-3 + SC-4 completes | idem |
| SC-6 Errors-Events | SC-3 + SC-4 + SC-5 completes | idem |

### Configuration requise

- **Python 3.10+** avec `pip install web3 py-solc-x`
- **Foundry installe** : `anvil` doit etre sur le PATH. Lancez `anvil` dans un terminal avant d'executer les cellules (les quatre notebooks s'y connectent en local).
- Aucune cle API, aucun faucet, aucun ETH reel necessaire : tout tourne sur le noeud local `anvil`.

---

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte, parcours global, glossaire |
| [00-Foundations](../00-Foundations/) | Prerequis | SC-2 (Setup Web3py) fournit l'environnement |
| [02-Solidity-Advanced](../02-Solidity-Advanced/) | Suite | SC-7+ (ERC-20/721/1155, DeFi, DAO, Account Abstraction) construisent sur ces fondamentaux |

---

## Points de vigilance (execution sur anvil)

- **Lancer `anvil` avant l'execution** : chaque notebook se connecte a un noeud local. Sans `anvil` actif, les cellules de deploiement echouent en `ConnectionRefusedError`.
- **`py-solc-x` telecharge le compilateur** au premier appel (`solcx.install_solc`) ; le versioning se fait via `foundry-lib/` au niveau de la serie.
- Les outputs committes proviennent d'executions reelles sur `anvil` : les adresses de contrat, les gas utilises et les receipts sont authentiques. La sous-serie 03 (Foundry) execute elle aussi `forge` pour de vrai (SC-12 re-execute la suite Foundry, SC-13 lance un fuzz qui decouvre un contre-exemple d'overflow) ; seuls certains notebooks restent en repli disclose quand l'outil est verrouille par acces commercial (SC-14 Certora) ou depend d'un CLI externe non installe (sous-serie 05 : Vyper / Bitcoin Script / Move / Rust).

---

## Ressources

- **Foundry Book** (Foundry contributors) -- `anvil`, `forge`, `cast`. Documentation officielle : book.getfoundry.sh.
- **Solidity Documentation officielle** (Ethereum Foundation) -- types, data locations, heritage, errors/events. docs.soliditylang.org.
- Wood, G. (2014) -- "Ethereum: A Secure Decentralised Generalised Transaction Ledger" (Yellow Paper) : EVM, gas, modele d'execution.
- Voir aussi les references transversales dans le [README parent de la serie](../README.md).

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette première sous-série de code Solidity vous a posé les **quatre piliers** sans lesquels aucune ligne de contrat sérieuse ne s'écrit. L'arc pédagogique procède de la brique minimale au contrat observable :

- **La syntaxe et les types** (SC-3) — la structure d'un contrat, les types valeur (`uint`, `address`, `bool`, `bytes`), les variables d'état vs locales, et les conversions explicites. Premier déploiement réel sur `anvil`.
- **Les fonctions et l'état** (SC-4) — le cœur de la programmation Solidity : les trois **data locations** (`storage`, `memory`, `calldata`) et leur coût en gas, la visibilité (`public`/`external`/`internal`/`private`), et les modifiers qui restreignent l'accès (`view`, `pure`, `payable`).
- **L'héritage et l'abstraction** (SC-5) — l'héritage multiple via `is`, les interfaces, les contrats `abstract` et l'`override`. Cette étape prépare directement aux standards ERC de la sous-série suivante.
- **Les erreurs et l'observabilité** (SC-6) — `require` (conditions d'entrée), `revert` (erreurs complexes), `assert` (invariants internes), les custom errors économes en gas depuis 0.8.4, et les events pour le logging hors-chaîne.

Chaque concept est illustré par un contrat compilé et déployé **réellement** sur `anvil` — les adresses et receipts dans les outputs sont authentiques, et le pattern `compile -> deploy -> call` hérité de [SC-2](../00-Foundations/SC-2-Setup-Web3py.ipynb) est celui repris dans toute la suite.

### Prochaines étapes

- **Standards et cas d'usage réels** : la suite immédiate est [02-Solidity-Advanced](../02-Solidity-Advanced/README.md) (SC-7 à SC-11), qui construit sur ces fondamentaux — ERC-20/721/1155, primitives DeFi, gouvernance DAO, account abstraction, assistance LLM.
- **Revenir aux fondations** : si la théorie du gas et des data locations (SC-4) reste abstraite, reprenez [SC-0-Cypherpunk-Origins](../00-Foundations/SC-0-Cypherpunk-Origins.ipynb) — comprendre *pourquoi* une blockchain fait payer chaque opération éclaire le modèle économique de la EVM.
- **La série dans son ensemble** : le [sommaire SmartContracts](../README.md) cartographie les six sous-séries — celle-ci n'est que le socle du langage.

### Le fil rouge

Les fondations de Solidity proposent un changement de regard sur la programmation : ne plus écrire du code qui « tourne », mais du code qui **coûte** (chaque instruction a un prix en gas) et qui est **observable** (chaque état est public sur la chaîne). Comprendre les data locations, la visibilité et les events, c'est comprendre que sur la EVM, l'optimisation et la transparence ne sont pas des raffinements mais des contraintes structurelles — et que le pattern `compile -> deploy -> call` établi ici est le squelette de toute la série.
