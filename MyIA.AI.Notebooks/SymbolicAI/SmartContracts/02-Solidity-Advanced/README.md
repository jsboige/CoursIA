# 02-Solidity-Advanced — Standards, DeFi, DAO et Account Abstraction

[← 01 — Solidity Fondations](../01-Solidity-Foundation/README.md) | [↑ SmartContracts](../README.md) | [03 — Foundry Testing →](../03-Foundry-Testing/README.md)

## Ouverture — ce que cette partie enseigne (Licence)

Cette deuxième sous-série de code quitte la syntaxe pour les **cas d'usage réels** d'Ethereum : les standards de tokens (ERC-20, ERC-721, ERC-1155), les primitives DeFi (AMM à produit constant, liquidity pools), la gouvernance on-chain (votes pondérés, timelock), l'account abstraction (ERC-4337, Smart Accounts, Paymasters), et enfin l'assistance par LLM pour générer, auditer et documenter du Solidity. Comme la partie précédente, chaque concept est illustré par un contrat compilé et déployé **réellement** sur `anvil` — les adresses et receipts dans les outputs sont authentiques.

C'est ici que la série croise la **preuve formelle** : l'invariant de conservation de l'ERC-20, observé en Python dans le compagnon SC-7b, est démontré dans le lake Lean `erc20_lean` que le compagnon natif SC-7c interroge directement.

**À qui elle s'adresse.** Un lecteur ayant terminé [01-Solidity-Foundation](../01-Solidity-Foundation/README.md). Les prérequis exacts, notebook par notebook, sont en [Installation](#installation) ; les compagnons lettrés ont leurs prérequis propres en [Approfondissements](#approfondissements-licence).

Le décompte des carnets de cette sous-série est tenu par le [catalogue des cours](../../../../COURSE_CATALOG.generated.md), régénéré automatiquement.

## Comment lire ce README (Licence)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous construisez sur Ethereum** : suivez la table du parcours principal, de haut en bas — chaque notebook suppose les standards du précédent.
- **Vous creusez un palier** : deux paliers lettrés ici — [l'ERC-20 prouvé](#autour-de-07--lerc-20-prouvé) (7b, 7c) et [l'économie du fournisseur de liquidité](#autour-de-08--léconomie-du-fournisseur-de-liquidité) (8b).
- **Vous cherchez la recherche en cours** : la formalisation Lean de la série vit ici même — voir [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Licence)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 7 | [SC-07-Token-Standards-Python](SC-07-Token-Standards-Python.ipynb) | Les trois standards fondateurs — ERC-20 (fongibles), ERC-721 (NFT), ERC-1155 (multi-tokens) — construits sur les contrats sécurisés d'OpenZeppelin ; le point de passage obligé vers DeFi et gouvernance | Licence | [Vérification ERC-20](SC-7b-ERC20-Lean-Verification-Companion.ipynb) · [Lean natif](SC-07c-ERC20-Lean.ipynb) |
| 8 | [SC-08-DeFi-Primitives-Python](SC-08-DeFi-Primitives-Python.ipynb) | Automated Market Makers et formule à produit constant x\*y=k : construction d'un liquidity pool, mesure concrète du price impact et du slippage d'un swap | Licence | [Économie du LP et MEV](SC-08b-MEV-LP-Python.ipynb) |
| 9 | [SC-09-DAO-Governance-Python](SC-09-DAO-Governance-Python.ipynb) | Gouvernance on-chain : vote pondéré par balance de token, création et exécution de propositions, timelock qui retarde l'exécution — pont naturel avec le théorème d'Arrow de [GameTheory](../../../GameTheory/) | Licence | — |
| 10 | [SC-10-Account-Abstraction-Python](SC-10-Account-Abstraction-Python.ipynb) | ERC-4337 : séparation EOA / Smart Accounts programmables, UserOperations, Paymasters qui paient le gas, wallet sans clé privée traditionnelle | Licence | — |
| 11 | [SC-11-LLM-Assisted-Python](SC-11-LLM-Assisted-Python.ipynb) | Le LLM comme outil de développeur Solidity : prompting efficace, détection de vulnérabilités, documentation NatSpec — API Claude/OpenAI et alternative Qwen locale | Licence | — |

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Implémenter** les standards ERC-20/721/1155 sur des contrats OpenZeppelin ;
2. **Construire** un AMM à produit constant et mesurer price impact et slippage ;
3. **Composer** un système de gouvernance (vote pondéré, propositions, timelock) ;
4. **Programmer** un Smart Account ERC-4337 avec Paymaster ;
5. **Utiliser** un LLM pour générer, auditer et documenter du Solidity.

## Approfondissements (Licence)

### Autour de 07 — l'ERC-20 prouvé

Deux compagnons prolongent SC-7 vers la vérification formelle :

- [SC-7b — vérification par compagnon](SC-7b-ERC20-Lean-Verification-Companion.ipynb) reprend l'invariant de conservation `Σ balances = totalSupply` du contrat de SC-7. Il rejoue des transitions `mint`, `transfer` et `burn` en Python, puis sur une simulation Monte-Carlo de 10 000 transitions, et confronte cette observation à la garantie prouvée dans le lake Lean `erc20_lean` (voir [Lean-23](../../Lean/Lean-23-ERC20-Invariant-Companion.ipynb)). Prérequis en plus : SC-7 complété, notions d'ERC-20 ; kernel `python3`, aucune chaîne locale.
- [SC-07c — Lean natif](SC-07c-ERC20-Lean.ipynb) passe au noyau Lean lui-même (kernel `lean4-wsl`) : il évalue les signatures et les théorèmes du lake (`#check`, `#print axioms`, `#eval`) et liste les axiomes que ces preuves utilisent ; ses exercices demandent de compléter des preuves Lean. Prérequis en plus : SC-7b complété, Lean 4 via le kernel `lean4-wsl` (WSL), exécution depuis le répertoire du lake.

### Autour de 08 — l'économie du fournisseur de liquidité

[SC-08b — MEV et LP](SC-08b-MEV-LP-Python.ipynb) prend le même pool, mais du point de vue de l'économie plutôt que du swap : ce que le déposant **gagne** (frais, en fonction du volume) et ce qu'il **perd** (perte non-permanente, retrouvée par simulation *et* par la formule fermée), puis les deux extractions canoniques — **sandwich** et **backrun** — avec le profit de l'attaquant, la perte de la victime, et les deux bords où l'attaque cesse d'être rentable. Le carnet réutilise le noyau de swap de SC-8 (copie déclarée) et vérifie son équivalence contre la sortie déjà committée de SC-8 ; il porte des exercices non résolus. Prérequis en plus : SC-8 complété ; kernel `python3`, aucune chaîne locale requise.

## Sous-séries (Licence)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [SmartContracts](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Prérequis d'entrée** : [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) complété (SC-3 à SC-6).
- **Python 3.10+** avec `pip install web3 py-solc-x`.
- **`anvil` sur le PATH et lancé** avant l'exécution de SC-7 à SC-10 : chaque notebook se connecte à un nœud local. Sans `anvil` actif, les cellules de déploiement échouent en `ConnectionRefusedError`.
- **OpenZeppelin** : déjà vendored dans `foundry-lib/` ; la compilation se fait via `py-solc-x` avec le compilateur versionné.
- **SC-10** : dépend d'`@account-abstraction` et `@openzeppelin` (résolus via `foundry-lib/`) ; le déploiement invoque le `EntryPoint` officiel ERC-4337 sur anvil.
- **SC-11** : clé API lue depuis l'environnement (`os.getenv`) pour Claude/OpenAI ; un LLM local Qwen peut remplacer l'API cloud, et les cellules d'appel s'affranchissent proprement si la clé est absente. Aucune clé committée dans le notebook.
- **Compagnons lettrés** : SC-7b et SC-08b ne demandent que le kernel `python3` ; SC-07c exige le kernel `lean4-wsl` et le lake `erc20_lean` — sans ce kernel, le carnet ne s'exécute pas.
- Aucun faucet, aucun ETH réel pour SC-7 à SC-10 : tout tourne sur le nœud local `anvil`.

À noter : les swaps et le price impact de SC-8 sont calculés sur des réserves initiales petites pour rester pédagogiques — les effets de slippage y sont exagérés volontairement.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Le lake de la série, `erc20_lean`, formalise l'invariant de conservation de l'ERC-20 (`Σ balances = totalSupply`) — la garantie que SC-7b observe statistiquement et que SC-07c interroge à la source. C'est la seule sous-série qui consomme ce lake ; l'inventaire des modules, pins et mesure de `sorry` vit dans le README parent, il n'est pas recopié ici. Le pont avec [GameTheory/SocialChoice](../../../GameTheory/SocialChoice/README.md) joue le même rôle pour SC-9 : le théorème d'Arrow y est prouvé formellement et éclaire les limites de tout système de vote on-chain.

**Le fil de recherche.** Le smart contract n'est plus un objet isolé, mais une **brique composée dans un système** (tokens + pools + gouvernance + abstraction). La force d'Ethereum n'est pas un seul contrat mais leur **composition** — et cette composition exige à la fois des standards partagés (ERC), des mécanismes économiques (AMM), des garde-fous démocratiques (DAO/timelock) et des abstractions ergonomiques (ERC-4337), chacun introduisant ses propres compromis que la partie suivante (tests, fuzzing, vérification formelle) se charge de sécuriser. Pour l'assistance LLM, le même paradigme est appliqué à la preuve formelle dans les notebooks [Lean-7/8/9](../../Lean/).

## Ressources

- [SmartContracts — README de la série](../README.md) : le parcours global, les parties suivantes, l'inventaire Lean.
- [03 — Foundry Testing](../03-Foundry-Testing/README.md) : la suite immédiate — tests, fuzzing d'invariants, vérification formelle.
- [GameTheory/SocialChoice](../../../GameTheory/SocialChoice/README.md) : le théorème d'Arrow prouvé, en écho à SC-9.
- **ERC-20** (Vogelsteller & Buterin, 2015) · **ERC-721** (Shirley, Evans & Castano, 2018) · **ERC-1155** (Radomski & Cooke, 2018) — standards de tokens Ethereum (EIPs).
- **ERC-4337** (Ferro, Kolinkin et al., 2021) — Account Abstraction via entry point contract.
- **Uniswap V2** (Adams, Zinsmeister & Robinson, 2020) — core whitepaper : AMM à produit constant x\*y=k.
- **Foundry Book** (Foundry contributors) — `anvil`, `forge`, `cast` : book.getfoundry.sh.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
