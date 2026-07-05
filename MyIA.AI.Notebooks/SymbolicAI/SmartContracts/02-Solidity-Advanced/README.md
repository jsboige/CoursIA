# 02-Solidity-Advanced - Standards, DeFi, DAO et Account Abstraction

**Navigation** : [Sommaire de la série](../README.md) | [<< SC-6 Errors & Events](../01-Solidity-Foundation/SC-6-Errors-Events.ipynb) | [SC-12 Foundry Testing >>](../03-Foundry-Testing/SC-12-Foundry-Testing.ipynb)

Cette deuxième sous-série de code (SC-7 a SC-11) quitte la syntaxe pour les **cas d'usage réels** d'Ethereum : les standards de tokens (ERC-20, ERC-721, ERC-1155), les primitives DeFi (AMM a produit constant, liquidity pools), la gouvernance on-chain (votes pondérés, timelock), l'account abstraction (ERC-4337, Smart Accounts, Paymasters), et enfin l'assistance par LLM pour générer, auditer et documenter du Solidity. Comme la sous-série 01, chaque concept est illustre par un contrat compile et déployé réellement sur `anvil` -- les adresses et receipts dans les outputs sont authentiques.

---

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 7 | [SC-7-Token-Standards](SC-7-Token-Standards.ipynb) | 50 min | ERC-20, ERC-721, ERC-1155, contrats OpenZeppelin |
| 8 | [SC-8-DeFi-Primitives](SC-8-DeFi-Primitives.ipynb) | 55 min | AMM, formule x*y=k, liquidity pools, price impact, slippage |
| 9 | [SC-9-DAO-Governance](SC-9-DAO-Governance.ipynb) | 45 min | Vote pondéré, propositions, timelock |
| 10 | [SC-10-Account-Abstraction](SC-10-Account-Abstraction.ipynb) | 50 min | ERC-4337, UserOperations, Smart Account, Paymasters |
| 11 | [SC-11-LLM-Assisted](SC-11-LLM-Assisted.ipynb) | 45 min | LLMs (Claude/GPT) pour générer, auditer, documenter du Solidity |

**Total** : 5 notebooks, ~4h05.

---

## Parcours d'apprentissage

### Étape 1 : Standards de tokens (SC-7, 50 min)

Implémentation des trois standards fondateurs : **ERC-20** (tokens fongibles), **ERC-721** (NFTs) et **ERC-1155** (multi-tokens), en s'appuyant sur les contrats sécurisés d'OpenZeppelin. Cette étape est le point de passage obligé vers DeFi et la gouvernance.

### Étape 2 : Primitives DeFi (SC-8, 55 min)

Le coeur de la finance décentralisée : les **Automated Market Makers** et la formule a produit constant **x*y=k**. On construit un liquidity pool simple, puis on mesure concrètement le **price impact** et le **slippage** d'un swap. Cette étape mobilise les interfaces et appels externes Solidity vus en SC-5.

### Étape 3 : Gouvernance on-chain (SC-9, 45 min)

Les mécanismes de **vote pondéré** (par balance de token), la création et l'exécution de **propositions**, et le **timelock** qui retarde l'exécution pour laisser le temps de réagir. Pont naturel avec les résultats formels de la série GameTheory (théorème d'Arrow).

### Étape 4 : Account Abstraction (SC-10, 50 min)

L'ERC-4337 : séparation entre comptes externes (EOA) et **Smart Accounts** programables. **UserOperations**, **Paymasters** (qui paient le gas pour l'utilisateur), et le modèle d'un wallet sans clé privée traditionnelle.

### Étape 5 : Assistance LLM (SC-11, 45 min)

Le LLM comme outil de développeur Solidity : **prompting** efficace pour smart contracts, **détection de vulnérabilités**, **génération de documentation NatSpec**, intégration de l'API **Anthropic Claude**, et alternative open-source avec un **LLM local** (Qwen). Pont avec les notebooks Lean-7/8/9 (même paradigme d'assistance LLM pour la preuve formelle).

---

## Prérequis

### Par notebook

| Notebook | Fondations requises | Dépendances |
|----------|---------------------|-------------|
| SC-7 Token-Standards | SC-3 a SC-6 complètes ([01-Solidity-Foundation](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)) | `web3`, `py-solc-x`, OpenZeppelin |
| SC-8 DeFi-Primitives | SC-7 complète | idem |
| SC-9 DAO-Governance | SC-7 + SC-8 complètes ; ERC-20 et délégation | idem |
| SC-10 Account-Abstraction | SC-7 a SC-9 complètes ; modèle EOA vs contrat | idem ; ERC-4337 (@account-abstraction) |
| SC-11 LLM-Assisted | SC-3 a SC-6 complètes | clé API OpenAI/Anthropic (optionnel : Qwen local) |

### Configuration requise

- **Python 3.10+** avec `pip install web3 py-solc-x`
- **Foundry installe** : `anvil` sur le PATH. Lancez `anvil` dans un terminal avant d'exécuter les cellules (SC-7 a SC-10 s'y connectent en local).
- **SC-11** : clé API lue depuis l'environnement (`os.getenv`) pour Claude/OpenAI ; un LLM local Qwen peut remplacer l'API cloud. Aucune clé committee dans le notebook.
- Aucun faucet, aucun ETH réel nécessaire pour SC-7 a SC-10 : tout tourne sur le noeud local `anvil`.

---

## Ponts inter-séries

| Série | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte, parcours global, glossaire |
| [01-Solidity-Foundation](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb) | Prérequis | SC-3..6 (syntaxe, types, fonctions, héritage, errors/events) |
| [03-Foundry-Testing](../03-Foundry-Testing/) | Suite | SC-12+ (tests Foundry, fuzzing, vérification formelle) |
| [GameTheory](../../../GameTheory/) | SC-9 (DAO) | Théorème d'Arrow : limites des systèmes de vote on-chain (cf `social_choice_lean/Arrow.lean`) |
| [SymbolicAI/Lean](../../Lean/) | SC-11 (LLM) | Meme paradigme d'assistance LLM (Lean-7/8/9) applique a la preuve formelle |

---

## Points de vigilance (exécution sur anvil)

- **Lancer `anvil` avant l'exécution** de SC-7 a SC-10 : chaque notebook se connecte a un noeud local. Sans `anvil` actif, les cellules de déploiement echouent en `ConnectionRefusedError`.
- **SC-7 Token-Standards** : utilise les contrats OpenZeppelin (deja vendores dans `foundry-lib/`) ; la compilation se fait via `py-solc-x` avec le compilateur versionne.
- **SC-8 DeFi-Primitives** : les swaps et le price impact sont calcules sur des reserves initiales petites pour rester pédagogiques -- les effets de slippage y sont exageres volontairement.
- **SC-10 Account-Abstraction** : depend d'`@account-abstraction` et `@openzeppelin` (resolus via `foundry-lib/`). Le déploiement invoque le `EntryPoint` officiel ERC-4337 sur anvil.
- **SC-11 LLM-Assisted** : les cellules qui appelent l'API Claude/OpenAI s'affranchissent proprement si la clé est absente (mode mock ou skip disclosed) ; les outputs committes refletent un run realiste.

---

## Ressources

- **ERC-20** (Vogelsteller, Buterin, 2015) ; **ERC-721** (Shirley, Evans, Castano, 2018) ; **ERC-1155** (Radomski, Cooke, 2018) -- standards de tokens Ethereum (EIPs).
- **ERC-4337** (Ferro, Kolinkin, et al., 2021) -- Account Abstraction via entry point contract.
- **Uniswap V2** (Adams, Zinsmeister, Robinson, 2020) -- core whitepaper : AMM a produit constant x*y=k.
- **Foundry Book** (Foundry contributors) -- `anvil`, `forge`, `cast`. book.getfoundry.sh.
- Voir aussi les références transversales dans le [README parent de la série](../README.md).

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette deuxième sous-série quitte la syntaxe pour les **cas d'usage réels** d'Ethereum — le passage du « contrat isolé » aux **systèmes composés**. L'arc pédagogique relie cinq briques qui, ensemble, font tourner la finance décentralisée et la gouvernance on-chain :

- **Les standards de tokens** (SC-7) — ERC-20 (fongibles), ERC-721 (NFT), ERC-1155 (multi-tokens), construits sur les contrats sécurisés d'OpenZeppelin. Le point de passage obligé vers DeFi et la gouvernance.
- **Les primitives DeFi** (SC-8) — les Automated Market Makers et la formule à produit constant **x\*y=k**, la construction d'un liquidity pool, et la mesure concrète du price impact et du slippage d'un swap.
- **La gouvernance on-chain** (SC-9) — le vote pondéré par balance de token, la création et l'exécution de propositions, et le timelock qui retarde l'exécution. Pont naturel avec les résultats formels de [GameTheory](../../../GameTheory/) (théorème d'Arrow).
- **L'account abstraction** (SC-10) — l'ERC-4337 : séparation EOA / Smart Accounts programables, UserOperations, Paymasters qui paient le gas, et le modèle d'un wallet sans clé privée traditionnelle.
- **L'assistance LLM** (SC-11) — le LLM comme outil de développeur Solidity (génération, audit, documentation NatSpec), pont avec les notebooks Lean-7/8/9 (même paradigme appliqué à la preuve formelle).

Comme la sous-série 01, chaque concept est illustré par un contrat compilé et déployé réellement sur `anvil`.

### Prochaines étapes

- **Tester ce qu'on a construit** : la suite immédiate est [03-Foundry-Testing](../03-Foundry-Testing/README.md) (SC-12 à SC-14) — tests, fuzzing d'invariants et vérification formelle. On ne peut déployer en production des standards ERC et des pools DeFi sans une assurance sur leurs propriétés.
- **Approfondir la gouvernance** : SC-9 (DAO) mérite d'être relu après [GameTheory/SocialChoice](../../../GameTheory/SocialChoice/README.md) — le théorème d'Arrow y est prouvé formellement, et éclaire les limites de tout système de vote on-chain.
- **La série dans son ensemble** : le [sommaire SmartContracts](../README.md) cartographie les sept sous-séries — celle-ci est le cœur applicatif.

### Le fil rouge

Solidity avancé propose un changement de regard : le smart contract n'est plus un objet isolé, mais une **brique composée dans un système** (tokens + pools + gouvernance + abstraction). Comprendre ces cinq cas d'usage, c'est comprendre que la force d'Ethereum n'est pas un seul contrat mais leur **composition** — et que cette composition exige à la fois des standards partagés (ERC), des mécanismes économiques (AMM), des garde-fous démocratiques (DAO/timelock) et des abstractions ergonomiques (account abstraction), chacun introduisant ses propres compromis que la suite (tests, preuve, déploiement réel) se chargera de sécuriser.
