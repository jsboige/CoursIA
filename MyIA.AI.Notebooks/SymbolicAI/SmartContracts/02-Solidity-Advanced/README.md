# 02-Solidity-Advanced - Standards, DeFi, DAO et Account Abstraction

**Navigation** : [Sommaire de la serie](../README.md) | [<< SC-6 Errors & Events](../01-Solidity-Foundation/SC-6-Errors-Events.ipynb) | [SC-12 Foundry Testing >>](../03-Foundry-Testing/SC-12-Foundry-Testing.ipynb)

Cette deuxieme sous-serie de code (SC-7 a SC-11) quitte la syntaxe pour les **cas d'usage reels** d'Ethereum : les standards de tokens (ERC-20, ERC-721, ERC-1155), les primitives DeFi (AMM a produit constant, liquidity pools), la gouvernance on-chain (votes ponderes, timelock), l'account abstraction (ERC-4337, Smart Accounts, Paymasters), et enfin l'assistance par LLM pour generer, auditer et documenter du Solidity. Comme la sous-serie 01, chaque concept est illustre par un contrat compile et deploye reellement sur `anvil` -- les adresses et receipts dans les outputs sont authentiques.

---

## Notebooks

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 7 | [SC-7-Token-Standards](SC-7-Token-Standards.ipynb) | 50 min | ERC-20, ERC-721, ERC-1155, contrats OpenZeppelin |
| 8 | [SC-8-DeFi-Primitives](SC-8-DeFi-Primitives.ipynb) | 55 min | AMM, formule x*y=k, liquidity pools, price impact, slippage |
| 9 | [SC-9-DAO-Governance](SC-9-DAO-Governance.ipynb) | 45 min | Vote pondere, propositions, timelock |
| 10 | [SC-10-Account-Abstraction](SC-10-Account-Abstraction.ipynb) | 50 min | ERC-4337, UserOperations, Smart Account, Paymasters |
| 11 | [SC-11-LLM-Assisted](SC-11-LLM-Assisted.ipynb) | 45 min | LLMs (Claude/GPT) pour generer, auditer, documenter du Solidity |

**Total** : 5 notebooks, ~4h05.

---

## Parcours d'apprentissage

### Etape 1 : Standards de tokens (SC-7, 50 min)

Implementation des trois standards fondateurs : **ERC-20** (tokens fongibles), **ERC-721** (NFTs) et **ERC-1155** (multi-tokens), en s'appuyant sur les contrats securises d'OpenZeppelin. Cette etape est le point de passage obligé vers DeFi et la gouvernance.

### Etape 2 : Primitives DeFi (SC-8, 55 min)

Le coeur de la finance decentralisee : les **Automated Market Makers** et la formule a produit constant **x*y=k**. On construit un liquidity pool simple, puis on mesure concrètement le **price impact** et le **slippage** d'un swap. Cette etape mobilise les interfaces et appels externes Solidity vus en SC-5.

### Etape 3 : Gouvernance on-chain (SC-9, 45 min)

Les mecanismes de **vote pondere** (par balance de token), la creation et l'execution de **propositions**, et le **timelock** qui retarde l'execution pour laisser le temps de reagir. Pont naturel avec les resultats formels de la serie GameTheory (theoreme d'Arrow).

### Etape 4 : Account Abstraction (SC-10, 50 min)

L'ERC-4337 : separation entre comptes externes (EOA) et **Smart Accounts** programables. **UserOperations**, **Paymasters** (qui paient le gas pour l'utilisateur), et le modele d'un wallet sans cle privee traditionnelle.

### Etape 5 : Assistance LLM (SC-11, 45 min)

Le LLM comme outil de developpeur Solidity : **prompting** efficace pour smart contracts, **detection de vulnerabilites**, **generation de documentation NatSpec**, integration de l'API **Anthropic Claude**, et alternative open-source avec un **LLM local** (Qwen). Pont avec les notebooks Lean-7/8/9 (meme paradigme d'assistance LLM pour la preuve formelle).

---

## Prerequis

### Par notebook

| Notebook | Fondations requises | Dependances |
|----------|---------------------|-------------|
| SC-7 Token-Standards | SC-3 a SC-6 completes ([01-Solidity-Foundation](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)) | `web3`, `py-solc-x`, OpenZeppelin |
| SC-8 DeFi-Primitives | SC-7 complete | idem |
| SC-9 DAO-Governance | SC-7 + SC-8 completes ; ERC-20 et delegation | idem |
| SC-10 Account-Abstraction | SC-7 a SC-9 completes ; modele EOA vs contrat | idem ; ERC-4337 (@account-abstraction) |
| SC-11 LLM-Assisted | SC-3 a SC-6 completes | cle API OpenAI/Anthropic (optionnel : Qwen local) |

### Configuration requise

- **Python 3.10+** avec `pip install web3 py-solc-x`
- **Foundry installe** : `anvil` sur le PATH. Lancez `anvil` dans un terminal avant d'executer les cellules (SC-7 a SC-10 s'y connectent en local).
- **SC-11** : cle API lue depuis l'environnement (`os.getenv`) pour Claude/OpenAI ; un LLM local Qwen peut remplacer l'API cloud. Aucune cle committee dans le notebook.
- Aucun faucet, aucun ETH reel necessaire pour SC-7 a SC-10 : tout tourne sur le noeud local `anvil`.

---

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte, parcours global, glossaire |
| [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) | Prerequis | SC-3..6 (syntaxe, types, fonctions, heritage, errors/events) |
| [03-Foundry-Testing](../03-Foundry-Testing/) | Suite | SC-12+ (tests Foundry, fuzzing, verification formelle) |
| [GameTheory](../../GameTheory/) | SC-9 (DAO) | Theoreme d'Arrow : limites des systemes de vote on-chain (cf `social_choice_lean/Arrow.lean`) |
| [SymbolicAI/Lean](../Lean/) | SC-11 (LLM) | Meme paradigme d'assistance LLM (Lean-7/8/9) applique a la preuve formelle |

---

## Points de vigilance (execution sur anvil)

- **Lancer `anvil` avant l'execution** de SC-7 a SC-10 : chaque notebook se connecte a un noeud local. Sans `anvil` actif, les cellules de deploiement echouent en `ConnectionRefusedError`.
- **SC-7 Token-Standards** : utilise les contrats OpenZeppelin (deja vendores dans `foundry-lib/`) ; la compilation se fait via `py-solc-x` avec le compilateur versionne.
- **SC-8 DeFi-Primitives** : les swaps et le price impact sont calcules sur des reserves initiales petites pour rester pedagogiques -- les effets de slippage y sont exageres volontairement.
- **SC-10 Account-Abstraction** : depend d'`@account-abstraction` et `@openzeppelin` (resolus via `foundry-lib/`). Le deploiement invoque le `EntryPoint` officiel ERC-4337 sur anvil.
- **SC-11 LLM-Assisted** : les cellules qui appelent l'API Claude/OpenAI s'affranchissent proprement si la cle est absente (mode mock ou skip disclosed) ; les outputs committes refletent un run realiste.

---

## Ressources

- **ERC-20** (Vogelsteller, Buterin, 2015) ; **ERC-721** (Shirley, Evans, Castano, 2018) ; **ERC-1155** (Radomski, Cooke, 2018) -- standards de tokens Ethereum (EIPs).
- **ERC-4337** (Ferro, Kolinkin, et al., 2021) -- Account Abstraction via entry point contract.
- **Uniswap V2** (Adams, Zinsmeister, Robinson, 2020) -- core whitepaper : AMM a produit constant x*y=k.
- **Foundry Book** (Foundry contributors) -- `anvil`, `forge`, `cast`. book.getfoundry.sh.
- Voir aussi les references transversales dans le [README parent de la serie](../README.md).
