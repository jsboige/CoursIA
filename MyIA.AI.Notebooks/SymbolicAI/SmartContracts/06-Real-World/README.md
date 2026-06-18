# 06-Real-World - SmartContracts en Production

**Navigation** : [Sommaire de la serie](../README.md) | [<< SC-22 Solana & Anchor](../05-Alternative-Chains/SC-22-Solana-Anchor.ipynb)

La derniere sous-serie SmartContracts (SC-23 a SC-26) fait le passage de la theorie au deploiement reel. On quitte le bac a sable `anvil` local pour affronter des reseaux publics : testnets Ethereum/XRP, mainnets L2 (Base, Polygon), ponts cross-chain Chainlink CCIP, et un projet capstone qui combine vote, chiffrement homomorphique, preuve ZKP et tests Foundry.

Ces notebooks supposent que les cles API et private keys sont lues depuis l'environnement (`.env`, `os.getenv`) -- ils ne s'executent pas end-to-end sans configuration externe (faucet testnet, cle Infura/Alchemy, ETH sur L2). Les outputs committes documentent honnetement ce qui se passe quand la configuration est absente (messages `DEPLOYER_PRIVATE_KEY non configure`, simulations conceptuelles disclosees), et ce qui a reellement tourne quand elle est presente.

---

## Notebooks

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 23 | [SC-23-Cross-Chain](SC-23-Cross-Chain.ipynb) | ~45 min | Interoperabilite, Chainlink CCIP, bridge simple, securite cross-chain |
| 24 | [SC-24-Testnet-Deploy](SC-24-Testnet-Deploy.ipynb) | ~50 min | Sepolia via Alchemy/Infura, faucet, deploiement + interaction testnet, XRP Testnet via xrpl-py |
| 25 | [SC-25-Mainnet-Deploy](SC-25-Mainnet-Deploy.ipynb) | ~40 min | Choix L2 (Base/Polygon/Arbitrum), estimation de cout, deploiement mainnet, checklist securite, verification explorateur |
| 26 | [SC-26-Final-Project](SC-26-Final-Project.ipynb) | ~90 min | Capstone : vote Solidity + chiffrement Paillier + preuve ZKP + deploiement anvil/testnet + tests Foundry |

---

## Parcours d'apprentissage

### Phase 1 : Interoperabilite (SC-23, ~45 min)

Pourquoi deplacer un actif ou un message d'une chaine a l'autre, comment Chainlink CCIP fait transituer des donnees on-chain de maniere verifiable, et ou se cachent les attaques cross-chain (reentrancy de bridge, message spoofing). Le notebook reste en mode source-as-strings (les contrats CCIP sont lus comme texte pedagogique, non deployes).

### Phase 2 : Deploiement public (SC-24 + SC-25, ~1h30)

Le coeur metier de la sous-serie. SC-24 deploye sur Sepolia (Ethereum testnet) et envoie des transactions sur le XRP Testnet ; SC-25 monte en gamme vers un mainnet L2 (Base, chain_id 8453) ou un deploiement coute quelques centimes. Les deux notebooks couvrent le cycle complet : connexion RPC, wallet, gas, broadcast, verification.

> **Cout reel** : SC-25 sur Base/Polygon coute ~$0.01-0.50 par deploiement, contre des dizaines de dollars sur Ethereum L1. C'est le motif pedagogique des L2 : meme securite (settlement L1), cout divisé par 100-1000x.

### Phase 3 : Capstone (SC-26, ~90 min)

SC-26 assemble toute la serie (SC-0..25) en une DApp de vote complete : smart contract de gouvernance (cf SC-9), chiffrement homomorphique des bulletins via Paillier (cf SC-16-17), preuve zero-knowledge de validite du bulletin (cf SC-15), deploiement sur anvil puis testnet (cf SC-24), tests Foundry (cf SC-12-14). C'est le notebook de cloture -- il suppose tous les autres acquis.

---

## Prerequis

### Par notebook

| Notebook | Prerequis | Dependances |
|----------|-----------|-------------|
| SC-23 Cross-Chain | SC-3..SC-8 (Solidity), notions de bridges | Compte testnet Sepolia |
| SC-24 Testnet-Deploy | SC-2 (Setup web3.py), SC-3 (Solidity Basics) | `web3 py-solc-x xrpl-py python-dotenv` + cle API Alchemy/Infura |
| SC-25 Mainnet-Deploy | SC-24 complete | `web3 py-solc-x python-dotenv` + ETH sur Base/Polygon (~$0.01-0.50) |
| SC-26 Final-Project | SC-0..25 (toute la serie), en particulier SC-9/SC-15/SC-16-17/SC-24 | Foundry (forge, anvil), web3, pycryptodome |

### Configuration requise

Ces notebooks ne s'executent pas sans configuration externe. Variables d'environnement attendues (via `.env`, jamais inline dans le code) :

- `ALCHEMY_API_KEY` ou `INFURA_API_KEY` -- endpoint RPC Sepolia/Base
- `DEPLOYER_PRIVATE_KEY` -- wallet de deploiement (testnet ou L2 mainnet)
- XRP Testnet : wallet + seed generes via faucet XRP

Sans ces variables, les notebooks tournent en mode degrade et les outputs committes le documentent (messages `non configure`, `Interaction non disponible`).

---

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [05-Alternative-Chains](../05-Alternative-Chains/SC-22-Solana-Anchor.ipynb) | Precedent | Solana, Move, Vyper, XRP -- les blockchains abordees dans SC-24/25 |
| [03-Foundry-Testing](../03-Foundry-Testing/) | Tests | SC-26 capstone utilise forge/anvil |
| [04-Privacy-Cryptography](../04-Privacy-Cryptography/) | Crypto | SC-26 reutilise Paillier (SC-16-17) et ZKP (SC-15) |
| [SmartContracts parent](../README.md) | Vue d'ensemble | Progression complete SC-0..SC-26 |

---

## Points de vigilance (deploiement reel)

- **Jamais de cle privee dans le code** : `os.getenv("DEPLOYER_PRIVATE_KEY")` sans valeur par defaut. Un secret inline = leak (cf `.claude/rules/secrets-hygiene.md`).
- **Testnet avant mainnet** : SC-24 (Sepolia, gratuit) systematiquement avant SC-25 (Base/Polygon, payant).
- **Gas est un cout reel sur mainnet** : SC-25 sur L2 reste bon marche, mais un deploiement foire multiplie le cout. La checklist de SC-25 (audit, verification explorateur, proxy pattern) existe pour ca.
- **Verification de contrat** : apres deploiement mainnet, publier le source code sur l'explorateur (Basescan, Polygonscan) pour transparence et interaction depuis le front-end.

---

## Ressources

- [Chainlink CCIP Docs](https://docs.chain.link/ccip) -- cross-chain messaging (SC-23)
- [Sepolia Faucet](https://sepoliafaucet.com/) -- testnet ETH gratuit (SC-24)
- [XRP Ledger Testnet](https://xrpl.org/xrp-test-net-faucets.html) -- faucet XRP (SC-24)
- [Base / Polygon docs](https://docs.base.org/) -- L2 mainnet deployment (SC-25)
- [Basescan](https://basescan.org/) / [Polygonscan](https://polygonscan.com/) -- verification de contrat (SC-25)

Voir aussi les [Ressources Externes du README parent](../README.md#ressources-externes) pour les references academiques transversales (Foundry Book, OpenZeppelin, ElectionGuard).
