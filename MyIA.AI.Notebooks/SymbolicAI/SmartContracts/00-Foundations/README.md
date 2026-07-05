# 00-Foundations - Origines Cypherpunk et Environnement

**Navigation** : [Sommaire de la série](../README.md) | [SC-3 Solidity Basics >>](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)

La sous-série d'ouverture des SmartContracts (SC-0 a SC-2) pose les deux socles sur lesquels toute la série reposera : le **pourquoi** (les primitives cryptographiques qui font qu'une blockchain tient) et le **comment** (l'environnement de développement). On commence par remonter aux origines cypherpunk -- hachage, arbres de Merkle, preuve de travail, signatures, tables de hachage distribuees -- pour comprendre *pourquoi* une chaîne est immuable et resistante a la falsification. On installe ensuite **Foundry** (`forge`, `cast`, `anvil`), la trousse a outils de référence, puis on connecte **web3.py** + **py-solc-x** a `anvil` pour compiler, déployer et appeler un premier contrat Solidity entierement depuis Python.

A l'issue de cette phase (~2h10), l'environnement est opérationnel et le pattern de compilation/déploiement depuis Python -- réutilise dans tous les notebooks suivants -- est en place. Les notebooks suivants supposent cet environnement installe : Foundry sur le PATH, `web3`/`py-solc-x` disponibles, `anvil` capable de lancer une blockchain locale.

---

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 0 | [SC-0-Cypherpunk-Origins](SC-0-Cypherpunk-Origins.ipynb) | ~60 min | Mouvement cypherpunk, primitives cryptographiques (hash, signatures, PoW), mini-blockchain Python, arbre de Merkle, DHT/Kademlia |
| 1 | [SC-1-Setup-Foundry](SC-1-Setup-Foundry.ipynb) | ~30 min | Installation Foundry (forge/cast/anvil), vérification Solidity, premier projet, compilation + test d'un contrat simple |
| 2 | [SC-2-Setup-Web3py](SC-2-Setup-Web3py.ipynb) | ~40 min | web3.py + py-solc-x, connexion a anvil, compiler/déployer/appeler un contrat depuis Python, pattern réutilisable |

---

## Objectifs d'apprentissage

A l'issue de cette sous-série, vous serez capable de :

1. **Expliquer** les primitives cryptographiques fondatrices (hachage, Merkle, PoW, signatures) et leur role dans l'immutabilité d'une blockchain
2. **Installer** l'environnement de développement complet (Foundry + web3.py + py-solc-x)
3. **Compiler, déployer et appeler** un contrat Solidity depuis Python via anvil
4. **Etablir** le pattern de déploiement réutilisable pour les notebooks suivants

---

## Prérequis

| Notebook | Prérequis |
|----------|-----------|
| SC-0 Cypherpunk Origins | Python 3.10+ (`hashlib` stdlib), `pycryptodome` pour les signatures ; aucune connaissance blockchain préalable |
| SC-1 Setup Foundry | Python 3.10+, curl ou PowerShell, Git |
| SC-2 Setup Web3py | SC-1 complète (anvil installe), Python 3.10+, `pip install web3 py-solc-x` |

---

## Remarques pédagogiques

- **SC-0** travaille les primitives **from scratch en Python** : aucune blockchain externe n'est requise. La mini-blockchain et l'arbre de Merkle sont construits a la main pour rendre la théorie tangible.
- **SC-1 / SC-2** sont des notebooks de *setup* : ils installent et verifient l'environnement. Les outputs committes documentent honnêtement ce qui s'exécute (Foundry installe, anvil lance, contrat compile+déployé) -- ils ne contiennent pas d'erreurs volontaires et s'exécutent de bout en bout une fois les dépendances présentes.
- Le pattern `compile -> deploy -> call` etabli en SC-2 est celui repris dans toute la série (01-Solidity-Foundation et au-dela) : c'est la fondation technique autant que conceptuelle.

---

## Ponts inter-séries

| Série | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte et parcours global de la série |
| [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) | Suite immédiate | SC-3 Solidity Basics demarre après SC-2 |

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette sous-série d'ouverture vous a posé les **deux socles** sur lesquels toute la série SmartContracts reposera. L'arc pédagogique procède du *pourquoi* au *comment* :

- **Le socle conceptuel — les primitives cypherpunk** (SC-0) — vous êtes remonté aux origines de la blockchain en reconstruisant les briques cryptographiques from scratch en Python : le **hachage** (ancrage immuable), l'**arbre de Merkle** (preuve d'inclusion logarithmique), la **preuve de travail** (résistance à la falsification par le coût computationnel), les **signatures numériques** (authentification non-répudiable), et la **table de hachage distribuée / Kademlia** (coordination sans serveur central). Comprendre ces primitives, c'est comprendre *pourquoi* une chaîne est immuable : non par décret, mais parce que chaque brique rend la falsification exponentiellement plus coûteuse que la vérification.
- **Le socle technique — l'environnement Foundry + web3.py** (SC-1, SC-2) — vous avez installé la trousse à outils de référence (**`forge`**, **`cast`**, **`anvil`**) puis connecté **web3.py** + **py-solc-x** à une blockchain locale `anvil`. Le résultat n'est pas anecdotique : le pattern **`compile -> deploy -> call`** établi en SC-2 est celui repris dans *tous* les notebooks suivants. C'est la fondation opérationnelle autant que conceptuelle de la série.
- **La posture honnête** — les notebooks de *setup* documentent ce qui s'exécute réellement (Foundry installé, `anvil` lancé, contrat compilé et déployé), sans erreurs volontaires. La rigueur commence ici : un environnement reproductible est la condition de toute expérimentation sérieuse sur les smart contracts.

### Prochaines étapes

- **Solidity par la pratique** : la suite immédiate est [01-Solidity-Foundation](../01-Solidity-Foundation/README.md) (SC-3 Solidity Basics et au-delà), qui exploite l'environnement désormais opérationnel pour écrire de vrais contrats — variables, fonctions, modifiers, événements, héritage.
- **Approfondir les primitives** : [SC-0-Cypherpunk-Origins](SC-0-Cypherpunk-Origins.ipynb) mérite d'être repris après avoir écrit des contrats en Solidity — la théorie du hachage et de Merkle prend tout son sens quand on manipule `keccak256` et le stockage d'un contrat.
- **La série dans son ensemble** : le [sommaire SmartContracts](../README.md) cartographie les sept sous-séries (Foundations, Solidity Fondements, Solidity Avancé, Foundry-Testing, Privacy/Cryptography, Alternative-Chains, Real-World) — cette sous-série n'est que le seuil.

### Le fil rouge

L'ouverture propose un changement de regard sur les smart contracts : ne plus les voir comme du « code sur une blockchain » magique, mais comme la **composition de primitives cryptographiques dont l'immutabilité est mathématiquement fondée**, manipulées via un environnement d'outils reproductible. Cette sous-série vous a donné le *pourquoi* (les primitives cypherpunk) et le *comment* (Foundry + web3.py), en gardant à l'esprit que le pattern `compile -> deploy -> call` établi ici est le squelette de toute la suite — et que la rigueur de l'environnement est la condition non-négociable de toute expérimentation honnête.

---

## Navigation

[<- Sommaire SmartContracts](../README.md) | [SC-3 Solidity Basics ->](../01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb)
