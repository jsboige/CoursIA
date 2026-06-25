# 04-Privacy-Cryptography - Preuves Zero-Knowledge, Chiffrement Homomorphe et Vote Verifiable

**Navigation** : [Sommaire de la serie](../README.md) | [<< SC-14 Formal Verification](../03-Foundry-Testing/SC-14-Formal-Verification.ipynb) | [SC-18 Vyper >>](../05-Alternative-Chains/SC-18-Vyper.ipynb)

Cette quatrieme sous-serie (SC-15 a SC-17) explore la cryptographie avancee au service de la confidentialite sur blockchain : les **preuves a divulgation nulle** (Zero-Knowledge Proofs), le **chiffrement homomorphe** (calcul sur donnees chiffrees), et le **vote electronique de bout en bout verifiable** (E2E). Ces notebooks implementent les protocoles cryptographiques pour de vrai en Python (`pycryptodome`, `phe`, `tenseal`), avec la crypto Paillier et Schnorr reelement executee dans les outputs committes.

---

## Notebooks

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 15 | [SC-15-Zero-Knowledge-Proofs](SC-15-Zero-Knowledge-Proofs.ipynb) | 60 min | ZKP, protocole de Schnorr from scratch, Fiat-Shamir, Sigma protocols, Chaum-Pedersen |
| 16 | [SC-16-Homomorphic-Encryption](SC-16-Homomorphic-Encryption.ipynb) | 50 min | Chiffrement homomorphe (PHE/SHE/FHE), Paillier (`phe`), CKKS (`tenseal`), partage de secrets de Shamir |
| 17 | [SC-17-E2E-Verifiable-Voting](SC-17-E2E-Verifiable-Voting.ipynb) | 45 min | Paradoxe du vote electronique, vote a la main (Paillier + ZKP), bulletin board, ElectionGuard |

**Total** : 3 notebooks, ~2h35.

SC-17 ne présente pas une primitive de plus : il **assemble** les preuves à divulgation nulle (SC-15) et le chiffrement homomorphe (SC-16) pour résoudre le paradoxe du vote électronique — concilier **anonymat** et **vérifiabilité**. Ce diagramme en fait la synthèse : chaque primitive assure l'une des deux propriétés opposées du paradoxe, et le capstone SC-26 les réutilisera toutes deux.

```mermaid
flowchart LR
    SC15["SC-15 · Preuves à divulgation nulle<br/><b>prouver sans révéler</b><br/>Schnorr · Fiat-Shamir · Chaum-Pedersen"]
    SC16["SC-16 · Chiffrement homomorphe<br/><b>calculer sans déchiffrer</b><br/>Paillier · CKKS · Shamir"]
    SC17(("SC-17 · Vote E2E vérifiable<br/><b>anonymat + vérifiabilité</b>"))
    SC26["SC-26 · Capstone<br/>DApp de vote complète<br/>(réutilise ZKP + Paillier)"]
    SC15 -- "vérifiabilité<br/>(preuve de validité du bulletin)" --> SC17
    SC16 -- "anonymat<br/>(tally sur chiffré)" --> SC17
    SC17 --> SC26
```

---

## Parcours d'apprentissage

### Etape 1 : Preuves Zero-Knowledge (SC-15, 60 min)

Les **preuves a divulgation nulle** : prouver la connaissance d'un secret sans le reveler. Implementation from scratch du **protocole de Schnorr** (preuve de connaissance d'un logarithme discret), transformation de **Fiat-Shamir** (rendre un protocole interactif non-interactif via oracle aleatoire), et exploration des **Sigma protocols** avec le protocole de **Chaum-Pedersen**. Crypto `pycryptodome` reelle dans les outputs.

### Etape 2 : Chiffrement homomorphe (SC-16, 50 min)

Le calcul sur donnees chiffrees : trois variantes (**PHE** partiellement homomorphe, **SHE** partiellement, **FHE** completement). Schema de **Paillier** (additivement homomorphe) avec `phe`, schema **CKKS** pour l'arithmetique approchee avec `tenseal`, et **calcul multipartite securise** (MPC) via le partage de secrets de **Shamir**. Paillier et Shamir sont executes reellement ; CKKS/TenSEAL depend d'une installation optionnelle.

### Etape 3 : Vote verifiable (SC-17, 45 min)

Le **paradoxe du vote electronique** : concilier **anonymat** et **verifiabilite**. Construction d'un systeme de vote a la main combinant **Paillier + ZKP**, implementation d'un **bulletin board** publiquement verifiable, et decouverte d'**ElectionGuard** (Microsoft), l'etat de l'art en vote E2E verifiable. Le tally (3+2+2=7) est corroboré dans les outputs ; la partie ElectionGuard est disclosed comme simulation conceptuelle.

---

## Prerequis

### Par notebook

| Notebook | Fondations requises | Dependances |
|----------|---------------------|-------------|
| SC-15 Zero-Knowledge-Proofs | Arithmetique modulaire de base ; Python | `pycryptodome` (nombres premiers), `hashlib` (stdlib) |
| SC-16 Homomorphic-Encryption | Python ; notions de crypto | `phe` (python-paillier), `tenseal` (optionnel), `mpyc` (optionnel) |
| SC-17 E2E-Verifiable-Voting | [SC-15](SC-15-Zero-Knowledge-Proofs.ipynb) + [SC-16](SC-16-Homomorphic-Encryption.ipynb) completes | `phe`, `pycryptodome`, `electionguard` (optionnel SOTA) |

### Configuration requise

- **Python 3.10+** avec :
  - `pip install pycryptodome` (SC-15 grands nombres premiers, SC-17)
  - `pip install phe` (SC-16 Paillier, SC-17)
  - `pip install tenseal` (SC-16 CKKS — **optionnel**, depend d'une toolchain C++ ; sans lui, la partie CKKS tourne en repli disclose)
  - `pip install mpyc` (SC-16 MPC — optionnel)
  - `pip install electionguard` (SC-17 SOTA — optionnel)
- Aucune blockchain, aucun faucet necessaire : la crypto tourne en Python pur.

---

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [SmartContracts (parent)](../README.md) | Vue d'ensemble | Contexte, parcours global, glossaire |
| [03-Foundry-Testing](../03-Foundry-Testing/SC-12-Foundry-Testing.ipynb) | Predecesseur | SC-12..14 (tests Foundry, fuzzing, verification formelle) |
| [05-Alternative-Chains](../05-Alternative-Chains/SC-18-Vyper.ipynb) | Suite | SC-18..22 (Vyper, XRP, Bitcoin, Move, Solana) |
| [06-Real-World](../06-Real-World/SC-23-Cross-Chain.ipynb) | Capstone | SC-23..26 mobilisent ZKP + chiffrement homomorphe (projet final) |

---

## Points de vigilance (dependances cryptographiques)

- **Paillier + Schnorr executes reellement** (SC-15, SC-16, SC-17) : les outputs committes refletent une vraie execution crypto `phe`/`pycryptodome`. Les parametres (cles, challenges, reponses) sont authentiques.
- **CKKS / TenSEAL (SC-16) optionnel** : si `tenseal` n'est pas installe, la section CKKS tourne en repli honnetement disclose (message `TenSEAL non installe`), avec des plages d'erreur illustrees. Audit #3164 a verifie que les nombres measures au-dessus de ce repli sont honnetement documentes (PR #3382).
- **ElectionGuard (SC-17)** : la partie SOTA est disclose comme **simulation conceptuelle** (ElectionGuard requiert un setup lourd) ; le vote a la main Paillier+ZKP est lui reellement execute.
- **ZKP interactif vs non-interactif** : SC-15 implemente les deux formes ; verifier que la transformation Fiat-Shamir produit bien un proof non-transferable.

---

## Ressources

- **Schnorr, C.-P. (1991)** -- "Efficient Signature Generation by Smart Cards", *Journal of Cryptology* 4(3). Protocole de Schnorr.
- **Fiat, A., & Shamir, A. (1987)** -- "How To Prove Yourself: Practical Solutions to Identification and Signature Problems", *CRYPTO 1986*, LNCS 263. Transformation Fiat-Shamir.
- **Chaum, D., & Pedersen, T. (1993)** -- "Wallet Databases with Observers", *CRYPTO 1992*. Protocole Chaum-Pedersen.
- **Paillier, P. (1999)** -- "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes", *EUROCRYPT 1999*. Schema de Paillier (additivement homomorphe).
- **Shamir, A. (1979)** -- "How to Share a Secret", *Communications of the ACM* 22(11). Partage de secrets.
- **ElectionGuard** (Microsoft, 2019) -- specification du vote E2E verifiable. github.com/microsoft/electionguard.
- Voir aussi les references transversales dans le [README parent de la serie](../README.md).

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette quatrième sous-série explore la **cryptographie avancée au service de la confidentialité** sur blockchain. L'arc pédagogique attaque un par un les paradoxes qui rendent la vie privée difficile sur une chaîne publique :

- **Les preuves à divulgation nulle** (SC-15) — prouver la connaissance d'un secret sans le révéler. Implémentation from scratch du **protocole de Schnorr** (preuve de connaissance d'un logarithme discret), transformation de **Fiat-Shamir** (rendre un protocole interactif non-interactif via oracle aléatoire), et **Sigma protocols** avec **Chaum-Pedersen**.
- **Le chiffrement homomorphe** (SC-16) — le calcul sur données chiffrées : variantes PHE/SHE/FHE, schéma de **Paillier** (additivement homomorphe) avec `phe`, schéma **CKKS** pour l'arithmétique approchée, et calcul multipartite sécurisé via le partage de secrets de **Shamir**. Paillier et Shamir sont exécutés réellement.
- **Le vote vérifiable de bout en bout** (SC-17) — le **paradoxe du vote électronique** : concilier **anonymat** et **vérifiabilité**. Construction d'un système de vote combinant Paillier + ZKP, implémentation d'un bulletin board publiquement vérifiable, et découverte d'**ElectionGuard** (Microsoft), l'état de l'art.

La crypto `pycryptodome` et `phe` est réellement exécutée dans les outputs committés (Paillier, Schnorr, Shamir) ; les dépendances optionnelles (CKKS/TenSEAL, ElectionGuard) tournent en repli honnêtement disclosed.

### Prochaines étapes

- **Quitter la EVM** : la suite est [05-Alternative-Chains](../05-Alternative-Chains/README.md) (SC-18 à SC-22), qui élargit le horizon à Vyper, XRP, Bitcoin, Move et Solana.
- **Le capstone** : [06-Real-World / SC-26](../06-Real-World/SC-26-Final-Project.ipynb) réutilisera directement ZKP (SC-15) et Paillier (SC-16) dans une DApp de vote complète — ces primitives prennent tout leur sens assemblées.
- **La série dans son ensemble** : le [sommaire SmartContracts](../README.md) cartographie les six sous-séries — celle-ci est le socle cryptographique.

### Le fil rouge

La cryptographie de confidentialité propose un changement de regard sur la transparence : ne plus opposer **confidentialité** et **vérifiabilité** comme un compromis, mais les **réconcilier par la cryptographie**. Les preuves à divulgation nulle (prouver sans révéler), le chiffrement homomorphe (calculer sans déchiffrer) et le vote E2E (anonymat + vérifiabilité) sont trois variations du même idéal : faire confiance à la **preuve mathématique** plutôt qu'à l'**autorité** — un idéal particulièrement précieux sur une chaîne publique où chaque transaction est, par défaut, transparente.
