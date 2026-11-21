---
pagetitle: "Cryptography"
---

[← Information et calcul](../README.md) · [← Notebooks](../../README.md)

# Cryptographie

Protéger l'information : de la confiance dans un canal à la confiance devant un adversaire. La sous-série couvre, en C# / .NET BCL (0 NuGet), la chaîne complète — hacher et chiffrer, faire passer l'information d'un canal bruité à un canal adversarial, résister aux attaques avancées (chiffrement homomorphe, preuves à divulgation nulle), puis préparer le passage au post-quantique. C'est le pilier **sécurité** du hub [Information et calcul](../README.md) : ce qui fait qu'une information mesurée, codée et transformée reste **digne de confiance** sur le chemin.

## Les carnets

| # | Carnet | Ce qu'il apporte | État |
|---|--------|------------------|------|
| 01 | Hachage, chiffrement symétrique et HMAC (#27084) | Les briques : fonctions de hachage, chiffrement symétrique, intégrité HMAC — la confiance dans un canal | en PR |
| 02 | Du canal bruité au canal adversarial (#27127) | Le passage du bruit à l'adversaire : authentifier, détecter l'altération, ne plus supposer un canal bienveillant | en PR |
| 03 | Chiffrement homomorphe et preuves ZK (#27235) | La crypto avancée : calculer sur des données chiffrées, prouver sans révéler | en PR |
| 04 | [Le post-quantique](Cryptography-04-Post-Quantique-CSharp.ipynb) | Quand Shor casse RSA et ECC : ce qui tombe, ce qui survit, la migration vers la crypto post-quantique | **livré** (cette PR) |

## Le fil

Le fil de la sous-série est **le durcissement progressif de la confiance** : on part d'un canal que l'on suppose honnête (01, les briques), on lui adjoint un adversaire (02), on apprend à lui cacher à la fois la donnée et le fait de l'avoir (03), puis on se prépare au jour où les fondations algébriques d'aujourd'hui s'effondrent sous l'algorithme de Shor (04). Chaque carnet s'appuie sur le précédent et se lit par son numéro.

Le carnet 04 — celui de cette PR — est le premier à être **relogé sous le hub** Information et calcul ; les carnets 01 à 03 y convergent chacun par leur PR.

## Ponts — la même famille, côté chaîne

La série **Smart-Contracts** enseigne plusieurs de ces primitives depuis l'angle d'un protocole **déployé** : là, la preuve doit convaincre un tiers sans rien révéler du secret, et le chiffrement doit protéger un calcul **public**. Ce sont les mêmes équations que celles du carnet 03, avec la contrainte en plus d'un vérificateur qui ne peut pas faire confiance au calculateur.

| Ici, en BCL .NET, from-scratch | Là-bas, sur chaîne |
|---|---|
| Schnorr et RSA jouet, avec leurs témoins négatifs | [SC-15 — Zero-Knowledge Proofs](../../SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs-Python.ipynb) : la preuve appliquée au vote vérifiable |
| l'homomorphisme multiplicatif démontré par rejeu | [SC-16 — Homomorphic Encryption](../../SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-16-Homomorphic-Encryption-Python.ipynb) : le calcul chiffré sur une blockchain |
| le post-quantique prepares par les fondations algebriques d'aujourd'hui | [SmartContracts — index de la série](../../SymbolicAI/SmartContracts/README.md) : le meme invariant de confiance, en production |
