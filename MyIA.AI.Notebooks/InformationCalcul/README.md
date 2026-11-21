---
pagetitle: "Information et calcul"
---

[← Notebooks](../README.md)

# Information et calcul

Ce hub rassemble des séries qui posent la même question sous des angles complémentaires : **que peut faire une machine à une information, et à quel coût ?** La mesurer, la contracter sans la perdre, la faire traverser un canal bruité, la protéger contre un adversaire, ou reconnaître les calculs qui dépassent tout budget. Prises séparément, ces disciplines semblent périphériques aux séries d'apprentissage automatique du dépôt ; croisées, elles en sont le socle — un modèle qui apprend est d'abord une machine qui reçoit de l'information, la représente et paie chaque opération.

Le parcours ci-dessous relie donc les séries par leurs **objets**, pas par leur rang dans l'arborescence : l'entropie calculée sur un corpus devient la borne que vise un code, la capacité d'un canal dépend du signal qui le traverse, la sécurité d'un chiffrement repose sur un problème calculatoire difficile, et la complexité de Kolmogorov apparaît deux fois — comme limite de la compression et comme miroir descriptif de la calculabilité.

## Le parcours du lecteur

### 1. Mesurer une information

Toute la chaîne part d'une grandeur : **l'entropie**, le nombre de bits qu'une source produit réellement. Le carnet [Compression-01 — Codes préfixes : Shannon-Fano et Huffman](Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb) la construit sur des corpus exécutables, confronte la longueur moyenne d'un code de Huffman à cette borne et vérifie la condition de Kraft sur l'arbre obtenu. La même grandeur revient chez Complexity en miroir descriptif : [Complexity-07 — complexité de Kolmogorov bornée](Complexity/Complexity-07-KolmogorovBornee-Sequences-Python.ipynb) demande quelles séquences une machine à mémoire limitée peut écrire court.

### 2. Contracter sans perdre

Une fois l'information mesurée, on essaie de l'approcher : [Compression-02 — Huffman canonique](Compression/Compression-02-HuffmanCanonique-Python.ipynb) réduit le code à ses longueurs, [Compression-03 — LZ77](Compression/Compression-03-LZ77-Python.ipynb) transforme les répétitions en références, [Compression-04 — ANS](Compression/Compression-04-ANS-Python.ipynb) porte l'information fractionnaire dans l'état du codeur, et [Compression-06 — MDL et complexité de Kolmogorov](Compression/Compression-06-MDL-Kolmogorov-Python.ipynb) ajoute le coût du modèle à celui des données : la meilleure description minimise la somme. Le carnet [Compression-05 — compression des modèles appris](Compression/Compression-05-MLCompression-Python.ipynb) franchit le pont direct vers les réseaux de neurones du dépôt.

### 3. Reconnaître les murs du calcul

La compression a ses bornes ; le calcul a les siennes. [Complexity-01 — compter des pas](Complexity/Complexity-01-StepCounting-Python.ipynb) remplace la seconde par une unité auditable, [Complexity-02 — vérifier ou trouver](Complexity/Complexity-02-P-NP-Reduction-Python.ipynb) exécute une réduction de bout en bout pour donner un corps à P et NP, et [Complexity-05 — compter est plus dur que vérifier](Complexity/Complexity-05-CountingHarder-Permanent-Python.ipynb) montre la permanente comme frontière du comptage. Le fil continue jusqu'à la simulation d'un circuit quantique ([Complexity-06](Complexity/Complexity-06-Simuler-Circuit-Quantique-Classiquement-Python.ipynb)) et aux automates cellulaires universels ([Complexity-08 — Rule 30 et Rule 110](Complexity/Complexity-08-WolframRule30Aleatoire-Rule110Universelle-Python.ipynb)). Le [README de Complexity](Complexity/README.md) ordonne ce parcours par niveaux — découverte, licence, recherche.

### 4. Traverser un canal, puis le protéger

Deux séries en préparation prolongent ce fil côté canal :

- **InformationTheory** ([progression #27077](https://github.com/jsboige/CoursIA/issues/27077)) traite la théorie de l'information comme objet calculable — entropie conditionnelle, information mutuelle, divergence de Kullback-Leibler, capacité d'un canal — puis la **théorie des codes** : distance de Hamming, code de Hamming (7,4), décodage par syndrome, codes Reed-Solomon, LDPC et turbo. Le premier carnet est en révision dans la [PR #27080](https://github.com/jsboige/CoursIA/pull/27080) ; les suivants attendent l'archivage de leurs sources au gisement bibliographique.
- **SignalProcessing** ([progression #27086](https://github.com/jsboige/CoursIA/issues/27086)) calcule le signal lui-même — échantillonnage, FFT, filtrage, quantification — jusqu'à la formule de Shannon-Hartley qui relie bande passante, rapport signal/bruit et capacité. Le premier carnet est en révision dans la [PR #27087](https://github.com/jsboige/CoursIA/pull/27087).

- **Cryptography** ([progression #27081](https://github.com/jsboige/CoursIA/issues/27081)) change la nature du canal : non plus bruité, mais **adversarial**. Hachage, HMAC, chiffrement symétrique et asymétrique, puis homomorphie, preuves à divulgation nulle et post-quantique — la dureté y repose sur des problèmes proches de Complexity, et la crypto à base de codes fait le pont retour vers InformationTheory. Le premier carnet, en C# / .NET, est en révision dans la [PR #27084](https://github.com/jsboige/CoursIA/pull/27084).

Le pont vers les applications sur chaîne vit dans [SmartContracts](../SymbolicAI/SmartContracts/README.md), où les preuves à divulgation nulle et la confidentialité sont traitées côté systèmes.

## Les liens qui relient les séries

- **Entropie partagée** : Compression-01 la calcule sur une source ; InformationTheory en fera la grandeur centrale (information mutuelle, capacité) ; SignalProcessing en atteint la limite par Shannon-Hartley.
- **Kolmogorov en deux miroirs** : [Compression-06](Compression/Compression-06-MDL-Kolmogorov-Python.ipynb) en fait un principe de choix de modèle (payer modèle + données) ; [Complexity-07](Complexity/Complexity-07-KolmogorovBornee-Sequences-Python.ipynb) le rend calculable sous mémoire bornée.
- **Canal bruité contre canal adversarial** : les codes correcteurs d'InformationTheory corrigent ce que le bruit dégrade ; Cryptography défend ce qu'un adversaire observe. La crypto à base de codes (McEliece) utilise les premiers pour construire la seconde.
- **Sécurité et complexité** : la dureté d'un chiffrement repose sur des problèmes que Complexity mesure — le lien structurel entre les deux séries.
- **Signal et apprentissage** : le spectre et la convolution sont les opérateurs que l'on retrouve derrière les traitements audio et image des séries ML et GenAI ; [Compression-05](Compression/Compression-05-MLCompression-Python.ipynb) fait le pas correspondant côté modèles.

## Ponts vers les séries voisines de Physique

Deux séries voisines prolongent ces questions côté physique :

- [Information quantique](../Physique/InformationQuantique/README.md) — l'entropie et le codage transportés aux états quantiques ;
- [Constructeur](../Physique/Constructeur/README.md) — la construction de systèmes calculatoires, du déterministe au physique.

## Où en est chaque série

| Série | Contenu disponible sur `main` | Suite |
|---|---|---|
| [Complexity](Complexity/README.md) | Parcours complet, des bornes du calcul (machines de Turing, hiérarchie des complexités, le P/NP de l'IA) aux approfondissements de recherche ; plusieurs jumeaux C#. | dans le hub |
| [Compression](Compression/README.md) | Parcours complet des codes préfixes à MDL — Huffman, les arborescences, la frontière information/pression — avec compagnon Lean pour Kraft-McMillan-Huffman et jumeaux C#. | dans le hub |
| **InformationTheory** | Progression écrite et densifiée ([#27077](https://github.com/jsboige/CoursIA/issues/27077)) ; premier carnet en révision ([#27080](https://github.com/jsboige/CoursIA/pull/27080)), pas encore sur `main`. | Carnets 02-03 en circuit ; carnets suivants après archivage des sources. |
| **SignalProcessing** | Progression écrite et densifiée ([#27086](https://github.com/jsboige/CoursIA/issues/27086)) ; premier carnet en révision ([#27087](https://github.com/jsboige/CoursIA/pull/27087)), pas encore sur `main`. | Carnets suivants après archivage des sources. |
| **Cryptography** | Progression écrite ([#27081](https://github.com/jsboige/CoursIA/issues/27081)) ; premier carnet en révision ([#27084](https://github.com/jsboige/CoursIA/pull/27084)), pas encore sur `main`. | Carnets suivants après archivage des sources. |
| **Automates et langages** | Aucun carnet ; progression à ouvrir. | Automates finis, expressions régulières, machines de Turing, décidabilité — en renvoi vers les carnets existants de Complexity, Search, Sudoku et Lean. |
| **Algorithmique** | Aucun carnet ; progression à ouvrir. | Attend l'archivage de sa source de référence au gisement bibliographique. |

Les liens de ce README pointent vers les **chemins actuels** des séries déjà présentes ; ils seront mis à jour lors des déplacements, et le catalogue du dépôt reste généré par l'automatisation.
