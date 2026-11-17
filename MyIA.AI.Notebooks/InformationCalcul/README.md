---
pagetitle: "Information et calcul"
---

[← Notebooks](../README.md)

# Information et calcul

Ce hub rassemble les **séries sœurs** qui, prises séparément, diluent la thématique IA du dépôt — mais qui, groupées, la nourrissent toutes. « Information et calcul » est le territoire commun où l'on **mesure, code, compresse, transforme et protège** l'information : de l'entropie de Shannon aux bornes de la complexité, du codage de canal à la cryptographie, en passant par le signal en domaine fréquentiel. C'est le socle théorique sur lequel reposent les séries d'apprentissage automatique du dépôt.

Le modèle est celui de [SymbolicAI](../SymbolicAI/README.md) : un dossier-hub qui fédère des sous-séries, chacune avec son README et sa progression.

## Pourquoi ce hub

L'IA du dépôt ne se réduit pas à l'apprentissage automatique. Une grande partie de ses fondations — mesurer l'information, la coder, la compresser, la protéger, borner le calcul — vit dans des disciplines que l'on range ici. Le critère de ce hub est **le premier niveau de l'arborescence** : une série sœur se range dans un hub, elle ne s'ajoute pas à la racine. Aucune série ni sous-série nouvelle ne naît sans GO écrit du mainteneur.

**Physique reste hors du hub**, au premier niveau : elle est déjà un hub de six sous-séries à elle seule. Ce README renvoie explicitement vers ses sous-séries [Information quantique](../Physique/README.md) et [Constructeur](../Physique/README.md), qui font le pont entre les deux mondes.

## Les sous-séries

| Sous-série | Ce qu'elle apporte aux séries d'IA | État |
|---|---|---|
| [Complexity](../Complexity/README.md) | Les bornes du calcul : ce qu'une machine peut décider, optimiser, simuler — machines de Turing, hiérarchie des complexités, le P/NP de l'IA | sur `main` — déplacement vers le hub à venir |
| [Compression](../Compression/README.md) | L'entropie et le codage : Huffman, les arborescences, ce que l'on peut contracter sans perte — la frontière information/pression | sur `main` — déplacement vers le hub à venir |
| **InformationTheory** | Mesurer l'information : entropie, information mutuelle, distance de Hamming, codes correcteurs — et le **codage de canal** (théorie des codes) en branche | en construction (carnets en PR) |
| **SignalProcessing** | Le signal en domaine fréquentiel : la FFT et la représentation qui sous-tend le traitement des représentations, pont vers le neuronal | en construction (carnets en PR) |
| **Cryptography** | Protéger l'information : hachage, chiffrement symétrique, HMAC, canal adversarial, post-quantique, preuves à divulgation nulle — la confiance informationnelle, pont vers [SmartContracts](../SymbolicAI/SmartContracts/README.md) | en construction (carnets en PR) |

Deux sous-séries sont encore **à ouvrir** : **Automates et langages** (automates finis, expressions régulières, machines de Turing, décidabilité) et **Algorithmique** (en attente de l'archivage de sa source de référence). Une progression écrite dans l'Epic de chacune les ouvrira.

## Le parcours

Chaque sous-série est autonome et se lit par ses numéros, comme n'importe quelle série du dépôt. Le fil rouge du hub est **la chaîne information → calcul** :

- **mesurer** l'information : InformationTheory (entropie, information mutuelle) et Compression (l'entropie comme borne de codage) ;
- **coder** l'information : InformationTheory — codes correcteurs, codage de canal ;
- **transformer** le signal : SignalProcessing (domaine fréquentiel) ;
- **borner** le calcul : Complexity (ce que l'on peut et ne peut pas calculer) ;
- **protéger** l'information : Cryptography (du canal bruité au canal adversarial).

Un lecteur qui suit une seule sous-série en couvre une facette ; c'est en les croisant qu'il voit l'information circuler — mesurée, codée, protégée — jusqu'à la frontière du calculable.

## Les ponts vers Physique

Physique reste au premier niveau, mais deux de ses sous-séries font explicitement le pont avec ce hub :

- **Information quantique** — l'information quantique est l'extension, vers le quantique, de la théorie de l'information classique traitée ici : [Physique → Information quantique](../Physique/README.md) ;
- **Constructeur** — la construction de systèmes calculatoires, du déterministe au physique : [Physique → Constructeur](../Physique/README.md).

## Ce que ce hub ne fait pas

Il ne crée ni arborescence vide ni quota de carnets. Une sous-série commence par une **progression écrite** dans le body de son Epic — carnets, outils, renvois, sans répéter les séries sœurs — puis reçoit le GO du mainteneur, et seulement alors les carnets, dans `InformationCalcul/<sous-série>/`. Le catalogue et les blocs `CATALOG-STATUS` sont régénérés par l'automatisation, jamais à la main.
