# Compression — sous-série pédagogique

La compression de données **sans perte**, du premier principe (le code préfixe)
jusqu'aux codecs réels et au compromis description/données (MDL). La série se
déploie au format **Origami** : un pli à la fois, chaque pli s'ouvrant à la
livraison du précédent ([EPIC #18706](https://github.com/jsboige/CoursIA/issues/18706)).

Chaque carnet porte le suffixe de son noyau (`-Python`, `-Lean`) — le jumeau
Lean des définitions est prévu par les plis suivants.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un code préfixe optimal sur un alphabet de symboles à fréquences connues (algorithme de Huffman)
2. **Vérifier** la condition de Kraft sur un code arbitraire et reconnaître les codes qui violent la borne
3. **Comparer** les arbres Shannon-Fano et Huffman sur un même corpus pour comprendre l'origine du gain
4. **Calculer** la longueur moyenne d'un code et la confronter à la borne entropique de Shannon sur une source discrète
5. **Encoder et décoder** un message avec un code préfixe arbitraire, et détecter les codes ambigus

## Carnets

| Carnet | Niveau | Contenu |
|---|---|---|
| [Compression-01 — Codes préfixes : de Shannon-Fano à Huffman](Compression-01-ShannonFano-Prefixe-Python.html) | Découverte | codes préfixes, inégalité de Kraft, Shannon-Fano contre Huffman, l'entropie comme borne |

## Position dans le dépôt

La série est une voisine de
[Complexity](../Complexity/README.md) : Complexity traite du coût de
*calculer* une fonction, Compression du coût de *représenter* une information.
Les deux questions se rejoignent dans le compromis temps de calcul contre
taille de sortie — les renvois croisés se posent au fil des plis.

## Environnement

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du
dépôt ([common-commands](../../docs/reference/common-commands.md)).
