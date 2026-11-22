<!--
  FICHIER MANUEL — grille de rédaction, écrite à la main. Ni le catalogue ni
  les scripts de parcours ne produisent ce fichier ; il est référencé depuis
  docs/README.md et depuis les carnets pilotes.
-->

# Grille de rédaction — « intuition avant formalisme »

Une grille courte, applicable au corps d'un carnet de cours : par quoi il
commence, et dans quel ordre la situation, l'intuition et la formalisation
y apparaissent. Elle complète le parcours narratif
[IA Symbolique et Formalisation](symbolic-formalization.md) (issue #15806),
qui dit **dans quel ordre** faire les carnets ; la grille dit **comment chaque
carnet est écrit à l'intérieur**.

## Ce que #15806 a établi

Le parcours « IA Symbolique et Formalisation » fixe trois choses :

- un **fil** — « du symbole à la preuve » : un même objet (un argument, une
  contrainte, un plan) est d'abord *résolu* par un moteur, puis *certifié* par
  une preuve formelle ;
- une **colonne vertébrale** d'étapes, dont chaque ligne dit ce que l'étape
  apporte et ce qu'elle suppose ;
- une **rampe de prérequis** vérifiables en quelques minutes (Python, Jupyter,
  et Lean pour le seul bloc final).

Ce que #15806 ne dit pas : comment un carnet est écrit *à l'intérieur*. Un
parcours peut recommander un carnet dans un ordre parfait ; si le carnet
commence par une définition d'API, l'étudiant qui le suit n'a aucun point
d'appui avant la formalisation. C'est cet écart que la grille comble.

## Ce que la grille ajoute

> Chaque carnet s'ouvre sur une situation concrète, illustrée par une figure
> ou par un calcul que l'étudiant peut refaire à la main. La formalisation
> vient après, et elle prolonge ce qui a déjà été vu.

## Les cinq règles

**R1 — Situation d'abord.** La première section d'un carnet part d'un problème
concret : des objets, des nombres, une question à laquelle on peut répondre
par « oui, non » ou par un nombre. Aucune définition, aucun nom d'API,
aucun appel à l'outil du cours avant que l'étudiant ait vu le problème.

**R2 — Une intuition calculée ou figurée.** L'intuition se montre : une
cellule de code calcule le cas à la main — force brute, énumération, un
compte — ou trace la figure qui le rend visible. Elle n'utilise pas encore
l'outil du cours : l'outil arrive après, sinon on ne voit pas ce qu'il
apporte. Une figure est relue par un agent qui voit avant d'être commitée.

**R3 — Le pont.** Une lecture explicite relie l'intuition à la
formalisation : ce que l'étudiant a compté à la main, l'outil le déclare en
une ligne ; ce que la figure montrait, la contrainte l'exprime. Sans ce pont,
l'intuition est un décor et la formalisation recommence à zéro.

**R4 — Un fil conducteur.** Un carnet suit un objet d'une section à l'autre,
et le lecteur doit pouvoir nommer cet objet : la même instance, la même
contrainte, le même jeu. La question qui ouvre le carnet est celle à
laquelle la dernière section répond.

**R5 — La lecture vient après.** L'interprétation d'une cellule suit la
cellule qu'elle interprète ; une anticipation qui cite un résultat pas encore
produit n'est pas une intuition, c'est une promesse.

## Test d'application

Avant de merger une ouverture de carnet :

- [ ] les premières cellules donnent une situation, pas une définition ;
- [ ] une cellule de calcul ou une figure anticipe la formalisation ;
- [ ] une lecture fait le lien entre les deux ;
- [ ] l'objet suivi d'une section à l'autre est nommé ;
- [ ] la lecture est postérieure à la cellule interprétée.

## Ce qui n'est pas la grille

- Un **résumé du README** en tête de carnet : la situation doit apporter une
  information que le README ne donne pas.
- Un **contexte historique** (« depuis quand la logique propositionnelle
  existe-t-elle ? ») : la grille organise un apprentissage, pas l'histoire d'un
  domaine.
- Un **chiffre sans sortie** : la mesure se fait dans une cellule, la prose ne
  la fige pas.
- Un **récit de correction** : la prose enseigne le domaine, elle ne raconte
  pas d'où vient le texte.
- Une **situation non vérifiable** : elle doit se prêter à un calcul ou à une
  figure, pas seulement à une lecture plausible.

## Pilote — la série SMT / Z3-API

Le pilote porte sur
[SMT/Z3-API](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/), le bloc SMT du
parcours de #15806 — celui qui fait le lien direct entre « le symbole se
résout » et « la preuve se certifie ».

| Carnet | Situation d'ouverture | Intuition | Formalisation qui suit |
|---|---|---|---|
| Z3-01 Introduction | partager dix unités entre deux commandes, l'un strictement plus grand que l'autre | les solutions possibles énumérées à la main, puis tracées dans le plan | `Solver`, `add`, `check`, `model` |
| Z3-02 Sudoku | une grille imprimée, et les candidats d'une case | le nombre de candidats par case vide, après élimination par ligne, colonne et bloc | les trois familles de contraintes, puis la résolution déclarative |
| Z3-03 Tactiques | une chaîne d'implications qui se contredit | l'exploration de toutes les affectations possibles, face à la propagation qui coupe court | `Goal`, `Tactic`, `simplify`, le contrôle de la stratégie |

Chaque ouverture suit le même geste : la situation et son calcul d'abord, la
lecture qui fait le pont, puis la section formalisée déjà présente dans le
carnet. Le fil du carnet est l'objet nommé dans la situation : les dix unités
à partager, la grille de Sudoku, la chaîne d'implications.

## Limites connues

- Le pilote ne touche que le **strand Python** de la série. Les jumeaux C#
  portent le même contenu sous une autre API ; leur portage suit la grille
  dans un lot distinct, pour que la comparaison des deux formulations reste
  possible.
- La grille n'ordonne pas la **densité** des sections formalisées : elle
  règle l'ouverture, pas le niveau de détail.
- Une grille devenue un contrôle automatique de forme produirait des
  ouvertures stéréotypées. Elle reste une prescription de rédaction, appliquée
  à la main et relue par un pair.
