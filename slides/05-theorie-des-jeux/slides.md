---
theme: ../theme-ia101
title: "Intelligence Artificielle - Théorie des jeux"
info: IA 101 - Théorie des jeux, analyse stratégique, mécanismes
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Théorie des jeux

INTELLIGENCE ARTIFICIELLE -- V

**Analyse stratégique**

- Jeux Bayesiens
- Théorie des mécanismes
  - Jeux differentiels

---
layout: section
---

# Du cours aux notebooks

---
layout: default
---

# La série GameTheory : quatre façons de changer la question

| Si l’on change… | La question devient… | Porte d’entrée |
| --- | --- | --- |
| **la représentation** | Quelles propriétés survivent à une abstraction ou à la composition de deux jeux ? | [Métajeux · synthèse](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-18-Capstone-Metajeux-Python.ipynb) |
| **le temps ou les agents** | La coopération tient-elle si l’on rejoue, si l’on voit le code adverse ou si raisonner coûte ? | [Dynamiques · synthèse](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-19-Capstone-Dynamics-Python.ipynb) |
| **l’unité de décision** | Que peut obtenir un groupe en se formant, et comment répartir le surplus ? | [Coalitions · synthèse](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20-Capstone-Coalitions-Python.ipynb) |
| **la règle collective** | Comment voter ou apparier sans effacer les préférences ni créer de mauvaises incitations ? | [Choix social · synthèse](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-21-Capstone-Choix-Social-Python.ipynb) |

On commence par les décisions individuelles, puis on change une hypothèse à la fois. Les synthèses font le lien avec les expériences et les preuves ; le [guide de la série](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/README.md) détaille les parcours et leurs prérequis.

---
layout: dense
---

# Quand un problème devient-il stratégique ?

- **Un décideur, plusieurs effecteurs.** Il faut coordonner ou synchroniser leurs actions. La planification peut être centralisée (état commun) ou distribuée.
- **Plusieurs décideurs.** Chacun choisit à partir des informations dont il dispose. Le résultat dépend des choix de tous, que leurs objectifs coïncident ou non.
- **Pour modéliser un tour**, nommer les joueurs, leurs actions et leurs gains. Pour modéliser plusieurs tours, préciser aussi qui observe quoi, et quand.

Deux questions traversent le cours : **comment jouer sous des règles données ?** et **quelles règles adopter pour obtenir un meilleur résultat ?**

---
layout: image-overlay
---

# Morra : que garantit une stratégie ?

Chaque joueur montre un ou deux doigts ; l’un veut un total pair, l’autre un total impair. Si l’adversaire sait à l’avance quel nombre vous allez montrer, il peut choisir le total qui lui convient.

<img src="./images/img_001.png" alt="Variantes séquentielles de Morra et valeur garantie quand le premier joueur choisit un mélange" style="display:block; margin:8px auto; height:285px; width:auto; max-width:100%; object-fit:contain;">

**Le maximin** choisit le mélange qui maximise le gain garanti contre la pire réponse. [Modéliser Morra](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-01-Setup-Python.ipynb) · [Calculer le minimax](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05-ZeroSum-Minimax-Python.ipynb).

---
layout: section
---

# Analyse stratégique

---
layout: default
class: gt-matrix
---

# Dilemme du prisonnier : stable, mais pour qui ?

Les deux prisonniers décident sans connaître le choix de l’autre. Chaque case donne les gains **(ligne, colonne)** ; un nombre plus grand correspond à une peine plus courte.

| Joueur ligne ↓ / Joueur colonne → | Se taire | Avouer |
| --- | ---: | ---: |
| **Se taire** | (−1, −1) | (−12, 0) |
| **Avouer** | (0, −12) | (−8, −8) |

<v-click>

**Avouer domine strictement se taire** : contre le silence, 0 vaut mieux que −1 ; contre un aveu, −8 vaut mieux que −12. Le même calcul vaut pour l’autre joueur.

</v-click>

<v-click>

**Stable ne veut pas dire efficace.** Aucun joueur ne gagne à se taire seul en (−8, −8), mais les deux préfèrent (−1, −1) : l’issue des aveux est Pareto-dominée.

</v-click>

*À refaire : [Matrice, dominance et dilemme](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Python.ipynb).*

---
layout: default
class: gt-matrix
---

# Éliminer une stratégie change le jeu restant

**IESDS** — élimination itérée des stratégies strictement dominées. Pour le joueur colonne, comparer les **seconds** gains : quelle colonne peut-on rayer d’emblée ?

| Ligne ↓ / Colonne → | Gauche | Centre | Droite |
| --- | ---: | ---: | ---: |
| **Haut** | (13, 3) | (1, 4) | (7, 3) |
| **Milieu** | (4, 1) | (3, 3) | (6, 2) |
| **Bas** | (−1, 9) | (2, 8) | (8, −1) |

<v-click>

1. **Centre** élimine Droite : 4 > 3, 3 > 2, 8 > −1.
2. Sans Droite, **Milieu** élimine Bas pour le joueur ligne : 4 > −1 et 3 > 2.
3. Sans Bas, **Centre** élimine Gauche ; **Milieu** élimine alors Haut. Il reste **(Milieu, Centre)**.

</v-click>

*À explorer : [Rationalisation et IESDS](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02e-IESDS-Rationalisation-Python.ipynb) · [Définitions en Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-02b-Lean-Definitions-Lean.ipynb).*

---
layout: default
---

# Dominance stricte

> **Énoncé.** Une action strictement dominée ne peut recevoir de poids positif à un équilibre de Nash.

## Stratégie de preuve

À stratégie adverse fixée, transférer sa probabilité à la stratégie dominante améliore strictement le gain.

---
layout: default
class: gt-matrix
---

# Chasse au cerf : être prévisible ne suffit pas

Une **meilleure réponse** maximise mon gain *contre un choix adverse donné*. Une stratégie dominante, elle, est meilleure *quel que soit* ce choix.

| Ligne ↓ / Colonne → | Cerf | Lièvre |
| --- | ---: | ---: |
| **Cerf** | (3, 3) | (0, 2) |
| **Lièvre** | (2, 0) | (1, 1) |

<v-click>

Contre Cerf, mieux vaut Cerf ; contre Lièvre, mieux vaut Lièvre. **Aucune action ne domine**. Les deux diagonales sont des équilibres de Nash purs : en chacune, dévier seul ne paie pas.

</v-click>

<v-click>

**Le problème est de se coordonner.** Les deux joueurs préfèrent chasser le cerf ensemble, mais chasser le lièvre rapporte davantage si l’autre ne coopère pas.

</v-click>

*À calculer : [Meilleures réponses et équilibres de Nash](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium-Python.ipynb).*

---
layout: image-overlay
---

# Repérer Nash dans une matrice à quatre actions

Dans chaque colonne, marquer tous les maxima du **premier** gain ; dans chaque ligne, tous ceux du **second**. Une case doublement marquée est un Nash pur. Garder les ex æquo.

<img src="./images/img_004.png" alt="Matrice Pass, One, Two, Three : les doubles étoiles sont aux quatre cases où les deux joueurs choisissent Pass ou Three" style="display:block; margin:12px auto; height:265px; width:auto; max-width:100%; object-fit:contain;">

Les quatre combinaisons où chacun choisit **Pass** ou **Three** sont des équilibres purs. L’absence de double marque dans un autre jeu n’exclurait pas un équilibre mixte.

---
layout: dense
---

# Stratégies mixtes

Au penalty, annoncer son côté favori aide le gardien. Comment choisir des probabilités plutôt qu’une direction fixe ?

<div v-click="[1, 2]" style="position:absolute; inset:145px 52px 95px; display:grid; grid-template-columns: 32% 1fr; gap:24px; align-items:center;">
  <div><h2>1 · Mélanger</h2><p>Une stratégie mixte attribue une probabilité à chaque action pure. Comme à pile ou face, le tirage reste imprévisible même si sa loi est connue.</p><p>Tout jeu fini possède un équilibre de Nash en stratégies mixtes, éventuellement pures.</p></div>
  <img src="./images/img_006.png" alt="Exemple du penalty : actions pures et mélange" style="width:100%; height:280px; object-fit:contain;">
</div>
<div v-click="[2, 3]" style="position:absolute; inset:145px 52px 95px; display:grid; grid-template-columns: 40% 1fr; gap:24px; align-items:center;">
  <div><h2>2 · Rendre indifférent</h2><p>Si les deux actions sont jouées à l’équilibre, elles doivent rapporter autant. On cherche la probabilité de l’<em>autre</em> joueur qui égalise leurs gains.</p><p>Colonne : 1 − 4u = 2u, donc u = 1/6.<br>Ligne : 5ℓ − 2 = −ℓ, donc ℓ = 1/3.</p></div>
  <img src="./images/img_007.png" alt="Matrice utilisée pour égaliser les gains espérés" style="width:100%; height:280px; object-fit:contain;">
</div>
<div v-click="3" style="position:absolute; inset:145px 52px 95px; display:grid; grid-template-columns: 32% 1fr; gap:24px; align-items:center;">
  <div><h2>3 · Calculer le gain</h2><p>Dans la bataille des sexes, boxe et ballet donnent deux équilibres purs. Au mélange (1/3, 2/3), pondérer chaque case par sa probabilité donne un gain espéré de 2/3 à chacun.</p></div>
  <img src="./images/img_008.png" alt="Bataille des sexes : gains associés aux choix boxe ou ballet" style="width:100%; height:280px; object-fit:contain;">
</div>

<div style="height:390px"></div>

*Notebooks : [GameTheory-05-ZeroSum-Minimax-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05-ZeroSum-Minimax-Python.ipynb) (support mixte, somme nulle) · [GameTheory-04c-NashExistence-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-Python.ipynb) (existence calculee).*

---
layout: dense
---

# Preuves formelles : Nash et minimax en Lean

> **Nash.** Tout jeu fini à ensembles d’actions non vides possède un équilibre en stratégies mixtes.

**Idée de preuve.** Une application continue sur le produit des simplexes corrige les déviations profitables. À un point fixe, aucune ne subsiste.

- [GameTheory-04b-Lean-NashExistence-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04b-Lean-NashExistence-Lean.ipynb)
  - Simplexe standard (compact, convexe) -> point fixe -> equilibre mixte

> **Von Neumann.** Dans un jeu fini à deux joueurs à somme nulle, le maximum du gain garanti égale le minimum que peut imposer l’adversaire.

**Idée de preuve.** Le gain espéré est bilinéaire sur deux simplexes compacts : appliquer le théorème de minimax.

- [GameTheory-05b-Lean-Minimax-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05b-Lean-Minimax-Lean.ipynb)
  - Point de selle via le théorème de Sion.

---
layout: dense
---

# Equilibres de stratégie mixte

<div v-click.hide="1" class="gt-projection-step">
<div>

## Stratégie mixte dominant strictement une pure

- Ex: trois lignes, milieu dominee, calcul des probas

</div>
<img src="./images/img_009.png" alt="Strategie mixte dominant strictement une strategie pure : calcul des probabilites">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Dominance faible

- Domine ou indifferente (>=)
- Elimination iterative, mais reste autres equilibres

</div>
<img src="./images/img_010.png" alt="Dominance faible : elimination iterative">
</div>

<div v-click="[2, 3]" class="gt-projection-step">
<div>

## Equilibres infinis

- Ex: equilibres partiellement mixtes

</div>
<img src="./images/img_011.png" alt="Equilibres infinis : equilibres partiellement mixtes">
</div>

<div v-click="3" class="gt-projection-step">
<div>

## Règle impaire

- Presque tous les jeux ont un nombre impair d'equilibres
- Nombre infini ou pair généralement lie a la dominance faible
  - Ex nombre pair: l'argent gratuit
  - Sinon verifier si on n'a pas oublie une mixte

</div>
<img src="./images/img_012.png" alt="Regle impaire : nombre d'equilibres d'un jeu">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-03-Topology2x2-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2-Python.ipynb) (dominance faible, regle impaire) · [Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb) · [Metajeux-05-Temoins-Impossibilite-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-05-Temoins-Impossibilite-Python.ipynb).*

</div>

---
layout: dense
---

# Jeux séquentiels

Une menace de guerre des prix suffit-elle à décourager un concurrent d’entrer sur le marché ?

<div v-click="[1, 2]" class="gt-projection-step">
<div><h2>1 · Suivre les décisions</h2><p>L’entrant choisit entre rester dehors et entrer. Ce n’est qu’après une entrée que la firme en place décide d’accepter la concurrence ou de livrer une guerre des prix.</p></div>
<img src="./images/img_013.png" alt="Arbre de décision de l’entrant et de la firme en place">
</div>

<div v-click="[2, 3]" class="gt-projection-step">
<div><h2>2 · Remonter depuis les feuilles</h2><p>Dans cet arbre d’escalade, partez de la dernière décision. Comparez les gains du joueur qui décide, retenez sa meilleure réponse, puis remontez d’un nœud.</p></div>
<img src="./images/img_014.png" alt="Arbre du jeu d’escalade à lire des feuilles vers la racine">
</div>

<div v-click="3" class="gt-projection-step">
<div><h2>3 · Pourquoi plusieurs équilibres ?</h2><p>Le pointillé relie deux nœuds : le joueur 1 ne sait pas si le joueur 2 a choisi <em>Left</em> ou <em>Right</em>. Il ne peut donc pas adapter son choix à cette action.</p><p>Le mélange indiqué rapporte −1/3 au joueur 1 après <em>Go</em>, autant que <em>Stay</em>. À la racine, toute probabilité <em>p</em> est alors optimale.</p></div>
<img src="./images/img_015.png" alt="Le pointillé relie les deux nœuds indiscernables du joueur 1">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-07-ExtensiveForm-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-07-ExtensiveForm-Python.ipynb) (arbres, tours successifs) · [GameTheory-09-BackwardInduction-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09-BackwardInduction-Python.ipynb) (mille-pattes) · [GameTheory-10-ForwardInduction-SPE-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE-Python.ipynb).*

</div>

---
layout: dense
---

# Jeux a étapes

## Plusieurs manches

- Sous-jeux simultanes, Gains independants, connaissance du passe
- Difficile a dessiner (exponentiel)
- Theoremes:
  - Dernière étape -> Equilibre de Nash (passe non modifiable)
  - Autres: jouer equilibres de Nash = 1 equilibre de sous-jeu
  - Mais autres equilibres de sous-jeu possibles (cooperation)

*Notebook : [GameTheory-10-ForwardInduction-SPE-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE-Python.ipynb) (equilibres de sous-jeu, induction sur plusieurs manches).*

---
layout: dense
---

# Menaces credibles -- punition et engagement

<div v-click.hide="1" class="gt-projection-step">
<div>

## Que change la destruction du pont ?

Le pays 1 occupe l’île. Tant que son pont reste intact, il peut se retirer si le pays 2 envahit. Brûler son propre pont ne change pas les préférences du pays 1 : cela retire une action possible.

</div>
<img src="./images/img_016.png" alt="Île entre deux pays, reliée à chaque rive par un pont">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Se lier les mains

- Ex: bruler le pont derriere soi -> Rend la menace credible

</div>
<img src="./images/img_017.png" alt="Se lier les mains : bruler le pont rend la menace credible">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-09b-Commitment-Stackelberg-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09b-Commitment-Stackelberg-Python.ipynb) (se lier les mains, menace credible) · [Dynamics-01-Jeux-Repetes-Folk-Theorem-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb) (strategies de punition).*

</div>

---
layout: dense
---

# Jeux a étapes -- induction arriere et repetition

<div v-click.hide="1" class="gt-projection-step">
<div>

## La fouille : anticiper la réponse

Le garde préfère une fouille complète (3 plutôt que 2). En l’anticipant, le premier joueur préfère attendre le chien (2 plutôt que 1). Promettre une fouille rapide ne suffit pas.

</div>
<img src="./images/img_018.png" alt="Arbre de la fouille : attendre le chien ou laisser le garde choisir la fouille">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Récompenser ou punir à la seconde manche

Dans la matrice de droite, récompenser ensemble rapporte (3, 3). Punir ensemble rapporte (0, 0), mais aucun joueur ne gagne à changer seul. Ces deux équilibres permettent de conditionner la seconde manche à la coopération dans la première.

</div>
<img src="./images/img_019.png" alt="Deux matrices : dilemme du prisonnier puis choix de récompense ou punition">
</div>

<div v-click="[2, 3]" class="gt-projection-step">
<div>

## Induction vers l’avant : pourquoi renoncer au pub ?

Le pub garantit 2,5 au premier joueur. Le lapin ne lui rapporte jamais plus de 2. Si le second joueur interprète le refus du pub comme un choix rationnel, il a une raison de miser sur le cerf plutôt que sur le lapin.

</div>
<img src="./images/img_020.png" alt="Pub Hunt : option certaine à 2,5 ou chasse au cerf et au lapin">
</div>

<div v-click="3" class="gt-projection-step">
<div>

## Le mille-pattes : remonter jusqu’au début

Au dernier nœud, le joueur 2 préfère 101 à 100. Le joueur 1 l’anticipe au nœud précédent et préfère 100 à 99. En remontant ainsi, le modèle prédit un arrêt immédiat, même si continuer profiterait aux deux. Cette prédiction dépend de ce que chacun suppose de la rationalité des autres.

Pour comparer : dans un dilemme répété, une punition perpétuelle ou un « œil pour œil » fait dépendre la réponse du passé.

</div>
<img src="./images/img_021.png" alt="Mille-pattes : alternance des décisions, du premier nœud aux gains finaux">
</div>

<div class="gt-projection-links">

*Notebooks : [Dynamics-01-Jeux-Repetes-Folk-Theorem-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb) (folk theorem) · [GameTheory-06-EvolutionTrust-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06-EvolutionTrust-Python.ipynb) (evolution de la confiance).*

</div>

---
layout: dense
---

# Jeux répétés : du seuil au théorème folk

## Ce que Lean établit pour le dilemme du prisonnier

- [`grim_trigger_sustains_iff`](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/game_theory_lean/RepeatedGames/GrimTrigger.lean) compare le flux coopératif au flux après défection.
- [`grim_isSPE_iff`](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/game_theory_lean/RepeatedGames/Perfect.lean) établit l’équivalence entre le même seuil et l’équilibre parfait en sous-jeux du profil grim trigger.

## Au-delà du dilemme : le résultat général

> **Théorème folk (version à surveillance parfaite).** Dans un jeu fini répété, sous l’hypothèse de pleine dimension des gains réalisables, tout gain réalisable strictement au-dessus des niveaux minimax individuels peut être soutenu en équilibre parfait en sous-jeux pour des joueurs suffisamment patients.

**Stratégie.** Programmer un chemin qui réalise le gain, puis construire des sanctions crédibles. Le seuil de grim trigger ne formalise pas ce résultat général.

---
layout: default
---

# Punition permanente : un équilibre dans chaque sous-jeu

> **Énoncé.** Dans le dilemme du prisonnier infiniment répété ($T>R>P>S$, $0\leq\delta<1$), le profil grim trigger — coopérer tant que personne n’a fait défection, puis faire défection pour toujours — est un équilibre parfait en sous-jeux **si et seulement si** $\delta\geq\frac{T-R}{T-P}$.

## Stratégie de preuve

1. **Avant toute défection**, comparer $R/(1-\delta)$ à $T+\delta P/(1-\delta)$ : sous le seuil, dévier rapporte dès le départ.
2. **Après une défection**, la punition est irréversible et, face à une défection, faire défection rapporte plus que coopérer ($P>S$).
3. **À tout historique**, avec des gains bornés et $\delta<1$, le principe de déviation en un coup étend la vérification locale aux déviations de stratégie entières : l’effet de la fin du flux tend vers zéro.

*Notebook : [Dynamics-02 — Jeux répétés en Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-02-Jeux-Repetes-Lean-Python.ipynb).*

---
layout: dense
---

# Jeux combinatoires -- Grundy et les nimbers

## Sprague-Grundy

- Classe : information parfaite, sans hasard, somme nulle, fini (Nim)
  - Théorème de Sprague-Grundy : chaque position vaut un nimber, la somme disjointe vaut le XOR
  - Position perdante (P-position) ssi Grundy = 0 -- l'induction arrière devient un calcul
- Compagnons formels du corpus : port Lean « from scratch », puis lake natif dédié

*Notebooks : [GameTheory-08-CombinatorialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08-CombinatorialGames-Python.ipynb) (Nim, Grundy) · [GameTheory-08b-Lean-CombinatorialGames-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08b-Lean-CombinatorialGames-Lean.ipynb) (port Lean from scratch) · [GameTheory-08c-CombinatorialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08c-CombinatorialGames-Python.ipynb) · [GameTheory-08d-Lean-CGT-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08d-Lean-CGT-Lean.ipynb) (lake `conway_cgt_lean`).*

---
layout: default
---

# Sprague–Grundy

> **Énoncé.** En convention normale, la valeur d’une somme disjointe de jeux impartiaux finis sans cycle est le XOR de leurs nimbers.

## Stratégie de preuve

Calculer chaque nimber par le plus petit entier absent des valeurs accessibles. Une induction montre que depuis un XOR nul tout coup le rend non nul, et que depuis un XOR non nul un coup peut le ramener à zéro.

---
layout: dense
---

# Formes stratégiques avancees

<div v-click.hide="1" class="gt-projection-step">
<div>

## Raisonner avec des variables

- Ex: bataille des sexes, A>B>C, algorithme de stratégie mixte
  - $\sigma_u=\frac{b-c}{a+b-2c}$ et $0<\sigma_u<1$
- Ex: Topologie complete 2x2

</div>
<img src="./images/img_022.png" alt="Bataille des sexes : gains A, B et C en ordre décroissant">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Raisonner avec des variables

- Ex: bataille des sexes, A>B>C, algorithme de stratégie mixte
  - $\sigma_u=\frac{b-c}{a+b-2c}$ et $0<\sigma_u<1$
- Ex: Topologie complete 2x2

</div>
<img src="./images/img_023.png" alt="Topologie complete des jeux 2x2">
</div>

<div v-click="[2, 3]" class="gt-projection-step">
<div>

## Raisonner avec des variables

- Ex: bataille des sexes, A>B>C, algorithme de stratégie mixte
  - $\sigma_u=\frac{b-c}{a+b-2c}$ et $0<\sigma_u<1$
- Ex: Topologie complete 2x2

</div>
<img src="./images/img_024.png" alt="Algorithme de strategie mixte avec variables">
</div>

<div v-click="3" class="gt-projection-step">
<div>

## Equilibre de lame de couteau

- X>0 -> Up, Left vs x<0 -> down, right, x=0 -> tous
- Instable autour de x=0, probabilité faible -> ignore

</div>
<img src="./images/img_025.png" alt="Equilibre de lame de couteau : instabilite autour de x=0">
</div>

<div class="gt-projection-links">

*Notebook : [GameTheory-03-Topology2x2-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2-Python.ipynb) — topologie complete des jeux 2x2, cf slide suivante.*

</div>

---
layout: dense
---

# Formes stratégiques avancees -- causalite et cycles

<div v-click.hide="1" class="gt-projection-step">
<div>

## Modèles causaux

- Proprietes causales des inputs -> Statiques comparees
  - Calcul des gradients aux equilibres
- Ex: Football penalty: $\sigma_{KL}(x)=\frac1{1+x}$, $\sigma'_{KL}(x)=-\frac1{(1+x)^2}<0$
  - -> il tire davantage son cote faible (compense)

</div>
<img src="./images/img_026.png" alt="Modele causal du penalty au football : gradients aux equilibres">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Pierre, papier, ciseaux

- Pas de stratégie pure -> cycle
- Support des stratégies mixtes, EU egales dans le support
- Theoreme: 2 joueurs, symetrique a somme nulle -> EU = 0
- Resolution: indifference $\sigma_L=\tfrac14$ (ciseaux pour compenser)

</div>
<img src="./images/img_027.png" alt="Pierre-papier-ciseaux : matrice de gains a somme nulle">
</div>

<div v-click="2" class="gt-projection-step">
<div>

## Pierre, papier, ciseaux

- Pas de stratégie pure -> cycle
- Support des stratégies mixtes, EU egales dans le support
- Theoreme: 2 joueurs, symetrique a somme nulle -> EU = 0
- Resolution: indifference $\sigma_L=\tfrac14$ (ciseaux pour compenser)

</div>
<img src="./images/img_028.png" alt="Resolution de pierre-papier-ciseaux : support des strategies mixtes">
</div>

<div class="gt-projection-links">

*Notebooks : [Dynamics-09-Biens-Publics-N-Personnes-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb) (déformation, pierre-papier-ciseaux) · [GameTheory-05-ZeroSum-Minimax-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05-ZeroSum-Minimax-Python.ipynb) (somme nulle, EU = 0).*

</div>

---
layout: dense
---

# Topologie des jeux 2x2 : l'arc des notebooks

## De la matrice au paysage ordinal

- [GameTheory-03b-Chambres-Murs-Chemins-Lean-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03b-Chambres-Murs-Chemins-Lean-Python.ipynb) : partitionner l'espace des jeux 2x2 en chambres et murs, puis mesurer la distance qui separe deux chambres

## Deformations et quotient

- [Dynamics-09-Biens-Publics-N-Personnes-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb) : chemins continus entre classes
- [GameTheory-03-Topology2x2-Python (§9)](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2-Python.ipynb) : deriver la structure quotient (absorbé depuis l'ex-03g)

## Parcours et extensions

- [GameTheory-03e-Meta-Actions-Tarifees-Python (§4-8)](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03e-Meta-Actions-Tarifees-Python.ipynb) : versant d'integration (absorbé depuis l'ex-03f)
  - [GameTheory-03e-Meta-Actions-Tarifees-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03e-Meta-Actions-Tarifees-Python.ipynb) · [GameTheory-03d-Deux-Especes-de-Fleches-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-03d-Deux-Especes-de-Fleches-Python.ipynb) · [Dynamics-10-Joueur-LLM-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-10-Joueur-LLM-Python.ipynb)

---
layout: default
---

# Invariance dans une chambre

> **Énoncé.** Le long d’un chemin continu de matrices sans égalité de gains pour un joueur, son classement des issues ne change pas.

## Stratégie de preuve

Pour inverser deux issues, la différence de leurs gains doit passer par zéro. Ce passage est un mur ; il ne signifie pas que les joueurs ont choisi de modifier le jeu.

---
layout: default
---

# Espaces de stratégies infinis

<div v-click.hide="1" class="gt-projection-step">
<div>

## Jeux sans equilibre

- Nombre fini de stratégies pures -> Matrices + theoremes de Nash
- Certains jeux ont une infinite de stratégies pures
  - Pas de matrice, pas forcement d'equilibre de Nash

</div>
<img src="./images/img_029.png" alt="Jeu sans equilibre de Nash en strategies pures">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Duels

- 100 m, 2 balles, precisions différentes (0% a 100m, 100% a 0m)
- Equilibre = même distance (preuve par contradiction)
- Ex: date de sortie de produits concurrents

</div>
<img src="./images/img_030.png" alt="Duel : equilibre a meme distance">
</div>

<div class="gt-projection-links">

*Notebook : [GameTheory-04c-NashExistence-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-Python.ipynb) (existence d'un equilibre hors matrice finie).*

</div>

---
layout: default
---

# Loi de Hotelling et électeur médian

<style scoped>
.slidev-vclick-hidden { display: none; }
</style>

Deux vendeurs de glaces choisissent où s’installer. À prix égal, chaque client va au plus proche.

<div v-click="[1, 3]" style="text-align:center; margin:22px auto 12px"><img src="./images/img_031.png" alt="Plage graduée de 0 à 100 : la flèche rouge est à gauche de la bleue" style="width:72%; margin:auto"></div>

<div v-click="[1, 2]"><h2>1 · Où passe la frontière ?</h2><p>Elle est à mi-distance des deux flèches. Si le vendeur rouge se rapproche du bleu sans le dépasser, la frontière se déplace vers la droite : le rouge gagne des clients.</p></div>
<div v-click="[2, 3]"><h2>2 · Pourquoi au milieu ?</h2><p>Si les clients sont uniformément répartis et les deux stands au centre, chacun sert la moitié de la plage. S’écarter seul laisse plus de la moitié des clients à son rival.</p></div>
<div v-click="3"><h2>3 · Du client à l’électeur</h2><p>Sur un axe politique, supposons des préférences à sommet unique et un nombre impair de votants. Face à toute proposition située à droite du sommet médian, au moins la moitié plus un préfèrent ce sommet. Le raisonnement est symétrique à gauche : le sommet médian est vainqueur de Condorcet.</p></div>

*Notebook : [SocialChoice/ChoixSocial-03-Voting-Methods-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) (electeur median) ; preuve Lean `median_voter_theorem` dans game_theory_lean/SocialChoice/Voting.lean. Loi de Hotelling : pas de notebook dedie.*

---
layout: default
---

# Électeur médian

> **Énoncé.** Pour un nombre impair de votants aux préférences strictes à sommet unique sur un axe commun, le sommet médian bat toute autre option en duel.

## Stratégie de preuve

Face à une option à gauche du sommet médian, tous les sommets situés à droite, médiane comprise, préfèrent la médiane. Raisonner symétriquement à gauche.

---
layout: section
---

# Jeux Bayesiens

---
layout: dense
---

# Jeux Bayesiens

<div v-click.hide="1" class="gt-projection-step">
<div>

## Information incomplete

- Sur les autres joueurs (ex: recompenses)
- Representation = Distribution de probabilité sur les types de joueurs
  - Information imparfaite -> Analyse probabiliste

</div>

</div>

<div v-click="1" class="gt-projection-step">
<div>

## Formalisation

$G=\langle N,\Omega,(A_i,u_i,T_i,\tau_i,p_i,C_i)_{i\in N}\rangle$

- N joueurs, Omega etats de la nature, A_i actions du joueur i
- T_i type du joueur i, U_i recompense, p_i distribution des types
- Stratégies pures: $S_i=\{s_i:T_i\to A_i\}$

</div>
<img src="./images/img_032.png" alt="Formalisation Bayesienne : joueurs, etats, types et croyances">
</div>

<div class="gt-projection-links">

*Notebook : [GameTheory-11-BayesianGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11-BayesianGames-Python.ipynb) (types, croyances, formalisation).*

</div>

---
layout: dense
---

# Jeux Bayesiens -- equilibres et dilemme du Sheriff

<div v-click.hide="1" class="gt-projection-step">
<div>

## Equilibres de Nash Bayesien

- Objectif = maximisation de la recompense esperee
- De nombreux equilibres sans restrictions supplementaires

</div>
<img src="./images/img_033.png" alt="Equilibre de Nash Bayesien : maximisation de la recompense esperee">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Ex: Dilemme du Sheriff

- Criminel (p) vs civil (1-p), tirer ou pas
- Stratégies dominantes: tirer pour criminel, pas pour civil
- Pour le Sheriff: $E(\text{tirer})=p-1$, $E(\text{ne pas tirer})=-2p$
  - p>1/3 = tirer

</div>
<img src="./images/img_034.png" alt="Dilemme du shérif : tirer au-delà du seuil de probabilité 1/3">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-11-BayesianGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11-BayesianGames-Python.ipynb) (types, Nash bayesien) · [GameTheory-11b-Lean-BayesianGamesExt-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11b-Lean-BayesianGamesExt-Lean.ipynb) (extension Lean).*

</div>

---
layout: default
---

# Meilleure réponse par type

> **Énoncé.** Dans un jeu bayésien fini, un profil est un équilibre si chaque type de probabilité positive maximise son utilité espérée conditionnelle.

## Stratégie de preuve

Décomposer le gain total d’une déviation selon les types. Une amélioration pour un type suffit ; sans amélioration conditionnelle, aucune déviation globale ne rapporte.

---
layout: dense
---

# Equilibres Bayesiens parfaits (PBE)

<div v-click.hide="1" class="gt-projection-step">
<div>

## Jeux séquentiels

- Rappel SPE -> equilibres non plausibles (menaces non credibles)
- Systèmes de croyance: assignations de probabilités sur les types
  - "Consistant" -> Probabilités par application des stratégies (Bayes)
- Rationalite séquentielle: recompense esperee maximale

</div>
<img src="./images/img_035.png" alt="Jeu de signalisation : arbre avec systeme de croyances">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Definition PBE

- Profile stratégique et système de croyance consistant tels que les stratégies sont sequentiellement rationnelles

</div>

</div>

<div class="gt-projection-links">

*Notebook : [GameTheory-17b-Asymmetric-Information-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17b-Asymmetric-Information-Python.ipynb) — croyances consistantes et rationalite sequentielle.*

</div>

---
layout: dense
---

# Jeux de signalisation -- pooling, separating, semi-separation

<div v-click.hide="1" class="gt-projection-step">
<div>

## Trois categories de PBE

- Emetteur S (connait son type) -> message m, Recepteur R -> action a
- 3 catégories de PBE:
  - **Pooling**: emetteurs choisissent le même message (pas de signal)
  - **Separating**: messages toujours différents -> croyance déterministe
  - **Semi-separation** (partial-pooling): mixte

</div>
<img src="./images/img_036.png" alt="Arbre extensive d'un jeu de signalisation">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Exemples

- Jeu de reputation (guerre des prix): pooling ou separating
- Jeu d'education: doue ou pas, diplome ou pas (signal) -> PBE de separation
- Biere-quiche: P=0.9 -> pooling, P=0.2 -> stratégies mixtes

</div>
<img src="./images/img_037.png" alt="Exemples de PBE : pooling, separating et semi-separation">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-12-ReputationGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-12-ReputationGames-Python.ipynb) (pooling/separating) · [GameTheory-17d-Lean-Screening-Signaling-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17d-Lean-Screening-Signaling-Lean.ipynb) (screening formalise).*

</div>

---
layout: default
---

# Séparation et incitations

> **Énoncé.** Dans un équilibre séparateur, chaque type préfère son propre signal à celui d’un autre type, compte tenu de la réponse du destinataire.

## Stratégie de preuve

Tester les déviations type par type. Ces inégalités sont nécessaires, pas suffisantes : il faut aussi vérifier les croyances et la rationalité séquentielle.

---
layout: dense
---

# Information imparfaite -- le regret contraposé (CFR)

## Poker et apprentissage auto-centré

- Théorème de Kuhn : à rappel parfait, stratégies comportementales = mixtes
  - L'information set porte la croyance qui pilote la meilleure réponse
- CFR (Counterfactual Regret Minimization) : minimiser le regret contraposé
  - Convergence vers l'équilibre de Nash -- la famille qui a révolutionné la résolution du poker
  - Safe subgame solving : recoller une sous-partie sans supposer les croyances (le mauvais recollement produit un témoin adversarial)

*Notebooks : [GameTheory-13-ImperfectInfo-CFR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13-ImperfectInfo-CFR-Python.ipynb) (CFR, Kuhn) · [GameTheory-13b-Safe-Subgame-Solving-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13b-Safe-Subgame-Solving-Python.ipynb) · [GameTheory-13b-Safe-Subgame-Solving-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13b-Safe-Subgame-Solving-CSharp.ipynb) (jumeau C#) · [GameTheory-13d-Optimistic-CFR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13d-Optimistic-CFR-Python.ipynb).*

---
layout: default
---

# Kuhn

> **Énoncé.** Dans un jeu extensif fini à rappel parfait, stratégies mixtes et comportementales sont équivalentes en réalisation, pas nécessairement comme distributions sur les plans.

## Stratégie de preuve

Conditionner le plan tiré sur les décisions antérieures du joueur. Dans l’autre sens, tirer à l’avance une action à chaque ensemble d’information.

---
layout: section
---

# Questions?

---
layout: section
---

# Jeux cooperatifs

---
layout: dense
---

# Jeux cooperatifs

## Jeux d'assistance

- 2 joueurs, récompense $\theta$ incertaine pour l'assistant
- Ex: Jeu du trombone
  - Nash -> meilleure reponse myope incrementale
- Cas general similaire a un POMDP dont l’état caché inclut $\theta$

## Théorie des jeux cooperatifs

- Utilite transferable de coalition: $G=(N,v)$, $v(C)\geq0$
- Partitions = Structures de Coalitions CS(N)
- **Imputation**: $\sum_i x_i=v(N)$, $x_i\geq v(\{i\})$
- **Noyau**: imputations x telles que $\sum_{i\in C}x_i\geq v(C)$ pour tout C
- **Valeur de Shapley**: contribution marginale moyennee sur toutes les permutations
  - $\phi_i(v)=\frac1{n!}\sum_{\pi}\mathrm{mc}_i(\pi)$
  - Axiomes: Efficace, joueur nul, symetrie, additivite -> unique

## Calculs

- Reseaux de contribution marginale (representation compacte)
  - $\phi_i(R)=\sum_{C\ni i} x_C/\lvert C\rvert$ pour les coalitions contenant i
- Structures de coalition optimales: NP-Hard
  - Bons résultats avec exploration du graphe de structure

*Notebooks : [GameTheory-15-CooperativeGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames-Python.ipynb) (Shapley, noyau) · [GameTheory-15b-Lean-CooperativeGames-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15b-Lean-CooperativeGames-Lean.ipynb) (axiomes de Shapley prouves en Lean) · [SocialChoice/ChoixSocial-06b-Mobius-Coalitions-Lean-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-06b-Mobius-Coalitions-Lean-Python.ipynb).*

---
layout: default
---

# Caractérisation de Shapley

> **Énoncé.** Sur les jeux finis à utilité transférable normalisés, efficacité, symétrie, joueur nul et additivité caractérisent une unique valeur.

## Stratégie de preuve

Sur chaque jeu d’unanimité, les joueurs nécessaires se partagent également le gain. Ces jeux forment une base ; l’additivité détermine le partage pour tout jeu.

---
layout: section
---

# Conception de mécanismes

---
layout: dense
---

# Conception de mécanismes

## Théorie des jeux inverse

- Si les agents sont rationnels, quelles sont les bonnes règles?
- Dans le cadre Bayesien d'information imparfaite
  - Le "principal" souhaite inciter a reveler la vraie utilite

## Formalisme

- Le principal choisit la structure de recompense $y$
- Les agents declarent $\hat\theta$ (et peuvent mentir)
- Fonction de choix social $f(\theta)$ a implementer par $y(\hat\theta)$

## Principe de revelation

- Mécanisme incitatif verace (IC): non manipulable, revelateur
  - $\hat\theta(\theta)=\theta$
- S'il existe un mécanisme y implementant f, alors il existe une version IC
- 2 versions:
  - **DSIC**: Implementation en stratégies dominantes
  - **BNIC**: Equilibre de Nash Bayesien (plus faible)

*Notebooks : [GameTheory-16-MechanismDesign-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-Python.ipynb) (revelation, DSIC/BNIC) · [GameTheory-16b-Automated-Mechanism-Design-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16b-Automated-Mechanism-Design-Python.ipynb) (AMD) ; `amd_star_DSIC/IR` prouves en Lean.*

---
layout: default
---

# Principe de révélation

> **Énoncé.** Si un résultat est implémenté en équilibre, un mécanisme direct peut le reproduire par des déclarations véraces, pour le même concept d’équilibre.

## Stratégie de preuve

Simuler la stratégie du type annoncé. Mentir correspond alors à une déviation dans le mécanisme initial. La certification Lean du mécanisme AMD particulier n’est pas une preuve de ce principe général.

---
layout: dense
---

# Allocation de ressources par les encheres

<div v-click.hide="1" class="gt-projection-step">
<div>

## Encheres individuelles

- Valeur privee v_i de l'objet par l'individu i
- Enchere anglaise (ascendante): Efficace mais risque de collusion
- Enchere de Vickrey (second prix)
  - Equilibre DSIC = chacun declare la valeur "honnete"
  - Très repandu: eBay, AdWords etc.
- Theoreme d'equivalence de revenue

</div>

</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Bien commun

- Tragedie des communs (ex: pollution)
  - Stratégie de pollution dominante mais pas optimale (Pareto)
  - Necessite d'expliciter les externalites (ex: taxe carbone)

</div>

</div>

<div v-click="2" class="gt-projection-step">
<div>

## Mécanisme de Vickrey-Clarke-Groves (VCG)

- N Encherisseurs declarent utilite de M ressources
- Allocation maximisant la somme des utilites
- Taxe: $T_i=\max_a\sum_{k\ne i}v_k(a)-\sum_{k\ne i}v_k(a^*)$

</div>
<img src="./images/img_038.png" alt="Taxe VCG : T_i = U_max(sans i) - U_max(sans i, sans ressource j)">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-16-MechanismDesign-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-Python.ipynb) (Vickrey, VCG, equivalence de revenu) · [GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python.ipynb) ; `vickrey_truthful_bidder0/1` (deux enchérisseurs, valeurs naturelles). Bien commun : pas de notebook dedie.*

</div>

---
layout: default
---

# Second prix : véracité

> **Énoncé.** Avec valeurs privées et utilité quasi linéaire, enchérir sa valeur est faiblement dominant dans une enchère au second prix.

## Stratégie de preuve

Fixer la meilleure offre adverse. Gagner est préférable si sa propre valeur dépasse ce seuil ; sinon perdre est préférable. Enchérir sa valeur effectue exactement cette sélection.

---
layout: dense
---

# Allocation par les votes

## Théorie du choix social

- Préférences individuelles rationnelles -> Ordre de préférence social
- Proprietes d'une bonne fonction de choix social:
  1. Condition de Pareto / critere d'unanimite
  2. Indépendance des alternatives non pertinentes
  3. Pas de dictature

## Résultats negatifs

- **Paradoxe de Condorcet**: la majorité peut préférer A à B, B à C et C à A
- **Theoreme de Arrow**: Impossible de satisfaire 1, 2 et 3 simultanement (>= 3 options)
- **Theoreme de Gibbard-Satterthwaite**: Toute FCS déterministe avec Pareto et >2 choix est manipulable ou dictatoriale

*Notebooks : [SocialChoice/ChoixSocial-01-Arrow-Impossibility-Theorem-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-01-Arrow-Impossibility-Theorem-Python.ipynb) (Arrow) · [SocialChoice/ChoixSocial-05-Gibbard-Satterthwaite-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-05-Gibbard-Satterthwaite-Python.ipynb) · [SocialChoice/ChoixSocial-04-Computational-Aggregation-SAT-Z3-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-04-Computational-Aggregation-SAT-Z3-Python.ipynb) (verification SAT/Z3) ; `arrow` prouve en Lean (game_theory_lean), Gibbard-Satterthwaite dans social_choice_lean_peters.*

---
layout: default
---

# Deux impossibilités différentes

> **Énoncé.** Arrow : sur tous les classements stricts d’au moins trois options, un classement social transitif, unanime et indépendant des options non pertinentes est dictatorial. Gibbard–Satterthwaite : sur ce domaine, une règle déterministe surjective qui choisit un vainqueur est manipulable ou dictatoriale.

## Stratégie de preuve

Pour Arrow, réduire une coalition décisive jusqu’à un électeur. Pour Gibbard–Satterthwaite, partir de la monotonie imposée par la non-manipulabilité. Le premier résultat porte sur un classement, le second sur un choix.

---
layout: dense
---

# Critere de Condorcet

<div v-click.hide="1" class="gt-projection-step">
<div>

## Condition du vainqueur de Condorcet

- La meilleure aux autres options prises paire a paire
  - Ex: Uninominal a 2 tours: Bayrou vainqueur de Condorcet mais pas au 2e tour
- **Indifference aux petits candidats**: vainqueur stable aux changements
- Paradoxe de Condorcet: pas de garantie d'existence

</div>
<img src="./images/img_039.png" alt="Comparaisons par paires : recherche du vainqueur de Condorcet">
</div>

<div v-click="1" class="gt-projection-step">
<div>

## Theoremes de l'electeur median

- 1er theoreme: Gauche-droite -> existence du vainqueur -> electeur median
- 2e theoreme: Gauche-droite + valeur intrinseque

</div>
<img src="./images/img_040.png" alt="Theoremes de l'electeur median : resultats de vote">
</div>

<div class="gt-projection-links">

*Notebook : [SocialChoice/ChoixSocial-03-Voting-Methods-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) (Condorcet, electeur median).*

</div>

---
layout: dense
---

# En l’absence de vainqueur de Condorcet

<style scoped>
p:has(> em:only-child) { position:absolute; bottom:34px; left:42px; right:42px; }
</style>

<div v-click.hide="1" class="gt-projection-step"><div><h2>Un axe peut éviter les cycles</h2><p>La figure place les options sur une ligne : c’est le cas structuré du théorème de l’électeur médian. Sans préférences à sommet unique sur un axe commun, la majorité peut préférer A à B, B à C et C à A.</p></div><img src="./images/img_041.png" alt="Positions des options M, H, B, S et L sur un axe"></div>

<div v-click="[1, 2]" class="gt-projection-step"><div><h2>Minimax : limiter sa pire défaite</h2><p>Supposons que A batte B de 3 voix, B batte C de 5 voix et C batte A d’une voix. Les pires défaites de A, B et C ont pour marges 1, 3 et 5. Minimax, dans sa version par marges, choisit A.</p></div></div>

<div v-click="2" class="gt-projection-step"><div><h2>Schulze : comparer les chemins</h2><p>La force d’un chemin est celle de son duel le plus faible. En prenant les marges positives, A → B → C a pour force 3, contre 1 pour C → A. Le duel direct ne suffit donc pas à classer C devant A.</p></div></div>

*Notebooks : [SocialChoice/ChoixSocial-03-Voting-Methods-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) (Condorcet, Minimax, Schulze) ; `median_voter_theorem` prouve en Lean (game_theory_lean/SocialChoice/Voting.lean) ; tour Peters : Schulze, Split Cycle, Borda, IRV.*

---
layout: dense
---

# Procédures de vote : que mesure le dépouillement ?

<style scoped>
p:has(> em:only-child) { position:absolute; bottom:34px; left:42px; right:42px; }
</style>

<div v-click.hide="1" class="gt-projection-step"><div><h2>Une voix ou un classement ?</h2><p>Avec deux options, un référendum compare directement les voix. Avec plusieurs candidats, le scrutin uninominal ne compte que les premiers choix : c’est une incitation au vote utile.</p><p>Un classement permet soit d’éliminer le dernier et de transférer les voix (vote alternatif), soit d’attribuer des points à chaque rang (Borda). Ni l’un ni l’autre ne garantit le choix du vainqueur de Condorcet.</p></div></div>

<div v-click="[1, 2]" class="gt-projection-step"><div><h2>Compter les approbations</h2><p>Chaque personne peut soutenir plusieurs options. Comptez les traits, pas les rangs : TRUC est en tête avec neuf approbations sur quinze. La règle retient le plus grand total, sans exiger de majorité absolue.</p></div><img src="./images/img_042.png" alt="Dépouillement par assentiment : neuf voix pour TRUC"></div>

<div v-click="[2, 3]" class="gt-projection-step"><div><h2>Prendre la médiane</h2><p>Chaque personne évalue chaque option sur la même échelle. Ici, les notes sont rangées : c’est la note du milieu qui compte, pas la moyenne. BIDULE arrive en tête avec une médiane de 11.</p></div><img src="./images/img_043.png" alt="Notes ordonnées et médiane de chaque option"></div>

<div v-click="3" class="gt-projection-step"><div><h2>Comparer deux options à la fois</h2><p>Chaque colonne correspond à un adversaire. SCHMILBLICK bat chacun des autres en duel : c’est le vainqueur de Condorcet. En l’absence d’un tel vainqueur, une méthode comme celle de Schulze départage les options.</p></div><img src="./images/img_044.png" alt="Table des duels majoritaires remportés par SCHMILBLICK"></div>

*Notebook : [SocialChoice/ChoixSocial-03-Voting-Methods-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) (Borda, assentiment, jugement majoritaire).*

---
layout: dense
---

# Du bulletin à la loterie

<style scoped>
p:has(> em:only-child) { position:absolute; bottom:34px; left:42px; right:42px; }
</style>

<div v-click.hide="1" class="gt-projection-step"><div><h2>Trois bulletins, trois informations</h2><p>On peut approuver, noter ou classer. Que devient le résultat si, au lieu de compter les voix, on tire un bulletin au hasard ? Le bulletin ne détermine pas à lui seul la règle de dépouillement.</p></div></div>

<div v-click="[1, 2]" class="gt-projection-step"><div><h2>Approuver ou noter</h2><p>Ce bulletin approuve à la fois BIDULE et CHOSE ; les notes les distinguent, 14 contre 18. Ne pas confondre le nombre d’approbations et la médiane des notes.</p></div><div><img src="./images/img_045.png" alt="Bulletin pour ou contre" style="height:155px;margin:auto"><img src="./images/img_046.png" alt="Bulletin noté sur vingt" style="height:155px;margin:auto"></div></div>

<div v-click="[2, 3]" class="gt-projection-step"><div><h2>Tirer un bulletin au hasard</h2><p>Si ce bulletin est tiré, son premier choix, CHOSE, gagne. Chaque option a donc pour probabilité de victoire sa part de premières places. Dans cette règle, placer son véritable favori en tête est optimal.</p></div><img src="./images/img_047.png" alt="Bulletin classé : CHOSE première, BIDULE deuxième"></div>

<div v-click="3" class="gt-projection-step"><div><h2>Randomiser à partir des duels</h2><p>Une loterie maximale utilise plutôt les marges de majorité : on cherche une stratégie mixte d’équilibre du jeu à somme nulle entre options. Si un vainqueur strict de Condorcet existe, il reçoit toute la probabilité.</p></div></div>

*Notebook : [SocialChoice/ChoixSocial-03-Voting-Methods-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) (Borda, assentiment, jugement majoritaire). Scrutins stochastiques : pas de notebook dedie.*

---
layout: default
---

# Allocation par la negociation

<div v-click="0" class="gt-projection-step">
<div>

## Modèle des offres alternees

- Si pas d'accord: Accord de conflit -> fenêtre de negociation
- Nombre de manches:
  - 1 manche: Ultimatum (J1 a tout le pouvoir)
  - 2 manches: J2 a tout le pouvoir
  - N manches: JN a le pouvoir
- Agents impatients: facteurs de discompte $0\leq\gamma_i<1$
  - Offre a l'equilibre: $A_1=\frac{1-\gamma_2}{1-\gamma_1\gamma_2}$

</div>
<img src="./images/img_048.png" alt="Negociation a offres alternees : fenetre d'accord et partage a l'equilibre">
</div>

<div class="gt-projection-links">

*Notebooks : [GameTheory-04d-Marchandage-Asymetrique-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04d-Marchandage-Asymetrique-Python.ipynb) (offres alternees, discompte) · [GameTheory-07-ExtensiveForm-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-07-ExtensiveForm-Python.ipynb) (ultimatum).*

</div>

---
layout: dense
---

# Negociation -- protocoles et concession

## Domaines orientes tâches

- Offres (T1, T2) de repartitions de tâches parmi T
- Protocole de concession monotone

## Stratégie de Zeuthen

- Mesure de l'aversion au risque de conflit
- Le risque plus faible concede, sinon tirage au sort

*Zeuthen et la concession monotone : pas de notebook dedie dans la serie — la mesure d'aversion au risque reste traitee en cours.*

---
layout: default
---

# Théorie de la negociation

## Demarche

- Hypotheses -> Modèles de jeux -> Equilibres et pouvoirs de negociation

## Sources du pouvoir de negociation

- Pouvoir de proposition
- Patience
- Options alternatives
- Connaissance de l'autre utilite
- Monopole
- Reputation
- Engagement credible
- Signalement couteux

---
layout: section
---

# Questions?

---
layout: section
---

# Jeux differentiels

---
layout: dense
---

# Jeux differentiels

## Théorie des jeux + théorie du contrôle

- Interdependance: agents economiques, pollution, marches
- Dynamique: habitudes, technologies, accumulations, traffic
- Comportement stratégique: buts antagonistes, choix

## Definitions

- Joueurs M={1,...,m}, Vecteur de contrôle $u_j(t)$
- Vecteur d'etat $x(t)$, equation d'etat: $\dot x(t)=f(x(t),u(t),t)$
- Fonction de gain: $J_j=S_j(x(T))-\int_0^T g_j\,dt$ -> Minimisation de L

## Structure de l'information

- **Boucle ouverte**: conditions initiales + temps: $u_j(t)=\mu_j(x_0,t)$
- **Markovienne**: $u_j(t)=\sigma_j(t,x(t))$ (lineaire, quadratique, seuil)
- Non Markovienne: utilisation de l'historique
- **Hiérarchique**: le leader annonce sa stratégie

---
layout: dense
---

# Equilibres differentiels

<div v-click.hide="1" class="gt-projection-step">
<div>

## Equilibres de Nash pour jeux a somme nulle

- $J_1+J_2=0$, equilibres de point de selle
- P1 maximise, P2 minimise -> equilibre ssi point de selle existe

</div>
<img src="./images/img_049.png" alt="Point de selle d'un jeu differentiel a somme nulle">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Equilibres de Stackelberg

- Le "leader" annonce en tenant compte des reponses des autres
- Ex: croissance economique (taxe sur le capital + consommation)

</div>

</div>

<div v-click="2" class="gt-projection-step">
<div>

## Jeux cooperatifs/competitifs

- Possibilite de dialogue -> maximisation commune
- Division en partie cooperative et partie competitive (valeur co-co)

</div>

</div>

<div class="gt-projection-links">

*Notebook : [GameTheory-14-DifferentialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-14-DifferentialGames-Python.ipynb) (point de selle, Stackelberg differentiel).*

</div>

---
layout: dense
---

# Equilibres differentiels -- boucle ouverte et Markoviens

<div v-click.hide="1" class="gt-projection-step">
<div>

## Equilibres en boucle ouverte

- u* est un equilibre de Nash ssi aucun joueur ne peut ameliorer seul
- Resolution: 2 optimisations -> conditions necessaires

</div>
<img src="./images/img_050.png" alt="Equilibres en boucle ouverte : conditions necessaires">
</div>

<div v-click="[1, 2]" class="gt-projection-step">
<div>

## Equilibres Markoviens

- Resolution d'equations differentielles
- Jeux lineaires quadratiques -> solution analytique

</div>
<img src="./images/img_051.png" alt="Equilibres Markoviens : jeux lineaires quadratiques">
</div>

<div v-click="2" class="gt-projection-step">
<div>

## Equilibres Markoviens

- Resolution d'equations differentielles
- Jeux lineaires quadratiques -> solution analytique

</div>
<img src="./images/img_052.png" alt="Solution analytique des jeux lineaires quadratiques">
</div>

---
layout: default
---

# Méthodes calculatoires

<p v-click.hide="1">Comment chercher une trajectoire lorsque la cible se déplace elle aussi ?</p>

<div v-click="[1, 2]" class="gt-projection-step"><div><h2>Modéliser les mouvements</h2><p>Chaque équation décrit une vitesse : l’indice e désigne le fuyard, p le poursuivant. Chaque joueur agit sur sa trajectoire par sa commande u.</p></div><img src="./images/img_053.png" alt="Équations du mouvement du fuyard et du poursuivant"></div>

<div v-click="[2, 3]" class="gt-projection-step"><div><h2>Calculer une trajectoire ou une politique</h2><p>Une méthode directe discrétise les commandes et optimise sous les contraintes du mouvement. Une approche par programmation dynamique cherche plutôt la valeur du jeu en chaque état, en résolvant une équation aux dérivées partielles.</p></div></div>

<div v-click="3" class="gt-projection-step"><div><h2>Explorer par échantillonnage</h2><p>Comparez les quatre cartes : les obstacles ne bougent pas, mais l’arbre RRT s’étend au fil des tirages. Les branches sont des mouvements réalisables, pas des particules qui estiment une position cachée.</p><p>Davantage d’échantillons enrichit l’exploration ; ces images ne prouvent pas l’optimalité du trajet.</p></div><img src="./images/img_054.png" alt="Quatre cartes du même terrain avec un arbre de trajectoires de plus en plus développé"></div>

<style scoped>
p:has(> em:only-child) { position:absolute; bottom:34px; left:42px; right:42px; }
</style>

*Notebooks : [GameTheory-14-DifferentialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-14-DifferentialGames-Python.ipynb) (equilibres, LQ) · [GameTheory-09c-Stackelberg-SecurityGame-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09c-Stackelberg-SecurityGame-Python.ipynb) (Stackelberg). Poursuite-evasion par RRT : pas de notebook dedie.*

---
layout: dense
---

# Apprentissage multi-agents -- self-play, NFSP, PSRO

## Quand l'equilibre s'apprend au lieu de se calculer

- Self-play : l'agent devient son propre adversaire -- la population des strategies passees tient lieu d'opposant
  - Fictitious Play : meilleure reponse a la frequence empirique des coups adverses
  - NFSP : un reseau apprend la meilleure reponse, un autre la politique moyenne -- l'equilibre emerge de leur melange
  - PSRO (Policy-Space Response Oracles) : population de meilleures reponses imbriquees, l'echelle ou FP s'essouffle
- La serie se decline en jumeau C# pour les TP .NET

*Notebooks : [GameTheory-17-MultiAgent-RL-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL-Python.ipynb) (self-play, FP, NFSP, PSRO) · [GameTheory-17-MultiAgent-RL-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL-CSharp.ipynb) (jumeau C#).*

---
layout: dense
---

# Jeux de programmes : FairBot et DUPOC

## Même dilemme, autre objet de décision

**DUPOC** : faire défection sauf si l’on prouve la coopération adverse. **FairBot** applique cette règle au code de son vis-à-vis. Le choix porte sur un programme, pas sur un chemin entre matrices.

- Agent-programme : code public + budget de raisonnement fini (Barasz et al. 2014, Critch 2016)
  - Interprete total : budget nul = action immediate, budget epuise = arret -- la terminaison est structurelle, pas esperee
  - Simuler l'adversaire coute des steps : chaque borne `MAX_DEPTH` / `STEP_BUDGET` deplace l'equilibre atteignable
- Equilibre de programmes par simulation : deux adversaires au comportement identique sont traites pareil -- l'inspection syntaxique, elle, se trompe
- Compagnon formel : module `ProgramGames.Bounded` du lake `game_theory_lean` -- code public, budget, interprete `act`
- Oracles reflexifs (Fallenstein, Taylor, Christiano 2015) : decider sur sa propre decision sans paradoxe

*Notebooks : [Dynamics-04-Open-Source-Game-Theory-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-04-Open-Source-Game-Theory-Python.ipynb) · [Dynamics-05-Agents-Bornes-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-05-Agents-Bornes-Python.ipynb) · [Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb) (preuves bornees) · [Dynamics-05-Agents-Bornes-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-05-Agents-Bornes-Lean.ipynb) · [Dynamics-07-Equilibres-par-Simulation-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-07-Equilibres-par-Simulation-Python.ipynb) · [GameTheory-04e-Reflective-Oracles-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04e-Reflective-Oracles-Python.ipynb).*

---
layout: default
---

# Pourquoi deux FairBot peuvent coopérer

> **Énoncé.** Pour la version non bornée dans une théorie de preuve adaptée, FairBot face à sa copie coopère. Ce n’est pas une garantie pour tout budget fini.

## Stratégie de preuve

La coopération est déclenchée par sa propre démontrabilité contre la copie. Le théorème de Löb permet de conclure ; en version bornée, la taille des preuves doit aussi être contrôlée.

---
layout: dense
---

# Jeux ouverts et lentilles -- composer les jeux

## La theorie des jeux compositionnelle

- Open game : un jeu a frontieres -- entrees, sorties, couts, strategies locales
  - Lentille (get/set) : le regard qui lit l'etat global et reecrit localement -- composer les jeux, c'est composer les lentilles
  - Propriete de Hedges : la meilleure reponse de la composition est la composition des meilleures reponses -- quand elle tient
- Casser la composition : deux surfaces d'attaque ou la meilleure reponse composee cesse d'etre l'equilibre du jeu compose
- Abstraction a dette mesurable (Kroer & Sandholm) : resoudre le jeu abstrait puis retransporter la strategie -- avec une borne sur ce que le detour coute au pire cas

*Notebooks : [Metajeux-01-Open-Games-Lentilles-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-01-Open-Games-Lentilles-Python.ipynb) (lentilles, Hedges) · [Metajeux-02-Casser-la-Composition-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-02-Casser-la-Composition-Python.ipynb) (attaques) · [Metajeux-03-Abstraction-a-Dette-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-03-Abstraction-a-Dette-Python.ipynb) (bornes d'abstraction).*

---
layout: section
---

# Changer les règles, le jeu ou les agents

---
layout: default
---

# Métajeux : qui peut changer le jeu ?

**Composer.** Deux décisions s’enchaînent : le choix en amont modifie ce que l’agent en aval peut faire. Vérifier les meilleures réponses séparément ne dispense pas de vérifier les interfaces.

**Abstraire.** Résoudre un jeu réduit est utile si l’on peut mesurer ce que perd la stratégie une fois ramenée dans le jeu initial.

**Transformer.** Dans la topologie $2\times2$, un observateur fait varier les gains. Cela devient une **méta-action** si un joueur peut choisir la transformation : préciser son coût et son moment.

[Composer des jeux ouverts](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-01-Open-Games-Lentilles-Python.ipynb) · [Mesurer la dette d’abstraction](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-03-Abstraction-a-Dette-Python.ipynb) · [Explorer les chemins entre jeux](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb)

---
layout: default
---

# Trois mécanismes distincts de coopération

| Situation | Ce qui peut soutenir la coopération |
| --- | --- |
| **On se revoit.** | Un gain immédiat peut coûter une relation profitable : comparer les gains actualisés de la coopération et d’une déviation. |
| **On peut lire le programme adverse.** | Un agent peut conditionner son action à ce qu’il arrive à établir sur l’autre. Un budget de preuve ou de simulation limite ce qu’il voit. |
| **On contribue à plusieurs.** | Dans un bien public, on peut bénéficier de l’effort des autres sans contribuer. Observer les contributions individuelles et le résultat collectif. |

[Jeux répétés](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb) · [Coût du raisonnement](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb) · [Biens publics](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb) · [Joueur LLM](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-10-Joueur-LLM-Python.ipynb)

---
layout: default
---

# Coalitions : former un groupe, puis partager

- **Pouvoir.** Dans un vote pondéré, le poids seul ne suffit pas : un membre compte lorsqu’il fait passer une coalition de perdante à gagnante.
- **Surplus.** La valeur de Shapley répartit la valeur créée en moyennant les contributions marginales sur les ordres d’arrivée. Ce n’est pas un test de stabilité : le cœur demande qu’aucun groupe ne préfère partir.
- **Allocation.** Pour un échange de reins, les compatibilités imposent des échanges réalisables ; une affectation de coût minimal et un échange par cycles ne résolvent pas en général le même problème.

[Calculer le pouvoir avec SMT](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Coalitions/Coalitions-01-Pouvoir-Coalitionnel-SMT-Python.ipynb) · [Échange de reins et Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Coalitions/Coalitions-03-Echange-de-Reins-Lean-Python.ipynb) · [Certifier une affectation](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/Coalitions/Coalitions-05-Lean-Affectation-Lean.ipynb)

---
layout: default
---

# Choix social : élire, apparier, composer un comité

| Problème | Ce qu’il faut vérifier |
| --- | --- |
| **Classer des options.** | Les préférences individuelles peuvent être transitives alors que les majorités par paires forment un cycle. Le score et la règle par paires ne répondent pas à la même question. |
| **Apparier des personnes.** | Une paire absente de l’appariement peut-elle l’améliorer pour les deux personnes ? Si oui, l’appariement n’est pas stable. |
| **Élire plusieurs représentants.** | Un comité ne se juge pas seulement par la popularité de ses membres : qui représente-t-il, et peut-on modifier le résultat en votant stratégiquement ? |

[Comparer les scrutins](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb) · [Tester la stabilité](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-02-Stable-Marriage-Gale-Shapley-Python.ipynb) · [Manipulation en scrutin à plusieurs sièges](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-10-Manipulation-Strategique-MultiWinner-Python.ipynb)

---
layout: default
---

# Information privée : révéler, filtrer ou informer ?

- **Signaler.** Une personne déjà informée choisit un message ou une action observable. Le destinataire doit en déduire ce que l’émetteur sait.
- **Filtrer.** Le côté non informé conçoit un menu. Les choix des participants révèlent de l’information si les incitations les conduisent à se trier.
- **Persuader.** L’émetteur s’engage à l’avance sur une règle de divulgation. La question n’est plus seulement « que dire ? », mais « quelle expérience rendre publique ? ».

[Marché des citrons](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17b-Asymmetric-Information-Python.ipynb) · [Filtrer par un menu de loyers](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16j-Screening-Loyer-Information-Python.ipynb) · [Persuasion bayésienne](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17e-Bayesian-Persuasion-Python.ipynb)

---
layout: default
---

# Deux prolongements : transitions et règles exécutables

**Jeux stochastiques.** Deux joueurs ne choisissent pas seulement un gain immédiat : leurs actions modifient les probabilités du prochain état. À chaque état, le jeu de Shapley combine récompense du tour et valeur de continuation.

[Calculer la valeur par itération de Shapley](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-22-Jeux-Stochastiques-Shapley-Python.ipynb)

**Failles légales.** Un ensemble de règles autorise des opérations une à une ; leur enchaînement peut pourtant produire une issue que le mécanisme n’avait pas prévue. Le carnet sépare la recherche d’un chemin admissible de la preuve d’optimalité dans son modèle.

[Chercher le témoin avec Python, le vérifier avec Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-23-Loopholes-Fiscaux-Python-Lean.ipynb)

---
layout: default
---

# Valeur actualisée

> **Énoncé.** Dans un jeu stochastique fini à deux joueurs à somme nulle, avec facteur d’actualisation strictement inférieur à un, l’opérateur de Shapley admet une unique valeur fixe.

## Stratégie de preuve

Modifier toutes les valeurs de continuation d’au plus une unité change chaque gain actualisé d’au plus le facteur d’actualisation. La contraction donne unicité et convergence. Un témoin Lean pour un jeu de règles, lui, certifie un chemin particulier, pas cette convergence.

---
layout: section
---

# Questions ?

---
layout: section
---

# Plan du cours

---
layout: default
---

# Sommaire (suite)

- I. Introduction
- II. Resolution de problemes
- III. Bases de connaissances et logique
- IV. Incertitude et modèles probabilistes
- V. Théorie des jeux
- **VI. Apprentissage**
- VII. Traitement du langage naturel
- VIII. Presentation projets

---
layout: dense
---

# Projets de groupe

1. Moteur de recherche augmente par le raisonnement et le langage naturel
2. Conception de bots de services sur reseaux sociaux
3. Conception d'un modèle d'inference pour l'analyse de sentiment
4. Création d'une plateforme sémantique LDP
5. Resolution de Captchas par deep learning
6. Entrainement de stratégies de trading algorithmiques sur crypto monnaies
7. Amelioration par l'apprentissage d'un agent joueur de Go simple
8. Evolution de vaisseaux spatiaux par algorithmes génétiques dans le jeu de la vie
9. Pilotage d'un cluster de cache distribue pour le portage d'applications dans le Cloud

---
layout: end
---

# Merci

**Jean-Sylvain Boige**

jsboige@myia.org
