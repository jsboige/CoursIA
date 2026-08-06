# ICT — Jambe C4 — Grammaire de propagation & seuil de bascule (π, W, causalité) : quand une représentation locale transforme le tout

> **Statut.** Document de cadrage formel, grade **C-documentaire** (cadrage, pas de dispatch expérimental). Consolide la **jambe C4** de l'arc ICT — **jambe de rencontre** centrale entre les fils thomien, grothendieckien, luhmanien et fristonien, issue du tour 755 de la conversation de référence (2026-07-20). C4 est explicitement *inter-jambes* : elle **ne démarre pas** la série ICT, elle **articule** ce que les jambes autonomes (animats C1/C2, argumentation C3, LLM) auront produit. Issue-source : [#7743](https://github.com/jsboige/CoursIA/issues/7743). See [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT). *Part of* [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT).
>
> **Objet.** Documenter (a) **le cycle à quatre temps** sur lequel C4 est construite : *totalité → représentant local → énoncé condensé → action en retour sur la totalité* ; (b) **le seuil de bascule** sous forme d'une **jauge** `(π, W, causalité)` — prégnance de la représentation locale × accessibilité via le workspace × pouvoir causal do-calculus ; (c) **les instanciations** par jambe-sœur (animats C1/C2, argumentation C3, LLM) qui rendent la jauge mesurable ; (d) **le pont avec D1** (strate 7 cadrage formel, [#7745](https://github.com/jsboige/CoursIA/issues/7745), [`strate7-cadres-libres.md`](strate7-cadres-libres.md) livré c.1246) où la jauge (π, W, causalité) **est** le seuil ρ_c de performativité ; (e) **le déblocage potentiel de C3** [#7742](https://github.com/jsboige/CoursIA/issues/7742) (jambe de la morphogenèse rhétorique, *gelée* tant que corpus public non branché) : C4 fournit à C3 la *forme mesurable* de la qualité d'un coup ontologique `η`.
>
> **Discipline.** Cadrage grade C — **AUCUNE nouvelle dépendance expérimentale** n'est créée. Les ancres citées (notebooks ICT-19b, ICT-14b, modules `ict/`, fichiers `docs/ict/`, PRs [#9579](https://github.com/jsboige/CoursIA/pull/9579) [#9596](https://github.com/jsboige/CoursIA/pull/9596) [#9551](https://github.com/jsboige/CoursIA/pull/9551) [#9547](https://github.com/jsboige/CoursIA/pull/9547) [#7336](https://github.com/jsboige/CoursIA/pull/7336) [#7341](https://github.com/jsboige/CoursIA/pull/7341)) sont sur `origin/main` au moment de la rédaction. Le document **ne propose pas** de test direct de la grammaire de propagation — il la *cadrent* comme **jauge falsifiable** (qui rend dicibles à la fois les seuils franchis et les seuils non-franchis). Cf. [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) §« Pourquoi cette grille » — on ne confond pas une grille avec un verdict.
>
> **Avertissement méthodologique.** La jambe C4 est *de rencontre* : elle **assume** la multiplicité des jambes-sœurs (animats, argumentation, LLM) et **ne prétend pas** les réduire. Chaque jambe-sœur garde sa propre grille de mesure ; C4 *articule* ces grilles sous la forme d'une jauge commune `(π, W, causalité)`, mais ne les agrège pas en un scalaire unique. La dissolution successive de Φ / F / K ([`dissolution-scalaires.md`](dissolution-scalaires.md) PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) MERGED c.1238) reste la leçon : *pas de scalaire unique pour des phénomènes de complexités distinctes*. C4 *contourne* ce risque en posant une **jauge multi-composantes** (3 dimensions, pas 1), pas un scalaire.

## 0. Position dans la série

C4 se tient à l'intersection de plusieurs fils :

- **Fil thomien** : la *prégnance* π est directement héritée de la théorie des catastrophes (cf. [`docs/ict/synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md), et la lecture dédiée de la *Sémiophysique* — [#7739](https://github.com/jsboige/CoursIA/issues/7739), PR [#9559](https://github.com/jsboige/CoursIA/pull/9559) MERGED c.1240).
- **Fil grothendieckien** : la *non-canonicité* des prolongements d'un espace local (cf. [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md)) donne la forme de la *grammaire* (plusieurs prolongements non-équivalents admissibles, `|Ext(L_t, L_{t+1})| > 1`).
- **Fil luhmanien / fristonien** : l'*autopoïesis* et l'*active inference* donnent la forme de la boucle *représentation locale → action sur la totalité* (le système n'est pas *représenté* passivement, il agit pour maintenir ses propres conditions d'existence).
- **Fil do-calculus** : *P(R)* est directement l'application du do-calculus de Pearl (cf. *« Causality »*, Cambridge UP, 2009) à la grammaire de propagation : on interventionne la bascule représentation-locale → action-sur-tout, et on mesure la divergence des trajectoires.

C4 **opérationnalise** la convergence de ces fils en une jauge falsifiable : **« À quel moment une représentation locale acquiert-elle assez de prégnance, d'accessibilité et de pouvoir causal pour transformer le système global qui l'a produite ? »** (cf. [#7743](https://github.com/jsboige/CoursIA/issues/7743) verbatim).

## 1. Le cycle à quatre temps

C4 décrit un cycle que toute jambe-sœur instancie, et dont la *bascule* — le passage du temps 3 au temps 4 — est précisément **ce que la jauge (π, W, causalité) mesure**.

### 1.1 Temps 1 : totalité

L'état initial est un **système global** `S` (un animat, un débat argumentatif, un écosystème de modèles génératifs). `S` n'est pas *représenté* en propre : il est *vécu* par ses parties (agents, propositions, modèles), qui n'en ont qu'une vue locale. La *totalité* est ici *implicite* : elle n'existe comme telle que par la **récurrence** des représentations locales qui s'y rapportent.

Ce premier temps est celui de la **complexité non-réduite** : `S` est trop complexe pour qu'un seul représentant en capture la totalité. Toute représentation de `S` est donc *forcément locale* — et c'est précisément ce que le temps 2 installe.

### 1.2 Temps 2 : représentant local

Un sous-système (un agent, une proposition, une classe de modèles) **concentre** une partie de l'information de `S` en une *représentation locale* `r`. Cette concentration se fait sous une contrainte : `r` doit être *transportable* (entre agents, entre temps, entre substrats). La contrainte de transportabilité force une **condensation** : `r` n'est pas `S` mais un *résumé* de `S`, choisi sous la contrainte de ce qui est jugulable.

C'est ici que la **prégnance π** entre en jeu : `π_t(r)` mesure la *quantité d'information de `S` qui est préservée dans `r`* (cf. §2.1). Une représentation locale trop peu prégnante est *banale* (elle ne dit rien sur `S`) ; trop prégnante, elle est *paradoxale* (elle en dit trop, et sa contradiction interne la rend inutilisable). La *bonne* prégnance est celle qui préserve **l'information discriminante** sur `S` tout en restant condensable en un *énoncé*.

### 1.3 Temps 3 : énoncé condensé

L'énoncé condensé est **ce qui devient public** : la représentation locale `r` est *traduite* en une proposition, une phrase, un modèle, un signal, qui peut être *transmis* à d'autres sous-systèmes. C'est ici que **l'opérateur de workspace W_t** entre en jeu (cf. §2.2) : `W_t(r)` mesure *à quels autres sous-systèmes* `r` est *accessible* dans `S`. Sans `W_t`, la représentation locale reste *privée* (un seul agent y a accès) ; avec `W_t` suffisamment large, `r` devient *publique* et candidat à la bascule.

L'énoncé condensé n'est **pas** un simple *encodage* : c'est un acte de **sélection** — on choisit *ce qui devient public*, et ce choix est lui-même un acte de *mécanisme* (cf. D1, [`strate7-cadres-libres.md`](strate7-cadres-libres.md) §2.3, mécanisme `M`). Tous les sous-équivalents de `r` ne sont pas rendus publics — `M` choisit *lequel*.

### 1.4 Temps 4 : action en retour sur la totalité

C'est le **temps décisif** : la représentation locale condensée et rendue publique **agit** sur `S` lui-même. Ce n'est pas une *représentation de* `S` mais une *transformation de* `S`. La boucle se ferme : `S` est transformé par l'une de ses propres représentations locales (qui a passé la jauge π / W / causalité). C'est précisément ici que **P(R)** mesure la *puissance de la bascule* : sans `P(R)`, l'énoncé condensé est *décoratif* (il parle de `S` sans le transformer) ; avec `P(R)` suffisamment grand, l'énoncé devient *performatif* (il reconfigure `S`).

Le cycle complet est ce que la strate 7 appelle un **coup ontologique** `η` (cf. D1 §2.2) : un agent (au sens étendu : un mécanisme, une convention, une institution) *modifie* `L_t` en `L_{t+1}` en *proposant* `η : G_t → G_{t+1}`. La grammaire de propagation de C4 *est* le cycle des quatre temps vécu par un coup ontologique.

## 2. Le seuil (π, W, causalité)

La bascule du temps 3 au temps 4 est **mesurable** par une jauge à trois composantes. Chaque composante est strictement définie, falsifiable, et déjà instanciée dans au moins une jambe-sœur.

### 2.1 π_t — prégnance

La **prégnance** est la mesure *quantitative* de l'information de `S` préservée par la représentation locale `r`. Formellement, dans la matrice 4-objets de la série ICT (cf. [`dissociations-matrix.md`](dissociations-matrix.md), PR [#9584](https://github.com/jsboige/CoursIA/pull/9584) MERGED c.1244), π_t est la **3e composante** du tuple `(s, q, π, W)`. Elle se mesure :

- *Capacité de discrimination* : étant donné deux états globaux `S_1 ≠ S_2` proches, `π_t(r)` est grande si `r` les distingue ;
- *Stabilité sous perturbation* : `π_t(r)` est grande si `r` reste prégnante sous des perturbations locales de `S` ;
- *Compression utile* : `π_t(r)` est grande si le *résumé* `r` n'est pas trivialement équivalent à `S` (i.e. si condenser a *perdu* quelque chose, mais ce quelque chose est *non-essentiel*).

Une `π_t` faible indique que `r` est *banal* (perd toute information discriminante) ; une `π_t` excessive indique que `r` *est* `S` (la condensation n'a pas eu lieu). La *bonne* prégnance est dans la **bande intermédiaire** où `r` est à la fois *résumé* et *informative*.

### 2.2 W_t — accessibilité (workspace)

L'accessibilité via le workspace est **qui** dans `S` peut accéder à `r`. Formellement, `W_t(r)` est l'*opérateur* de la 4e composante de la matrice 4-objets : pour un sous-système `X ⊆ S`, `W_t(X) ⊆ S` est l'ensemble des sous-systèmes qui ont accès à l'information de `X` au temps `t`. `r` est *publique* dans `S` au temps `t` si `W_t(r) = S` (tous les sous-systèmes ont accès) ; `r` est *privée* si `W_t(r) = {X_r}` (seul l'agent qui l'a produite y a accès).

L'opérateur `W_t` est **l'objet ICT-24** (cf. [#5635](https://github.com/jsboige/CoursIA/issues/5635)) — l'axe Global Workspace de la série. La dissociation matrice ([`dissociations-matrix.md`](dissociations-matrix.md)) pose explicitement `q_t` *bon / W_t* *sélectif* comme **preuve par dissociation** que les deux grandeurs ne se réduisent pas l'une à l'autre : une représentation peut être de bonne qualité (`q_t` élevée) sans être largement accessible (`W_t` étroite) — c'est l'erreur classique du modèle « bonne idée, mal diffusée ».

### 2.3 P(R) — pouvoir causal (do-calculus)

Le pouvoir causal est l'**effet de la bascule** sur `S`. Formellement, c'est l'application du do-calculus de Pearl :

```
P(R) = D( Pr( trajectories of S | do(R) ) ‖ Pr( trajectories of S | do(¬R) ) )
```

où `do(R)` est l'intervention *poser la bascule* (rendre `r` public et le laisser agir sur `S`) et `do(¬R)` est l'intervention *ne pas poser la bascule* (garder `r` local, ou l'empêcher d'agir). `P(R)` est la divergence KL entre les distributions des trajectoires de `S` dans les deux cas.

`P(R) ≈ 0` : la bascule est *décorative* — qu'elle ait lieu ou non, `S` évolue de la même façon. C'est un *énoncé public* qui ne transforme rien.
`P(R) ≫ 0` : la bascule est *performatrice* — qu'elle ait lieu ou non, `S` évolue différemment. L'énoncé public *reconfigure* la totalité.

`P(R)` est la grandeur la plus directement liée à la **performativité** au sens de la strate 7 (cf. D1 §4.2) : un coup ontologique qui ne *bascule pas* est *cheap* ; un coup ontologique qui *bascule* est *performant*. `P(R)` est la mesure *quantitative* de cette bascule.

### 2.4 Critère de bascule : seuil et hystérésis

La **bascule** du temps 3 au temps 4 a lieu quand le *triplet* `(π_t, W_t, P(R))` franchit simultanément un **seuil critique** `ρ_c`. Formellement :

```
bascule(R, t) ⟺ π_t(r) ≥ π_c ∧ W_t(r) ≥ W_c ∧ P(R) ≥ P_c
```

où les seuils `(π_c, W_c, P_c)` sont **spécifiques à la jambe-sœur** :

- Pour les animats (C1/C2), les seuils sont liés à la *survie* de l'animat : la bascule représente *l'apprentissage* qui change la trajectoire de l'animat.
- Pour l'argumentation (C3), les seuils sont liés à la *stabilité du débat* : la bascule représente le moment où un argument *est retenu* et change la conclusion du débat.
- Pour les LLM, les seuils sont liés à l'*inoculation* (cf. ICT-23/ICT-25, [#5104](https://github.com/jsboige/CoursIA/issues/5104) [#5105](https://github.com/jsboige/CoursIA/issues/5105)) : la bascule représente le moment où une instruction *est internalisée* et change les générations futures.

L'**hystérésis** est une caractéristique importante du seuil : une fois la bascule effectuée, *rétrograder* `r` à un statut non-public coûte plus cher que de l'installer (c'est la **dette d'irréversibilité** de D1 §3.6). Cette asymétrie constitutive est ce qui distingue les *macro-faits* des *phénomènes transitoires* : une bascule qui s'est installée est, par construction, *difficile à défaire*.

## 3. Instanciations par jambe-sœur

La jauge (π, W, causalité) n'est pas un *abstrait* : elle est **instanciée** dans les jambes-sœurs de l'arc ICT. Cette section donne la forme concrète de chaque instanciation.

### 3.1 Animats (C1/C2)

Les jambes **C1 (animat qui explore)** et **C2 (animat inhibé de Laborit)** mesurent la grammaire de propagation sur des **animats simulés** (cf. ICT-15b [#7288](https://github.com/jsboige/CoursIA/issues/7288), ICT-15c/15d/15e bridge2 PR [#9477](https://github.com/jsboige/CoursIA/pull/9477) MERGED c.1236).

- **Temps 1 — totalité** : l'environnement de l'animat (un labyrinthe, un terrain, un graphe).
- **Temps 2 — représentant local** : une *carte interne* (un sous-ensemble de l'environnement que l'animat se représente).
- **Temps 3 — énoncé condensé** : une *action* de l'animat (un mouvement, un choix, un signal de marquage).
- **Temps 4 — action sur la totalité** : l'action de l'animat *transforme* l'environnement (l'animat mange une ressource, déplace un objet, modifie le marquage pour les autres animats).

La jauge (π, W, causalité) mesure alors : *quelle est la prégnance de la carte interne ?* (π) ; *à quels autres animats la carte est-elle accessible ?* (W, par marquage) ; *comment l'action transforme-t-elle la distribution des ressources ?* (P(R), par do-calculus appliqué à la trajectoire de l'environnement).

C'est dans cette jambe que **la dette d'irréversibilité** est la plus visible : un marquage qui a changé l'environnement est *difficile à défaire* (cf. [#7743](https://github.com/jsboige/CoursIA/issues/7743) verbatim *« la représentation locale agit en retour sur ce qu'elle représente »*).

### 3.2 Argumentation (C3)

La jambe **C3 (morphogenèse rhétorique de la transition)** [#7742](https://github.com/jsboige/CoursIA/issues/7742) mesure la grammaire sur des **débats argumentatifs** (cf. ICT argumentation Phase A [#7289](https://github.com/jsboige/CoursIA/issues/7289) PR [#7336](https://github.com/jsboige/CoursIA/pull/7336) MERGED + Phase B PR [#7341](https://github.com/jsboige/CoursIA/pull/7341) MERGED).

- **Temps 1 — totalité** : l'état du débat (les arguments en présence, les positions des agents, les croyances sur les croyances).
- **Temps 2 — représentant local** : un argument particulier (une proposition, un schéma, une figure rhétorique).
- **Temps 3 — énoncé condensé** : l'argument *est retenu* dans le débat (par d'autres agents).
- **Temps 4 — action sur la totalité** : l'argument retenu *change la conclusion du débat* (ou la déplace significativement).

La jauge (π, W, causalité) mesure alors : *quelle est la force persuasive de l'argument ?* (π, prégnance = quantité de position adverse déplacée) ; *à quels agents l'argument est-il accessible ?* (W, par les canaux rhétoriques) ; *comment l'argument retenu change-t-il l'issue du débat ?* (P(R), par do-calculus sur les trajectoires de croyances).

C'est dans cette jambe que **la dette d'irréversibilité** a la forme la plus saillante : un débat qui a *basculé* sur un argument retenu est, par la suite, *réinterprété* à travers cet argument (cf. ICT argumentation Phase B *« discursive irreversibility debt »*). C3 est *gelée* [#7742](https://github.com/jsboige/CoursIA/issues/7742) tant que corpus public non branché ; **C4 fournit à C3 la jauge falsifiable** qui rendrait la jambe *opérationnalisable* dès que le corpus devient disponible (cf. §5.3).

### 3.3 LLM (jambe LLM, strate 5)

La **jambe LLM** (ICT-21/22/23/24/25, cf. [#5101](https://github.com/jsboige/CoursIA/issues/5101) [#5102](https://github.com/jsboige/CoursIA/issues/5102) [#5104](https://github.com/jsboige/CoursIA/issues/5104) [#5635](https://github.com/jsboige/CoursIA/issues/5635) [#5105](https://github.com/jsboige/CoursIA/issues/5105)) mesure la grammaire sur des **modèles génératifs entraînés à l'échelle du milliard de paramètres**.

- **Temps 1 — totalité** : l'état du modèle (ses poids, sa distribution latente, ses SAE features).
- **Temps 2 — représentant local** : une *feature* extraite par un SAE (sparse autoencoder) ou une *latente* J-lens.
- **Temps 3 — énoncé condensé** : la feature *est activée* dans un prompt, et le modèle *génère* du texte qui la mobilise.
- **Temps 4 — action sur la totalité** : la génération *transforme* les états futurs (par RLHF, par inoculation, par le simple fait d'être archivée dans des corpus d'entraînement futurs).

La jauge (π, W, causalité) mesure alors : *quelle est la prégnance de la feature ?* (π, capacité de discrimination entre inputs) ; *à quelles têtes d'attention la feature est-elle accessible ?* (W, par les têtes qui s'activent sur la feature) ; *comment la génération change-t-elle la trajectoire du modèle ?* (P(R), par inoculation RL PR [#9592](https://github.com/jsboige/CoursIA/pull/9592) OPEN c.1249 reward_dynamics).

C'est dans cette jambe que **le seuil ρ_c** est le plus directement comparable à celui de la strate 7 : l'inoculation ICT-25 est *précisément* le moment où une représentation (instruction, persona, cadrage) acquiert assez de π / W / P(R) pour transformer le modèle.

### 3.4 Synthèse cross-jambes

Les trois jambes-sœurs partagent la **structure** du cycle à quatre temps mais diffèrent dans :

- *Ce qui tient lieu de « totalité » `S`* : environnement, débat, modèle.
- *Ce qui tient lieu de « représentant local » `r`* : carte interne, argument, feature SAE.
- *Ce qui tient lieu de « mécanisme `M` »* : choix d'action de l'animat, rhétorique du débat, instruction RL.
- *Ce qui tient lieu de « dette d'irréversibilité »* : marquage environnemental, conclusion retenue, persona internalisée.

La jauge (π, W, causalité) est **invariante par instanciation** : c'est précisément *ce qui rend la grammaire de propagation commune* aux trois jambes. C'est cette invariance qui fait de C4 une *jambe de rencontre* et non une jambe isolée.

## 4. Pont avec D1 (strate 7 cadrage formel)

La jambe C4 et la strate 7 cadrage D1 sont **complémentaires, pas concurrentes** : C4 *opérationnalise* la jauge `(π, W, causalité)` ; D1 *cadrent* la strate 7 sous la forme d'un jeu évolutif `G_t` à 6 proxys. Le présent paragraphe explicite le pont.

### 4.1 Le seuil (π, W, causalité) instancie ρ_c

D1 §2.4 introduit la notion de **mécanisme** `M(η_1, ..., η_n) = G_{t+1}` qui décide ce qui devient public. La question centrale posée par D1 est : *« quelles institutions permettent l'apparition de vocabulaires utiles sans capture immédiate par les stratégies manipulatrices ? »*. Le seuil `(π, W, causalité)` de C4 est **la jauge falsifiable** qui répond à cette question : un coup ontologique `η` est *performant* (et *non manipulateur*) s'il franchit simultanément `π ≥ π_c`, `W ≥ W_c`, `P(R) ≥ P_c`, **avec** `I(R) > 0` (la dette d'irréversibilité est *positive*, ce qui distingue un coup performatif d'un coup ornemental qui s'évapore).

`ρ_c` dans D1 = `(π_c, W_c, P_c)` dans C4. **Le seuil de performativité** de la strate 7 est le même objet que **le seuil de bascule** de C4, vu sous deux angles : D1 le *nomme* (en termes de jeu évolutif), C4 le *mesure* (en termes de prégnance / accessibilité / causalité).

### 4.2 Le seuil comme proxy P(R) parmi les 6

Dans le 6-uplet de D1 §3 (`O_t, ΔA_t, C_t = |Ext(G_t)|, P(R), institutionnalisation, I(R)`), la grandeur `P(R)` (pouvoir performatif, do-calculus) est **directement** la grandeur `P(R)` de C4 §2.3. Les deux grandeurs sont *la même grandeur* : la divergence KL entre les distributions des trajectoires du système sous l'intervention et sous la non-intervention. C4 *spécifie* la mesure ; D1 *positionne* la grandeur dans le 6-uplet (comme une composante parmi 5 autres, pas comme un agrégat).

Les autres grandeurs du 6-uplet trouvent aussi leur pendant en C4 :

- `O_t` (expansion ontologique) ↔ le temps 2 de C4 (concentration d'information dans `r`).
- `ΔA_t` (ouverture politique) ↔ le temps 3 de C4 (rendre `r` public = ouvrir des actions nouvelles).
- `C_t = |Ext(G_t)|` (non-canonicité) ↔ l'extension non-canonique qui *choisit* quel `r` devient public (le mécanisme `M`).
- `I(R)` (dette d'irréversibilité) ↔ l'hystérésis de C4 §2.4.

### 4.3 La grammaire de propagation *est* la tresse opérationnelle

La **tresse** ([`tresse-cartographie.md`](tresse-cartographie.md) PR [#9551](https://github.com/jsboige/CoursIA/pull/9551) MERGED c.1239) pose l'horizontalité : *quatre opérations distinctes* (Grothendieck, Schmidhuber, Thom, Friston) *ne se réduisent pas* les unes aux autres. C4 montre comment ces quatre opérations **se rencontrent** dans le cycle à quatre temps :

- *Opération grothendieckienne* = *temps 3 → 4* : l'extension non-canonique `η : G_t → G_{t+1}` qui *fait* la bascule.
- *Opération fristonienne* = *temps 4 → 1* : l'inférence active qui *ferme* la boucle en laissant le système percevoir son nouvel état.
- *Opération thomienne* = *temps 1 → 2* : la *prégnance* `π_t` qui sélectionne la forme condensable.
- *Opération schmidhubérienne* = *temps 2 → 3* : la *compression* qui produit l'énoncé public.

**La grammaire de propagation est la tresse rendue opérationnelle** : ce sont *les mêmes opérations*, vues non pas comme une cartographie horizontale mais comme une *succession dans le temps*.

## 5. Pourquoi cette jambe est *de rencontre*

### 5.1 L'origine — tour 755

C4 est issue du **tour 755** de la conversation de référence (2026-07-20). C'est un moment où plusieurs jambes *autonomes* (animats, argumentation, LLM) étaient déjà bien avancées, et où la question s'est posée de savoir *ce qui les rend commensurables*. La réponse à cette question *est* C4 : la commensurabilité des jambes est dans **la grammaire de propagation** qu'elles partagent, pas dans un quelconque agrégat scalaire.

Cette origine *par rencontre* est ce qui distingue C4 des autres jambes : C1, C2, C3 sont issues d'une *question* spécifique (l'animat, l'animat inhibé, le débat argumentatif) ; C4 est issue d'une *question de commensurabilité* entre les autres jambes.

### 5.2 L'articulation inter-jambes

C4 *articule* ce que les jambes-sœurs auront produit en posant la jauge `(π, W, causalité)` comme **jauge inter-jambes** : une grandeur qui, mesurée sur une jambe-sœur, est *comparable* à la grandeur mesurée sur une autre jambe-sœur (à condition que la *bande intermédiaire* de π, le *W* minimal pour rendre l'énoncé public, et le *seuil P_c* soient calibrés sur la jambe-sœur, pas universels).

C'est cette articulation qui permet à C4 de **rendre dicibles** à la fois :

- les cas où une jambe-sœur a *basculé* (la jauge a été franchie simultanément sur ses trois dimensions) ;
- les cas où une jambe-sœur *n'a pas basculé* (au moins une des trois dimensions est sous le seuil) ;
- les cas où une jambe-sœur a *partiellement basculé* (par exemple `π ≥ π_c` mais `W < W_c` — *énoncé prégnant mais inaccessible*).

Les trois cas sont *honnêtement dicibles* par la même jauge, ce qui est la *promesse falsifiabiliste* que D1 §7 appelle de ses vœux pour la strate 7.

### 5.3 Le déblocage potentiel de C3

C3 (jambe de la morphogenèse rhétorique, [#7742](https://github.com/jsboige/CoursIA/issues/7742)) est *gelée* tant que corpus public non branché. La gelure a deux composantes :

- *Corpus* : un *grand corpus public de débats argumentatifs* (par exemple issu de débats parlementaires, de plateformes de débat, de corpus journalistiques annotés en rhétorique) est nécessaire pour mesurer la jauge `(π, W, causalité)` *sur la jambe argumentation* ;
- *Calibration* : les seuils `(π_c, W_c, P_c)` spécifiques à la jambe argumentation doivent être *calibrés* sur des cas où la bascule a effectivement eu lieu, pour servir de référence.

C4 ne lève pas la gelure — elle ne *crée* pas le corpus, et elle ne *calibre* pas les seuils. Mais C4 *fournit la forme* sous laquelle la gelure pourra être levée : une fois un corpus public disponible, et une fois des cas de référence identifiés, la jauge `(π, W, causalité)` est *immédiatement opérationnelle* sur la jambe argumentation. C3 *gagne en attente* une grille de mesure déjà construite — il suffira de l'instancier.

C'est le sens du verbe **articuler** dans la phrase *« C4 ne démarre pas la série ; elle articule ce que les jambes autonomes auront produit »* : C4 *prépare la commensurabilité* des jambes sans *forcer* leur démarrage.

## 6. Ce que ce document n'est pas

Pour éviter la confusion entre jauge et verdict, ce document assume explicitement ce qu'il n'est **pas** :

- **Ce n'est pas une mesure de la jauge.** Le présent document *pose* la jauge `(π, W, causalité)` ; il ne la *mesure* sur aucun cas particulier. Les mesures sont dans les jambes-sœurs (ICT-15b/15c/15d/15e pour les animats, ICT argumentation Phase A/B pour l'argumentation, ICT-21 à ICT-25 pour les LLM).
- **Ce n'est pas une unification des jambes-sœurs.** C4 *articule* la commensurabilité des jambes, mais ne les réduit pas. Les animats, les débats, les LLM restent des *phénomènes distincts*, et la jauge est *invariante par instanciation*, pas *universelle*. Les seuils `(π_c, W_c, P_c)` sont propres à chaque jambe.
- **Ce n'est pas une thèse sur la conscience.** La grammaire de propagation est un *objet formel* (un cycle à quatre temps, une jauge à trois dimensions) ; elle n'est **pas** une thèse sur le sujet, l'esprit, ou la conscience. La posture est la même que dans D1, D3, et l'arc général ICT : on décrit la *forme*, pas le *contenu* subjectif.
- **Ce n'est pas une PR de code ou de notebook.** C'est un **cadrage formel** d'une *jambe* ICT. Aucun notebook n'est créé ou modifié par ce document. La jauge est *posée*, pas *opérationnalisée sur un cas*.
- **Ce n'est pas un déblocage immédiat de C3.** C4 fournit à C3 *la forme* d'une jauge opérationnelle, mais C3 reste *gelée* tant que le corpus public de débats argumentatifs n'est pas branché (cf. §5.3). Le présent document *ouvre un chemin*, pas un résultat.
- **Ce n'est pas un matériau strate 6/7 sensible.** Cf. [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 3 — la frontière privé → public est stricte. Ce cadrage reste au niveau de la *forme* (jauge, seuils, hystérésis, dette) ; il ne traite pas des *cas* au-delà des instanciations canoniques (animat, débat, LLM).

## 7. Statut hiérarchique (mesuré / construit / nommé sans démonstration)

| Niveau | Élément |
|---|---|
| **Mesuré** (par les jambes-sœurs) | `π_t` via ICT-14b / ICT-Dissociation-SaillancePregnance (`docs/ict/dissociations-matrix.md` PR [#9584](https://github.com/jsboige/CoursIA/pull/9584) MERGED c.1244) · `W_t` via ICT-24 [#5635](https://github.com/jsboige/CoursIA/issues/5635) · `P(R)` via inoculation RL ICT-25 [#5105](https://github.com/jsboige/CoursIA/issues/5105) PR [#9592](https://github.com/jsboige/CoursIA/pull/9592) OPEN (reward_dynamics 4th detector) |
| **Construit** (formalisé dans le présent cadrage) | Le cycle à quatre temps · la jauge `(π, W, causalité)` · la notion de *bascule* · la notion d'*hystérésis* · la correspondance C4 ↔ D1 (ρ_c = (π_c, W_c, P_c)) · la lecture C4 = tresse opérationnelle · le déblocage potentiel de C3 par la forme |
| **Nommé sans démonstration** (grade C, posé pour cadrage) | L'idée que *la grammaire de propagation est invariante par instanciation* (§3.4) · l'idée que *la tresse est rendue opérationnelle par C4* (§4.3) · l'idée que *C4 prépare la commensurabilité sans forcer le démarrage* (§5.3) |

Le passage « nommé sans démonstration » au rang « construit » ou « mesuré » est un **livrable futur** :

- *Construire* = instancier la jauge sur une nouvelle jambe-sœur (par exemple : l'audio génératif, la robotic swarm) et vérifier que le cycle à quatre temps + la jauge *captent* effectivement la grammaire de propagation.
- *Mesurer* = calibrer les seuils `(π_c, W_c, P_c)` sur cette nouvelle jambe-sœur et observer des cas de bascule effective.

Ce passage n'est **pas** un claim actuel. Si C4 tient ce passage, ce sera une PR grade B à célébrer ; sinon, les éléments resteront au statut « nommé sans démonstration », et le cadrage restera cadrage.

## Voir aussi

- **Issue source** : [#7743](https://github.com/jsboige/CoursIA/issues/7743) — jambe C4 — grammaire de propagation & seuil de bascule. Le présent document en est la livraison.
- **Epic umbrella** : [#4588](https://github.com/jsboige/CoursIA/issues/4588) (ICT strate 5+).
- **Cadrage D1 (strate 7, variables libres, free coordinates)** : [#7745](https://github.com/jsboige/CoursIA/issues/7745), [`strate7-cadres-libres.md`](strate7-cadres-libres.md) — livré en PR [#9596](https://github.com/jsboige/CoursIA/pull/9596) c.1246. C4 instancie la jauge `(π, W, causalité)` ; D1 pose le 6-uplet et le seuil ρ_c = `(π_c, W_c, P_c)` en tant qu'instance.
- **Cadrage D3 (strate 7 boussole narrative)** : [#7747](https://github.com/jsboige/CoursIA/issues/7747), [`strate7-boussole-myth.md`](strate7-boussole-myth.md) — livré en PR [#9579](https://github.com/jsboige/CoursIA/pull/9579) MERGED c.1243. D3 *raconte* la strate 7 ; D1 la *formalise* ; C4 *opérationnalise* le seuil de bascule.
- **Jambe C3 (morphogenèse rhétorique, gelée)** : [#7742](https://github.com/jsboige/CoursIA/issues/7742). C3 *gelée* tant que corpus public non branché ; C4 fournit *la forme* d'une jauge opérationnelle qui rendra C3 *opérationnalisable* dès que le corpus sera disponible.
- **Jambe C1/C2 (animats)** : ICT-15b [#7288](https://github.com/jsboige/CoursIA/issues/7288), ICT-15c/15d/15e bridge2 PR [#9477](https://github.com/jsboige/CoursIA/pull/9477) MERGED c.1236. Instanciation animat de C4.
- **Jambe argumentation (Phase A et B)** : [#7289](https://github.com/jsboige/CoursIA/issues/7289), PR [#7336](https://github.com/jsboige/CoursIA/pull/7336) MERGED + PR [#7341](https://github.com/jsboige/CoursIA/pull/7341) MERGED. Instanciation débat de C4.
- **Jambe LLM (ICT-21 à ICT-25)** : [#5101](https://github.com/jsboige/CoursIA/issues/5101) [#5102](https://github.com/jsboige/CoursIA/issues/5102) [#5104](https://github.com/jsboige/CoursIA/issues/5104) [#5635](https://github.com/jsboige/CrossIA/issues/5635) [#5105](https://github.com/jsboige/CoursIA/issues/5105). Instanciation LLM de C4.
- **Cartographie tresse (B4 non-recollement)** : [#7738](https://github.com/jsboige/CoursIA/issues/7738), [`tresse-cartographie.md`](tresse-cartographie.md) — livré en PR [#9551](https://github.com/jsboige/CoursIA/pull/9551) MERGED c.1239. C4 = la tresse rendue opérationnelle (cf. §4.3).
- **Dissolution des scalaires** : [#7736](https://github.com/jsboige/CoursIA/issues/7736), [`dissolution-scalaires.md`](dissolution-scalaires.md) — livré en PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) MERGED c.1238. C4 *contourne* le risque du scalaire unique en posant une jauge multi-composantes (3 dimensions, pas 1).
- **Matrice de dissociations** : [#7734](https://github.com/jsboige/CoursIA/issues/7734), [`dissociations-matrix.md`](dissociations-matrix.md) — livré en PR [#9584](https://github.com/jsboige/CoursIA/pull/9584) MERGED c.1244. Les grandeurs `π_t` et `W_t` de C4 sont *directement* la 3e et la 4e composante du tuple `(s, q, π, W)`.
- **Synthèse invariants/dissociations/obstructions** : [#7399](https://github.com/jsboige/CoursIA/issues/7399), [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md). La jauge C4 *s'ajoute* à la grille 3-régimes comme une 4e dimension (la *bascule* est ce qui rend la grille falsifiable *opérationnellement*).
- **Cadrage N2 (trajectoires de représentations)** : [#7396](https://github.com/jsboige/CoursIA/issues/7396), [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md) — livré en PR [#8541](https://github.com/jsboige/CoursIA/pull/8541) MERGED. Le pivot états → représentations *précède* C4 : il pose que la *représentation* est l'objet à mesurer, et C4 prend le relais pour *mesurer sa bascule*.
- **Lecture dédiée Thom (Sémiophysique)** : [#7739](https://github.com/jsboige/CoursIA/issues/7739), PR [#9559](https://github.com/jsboige/CoursIA/pull/9559) MERGED c.1240. La notion de *prégnance* `π_t` est *directement* issue de la lecture thomienne (cf. C4 §0).
- **Contexte de la conversation (tour 755)** : Conversation 2026-07-20, distillation *par rencontre* (cf. C4 §5.1).

— *CoursIA-2 — c.1247 (po-2025) — 2026-08-06*
