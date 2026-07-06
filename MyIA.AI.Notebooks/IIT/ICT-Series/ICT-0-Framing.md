# ICT-0 — Cadrage de la série *Integrated Causal Trajectories*

> Document de cadrage de l'Epic **#4588**. La série **ICT** prolonge la série **IIT / PyPhi** :
> elle passe de l'étude des structures causales *à un instant* à celle de leurs *trajectoires*.

## De l'état à la trajectoire

La série [IIT](README.md) apprend à mesurer l'organisation causale d'un système **à un état donné** :
matrice de transition (TPM), sous-système, $\Phi$, structure cause-effet (CES), partitions,
coarse-graining. C'est une photographie : une forme causale figée.

La série **ICT** (Integrated Causal Trajectories) déplace la question vers le **film** :

```
C0 → C1 → C2 → ... → Cn
```

où chaque $C_t$ est une description causale intégrée — ou un résumé causal — du système à
l'instant $t$. L'intuition directrice :

> une structure intégrée n'est pas seulement une forme causale à un instant donné ; elle peut
> aussi être étudiée comme une forme qui **se maintient**, **se transforme**, **se répare**,
> **change d'échelle** et **traverse un espace de possibles**.

Les questions centrales deviennent dynamiques et multi-échelles :

- comment une structure causale évolue-t-elle dans le temps ?
- une trajectoire conserve-t-elle une **identité** malgré les perturbations ?
- quelles transformations sont locales, globales, réversibles, irréversibles ?
- existe-t-il une **macro-description** plus lisible ou plus causale que la micro-description ?
- quelles échelles contribuent vraiment à l'explication du comportement ?
- certains systèmes produisent-ils spontanément des signatures multi-échelles, voire scale-free ?

## Double lecture du sigle

L'acronyme **ICT** porte **deux lectures** qu'il faut tenir ensemble :

1. **« Integrated Complexity Theory »** — la théorie fondatrice, héritée d'IIT et reformulée par
   une discussion de référence (préservée verbatim dans
   [`ICT-0-Annexe-IntegratedComplexityTheory.md`](ICT-0-Annexe-IntegratedComplexityTheory.md)) :
   un $\Phi_\text{dyn}$ qui répond aux critiques classiques d'IIT (intractabilité, caractère statique,
   absence de dynamiques temporelles, explosion combinatoire, adéquation phénoménologique) en
   introduisant (a) une **intégration dynamique** sur des mécanismes significatifs, (b) une
   **décomposition hiérarchique** à plusieurs échelles, et (c) des **méthodes d'approximation**
   pour rendre le calcul praticable.

2. **« Integrated Causal Trajectories »** — la méthode construite dans `ICT-Series/` (filiation
   Levin, Hoel, Thom) : partir d'un substrat minimal (le tri auto-organisé), y exhiber
   expérimentalement la robustesse, le délai de gratification, l'agrégation par affinité, l'émergence
   causale multi-échelles, puis remonter vers les grandeurs que la théorie cherche à formaliser.

La réconciliation tient en **une phrase** : *les trajectoires causales intégrées sont la voie
calculable vers la théorie de la complexité intégrée.* La méthode porte le second nom, l'ambition
porte le premier. Aucun des deux ne remplace l'autre :

- la **théorie** pose le langage unificateur (ce que $\Phi_\text{dyn}$, l'énergie libre, la
  compression cherchent à capturer) ;
- la **méthode** construit les cas calculables qui instancient ce langage et permettent de le
  mesurer *sans complaisance* ;
- la **strate 5** (ICT-14 → ICT-24) ferme la boucle : sur le banc cross-substrat (ICT-15 #5090),
  les trois scalaires fondateurs $\Phi / F / K$ se rencontrent ; l'identité MDL (ICT-16 #5099),
  l'$\epsilon$-machine (ICT-17 #5100) et le LLM comme quatrième substrat (ICT-22 #5102) réalisent
  littéralement la théorie fondatrice, sur des substrats où le tri ne suffit plus.

Cette double lecture est assumée et documentée ici précisément parce qu'elle a longtemps été
implicite — la série se présentait comme « Integrated Causal Trajectories » (méthode), alors que
la théorie fondatrice parle « Integrated Complexity Theory ». Le cadrage explicite évite la
confusion et nomme l'enjeu.

## Flèche du temps & réversibilisation — l'idée fondatrice

Le panorama qui a orienté la série vers la *complexité intégrée* portait un **fil conducteur
resté non-dit** : la **réversibilisation**. Une trajectoire qui développe une compétence
« gratuite » (*for free*), non prévue par le mécanisme programmé, est exactement ce qu'un
processus **à l'équilibre / réversible** (au sens du *detailed balance*) ne peut PAS produire.
L'émergence a une **signature thermodynamique** : elle brise la symétrie temporelle. Or, jusqu'ici,
la série mesurait l'intégration ($\Phi$), la surprise ($F$), la compression ($K$) — jamais
l'irréversibilité elle-même. Il manquait l'**instrument de mesure** de la flèche du temps.

**L'ancrage Levin / Fridman.** Dans son entretien avec Lex Fridman sur les algorithmes de tri,
Michael Levin est fasciné par l'émergence, dans un simple tri, d'un **mécanisme algorithmique
non programmé** — un travail supplémentaire *for free* qui va, dit-il, « dans le sens d'une
réversibilisation ». C'est très précisément la compétence *for free* que **ICT-3**
(`RobustnessDelayedGratification`) démontre en strate 1 : le tri « fait plus que trier ». La
flèche du temps est ici une **flèche causale** (Reichenbach, ordre de Pearl, flèche
thermodynamique) ; la **production d'entropie** en est la signature quantitative — la marque
thermodynamique de l'agentivité.

**Cet instrument est construit en ICT-18 — Flèche du temps & réversibilisation** ([#5279](https://github.com/jsboige/CoursIA/issues/5279),
GPU-free). Appliqué *rétrospectivement* aux trajectoires déjà enregistrées (tri, May bistable,
Axelrod, Gray-Scott), il répond à une question centrale et falsifiable : **« que perd-on quand
on force une trajectoire ICT à devenir réversible ? »** La réponse, mesurée (production d'entropie
$\sigma$, erreur de *detailed balance*, quantités effacées par la projection réversible), est la
quantité d'agentivité / de calcul émergent que la trajectoire portait.

## Deux articles fondateurs

La série s'appuie sur **deux publications scientifiques** — une par branche — et, pour chacune, sur
un **éclairage informel** qui en rend les enjeux intuitifs sans en relâcher l'exigence. La branche du
**tri-morphogenèse** (Zhang, Goldstein & Levin) est éclairée par l'entretien de Michael Levin avec
Lex Fridman ; la branche de l'**émergence causale** (Jansma & Hoel) par l'essai de vulgarisation
d'Erik Hoel *I Figured Out How to Engineer Emergence*. Les deux éclairages jouent le même rôle : ils
fournissent le **vocabulaire** et l'**intuition** de chaque programme, jamais un blanc-seing — les
revendications spéculatives y sont tenues à distance et ne sont créditées que par la mesure (voir le
[principe méthodologique](#principe-méthodologique) plus bas).

### 1. Le tri comme morphogenèse minimale (Zhang, Goldstein & Levin, 2025)

**Classical sorting algorithms as a model of morphogenesis: self-sorting arrays reveal
unexpected competencies in a minimal model of basal intelligence**, *Adaptive Behavior*, 2025
— [arXiv:2401.05375](https://arxiv.org/abs/2401.05375).

Les auteurs prennent des algorithmes de tri classiques et les transforment en systèmes
**distribués** : au lieu d'un contrôleur global, chaque élément devient une cellule locale qui
applique sa propre politique de mouvement. Le tri devient une **trajectoire collective** dans
un espace de configurations — une morphogenèse minimale, totalement transparente et calculable,
où apparaissent pourtant des compétences inattendues : robustesse aux cellules endommagées,
*délai de gratification*, agrégation par « kin » (algotype), récupération après lésion.

C'est le **banc d'essai d'entrée** de la série : tout est observable, les règles sont simples,
les trajectoires sont enregistrables. Notebooks associés : **ICT-2**, ICT-3, ICT-4.

### 2. L'ingénierie de l'émergence multi-échelle (Jansma & Hoel, 2025)

**Engineering Emergence**, Abel Jansma & Erik Hoel, 2025 —
[arXiv:2510.02649](https://arxiv.org/abs/2510.02649) — prolongé par le cadre *Causal Emergence 2.0*
([arXiv:2503.13395](https://arxiv.org/abs/2503.13395)).

Les auteurs cherchent **systématiquement les échelles causales pertinentes** d'un système dynamique.
Partant de sa matrice de transition (TPM), ils parcourent le **treillis des partitions** de ses états
— chaque partition est un *coarse-graining* candidat, une macro-échelle obtenue en « regroupant » des
micro-états — et attribuent à chacune un **score d'émergence** entre 0 et 1, bâti sur deux primitives
information-théoriques (un gain de **déterminisme**, une baisse de **dégénérescence**). La plupart des
échelles n'apportent rien ; seul un petit sous-ensemble **irréductible** contribue, et il s'ordonne du
micro vers le macro en une **hiérarchie émergente**. Certains réseaux (Barabási–Albert au voisinage de
$\alpha = 1$) produisent même une signature **scale-free**.

C'est le **second banc d'essai** de la série : là où Levin fournit le vocabulaire cognitif, Hoel
fournit l'**outillage multi-échelle** (micro / méso / macro, partitions, hiérarchies de contributions,
signatures scale-free) qu'ICT branche sur le tri. Notebooks associés : **ICT-5**, **ICT-6**, ICT-7.

## Pourquoi parler de « compétences » pour un algorithme de tri ?

Toute la série emploie un vocabulaire cognitif — *compétences*, *robustesse*, *délai de
gratification*, *mémoire de la cible* — pour décrire un algorithme de tri parfaitement
déterministe. Métaphore commode, ou affirmation qu'on peut défendre ? Le **programme de
recherche sur l'intelligence diverse** de Michael Levin (dont est issu le papier ci-dessus)
fournit la réponse — et, surtout, la **méthode** qui la rend honnête. On en résume ici les
quatre idées qui éclairent la série ; l'entretien de Levin avec Lex Fridman les expose longuement
(voir *Pour aller plus loin*).

### 1. L'intelligence est un spectre, et notre intuition sur le substrat est faillible

Le réflexe naturel est de décider *a priori* qu'un tableau qui se trie « ne peut pas » avoir de
compétences — parce qu'il ne ressemble pas à un animal. Levin invite à se méfier de ce réflexe :

> « We don't have a magic sense or really good intuition for what the mapping is between the
> embodiment of something and the degree of intelligence it has. We think we do because we have
> an N of one example on Earth. » — *M. Levin*

Nous n'avons **aucune intuition fiable** de la correspondance entre la *forme* d'un système et son
*degré* d'intelligence : nous croyons en avoir une, mais elle repose sur un unique exemple (la vie
terrestre telle que nous la connaissons). La conséquence méthodologique est nette : plutôt que de
trancher d'avance, on **teste**. Et c'est précisément ce que demandait Lex Fridman à propos de ce
type de travaux — « *to see if there are minds inside those sorting algorithms* » : non pas affirmer
qu'il y en a, mais déployer les outils comportementaux et regarder ce qu'ils révèlent.

### 2. Une définition opérationnelle : franchir des barrières vers un but

Pour sortir de la métaphore, il faut une définition **mesurable**. Levin reprend celle de William
James — l'intelligence comme capacité à atteindre *« the same goal by different means »* (le même
but par des moyens différents) — et la rend expérimentale :

> « Intelligence is the degree of ingenuity that it has in overcoming barriers between it and its
> goal. » — *M. Levin*

La recette est alors limpide : **placer une barrière entre le système et son but, et observer son
ingéniosité à la contourner.** C'est, mot pour mot, le protocole d'**ICT-2** et **ICT-3** :

- les cellules `frozen`, le régime `obstacle`, la lésion exogène **sont les barrières** ;
- la dégradation *gracieuse* de la sortedness, l'auto-réparation *systématique* (24/24 essais
  reviennent à 1.0 dans ICT-3), le *délai de gratification* compté épisode par épisode **sont la
  mesure** de cette ingéniosité.

Le vocabulaire cognitif n'est donc pas décoratif : il **nomme la grandeur que chaque expérience
sonde**. Quand ICT-3 balaie le taux de lésion, il ne fait pas qu'« étudier un algorithme de tri » —
il applique le test d'intelligence de Levin à un substrat minimal.

### 3. Le cône de lumière cognitif

Levin propose un axe unique pour ranger tout le spectre — le **cône de lumière cognitif** :

> « The cognitive light cone is the size of the biggest goal state that you can pursue. » — *M. Levin*

Ce n'est ni la portée des capteurs ni celle des effecteurs, mais **l'échelle du plus grand but
qu'un système peut activement poursuivre** : pour une bactérie, le sucre dans un rayon de 20 µm ;
pour un humain, des objectifs qui le dépassent dans l'espace et dans le temps (jusqu'« après sa
mort »). Ce qui varie le long du spectre, « *all the way down* », c'est la **taille de ce cône**.
Le tableau auto-organisé occupe l'extrémité minimale : son unique « but » est l'attracteur trié, et
la série ICT étudie comment cette poursuite de but **se maintient, se répare et change d'échelle**
sous perturbation — exactement les transformations de trajectoire annoncées plus haut.

### 4. Les revendications cognitives sont des revendications de protocole

Reste l'objection de fond : « mais est-ce *vraiment* de l'intelligence ? » Levin la dissout en
déplaçant la nature même de l'affirmation :

> « Cognitive claims are really protocol claims. When you tell me that something has some degree of
> intelligence, what you're really saying is, "This is the set of tools I'm going to deploy, and we
> can all find out how that worked out." » — *M. Levin*

Attribuer un degré d'intelligence à un système, ce n'est pas poser une thèse métaphysique : c'est
**s'engager sur une boîte à outils expérimentale** et exposer publiquement le résultat. L'affirmation
devient *falsifiable*. C'est le pendant exact du [principe méthodologique](#principe-méthodologique)
d'ICT — *mesurer ce que le modèle fait vraiment, pas ce qu'on espérait*. La même discipline impose
le garde-fou : ICT-2 rapporte honnêtement que le modèle minimal reproduit la robustesse et le délai
de gratification, **mais pas** l'agrégation « kin » du papier. Le cadre de l'intelligence diverse est
un **permis d'enquêter avec les bons outils**, pas un blanc-seing pour sur-interpréter — tout comme
l'IIT (voir la section « Portée scientifique et débats » du [README](README.md)) reste une théorie
vivante et contestée. C'est là que se loge l'humilité épistémique de Levin : le procès en
anthropomorphisme est, selon lui, mal posé — « *we have the same magic that everything has* » — mais
cette continuité ne s'établit qu'instrument en main, jamais par décret.

## Pourquoi une macro-échelle ferait-elle un *vrai* travail causal ?

La branche « émergence » emploie, elle aussi, un vocabulaire fort — une macro-échelle qui *émerge*,
qui *fait un travail causal*, une organisation qu'on *ingénierie*. Là encore : intuition commode, ou
affirmation défendable ? L'essai d'Erik Hoel *I Figured Out How to Engineer Emergence* — l'éclairage
informel de cette seconde jambe — expose l'intuition, et le cadre *Engineering Emergence* / *Causal
Emergence 2.0* fournit la **méthode** qui la rend honnête. On en retient quatre idées qui éclairent
ICT-5/6/7 (voir *Pour aller plus loin*).

### 1. L'objection réductionniste : la causalité « s'écoule » vers le micro

Le réflexe symétrique de celui de la branche Levin consiste à décider *a priori* qu'une macro-échelle
« ne peut pas » faire un vrai travail causal — que seule la micro-physique agit, et que tout niveau
supérieur n'est qu'un résumé commode. Hoel nomme ce réflexe et le pousse à sa conclusion :

> « Either you say everything is overdetermined, or you say that only the microscale is really doing
> anything (the classic reductionist option). » — *E. Hoel*

C'est ce que le philosophe Ned Block appelait le fait que la causalité « *drains away* » vers le
micro. La réponse d'ICT n'est pas de trancher par principe, mais de **mesurer** : à chaque
macro-échelle candidate, la structure causale gagne-t-elle en netteté, ou non ? C'est exactement le
protocole d'**ICT-5**, qui compare l'information effective et le $\Phi$ aux échelles micro et macro
avec le vrai `pyphi.macro` — et n'accorde d'émergence qu'à celles qui l'obtiennent réellement.

### 2. Une définition opérationnelle : un score sur le treillis des partitions

Pour sortir de la métaphore, il faut, ici aussi, une grandeur **mesurable**. « Émerger » cesse d'être
une impression : c'est un **score entre 0 et 1** attribué à chaque *coarse-graining*, bâti sur deux
primitives information-théoriques — un gain de **déterminisme**, une baisse de **dégénérescence**. On
parcourt le **treillis des partitions** des états du système et on lit quelles échelles gagnent
réellement en clarté causale.

> « The etymology of the word "system" is something like "I cause to stand together." » — *E. Hoel*

Autrement dit, ce qui fait qu'un ensemble de micro-états forme un « système » à une échelle donnée est
une **affirmation causale** — précisément ce que le score quantifie. C'est le cœur d'**ICT-6**, qui
estime une chaîne de Markov depuis les trajectoires de tri d'ICT-2, puis cherche l'émergence causale
multi-échelles avec l'outillage *Causal Emergence 2.0*, au-delà de la borne de taille de PyPhi.

### 3. Peu d'échelles comptent : la hiérarchie émergente

Le balayage ne consacre pas toutes les échelles. La plupart des partitions n'apportent rien ; seul un
petit sous-ensemble **irréductible** contribue — et ce sous-ensemble s'ordonne du micro vers le macro
en une **hiérarchie émergente**. L'idée est ancienne ; Herbert Simon la formulait dès 1962 :

> « …complexity takes the form of hierarchy—the complex system being composed of subsystems that, in
> turn, have their own subsystems, and so on. » — *H. Simon, "The Architecture of Complexity", 1962*

Distinguer les rares échelles porteuses de la masse des découpages inertes est ce que mesurent
**ICT-6** (hiérarchies de contributions) et **ICT-7**, qui va jusqu'à traquer une signature
**scale-free** — mais *sans se faire avoir* : MLE de Hill, choix de $x_{\min}$, test KS à la Clauset.
Un système peut *paraître* sans échelle tout en possédant une taille caractéristique ; ICT-7 refuse le
diagnostic hâtif.

### 4. « Engineer emergence » est un titre, pas une preuve

Reste la revendication forte — le titre lui-même, *« I figured out how to engineer emergence »*, et
son imagerie (les « ballons », le « jardin de pierres » des hiérarchies). ICT l'accueille comme un
**permis d'enquêter**, pas comme un résultat à importer. Hoel décrit d'ailleurs lui-même son essai
comme

> « an overview built for a larger audience, constructed in favor of conceptual understanding » —
> *E. Hoel*

c'est-à-dire une vulgarisation *conceptuelle*, assumée comme telle. Ce qu'ICT retient n'est donc pas
la promesse d'« ingénierie », mais le **score falsifiable** : et la même discipline oblige à rapporter
les échecs. Quand une macro-échelle **n'émerge pas**, ou quand un signal scale-free se révèle un
**fantôme statistique** (degrés de liberté cachés), les notebooks le disent. C'est le pendant exact,
pour cette branche, du [principe méthodologique](#principe-méthodologique) d'ICT — *mesurer ce que le
modèle fait vraiment, pas ce qu'on espérait* — et de la thèse de Levin sur les revendications de
protocole : l'émergence causale est une **grandeur qu'on expose au risque de la mesure**, jamais un
décret.

## Architecture : une couche `ict/` à côté de PyPhi

L'approche privilégiée ajoute un package léger `ict/` **à côté** de PyPhi. Cette couche
fonctionne de façon autonome pour les simulations, trajectoires et mesures simples (dépendances
minimales : bibliothèque standard + numpy/matplotlib pour les notebooks), et n'appelle PyPhi que
pour revenir à des calculs IIT stricts sur de petits systèmes.

```
IIT/
├── ICT-0-Framing.md                       # ce document
├── ICT-1-PhiTrajectories.ipynb            # ✅ trajectoires de Φ (vrai PyPhi)
├── ICT-2-SelfSortingMorphogenesis.ipynb   # ✅ premier livrable (#4588)
├── ICT-3-RobustnessDelayedGratification.ipynb  # ✅ étude quantitative
├── ICT-4-ChimericArraysKinAggregation.ipynb  # ✅ jeu de règles riche : agrégation « kin » émergente
├── ICT-5-CausalEmergence.ipynb            # ✅ émergence causale micro/macro (vrai pyphi.macro)
├── ICT-6-SortingToTPM-CausalEmergence.ipynb  # ✅ pont tri → TPM → émergence causale (CE 2.0)
├── ICT-7-ScaleFreeSignatures.ipynb        # ✅ signatures scale-free & criticalité (loi de Borel τ=3/2)
├── ICT-8-AttractorLandscapesEWS.ipynb     # ✅ strate 2 : paysages d'attracteurs + early-warning signals
├── ICT-9-AgencyRegeneration.ipynb         # ✅ strate 2 : agence = régénération réaction-diffusion (Gray-Scott)
├── ICT-10-CatastropheGrammar.ipynb        # ✅ charnière strate 2→3 : grammaire des catastrophes (fronce, pli, lacet de prédation)
└── ict/
    ├── self_sorting.py      # ✅ modèle vue-cellule (Cell, SelfSortingArray, scheduler)
    ├── kin_sorting.py       # ✅ règles enrichies : réparation bidirectionnelle + affinité kin
    ├── sorting_metrics.py   # ✅ sortedness, monotonie, inversions, agrégation, recovery
    ├── trajectories.py      # ✅ évolution d'états, attracteurs, trajectoire de Φ, événements
    ├── causal_emergence.py  # ✅ CE 2.0 (Hoel 2025) : primitives causales, apportionnement, EC
    ├── tpm_estimation.py    # ✅ pont simulation → chaîne de Markov → TPM (état-à-état)
    ├── scale_free.py        # ✅ diagnostic scale-free (MLE de Hill, KS, choix de xmin, branchement)
    ├── bistable.py          # ✅ strate 2 : modèle de pâturage de May, potentiel effectif, bifurcation pli
    ├── early_warning.py     # ✅ strate 2 : variance/AR1 roulantes, τ de Kendall, amincissement, détrendage
    ├── reaction_diffusion.py # ✅ strate 2 : simulateur Gray-Scott (Laplacien périodique, diffusion pure de contrôle)
    ├── agency.py            # ✅ strate 2 : ablation do(·), structure, recovery_score, repair_gain, similarité spectrale
    ├── catastrophe.py       # ✅ charnière strate 2→3 : fronce (cusp), équilibres/plis, lacet d'hystérésis, représentant interne p̂
    ├── distances.py         # à venir : distances entre états / structures / trajectoires
    └── ...
```

## Feuille de route des notebooks

| Notebook | Sujet | État |
|----------|-------|------|
| **ICT-0** | Cadrage de la série (ce document) | ✅ |
| **ICT-2** | [Self-sorting arrays : le tri comme morphogenèse](ICT-2-SelfSortingMorphogenesis.ipynb) — trajectoire, robustesse, délai de gratification, auto-réparation, impasses chimériques | ✅ |
| **ICT-1** | [Trajectoires de $\Phi$](ICT-1-PhiTrajectories.ipynb) — paysage de $\Phi$, trajectoire de $\Phi$ sur l'attracteur (pulsations), robustesse aux perturbations (vrai PyPhi) | ✅ |
| **ICT-3** | [Robustesse & délai de gratification](ICT-3-RobustnessDelayedGratification.ipynb) — étude quantitative : dégradation gracieuse, distributions de récupération, comptage du délai de gratification | ✅ |
| **ICT-4** | [Tableaux chimériques & agrégation émergente](ICT-4-ChimericArraysKinAggregation.ipynb) — réparation bidirectionnelle (guérit l'impasse d'ICT-2) puis affinité « kin » : l'agrégation par algotype émerge dans les degrés de liberté laissés par le tri, mesurée honnêtement (sans liberté, pas d'agrégation ; signe → ségrégation à la Schelling) | ✅ |
| **ICT-5** | [Émergence causale](ICT-5-CausalEmergence.ipynb) — $\Phi$ et information effective aux échelles micro/macro, recherche de coarse-graining (vrai `pyphi.macro`), émergence discriminante (Jansma & Hoel) | ✅ |
| **ICT-6** | [Pont tri → TPM](ICT-6-SortingToTPM-CausalEmergence.ipynb) — chaîne de Markov estimée depuis les trajectoires de tri, émergence causale multi-échelles (CE 2.0 *scale-free*, au-delà de la borne de taille de PyPhi) | ✅ |
| **ICT-7** | [Signatures scale-free & criticalité](ICT-7-ScaleFreeSignatures.ipynb) — détecter une signature sans échelle *sans se faire avoir* (MLE de Hill, choix de $x_{\min}$, KS, comparaison de modèles à la Clauset et al.) ; étalon critique (branchement, exposant $3/2$) vs tri auto-organisé qui *paraît* à queue lourde mais possède une échelle caractéristique (la taille), révélée par effondrement d'échelle | ✅ |
| **ICT-8** | [Paysages d'attracteurs & signaux précurseurs](ICT-8-AttractorLandscapesEWS.ipynb) — **strate 2**. Modèle de pâturage de May (1977), bistabilité + bifurcation pli ; *early-warning signals* (Scheffer 2009) : potentiel effectif, valeur propre → 0, variance ↑, autocorrélation ↑ (τ de Kendall), avec la leçon de protocole *sans complaisance* (amincir, détrendre) | ✅ |
| **ICT-9** | [Agence & régénération](ICT-9-AgencyRegeneration.ipynb) — **strate 2**. Morphogenèse réaction-diffusion de Gray-Scott (Pearson 1993) : un système qui **répare** sa forme vers un point de consigne **intrinsèque** après une ablation `do(·)`, l'agence **mesurée** comme *gain de réparation* (réaction-diffusion vs diffusion pure, deux mondes contrefactuels de Pearl). *Sans complaisance* : les mesures naïves de ressemblance (pixel-à-pixel, cosinus spectral) fabriquent un signal fantôme ; seule la structure restaurée contrastée au contrôle passif tient | ✅ |
| **ICT-10** | [Grammaire des catastrophes](ICT-10-CatastropheGrammar.ipynb) — **charnière strate 2→3**, prélude sémiophysique de R. Thom. Le squelette catastrophique (fronce, pli, fourche, hystérésis) **mesuré** : le métathéorème (le comptage d'équilibres ne change qu'aux plis, clôt la strate 2) et le **lacet de prédation** (cycle d'hystérésis à 2 catastrophes + représentant interne `p̂` qui anticipe, ouvre la strate 3). La correspondance linguistique du Ch.2 de Thom (pivots ↔ transitions de comptage ; verbe transitif SVO ↔ lacet ; anticipation ↔ `p̂`) **nommée**, avec le caveat de non-prédictivité et les barreaux du pont basse-dim → haute-dim (neurosymbolique, Lean, veille EML #4653). *Sans complaisance* : hors régime non dégénéré ($a<0$), zéro saut — fantôme | ✅ |
| **ICT-11** | [Profils d'agence causale](ICT-11-CausalAgencyProfiles.ipynb) — **strate 3**. L'agence de réaction-diffusion mesurée à plusieurs résolutions (micro/méso/macro) puis raccordée à l'émergence causale (Hoel, info effective, TPM à macro-variable scalaire = structure/variance du champ moyenné). *Sans complaisance* : les deux mesures d'agence se contredisent — `repair_gain` pic méso mais artefact-contaminé (score > 1, plancher de résolution), `basin_return_probability` strictement décroissante. Le raccord Hoel suit la mesure inflatée (`r≈+0.50` avec `repair_gain`) et ignore la mesure honnête (`r≈−0.14` avec `basin_return`) — suggestif mais non robuste. Verdict honnête : pas d'échelle privilégiée, l'hypothèse méso-émergente n'est pas confirmée | ✅ |
| **ICT-12** | [Champs de valence et animats](ICT-12-ValenceFieldsAndAnimats.ipynb) — **strate 3**. Premier toy model **actantiel spatial** : des animats évoluent dans un champ de valence (source attractive + obstacles repulsifs) ; la scène actantielle de Thom cesse d'être une correspondance nommée — les **rôles deviennent des grandeurs mesurées** (capture, évasion, irréversibilité, switching). Animat **réactif** (gradient instantané) vs **anticipateur `p̂`** (extrapolation). *Sans complaisance* : `p̂` **gagne** en balistique rapide (capture x4) mais **perd** en erratique (prédictions trompées par les demi-tours) et perd sur source bruitée. Le modèle interne paie son coût là où la source échappe au réactif **et** reste prévisible — régime-dépendant, ni universellement avantageux ni ruineux | ✅ |
| **ICT-13** | [Morphodynamique stratégique](ICT-13-AxelrodStrategicMorphodynamics.ipynb) — **strate 3**. Le dilemme du prisonnier itéré d'Axelrod (T=5, R=3, P=1, S=0) sert de morphospace stratégique : six stratégies (AllC, AllD, TFT, TFT généreuse, Pavlov, Grim) en tournoi round-robin, dynamique de réplication, bassins d'invasion. Quatre gates falsifiables mesurent la « stabilité de forme ». *Sans complaisance* : **Gate 1** TFT/Grim co-dominent (2.635) ; **Gate 2** Folk theorem analytique δ* = 0.500 vs numérique 0.550 ; **Gate 3** sous bruit d'exécution la réciprocité active (TFT) est le point de rupture (chute +0.40), Grim paradoxalement le plus robuste (+0.29) — contredit la prédiction Nowak-Sigmund ; **Gate 4** bassins d'invasion : TFT/Grim dès 2%, TFT généreuse à 34%, Pavlov/AllC jamais. Verdict honnête : la robustesse stratégique est **fonction du régime**, pas une propriété intrinsèque | ✅ |
| **ICT-14** | [Surprise & énergie libre](ICT-14-FreeEnergySurprise.ipynb) — **strate 4**. La jambe énergie-libre du représentationnel : *free energy* et *expected free energy* comme substrat computationnel de l'anticipation, articulation avec la trajectoire $\Phi_\text{dyn}$ et le représentant interne `p̂` d'ICT-10. Voir issue #5089 | ✅ |
| **ICT-Synthèse** | [Synthèse cross-substrat](ICT-Synthese-CrossSubstrat.ipynb) — **capstone strate 3**. Un seul appareil (la trajectoire causale intégrée) sur trois substrats (tri, Gray-Scott, Axelrod), trois échelles, trois régimes. *Sans complaisance* : chaque substrat pousse ses mesures à sa frontière et c'est précisément là que la méthode s'éprouve. Boucle de la strate 3 vers la **strate 5** : cross-substrat ouvre la possibilité de bancs partagés | ✅ |
| **ICT-15** | IntegratedComplexity — convergence Φ/F/K sur le banc cross-substrat. Le gate de convergence des trois scalaires fondateurs (information intégrée, énergie libre, complexité de Kolmogorov) sur le squelette de Thom. *Strate 4 / charnière vers strate 5*. Voir issue #5090 | 🚧 planifié |
| **ICT-16** | MDLTwoPartCode — le pont MDL : F (énergie libre) est la partie résiduelle du code K (Kolmogorov) + la bosse complexité-entropie. Identité MDL ↔ énergie libre. *Strate 5*. Voir issue #5099 | 🚧 planifié |
| **ICT-17** | EpsilonMachine — états causaux, complexité statistique, entropie d'excès : le gate Crutchfield vs Hoel. L'$\epsilon$-machine comme alternative computationnelle à l'émergence causale Hoel. *Strate 5*. Voir issue #5100 | 🚧 planifié |
| **ICT-18** | Flèche du temps & réversibilisation — l'**idée fondatrice** enfin outillée. Instrument rétrospectif GPU-free (`ict/time_arrow.py`) appliqué aux trajectoires déjà construites (tri, May, Axelrod, Gray-Scott) : distribution stationnaire, inversion temporelle, réversibilisation, production d'entropie. Question centrale : *que perd-on quand on force une trajectoire ICT à devenir réversible ?* Ancré ICT-3 (compétence *for free*) + entretien Fridman/Levin. *Strate 5, GPU-free*. Voir issue #5279 | 🚧 planifié |
| **ICT-19** | **Batterie de l'ENJEU** — construire la seconde batterie (auto-maintien / retour-au-bassin après `do(·)`) que ICT-18 nomme *hors de sa portée*, et la fusionner à la batterie MOYEN d'ICT-18 sur les substrats S1-S5 (Gray-Scott S4 = agent, S5 = pur dissipateur = contrôle négatif obligatoire). Cadrage B verrouillé (user 2026-07-06). Ancré sur la triade **moyen / fin / enjeu** du reframe #5352. GPU-free. Spec cadrage : #5483 — livrable cible : #5489. *Strate 5, GPU-free*. → Epic #4588 | 🚧 planifié |
| **ICT-20** | FeatureCatastrophes — calibration : changepoints, EWS et hystérésis sur transitions anodines en feature-space. *Strate 5*. Voir issue #5103 | 🚧 planifié |
| **ICT-21** | SAETrajectoires — Qwen + Qwen-Scope : des features SAE aux trajectoires d'états discrets, le substrat S4 (LLM sparse autoencoder). *Strate 5, GPU-required*. Voir issue #5101 | 🚧 planifié |
| **ICT-22** | LLMSubstrat — le transformer comme quatrième substrat du banc cross-substrat (tri, Gray-Scott, Axelrod, LLM). Double contrôle (passif / actif). *Strate 5, GPU-required*. Voir issue #5102 | 🚧 planifié |
| **ICT-23** | PersonaCatastrophe — expliquer le désalignement émergent par fronce, énergie libre et MDL : jouet + mesure in-context (capstone strate 5). Voir issue #5104 | 🚧 planifié |
| **ICT-24** | InoculationRL — réplication poids : GRPO à récompense hackable × inoculation, rewardspy, panel persona (capstone final, pont PostTraining). *Strate 5, GPU-required*. Voir issue #5105 | 🚧 planifié |

## Strate 2 — du tri transparent à la morphogenèse dynamique

La **strate 1** (ICT-1 à ICT-7) a fait du **tri auto-organisé** un marche-pied idéal : tout y est
calculable, les trajectoires sont enregistrables, et des compétences réelles (robustesse, délai de
gratification, agrégation « kin ») y apparaissent. Mais ce banc d'essai bute sur **trois limites**
dès qu'on veut voir émerger l'**agence** et l'**organisation générative** :

1. un **attracteur global unique**, dont le but (le tableau trié) est **imposé de l'extérieur** ;
2. **aucun point de consigne intrinsèque** — rien que le système « cherche » de lui-même ;
3. **pas de hiérarchie génératrice** — la richesse multi-échelle de la strate 1 est *analytique*
   (on la lit dans les TPM), pas **produite** par la dynamique.

La **strate 2** ouvre la *morphogenèse dynamique* sur des substrats dont le **paysage
d'attracteurs est engendré par la dynamique elle-même**, et lève ces limites une à une :

- **ICT-8** (bifurcation pli + *early-warning signals*) lève les limites **1** et **3** : un vrai
  paysage à **plusieurs bassins** séparés par un col, une **bifurcation** qui crée et détruit des
  attracteurs, et une hiérarchie naturelle (les deux bassins forment un gros-grain à deux
  macro-états, branché sur la causal emergence d'ICT-5/6). Le substrat — le modèle de pâturage de
  May, canonique des EWS (Scheffer 2009 ; Dakos 2012) — porte la narration *« les deux tressées »* :
  chaque image métaphorique (la vallée qui s'aplatit, la mémoire du danger, l'alerte avant la
  bascule) est **adossée à une grandeur mesurée**, et la leçon *sans complaisance* montre qu'une
  mesure naïve **fabrique ou masque** le signal — la métaphore n'est créditée que par la rigueur du
  protocole.
- **ICT-9** (réaction-diffusion régénérante, type Gray-Scott) lève la limite **2** : l'**agence**
  comme capacité à **maintenir et réparer sa propre forme** vers un *point de consigne intrinsèque*,
  démontrée *par contraste* — la réaction répare là où la simple diffusion dissout (l'analogue
  dynamique du « sans liberté, pas d'agrégation » d'ICT-4). L'agence n'y est jamais *déclarée* : elle
  est **mesurée** comme un gain de récupération sur un contrôle passif, après une intervention `do(·)`
  identique appliquée à deux mondes contrefactuels (Pearl). La leçon *sans complaisance* y est que les
  mesures naïves de ressemblance (distance pixel-à-pixel, similarité cosinus) **fabriquent un signal
  fantôme** sur un attracteur mitotique ou un champ sans structure — seule la structure restaurée,
  contrastée, tient.

- **ICT-10** (grammaire des catastrophes) est la **charnière** : il ferme la strate 2 sur son squelette
  catastrophique (le métathéorème — *l'obstacle engendre les êtres* — mesuré comme « le comptage d'équilibres
  ne change qu'aux plis ») et ouvre la strate 3 (agents) sur le **lacet de prédation** de Thom : un cycle
  d'hystérésis à deux catastrophes (perception, capture) et un **représentant interne** `p̂` dont le contenu
  anticipateur est *mesuré* contre trois baselines adverses sur trois familles de trajectoires — verdict
  honnête : avantage **régime-dépendant**, réel là où l'inertie est exploitable, illusoire ailleurs. C'est le **prélude
  sémiophysique** de R. Thom, tenu *sans complaisance* — chaque image (saillance, prégnance, actant) attachée
  à une grandeur calculée sur la fronce canonique, le caveat de non-prédictivité (Thom lui-même) explicite.

Les notebooks suivants (**ICT-11/12** profils d'agence causale et renormalisation causale,
**ICT-Synthèse**) poursuivront la même règle : *ne pas ouvrir cinq fronts à la fois* — une métaphore
n'entre dans ICT que lorsqu'elle est **attachée à une mesure**.

C'est la même discipline que la strate 1 (exécuter, mesurer, narrer le résultat réel) appliquée à
une dynamique qui, cette fois, **génère** son propre paysage de buts plutôt que de le recevoir.

## Principe méthodologique

ICT mesure ce que les modèles font **vraiment**, pas ce qu'on espérait. ICT-2 l'illustre :
le toy model minimal reproduit fidèlement la robustesse et le délai de gratification, mais
**pas** l'agrégation « kin » positive du papier (ses règles uni-directionnelles produisent au
contraire des impasses de coordination). Le notebook le dit honnêtement et renvoie l'agrégation
à ICT-4. [ICT-4](ICT-4-ChimericArraysKinAggregation.ipynb) tient cette promesse avec un jeu de
règles plus riche — et la même discipline : l'agrégation émerge, mais **seulement** dans les
degrés de liberté laissés par le tri (sans valeurs répétées, elle disparaît), ce que le notebook
mesure au lieu de le proclamer. Cette discipline — exécuter, mesurer, narrer le résultat réel —
est le fil conducteur de la série. C'est aussi la traduction concrète de la thèse de Levin selon
laquelle *les revendications cognitives sont des revendications de protocole* (cf. la section
**« Pourquoi parler de compétences ? »** ci-dessus) : une compétence n'est créditée à un modèle
qu'au vu de ce qu'une expérience explicite en mesure.

## ICT-19 — squelette de spec (cadrage B, voir #5483)

ICT-19 construit la **seconde batterie** (celle de l'**ENJEU**) qu'ICT-18 nomme *hors de sa portée*
dans son reframe #5352 (triade **moyen / fin / enjeu**), puis la **fusionne** à la batterie MOYEN
d'ICT-18 sur le banc de substrats S1-S5 de l'ICT-Synthèse.

### Périmètre (cadrage B, auto-maintien seul)

- **Batterie MOYEN** (empruntée ICT-18) — production d'entropie / réversibilisation thermodynamique
  (`ict/time_arrow.py`) : la *seule* grandeur `I_thermo` mesure.
- **Batterie ENJEU** (à construire) — mesure opérationnelle d'**auto-maintien** : retour au bassin
  attracteur `B` après une perturbation contrefactuelle `do(x ← x + δ)` (Pearl, fil rouge
  causalité ICT-5). `I_stake` = distance normalisée parcourue vers `B` (gain de réparation).
- **Livrable = PAIRE** `{I_thermo, I_stake}`, **pas indice agrégé**.

### Substrats (réutilisés de l'ICT-Synthèse, zéro nouveau substrat)

- **S1** (ICT-2 tri) — auto-organisé, point de consigne faible.
- **S2** (ICT-8 bistable) — deux bassins, pas de défense d'un point de consigne.
- **S3** (ICT-13 Axelrod) — réplicateur stratégique, équilibre de population.
- **S4** (ICT-9 Gray-Scott) — *l'agent* : dissipe *et* défend un point de consigne via la
  compétition Tu/Snell-Scott.
- **S5** — *pur dissipateur*, contrôle négatif **obligatoire** : système qui dissipe sans enjeu
  (réaction-diffusion hors-régime, ou chaîne markovienne stationnaire sans maintenance).

### Gates falsifiables

- **Gate ENJEU-1** : `I_stake(S4) > I_stake(S5) + marge`, avec `I_thermo(S4) ≈ I_thermo(S5)`
  (l'ICT-18 Gate 7 montre déjà que le MOYEN seul allume S4 et S5 à égalité). La PAIRE doit donc
  *séparer* l'agent du pur dissipateur là où le MOYEN seul ne le peut pas.
- **Gate ENJEU-2** (graduation) : `I_stake(S4) > {S3, S1} > S2 > S5`.

### Distinction sémantique (critique)

- **Réversibilité thermodynamique** (detailed balance, `σ=0`) = le **MOYEN** que `I_thermo` mesure.
- **Réversibilité comportementale** (récupérabilité cinématique de l'espace d'états,
  ICT-2/3/9, Levin *competency for free*) = la **FIN** que la lutte thermodynamique poursuit —
  *pas* un second axe à mesurer. Le retour au bassin `B` après `do(·)` est précisément **la
  manifestation opérationnelle de cette récupérabilité**, là où la production d'entropie en est
  le coût.

### Contraintes

- **GPU-free** (chaînes de Markov + ODE + reaction-diffusion 2D petit champ, kernel CPU).
- **Contrôle négatif obligatoire** (S5) : sans lui, la batterie ne prouve rien ; c'est
  l'ingrédient nommément manqué d'ICT-18, désormais comblé.
- **Résultat nul honnête** : si ENJEU-1 échoue, le verdict est *négatif* — pas maquillé en succès.
- Notebook exécuté CPU, outputs C.2 réels, 0 `raise NotImplementedError` (C.1), ≥3 exercices
  (return-to-basin / repair-gain / extension substrat), prose FR.

### Liens cadrage ICT-19

- Issue de cadrage : **#5483** — décision user 2026-07-06 (cadrage B verrouillé).
- Issue d'implémentation : **#5489** — acceptance criteria + livrables.
- Reframe parent : **#5352** — triade moyen / fin / enjeu (ICT-18 v2).
- Epic : **#4588** — registre des livrables ICT.

## Voir aussi

- [README de la série IIT](README.md) — fondations PyPhi (TPM, $\Phi$, CES, coarse-graining).
- Epic **#4588** — registre des livrables ICT.

### Pour aller plus loin — l'intelligence diverse (Levin)

- **Entretien Michael Levin × Lex Fridman** (transcript) — exposé long du programme : spectre de
  la cognition, cône de lumière cognitif, intelligence comme franchissement de barrières,
  revendications-protocole : <https://lexfridman.com/michael-levin-2-transcript/>. (Toutes les
  citations de la section « Pourquoi parler de compétences ? » en sont tirées.)
- Levin, *The Computational Boundary of a "Self": Cellular Decision-Making by the Collective
  Intelligence of Morphogenesis*, Frontiers in Psychology, 2019 — fondations théoriques du cône de
  lumière cognitif et de l'agentivité multi-échelle.
- Zhang, Goldstein & Levin, *Classical sorting algorithms as a model of morphogenesis*, Adaptive
  Behavior, 2025 — [arXiv:2401.05375](https://arxiv.org/abs/2401.05375) — le banc d'essai d'ICT-2/3.

### Pour aller plus loin — l'émergence causale (Hoel)

- **Erik Hoel, *I Figured Out How to Engineer Emergence*** (The Intrinsic Perspective, 2025) —
  l'exposé grand public du programme : coarse-graining sur le treillis des partitions, score
  d'émergence, hiérarchies émergentes, signatures scale-free :
  <https://www.theintrinsicperspective.com/p/i-figured-out-how-to-engineer-emergence>. (Toutes les
  citations de la section « Pourquoi une macro-échelle ferait-elle un vrai travail causal ? » en sont
  tirées.)
- Jansma & Hoel, *Engineering Emergence*, 2025 — [arXiv:2510.02649](https://arxiv.org/abs/2510.02649)
  — le cadre formel : primitives causales (déterminisme, dégénérescence), score d'émergence, treillis
  des partitions.
- *Causal Emergence 2.0* — [arXiv:2503.13395](https://arxiv.org/abs/2503.13395) — l'arrière-plan
  conceptuel : lever l'axiome d'exclusion de la formulation d'origine (Hoel, Albantakis & Tononi,
  PNAS 2013), pour que l'émergence puisse s'exprimer à *plusieurs* échelles à la fois.
