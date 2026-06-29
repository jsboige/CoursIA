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

## Deux articles fondateurs

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

### 2. Engineering Emergence (Jansma & Hoel, 2025)

**Engineering Emergence**, Abel Jansma, Erik Hoel, arXiv 2025 (et *I figured out how to engineer
emergence*, Erik Hoel, The Intrinsic Perspective, 2025).

Second pilier conceptuel : la recherche **systématique des échelles causales pertinentes**. Un
système dynamique peut être analysé à plusieurs niveaux ; certaines macro-échelles ne sont pas
de simples compressions pratiques, elles révèlent une organisation causale plus nette, plus
déterministe, moins dégénérée. ICT y puise son outillage multi-échelle (micro / méso / macro,
partitions, hiérarchies de contributions, signatures scale-free). Notebooks associés : ICT-5,
ICT-6, ICT-7.

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
└── ict/
    ├── self_sorting.py      # ✅ modèle vue-cellule (Cell, SelfSortingArray, scheduler)
    ├── kin_sorting.py       # ✅ règles enrichies : réparation bidirectionnelle + affinité kin
    ├── sorting_metrics.py   # ✅ sortedness, monotonie, inversions, agrégation, recovery
    ├── trajectories.py      # ✅ évolution d'états, attracteurs, trajectoire de Φ, événements
    ├── causal_emergence.py  # ✅ CE 2.0 (Hoel 2025) : primitives causales, apportionnement, EC
    ├── tpm_estimation.py    # ✅ pont simulation → chaîne de Markov → TPM (état-à-état)
    ├── scale_free.py        # ✅ diagnostic scale-free (MLE de Hill, KS, choix de xmin, branchement)
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
