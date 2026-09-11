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
- le **virage représentationnel** — la **strate 4** (scalaires fondateurs $\Phi/F/K$ sur substrats
  non-LLM, ICT-14 → ICT-20) puis la **strate 5** (représentations internes des LLMs, ICT-21 → ICT-25),
  la charnière **grokking** (ICT-17b) entre les deux (cf. § *Deux axes*) — ferme la boucle : sur le
  banc cross-substrat (ICT-15),
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

## Extensions 2026-07 — la fin, la canonicité, l'identité et le discours

Le cadrage stratégique de 2026-07 (Epic #4588) étend la série sur **quatre fronts**, chacun ancré dans un
résultat déjà livré : la **fin** de la réversibilisation, mesurée (#7287, slot ICT-18b) ; la **canonicité**
des scalaires du zoo (#7288, slot ICT-15b) ; le **secret** comme canal d'irréversibilisation de l'identité
(ICT-23 → ICT-25, #5105) ; le **discours** comme substrat — graine de strate 6 (#7289, puis horizon #7291).
Les insertions se font par suffixe `b`, sous la clause **zéro renumérotation** : la renumérotation linéaire
(#5081) les absorbera en une PR atomique unique, déclenchée par la livraison d'ICT-24b + ICT-24c + les
verdicts de #7287/#7288 (décision complète : [#7260](https://github.com/jsboige/CoursIA/issues/7260)).

Détail des quatre fronts, verbatim : [`docs/ict/extensions-2026-07.md`](../../../docs/ict/extensions-2026-07.md).

## Deux axes de lecture : strates verticales × tresse transverse

Passé la strate 3, la numérotation linéaire `ICT-N` a cessé d'être un ordre total : le programme
s'est déployé sur **deux axes** qu'il faut lire ensemble. Les rendre explicites lève le flou de « la
strate d'un notebook » — deux structures différentes étaient projetées sur une seule échelle.

**Cette section est la source de vérité unique pour les strates** ([#13908](https://github.com/jsboige/CoursIA/issues/13908)) : le tableau ci-dessous fait foi, et
toute autre carte du dépôt — au premier chef celle du [README de la série](README.md) — s'y aligne
au lieu d'en proposer une variante. Les deux cartes avaient divergé précisément parce qu'aucune
n'était nommée comme la référence.

### Axe vertical — les substrats (strates)

L'échelle des substrats sur lesquels on mesure $\Phi$ / $F$ / $K$ et la flèche du temps, du plus
transparent au plus opaque :

| Strate | Substrat | Notebooks | Traceur |
|--------|----------|-----------|---------|
| **S1** | tri auto-organisé | ICT-1 → ICT-7 | — |
| **S2** | morphogenèse dynamique (attracteurs engendrés) | ICT-8 / ICT-9, charnière ICT-10 | — |
| **S3** | agents : réactifs → inhibés → stratégiques | ICT-11 / ICT-12 / ICT-13 + Synthèse | — |
| **S4** | scalaires fondateurs $\Phi/F/K$ sur substrats **non-LLM** | ICT-14 → ICT-20 | — |
| *charnière S4→S5* | **grokking** — le représentant interne cesse d'anticiper un comportement (`p̂` d'ICT-10) pour devenir un état de représentation apprise | ICT-17b | #7735 |
| **S5** | représentations internes des LLMs | ICT-21 → ICT-25 | — |
| **S6** | argumentation (+ jambe explicabilité LLM) | graine #7289 | #7289 · #7291 |
| **S7** | freebits d'ordre 2 & réversibilité agentique | cadrage D1 | #7745 |

Correction de bord la plus importante : les substrats **non-LLM** (identité MDL, $\epsilon$-machine,
flèche du temps, budget, enjeu, calibration feature-space = ICT-16 → ICT-20) relèvent de **S4** — les
trois scalaires fondateurs s'y rencontrent hors LLM. La **strate 5 commence à ICT-21** (SAE), là où
le substrat *est* un transformer entraîné. Le **grokking (ICT-17b)** est la **charnière**, pas une
strate pleine : c'est l'instant où un représentant interne cesse d'anticiper un comportement pour
devenir un état de représentation apprise — terminus du fil généalogique de `p̂` (#7735 : ICT-10 →
ICT-12 → ICT-14 → ICT-17b). **Zéro renumérotation** : seule l'étiquette de strate change, les numéros
`ICT-N` sont intacts (#7260). *(À ne pas confondre avec les « S1-S5 » de la batterie ICT-19/19b, qui
désignent des **substrats** — tri, May, Axelrod, Gray-Scott, dissipateur — et non des strates.)*

### Axe transverse — la tresse (jambes & dimensions)

Orthogonalement aux strates, une famille d'expériences (planifiée dans #7734 → #7747) éclaire un même
substrat sous plusieurs angles. Elles ne s'insèrent **pas** dans l'échelle des strates — ce sont des
**pattes, pas des barreaux**, ce qui résout le décalage : ajouter une jambe ne renumérote aucune
strate.

- **Jambe C1** — animat prégnance / valence à transfert : opérationnaliser l'investissement thomien
  (#7740). Patte de S3.
- **Jambe C2** — **animat inhibé (Laborit)** : contrôlabilité de l'environnement, inhibition de
  l'action (#7741). Patte de S3, parallèle à C1 — *pas* un barreau « ICT-12b ». C'est la réponse au
  « si Laborit atterrit après Animat, les strates supérieures seront décalées » : Laborit est une
  **jambe**, elle ne décale rien.
- **Jambe C3** — morphogenèse rhétorique de la transition (#7742). Patte de S6.
- **Jambe C4** — grammaire de propagation & seuil de bascule ($\pi$, $W$) (#7743). Patte de S6.
- **Jambe C5** — méta-proxy → cochaîne de Čech pondérée (#7744).
- **Dimension D1** — cadrage **strate 7** : *free coordinates* / freebits de 2e ordre, jeu évolutif
  $G_t$ + mécanisme $M$, six proxys (#7745).
- **Dimension D2** — cinq expériences du jeu évolutif (vocabulaire fixe / invention de symboles /
  seuil $\rho_c$ / inoculation / inhibition de l'innovation) (#7746).
- **Dimension D3** — mythe fondateur / boussole : auto-référence performative (#7747).

Une **jambe** (C1-C5) est une expérience *sur* une strate ; une **dimension** (D1-D3) cadre l'horizon
des strates hautes (S6/S7). La **matrice de dissociations** (#7734) lit chaque *claim* à
l'intersection des deux axes.

### Les trois divergences tranchées (#13908)

Deux cartes des strates coexistaient — celle-ci et celle du [README de la série](README.md) — et
elles divergeaient sur trois points. Les voici tranchées, avec la raison. Sous la clause **zéro
renumérotation** : aucun numéro `ICT-N` ne bouge, seules des étiquettes de strate sont corrigées.

**1. Frontière S4 / S5 — le tableau ci-dessus l'emporte.** Le README rattachait ICT-15 → ICT-25 à une
seule « strate 5 » (théorie fondatrice *et* LLM). Or l'axe vertical est celui des **substrats** :
ICT-16 → ICT-20 (identité MDL, $\epsilon$-machine, flèche du temps, budget, enjeu) se mesurent hors
LLM et relèvent de **S4**, tandis que **S5 commence à ICT-21** (SAE), là où le substrat *est* un
transformer entraîné. **ICT-17b (grokking) est la charnière** S4→S5, pas une strate pleine (#7735).
Ce qui tranche est que le critère est écrit — « du plus transparent au plus opaque » — et que l'autre
carte n'en proposait aucun.

**2. « Strate 6 = Thom » n'est pas une strate : c'est un socle transverse.** Le README la décrit
lui-même comme « un socle théorique transverse », et sa propre table des matières ne contient
**aucune** section « Strate 6 » — elle titre `## Socle théorique transverse — distillation Thom
1991`. La sémiophysique irrigue ICT-10, ICT-13 et les jambes C3/C4, et **ne porte aucun notebook en
propre** : un barreau de l'axe vertical est un substrat *sur lequel on mesure*, Thom est un outil de
lecture. La **strate 6 reste donc celle du tableau — l'argumentation** (graine #7289), non livrée,
avec C3 et C4 pour pattes.

**3. « Strate 7 = ICT-26 → ICT-30 » est en réalité la dimension D2, livrée.** La correspondance avec
l'énoncé de D2 (#7746) est terme à terme, dans l'ordre :

| D2 — « cinq expériences du jeu évolutif » | notebook livré | lettre au README |
|---|---|---|
| vocabulaire fixe | [ICT-26-SignalingConvention](ICT-26-SignalingConvention.ipynb) | A — convention |
| invention de symboles | [ICT-27-SymbolInvention](ICT-27-SymbolInvention.ipynb) | B — invention |
| seuil $\rho_c$ | [ICT-28-CollectiveAdoption](ICT-28-CollectiveAdoption.ipynb) | C — adoption |
| inoculation | [ICT-29-ConceptInoculation](ICT-29-ConceptInoculation.ipynb) | D — inoculation |
| inhibition de l'innovation | [ICT-30-InhibitedInvention](ICT-30-InhibitedInvention.ipynb) | E — inhibition |

Le README **cite déjà #7746** comme Epic de sa « strate 7 » : les deux cartes s'accordaient donc sur
l'objet et divergeaient seulement sur son axe. Ces cinq notebooks sont des **pattes, pas des
barreaux**. La **strate 7 reste celle du tableau — les freebits d'ordre 2 et la réversibilité
agentique** (#7745), que D1 cadre et que D2 alimente ; elle n'est pas livrée par ICT-26 → ICT-30.

Les divergences 2 et 3 avaient la **même cause** : un objet transverse projeté sur l'axe vertical.
C'est exactement le flou que cette section existe pour lever — et c'est pourquoi aucune des deux ne
demande de renumérotation. Il suffit de rendre chaque objet à son axe.

### Ce que cette carte ne place pas encore : le substrat « Jeu de la Vie certifié »

Cinq documents issus de la phase #5726 ne figurent sur **aucun** des deux axes. Le README en range
quatre « hors séquence numérotée », ce qui les sort de la carte sans les y placer, et ICT-34
n'apparaissait jusqu'ici dans aucune des deux cartes. Leur nature se lit pourtant sans ambiguïté :

| Document | Nature | Axe |
|---|---|---|
| [ICT-Life-SubstratCertifie](ICT-Life-SubstratCertifie.ipynb) | calibration du substrat GOL (B3/S23, correction certifiée en Lean) | vertical — substrat |
| [ICT-32-StratificationCausaleLife](ICT-32-StratificationCausaleLife.ipynb) | apportionment de Hoel **sur** ce substrat | vertical — substrat |
| [ICT-33-SoupCollisions](ICT-33-SoupCollisions.ipynb) | ensembles ouverts et bruit macro **sur** ce substrat | vertical — substrat |
| [ICT-31-ContrasteTroisSubstrats](ICT-31-ContrasteTroisSubstrats.ipynb) | contraste mesuré **entre** bistable, Gray-Scott et GOL | transverse — cross-substrat |
| [ICT-34-BancRecollementLectures](ICT-34-BancRecollementLectures.ipynb) | banc de recollement de quatre lectures, un seul verdict | transverse — cross-substrat |

**Les deux derniers sont des pattes**, par le critère même de la divergence 3 : ils portent sur
plusieurs substrats à la fois. **Les trois premiers appellent un barreau**, et ce barreau n'est
**pas** tranché ici. La raison est de méthode : l'échelle est ordonnée « du plus transparent au plus
opaque », or un automate cellulaire déterministe dont la correction est certifiée en Lean est le
substrat **le plus transparent de toute la série**. L'y insérer demande de décider s'il précède S1 ou
s'il constitue une entrée latérale — un déplacement d'étiquettes qui excède les trois divergences
arbitrées ici, et qu'il vaut mieux nommer comme **question ouverte** que trancher en passant.

## Feuille de route des notebooks

*Le substrat (strate) de chaque notebook est indiqué en gras dans la colonne « Sujet » de la table, selon
l'axe vertical du § Deux axes ci-dessus ; les numéros `ICT-N` sont l'ordre pédagogique de livraison, pas
l'ordre des strates.*

L'inventaire notebook par notebook — sujet, strate, état de livraison, issues de rattachement et slots
réservés — est déporté, verbatim, dans
[`docs/ict/feuille-de-route-notebooks.md`](../../../docs/ict/feuille-de-route-notebooks.md).

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

  > **Note de rigueur (audit #4, [#7733](https://github.com/jsboige/CoursIA/issues/7733)).** Le **représentant interne `p̂`** mesuré dans ICT-10/12/14 est un **anticipateur** (extrapolation à partir du signal observé) ; il n'est **PAS** la **prégnance thomienne**, qui est chez R. Thom « un fluide invasif qui se propage de forme saillante en forme saillante » — une *section locale* au sens de Grothendieck, pas une grandeur interne à l'agent. L'identification `p̂ ≡ prégnance` relèverait d'une lecture spéculative des deux côtés : chez Thom, la prégnance est biologique et transférable ; ici, `p̂` est représentationnel et contraint. La correspondance `p̂ ↔ anticipation` du Ch.2 « Le Langage » de Thom est **nommée** (cf. ligne 394 ci-dessus), pas démontrée — le grade C documentaire est explicitement reconnu (`docs/grothendieckian-lens.md` §3, ligne 41-43, en fait le cadrage canonique). Cf. note de rigueur dédiée en fin de document.

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

## ICT-19 / ICT-19b — batterie de l'ENJEU (livré)

La batterie de l'**ENJEU** — auto-maintien / retour au bassin attracteur `B` après une
perturbation contrefactuelle `do(·)` (Pearl, fil rouge causalité ICT-5), fusionnée à la batterie
MOYEN d'ICT-18 sur le banc de substrats S1-S5 de l'ICT-Synthèse (S5 = *pur dissipateur* = contrôle
négatif **obligatoire**) — est **livrée** : [ICT-19](ICT-19-EnjeuBattery.ipynb) (#5489, cadrage B
verrouillé user 2026-07-06) puis raffinée par
[ICT-19b](ICT-19b-EnjeuBattery-Raffinement.ipynb) (#5728, mesure S4 en espace de champ ; renommée
**ICT-19b**, #7260). Le livrable est la **paire** `{I_thermo, I_stake}` (jamais un indice agrégé),
séparée par les gates falsifiables ENJEU-1 / ENJEU-2, sur la **distinction sémantique** :
réversibilité *thermodynamique* (detailed balance, `σ=0` — le MOYEN que `I_thermo` mesure) ↔
récupérabilité *comportementale* (Levin *competency for free* — la FIN que la lutte thermodynamique
poursuit). Spec de cadrage complète : **#5483** ; reframe parent triade moyen / fin / enjeu :
**#5352** ; registre des livrables : **#4588**.

## Voir aussi

- [README de la série IIT](README.md) — fondations PyPhi (TPM, $\Phi$, CES, coarse-graining).
- [Distillation Thom 1991 Sémiophysique](thom-synthese-distillation.md) — socle théorique pour strates 6/7 (universalisme linguistique, valence Tesnière, opérations catastrophistes, prototype / hypergenre).
- Epic **#4588** — registre des livrables ICT.
- **Matrice de dissociations** (notebook × claim × proxy × contrôle × seeds × verdict × portée, ossaturée par la factorisation 4-objets `s, q, π, W`) : [`docs/ict/dissociations-matrix.md`](../../../docs/ict/dissociations-matrix.md) ([#7734](https://github.com/jsboige/CoursIA/issues/7734)). Lit chaque claim de la série dans l'espace `s_t` (saillance) / `q_t(z)` (représentation prédictive) / `π_t(z)` (prégnance-valence) / `W_t` (workspace), avec verdict sobre et portée explicite. **Complémentaire** de la grille 3-régimes ([`docs/ict/synthese-invariants-dissociations-obstructions.md`](../../../docs/ict/synthese-invariants-dissociations-obstructions.md), #7399) — la grille est conceptuelle et transversale ; la matrice est opérationnelle et par-claim.
- **Dette de rigueur audit #4** ([#7733](https://github.com/jsboige/CoursIA/issues/7733)) — 5 corrections A1-A5 propagées (PR #7889) : `p̂` ≠ prégnance thomienne, `H¹ ≠ 0` *candidat* (pas érigé en impossibilité sauf Kochen-Specker / Arrow), MGS = banc collectif Fil-A en aval strate 6, SAE = gamme Qwen complète (jalon 9B), pont pédagogique Axelrod → LLM → argumentation explicité.
- **Quatrième fil de lecture — généalogie de `p̂`** (ICT-10 → ICT-17, [#7735](https://github.com/jsboige/CoursIA/issues/7735)) : [`docs/ict/genealogy-representation-interne.md`](../../../docs/ict/genealogy-representation-interne.md). Diachronique, **orthogonal à la grille 3-régimes** : raconte comment un représentant interne ponctuel (`p̂` scalaire, ICT-10) devient, par insuffisances successives, un *état causal prédictif* (ε-machine Crutchfield, ICT-17). **Le descendant formel le plus naturel de `p̂` n'est ni le SAE, ni la J-lens, c'est l'état causal prédictif.** Deux garde-fous honnêteté (audit #4) : continuité conceptuelle, pas expérimentale (pas de transport formel `p̂` → SAE/J-lens observé) ; le global workspace ICT-24 (`W_t`) n'est **pas** une version structurée de `p̂`. Raccroche le parapluie [#7396](https://github.com/jsboige/CoursIA/issues/7396) (pivot états → représentations).

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

---

## Note de rigueur — prégnance thomienne vs représentant interne `p̂` (audit #4, [#7733](https://github.com/jsboige/CoursIA/issues/7733))

> Cette note consolide et explicite le caveat introduit inline à la description d'ICT-10 plus haut.

| | `p̂` (représentant interne ICT) | Prégnance (R. Thom, *Sémiophysique*) |
|---|---|---|
| **Nature** | Anticipateur représentationnel — extrapolation du signal observé (persistance, moyenne mobile, AR(1) testées en baseline) | « Fluide invasif qui se propage de forme saillante en forme saillante » |
| **Localisation mathématique** | Grandeur interne à l'agent (`ICT-10`, mesure sur 3 familles de trajectoires × 3 baselines adverses) | *Section locale* d'un site au sens de Grothendieck (cf. `docs/grothendieckian-lens.md` § 3) |
| **Statut épistémique** | **Mesurée** : banc durci, verdict régime-dépendant (réel sur trajectoire lisse 5/5 graines, illusoire sur dérive et créneau) | **Nommée / spéculative** : pas de mesure correspondante dans le dépôt |
| **Transférabilité** | Non-transférable — apprentissage spécifique par agent | Transférable — passe de forme saillante en forme saillante (propriété biologique thomienne) |
| **Référence canonique** | ICT-10 charnière strate 2→3 | `docs/grothendieckian-lens.md:41` (cadrage Grothendieck + Thom explicite) |

La correspondance **`p̂ ↔ anticipation`** du Ch.2 « Le Langage » de Thom (cf. ligne 394) est *nommée* dans le dépôt — pas démontrée. L'identification **`p̂ ≡ prégnance`** relèverait d'une lecture **spéculative des deux côtés**, à éviter :

- chez Thom, la *prégnance* est **biologique** et **transférable** (analogue sémiotique d'une substance invasive) ;
- ici, `p̂` est **représentationnel** et **contraint** (sortie d'un algorithme d'extrapolation).

Le grade C documentaire est **explicitement reconnu** dans `docs/grothendieckian-lens.md` § 3 (« une direction et non un théorème livré ») ; cette note de rigueur rend la même prudence lisible côté ICT. Pré-enregistré : [#7733](https://github.com/jsboige/CoursIA/issues/7733) (mandat user 2026-07-20, audit #4).
