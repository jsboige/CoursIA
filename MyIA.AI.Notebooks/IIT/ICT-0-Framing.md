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
est le fil conducteur de la série.

## Voir aussi

- [README de la série IIT](README.md) — fondations PyPhi (TPM, $\Phi$, CES, coarse-graining).
- Epic **#4588** — registre des livrables ICT.
- Levin, *The Computational Boundary of a "Self"*, Frontiers in Psychology, 2019.
