# Discrepancy_lean comme contrôle négatif d'allégation de strate-advance

> Issue de référence : **#13565**.
> Lake : `MyIA.AI.Notebooks/Search/discrepancy_lean/Discrepancy/`.
> Mesure sorry (instrument canonique) : `python scripts/lean/count_code_sorry.py --json`
> → champ `distinct_code_sorry = 0` pour `discrepancy_lean` au 2026-09-03.
> Le lake est **un certificat** : zéro `sorry` réel, donc les théorèmes qu'il
> porte peuvent servir de base à un contrôle négatif sans risque que la
> chaîne d'inférence soit elle-même trouée.

## L'idée

Avant de conclure qu'un agent a **élargi son espace de possibles** (transition
de strate au sens de `ICT-Series`, émancipation de niveau), il faut éliminer
l'hypothèse concurrente : il existait un **degré de liberté latent** dans
l'ancien espace, et l'agent ne l'avait pas su exploiter. Élargir n'est pas la
seule lecture compatible avec les observations ; **exploiter** l'est aussi, et
l'attribution « extension » sur cette seule base est un **faux positif
structurel**.

`discrepancy_lean` fournit un cas où ce degré de liberté latent existe, et il
est **certifié en Lean 4** (sans `sorry`, distinct_code_sorry = 0, lake
construit en `Basic → Kernel → Progress → BeckFiala`). C'est la
référence canonique pour rédiger le geste de contrôle négatif : **avant
d'écrire « l'agent a étendu son espace », chercher le noyau / le slack de
l'espace initial, et écrire ce qu'on a cherché.**

## Désambiguïsation obligatoire

`Basic.lean` ligne 13-19 avertit explicitement : la **discrépance combinatoire**
formalisée dans ce lake (sommes colorées signées, théorie de Spencer, Beck-Fiala,
Banaszczyk, Bansal-Jiang 2025) **n'a aucun rapport mathématique** avec la
**Limited Discrepancy Search** de Harvey & Ginsberg enseignée dans
`Search-13-LimitedDiscrepancySearch` (même série `Search/`). Confondre les deux
serait exactement le défaut de vocabulaire que ce document cherche à prévenir.
Le geste de contrôle négatif se transporte, le mot `discrepancy` ne voyage pas.

## Le patron certifié

Trois théorèmes, lus firsthand dans le lake, posent le patron :

1. **`Kernel.lean` — `card_dangerous_lt_card_floating` + `exists_dangerous_kernel_vec`**
   (b1, étapes 1 et 2). Tant qu'il y a plus de variables flottantes que de
   contraintes dangereuses, le système linéaire `D × X` a un **noyau non
   trivial** : il existe une direction de déplacement non nulle qui
   **préserve exactement** toutes les sommes colorées des lignes dangereuses.
   C'est ce degré de liberté qui permet de figer un flottant à chaque phase
   sans déranger les lignes déjà sous contrôle.

2. **`Progress.lean` — `exists_step_hits_boundary`** (b3). Suivre la direction
   de noyau jusqu'au **premier contact** avec la frontière du cube `[-1, 1]` :
   le pas est strictement positif, garde tout le monde dans le cube fermé,
   et fige au moins un nouveau flottant en `±1`.

3. **`BeckFiala.lean` — `beck_fiala_classic`** (b4). Boucle : chaque phase
   préserve les invariants **et fait strictement décroître** le nombre de
   flottants. La récursion est bien fondée sur `|X|`. Résultat : toute famille
   de degré maximal `≤ k` (`k ≥ 1`) admet une coloration `±1` de discrépance
   `≤ 2k−1`.

**Lecture en contrôle négatif.** Beck-Fiala montre qu'on peut obtenir un
**résultat mesurable** (coloration `±1`, borne `2k−1`) sans qu'aucun pas
n'élargisse l'espace ambiant : `|X|` ne fait que décroître, l'espace actif se
**contracte**. Le progrès est réel, le certificat est constructif, et **aucune
possibilité nouvelle n'a été inventée**. C'est précisément la lecture
alternative à « l'agent a étendu son espace » qu'il faut avoir cherché avant de
claim l'élargissement.

## Le vocabulaire que ça corrige

Le contraste binaire « meilleure navigation » vs « espace élargi » est trop
grossier. Il faut au moins **quatre objets** pour discriminer les gestes :

| Geste | ambiant | admissible | liberté résiduelle | politique |
|---|---|---|---|---|
| meilleure heuristique | = | = | = | change |
| descente guidée dans une taxonomie | = | = | = | change |
| **Beck-Fiala** | **=** | **préservé sous invariants** | **diminue** | exploite le noyau |
| relaxation PDDL | = | **s'élargit** | augmente | éventuellement = |
| ajout d'une macro-action | **change** | change | change | éventuellement = |
| nouvelle règle institutionnelle | **change de langage** | change | change | change |

Beck-Fiala occupe **une ligne qu'aucune autre n'occupe**, et c'est la **seule
avec un certificat** vérifiable. Les autres lignes sont des gestes plausibles
mais **non-certifiés** : il est possible qu'ils étendent l'espace, il est aussi
possible qu'ils exploitent un noyau non documenté.

## Obligation méthodologique proposée

Avant de publier un témoin « l'agent a dû étendre son espace » :

1. **Caractériser** l'espace initial (ambient + admissible + liberté
   résiduelle, selon la table 4-objets).
2. **Chercher** le noyau ou le slack de cet espace (variables inactives,
   contraintes redondantes, dimension cachée, colonnes de marge).
3. **Écrire** ce qu'on a cherché, ce qu'on a trouvé, et ce qu'on n'a **pas**
   trouvé. **« Je n'ai pas cherché » n'est pas une option** — c'est
   précisément le geste de contrôle négatif qui fait défaut.
4. **Si** un noyau est trouvé et exploité : reformuler le claim en
   « exploitation d'un degré de liberté latent », pas en « extension ».
5. **Si** aucun noyau n'est trouvé : le claim « extension » reste sur la
   table, mais avec la mention explicite que la recherche de noyau a été
   conduite et est négative. **C'est cette mention qui transforme un
   claim narratif en un résultat falsifiable.**

Hors du cas linéaire, « noyau » devient analogique. Exemples de transport :

- **Planning** : atteignabilité dans l'espace d'états, actions dominées non
  explorées.
- **SAT** : backbone, nombre de modèles, littéraux gelés.
- **Jeux** : actions dominées ou symétriques, strates de profondeur jamais
  atteinte.
- **ICT-Series** : variables latentes non contraintes, régime du modèle
  jamais atteint, mode latent non sollicité.

C'est le **geste** qui se transporte (« chercher la marge dans l'ancien
espace, écrire ce qu'on a cherché »), pas la formule.

## Quand ce contrôle négatif s'applique

| Terrain | Application concrète | Référence canonique |
|---|---|---|
| ICT-Series | Avant toute allégation de transition de strate (sortie ICT-19 vers 21/22) | `ICT-21-SAETrajectoires.ipynb`, `ICT-SAE-JLens-TeteATete.ipynb` |
| GameTheory | Avant toute allégation « le joueur découvre une nouvelle stratégie » | `game_theory_lean/`, identifier si la stratégie existait dans le réservoir initial |
| Probas / Infer.NET | Avant toute allégation « le modèle identifie un nouveau régime » | `discrepancy_lean` + transport au PBPI/Bande de Credibilité |
| Planners | Avant toute allégation « le solveur explore au-delà du domaine » | domaine relaxé (PDDL relaxation) vs domaine initial |
| Lean | Avant tout claim « le prouveur a découvert un nouveau fait » | tactics, casse-disjonctions, lemmes cachés dans le contexte |

## Limites du contrôle négatif

- **Le contrôle négatif ne ferme pas la question**, il élimine une classe
  d'explication alternative. Beck-Fiala montre que l'**exploitation** est
  compatible avec les observations de progrès sans extension. Cela n'établit
  pas qu'**aucune extension** n'a eu lieu — cela déplace le fardeau de la
  preuve vers celui qui claim l'extension.
- **Le transport analogique** (noyau → atteignabilité → backbone → mode
  latent) est plus délicat que le cas linéaire. Le geste de chercher la marge
  reste, mais la preuve d'absence de marge est rarement absolue.
- **Le coût de la recherche** est non-trivial. Une recherche exhaustive de
  noyau sur un grand système linéaire est elle-même un calcul qu'il faut
  borner. Le présent document ne tranche pas la question du **niveau
  d'effort** minimal qui suffirait à écrire « j'ai cherché » honnêtement —
  c'est une question ouverte que cette doctrine ne prétend pas résoudre.

## Statut de la doctrine

- **Source** : issue #13565 (po-2025), rédigée par po-2025 le 2026-09-XX,
  claimée par `myia-po-2026:CoursIA-2` le 2026-09-03 dans le cadre du grain
  c.911.
- **Référence interne au lake** : `Discrepancy/Basic.lean` (désambiguïsation
  ligne 13-19) + `Kernel.lean` + `Progress.lean` + `BeckFiala.lean`. Aucun
  `sorry` réel (`distinct_code_sorry = 0` au 2026-09-03, instrument
  canonique `scripts/lean/count_code_sorry.py`).
- **Périmètre d'application** : tout allégation de transition de strate
  (élargissement d'espace, émancipation de niveau, découverte d'un nouveau
  régime) sur le dépôt.
- **Force normative** : **médium**. La doctrine pose un geste et un
  vocabulaire ; elle ne crée pas un gate bloquant (qui exigerait une
  couverture exhaustive et un coût de revue disproportionné). Le geste se
  transporte d'abord, l'enforcement vient ensuite si l'usage s'avère.

## Voir aussi

- **Issue #13565** — source de la doctrine, motivation et désambiguïsation
  (limitée à ce que la doctrine formalise).
- **`docs/lean/README.md`** — index des documents de doctrine Lean du
  dépôt ; ce document s'y inscrit.
- **`.claude/rules/pr-review-discipline.md` §H** — Vrai outil SOTA, geste de
  contrôle négatif compatible.
- **`scripts/lean/count_code_sorry.py`** — instrument canonique de mesure
  des `sorry` réels, à utiliser **avant** d'invoquer un lake comme
  certificat (un lake avec `distinct_code_sorry > 0` ne peut pas servir).
- **`docs/lean/i18n-sibling-patterns.md`** — convention i18n FR/EN siblings
  appliquée au lake ; la version EN de ce document (`_en.md` suffixé) n'est
  **pas** un livrable de ce grain mais reste un suivi possible.
