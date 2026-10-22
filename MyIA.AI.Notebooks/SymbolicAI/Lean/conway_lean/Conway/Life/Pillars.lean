/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Pillars — Témoins communautaires (scaffolding Phase 3c)

Ce module est un **scaffolding** pour les quatre « piliers » de la
communauté Conway Life que nous voulons certifier via `native_decide`
une fois le Hashlife mémoïsé (`Conway.Life.HashlifeMemo`) en place.

### Les quatre piliers

| Pilier              | Auteur       | Année | Pattern               | Générations | Niveau |
|---------------------|--------------|-------|-----------------------|-------------|--------|
| OTCA metapixel      | Brice Due    | 2006  | Transition OTCA on/off| 35 328      | ~9     |
| Unit cell           | Nicolay Beluchenko | 2011 | p5760unitlifecell.rle | 5 760 | ~7  |
| Gemini              | Andrew Wade  | 2010  | gemini.rle           | 33 699 586  | ~14   |
| CPU (digital)       | Nicolay Beluchenko / Andy Stearns | 2016 | digital_cpu.rle | 1 048 576 | ~12   |

Chaque témoin affirme que `evolveHashlifeFastMemo N motif` produit
la configuration cible attendue après `N` générations. Le nombre de
générations est choisi à un jalon notable de la démo publique du
motif (par exemple le cycle OTCA « on/off » dure 35 328 générations,
la Gemini publie une auto-réplication complète en 33 699 586).

### Statut

- **Phase 3b** : `hashlifeResultAux` prouvée structurellement
  récursive, lemme de cône lumineux `mem_lightCone_of_manhattan_le`
  clos (PR #2173). Les `sorry` restants dans
  `Conway.Life.HashlifeCorrectness` sont des lemmes de confinement
  level-2/étape, indépendants de ce fichier.
- **Phase 3c mémoïsation** : TERMINÉE. `Conway.Life.HashlifeMemo`
  fournit désormais un vrai Hashlife mémoïsé fuel-keyed
  (`evolveHashlifeFastMemo`) prouvé égal à la référence Phase 3b
  (`evolveHashlifeFastMemo_eq_evolveHashlifeFast`, sans `sorry`).
- **Phase 3c motifs** (ce fichier) : l'UnitCell (15 Ko) puis l'OTCA (165 Ko)
  sont désormais chargés pour de vrai (`include_str` + `RLE.parseRLE!`,
  voir ci-dessous) — le mécanisme de chargement par fichier que ce module
  attendait existe depuis Lean 4.33, et le noyau parse sans littéral source
  le plus gros RLE de l'archive. Gemini et CPU restent des *grilles vides
  placeholder* (le RLE de la Gemini est gitignoré, celui du CPU est absent)
  et leurs témoins restent **vacuous** (`evolveHashlifeFastMemo_empty`).
- **Le RLE présent n'est pas le motif du pilier** : cette ligne visait
  l'UnitCell de Beluchenko (2011, période **4 096**), mais l'archive ne
  contient que `p5760unitlifecell.rle` — le « plus proche disponible », que
  `patterns/README.md` attribue à **David Bell** et annonce à **5 760**.
  Mesure du 2026-10-09 : ce dernier est bien de période 5 760, donc le
  « 4 096 » n'était pas un chiffre faux — il décrit **un autre motif**, absent
  de l'archive. Le `unitcellGens := 5760` ci-dessous décrit donc le motif
  **réellement chargé**. L'attribution d'auteur (Beluchenko 2011 ici, David
  Bell dans `patterns/README.md`) reste **ouverte** : la mesure ne tranche pas
  une paternité.
- **Le témoin de période de l'UnitCell est INEXPRIMABLE dans ce moteur**
  (mesuré le 2026-10-09, #19989) — et ce n'est pas une question de budget :
  `Grid` est une liste creuse **sans bord** (`evolveHashlifeFastMemo` retombe
  sur `evolve`), or l'UnitCell est un **système ouvert** qui émet des planeurs
  partant indéfiniment. Simulateur creux calibré contre `life_synthesize` :
  en 8 000 générations la population reste ~4 840 quand l'étendue passe de
  499² à 3 705 × 3 795, et **aucun état ne se répète** — donc
  `evolveHashlifeFastMemo N unitcellInitial = unitcellInitial` n'a aucune
  solution `N`. La période **5 760** est en revanche confirmée *sans bord* sur
  un **tore 500 × 500** (première répétition gen 11324 == gen 5564), ce qui
  valide à la fois le nom du fichier source et la ligne « 5 760 » de
  `patterns/README.md`.
  La formaliser demande un moteur **torique**, absent du lac : c'est la suite
  naturelle de cette tranche.
- **L'OTCA : confinement observé sur la fenêtre mesurée — mesure du
  2026-10-09 (#19989, tranche 3), qui ne réfute rien** : sur 1 800
  générations, l'étendue reste **strictement** 2058 × 2058 (aucune
  cellule hors de la boîte initiale à aucun relevé) pendant que la
  population oscille en [63 955, 64 798] : la machinerie tourne et la
  fenêtre ne montre **aucune évasion** — contrairement à l'UnitCell,
  dont l'ouverture est mesurée. La mesure borne trois questions
  distinctes et n'en tranche **aucune** : (a) **confinement observé ≠
  confinement prouvé** — un planeur né entre deux relevés peut
  interagir ou mourir sans qu'aucun relevé le voie, la fenêtre
  n'exclut donc aucune sortie transitoire ; (b) **récurrence
  éventuelle** — même un confinement permanent rendrait l'espace
  d'états fini et imposerait une entrée en cycle après un transitoire
  éventuel, sans en dire la longueur ; (c) **retour à l'état initial**
  — le témoin de période `evolveHashlifeFastMemo 35328 otcaInitial =
  otcaInitial` reste une **hypothèse ouverte** : ni la période exacte
  sur le motif isolé ni la faisabilité ne sont confirmées (test de
  performance du Hashlife mémoïsé à 64 691 cellules). La tranche 4 a
  **mesuré** le coût de cette faisabilité : l'évaluation `native_decide`
  du témoin ne termine pas en 2 h sur cette machine (double tentative,
  replays du lake consommés en quelques secondes puis silence jusqu'au
  délai, aucun `.olean` produit) — plafond de l'organe **mesuré ici**,
  levable sur une machine plus dotée. La prédiction « un métapixel isolé sur grille sans bord
  n'est pas périodique non plus » est donc **ni confirmée ni
  réfutée** pour l'OTCA.
- **Témoins négatifs appariés** (critère 2 de #19989) : `pulsar_period1_negative`
  et `pulsar_period2_negative` accompagnent `pulsar_period3` — la période vaut
  donc **exactement** 3, et non un simple diviseur de 3. C'est le seul témoin de
  période **positif** du lake, donc le seul qui puisse recevoir une paire :
  pour l'UnitCell la paire est impossible *a fortiori* (le positif ne
  l'est pas — système ouvert mesuré, cf. ci-dessus) ; pour l'OTCA la
  question est **ouverte** (confinement observé sur la fenêtre mesurée
  — le positif reste une hypothèse, cf. ci-dessus) ; pour Gemini/CPU les grilles
  sont encore vides, où un négatif ne mesurerait rien de réel.
- **Futur** : le CPU (une fois son RLE chargé par le même mécanisme) — sa
  question du bord reste à trancher par la même méthode de mesure.

### Politique d'ancrage `native_decide` (#21833)

Chaque déclaration `native_decide` crée un axiome **nommé**
(`<thm>._native.native_decide.ax_1_1`) : le gate `proof-integrity-audit`
les liste **par nom**, jamais par un joker.

| Fichier | Ancres avant #21833 | Ancres après | Déclarations redevenues dérivées |
|---|---|---|---|
| `Conway.Life.Pillars` | 7 | 5 | `otca_initial_nonempty`, `unitcell_initial_nonempty` |
| `Conway.Life.Pillars_en` | 7 | 5 | les deux siblings `_en` |

Les 5 ancres **retenues** par fichier sont les certifications **indépendantes**
du noyau : `pulsar_period3` (positif — période 3), `pulsar_period1_negative`
et `pulsar_period2_negative` (négatifs appariés), `otca_initial_population`
(64 691 cellules) et `unitcell_initial_population` (4 761 cellules) — chacune
porte une affirmation que rien d'autre ne porte.

Les 2 déclarations retirées ne perdent rien : `otca_initial_nonempty` et
`unitcell_initial_nonempty` se **déduisent** de la population mesurée
(`omega` sur la longueur). Un théorème qui dépend d'un autre ancrage n'en
crée pas de nouveau — c'est `#print axioms` qui fait foi, pas la présence
d'un `native_decide` dans le texte.

Mesure : 7 déclarations par fichier avant, **5 ancres mesurées par
`#print axioms`** après (14 → 10 pour la paire FR/`_en`), build
`Build completed successfully (3014 jobs)` (`Conway.Life.Pillars` : 804 s,
`Conway.Life.Pillars_en` : 803 s), toolchain épinglé `v4.33.0`.

### Pourquoi un fichier séparé ?

Ces théorèmes exercent `native_decide` sur de grands motifs ; les
temps de compilation explosent (récursion `9^k` sur chaque
sous-cellule). Les garder dans un module distinct laisse le reste de
`Conway.Life` se construire rapidement tandis que `Pillars.lean`
peut être opt-in via `lake build Conway.Life.Pillars` quand
nécessaire.

### Pourquoi scaffolder les témoins maintenant ?

Mandat user 2026-06-01 : préparer un scaffold de présentation
complète pour que la roadmap §11 du notebook
`Lean-16b-Conway-Game-of-Life-Lean.ipynb` soit concrète et visible.
La mémoïsation a été validée au début de la Phase 3 ; les témoins
sont le point d'arrivée naturel.
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.HashlifeMemo
import Conway.Life.RLE

namespace Conway
namespace Life
namespace Pillars

/-! ## Archive de motifs

Les fichiers RLE des quatre piliers vivent dans `patterns/` à côté
de ce projet Lean. Ils ont été téléchargés depuis le miroir copy.sh
de l'archive communautaire LifeWiki :

  `https://copy.sh/life/examples/<name>.rle`

| Fichier                | Taille grille | Taille (Ko) | Théorème pilier        |
|------------------------|---------------|-------------|------------------------|
| `otcametapixel.rle`    | 2058 × 2058  | 165         | `otca_initial_population` |
| `p5760unitlifecell.rle`| 499 × 499    | 15          | `unitcell_initial_population` |
| `turingmachine.rle`    | 1714 × 1647  | 104         | `turingmachine_initial_population` |
| `gemini.rle`           | énorme       | 5 300       | `gemini_witness`       |

`gemini.rle` (5,3 Mo) est gitignoré pour cause de taille ; la
fonction `fetch_rle()` du notebook le retélécharge à la demande
avec cache disque.

Les fichiers RLE sont **trop gros** pour des littéraux chaîne Lean
(OTCA seul fait 165 Ko de texte RLE ; le noyau Lean devrait le
parser au moment de la compilation). Le mécanisme de chargement par
fichier existe en revanche depuis Lean 4.33 : `include_str` embarque
le contenu à la compilation, le chemin étant relatif au fichier
source. Il est utilisé ci-dessous pour l'UnitCell (15 Ko) et l'OTCA
(165 Ko) ; seule la Gemini (gitignorée) reste à faire.

## Placeholders de motifs

Chaque pilier a besoin (a) de sa `Grid` initiale décodée du RLE, (b)
du compte de générations cible, (c) de la `Grid` post-évolution
attendue (elle aussi depuis la source publiée). Pour le scaffold
nous déclarons des noms opaques avec un corps trivial ; les vrais
motifs seront chargés via `Conway.Life.RLE.parseRLE` en Phase 3c.

Ce sont des **def**, pas des `axiom` — ils ont un corps trivial
concret (`Grid.empty`) donc aucun axiome n'est introduit. Ils
seront remplacés par le RLE parsé dans la PR pilier réelle. -/

/-- Source RLE de l'OTCA metapixel, embarquée à la compilation par `include_str`.
    Le chemin est relatif à CE fichier (`Conway/Life/`). À 165 Ko, c'est le plus
    gros motif jamais chargé dans le lac — l'hypothèse « trop gros pour le
    noyau » est ce que cette tranche teste (voir « Statut » ci-dessus). -/
def otcaRLE : String := include_str "../../patterns/otcametapixel.rle"

/-- État initial de l'OTCA metapixel, décodé du RLE par l'analyseur **prouvé**
    du dépôt (`Conway.Life.RLE.parseRLE`). Population mesurée : 64 691 cellules
    vivantes sur une boîte 2058 × 2058. -/
def otcaInitial : Grid := RLE.parseRLE! otcaRLE

/-- Nombre de générations du cycle on/off de la métacellule (valeur publiée
    de la démo Brice Due). -/
def otcaGens : Nat := 35328

/-- Source RLE de l'UnitCell, embarquée à la compilation par `include_str`.
    Le chemin est relatif à CE fichier (`Conway/Life/`), et non à la racine
    du paquet. -/
def unitcellRLE : String := include_str "../../patterns/p5760unitlifecell.rle"

/-- État initial de l'UnitCell, décodé du RLE par l'analyseur **prouvé** du
    dépôt (`Conway.Life.RLE.parseRLE`). Population mesurée : 4 761 cellules
    vivantes sur une boîte 499 × 499. -/
def unitcellInitial : Grid := RLE.parseRLE! unitcellRLE

/-- Nombre de générations d'une période du motif **réellement chargé** :
    **5 760**, valeur mesurée (voir « Statut » ci-dessus). Le `4 096` qui
    figurait ici décrit l'UnitCell de Beluchenko, qui n'est **pas** le motif
    de l'archive (`p5760unitlifecell.rle`, cf. `patterns/README.md`). -/
def unitcellGens : Nat := 5760

/-- État initial de l'auto-réplicateur Gemini. Chargé depuis RLE en Phase 3c. -/
def geminiInitial : Grid := ([] : Grid)

/-- État de la Gemini après un cycle complet d'auto-réplication (33 699 586 générations). -/
def geminiTarget : Grid := ([] : Grid)

/-- Nombre de générations pour un cycle d'auto-réplication de la Gemini. -/
def geminiGens : Nat := 33699586

/-- État initial du CPU digital. Chargé depuis RLE en Phase 3c. -/
def cpuInitial : Grid := ([] : Grid)

/-- État du CPU digital après un cycle représentatif (1 048 576 générations). -/
def cpuTarget : Grid := ([] : Grid)

/-- Nombre de générations pour un cycle du CPU digital. -/
def cpuGens : Nat := 1048576

/-! ## Exemple témoin prouvé par RLE

Le Pulsar (oscillateur de période 3) est parsé depuis son RLE dans
notre module RLE.lean et vérifié comme oscillateur. Il sert de
démonstration concrète que le pipeline RLE → Grid → evolve marche
de bout en bout. L'UnitCell (15 Ko) puis l'OTCA (165 Ko) sont
désormais chargés par `include_str` (voir ci-dessus) ; la Gemini
(gitignorée) et le CPU (RLE absent) attendent le même branchement. -/

/-- Le Pulsar parsé depuis sa représentation RLE.
    Prouvé égal à la constante écrite à la main dans RLE.lean. -/
def pulsarGrid : Grid := RLE.pulsar_parsed

/-- Le Pulsar est un oscillateur de période 3 : après 3 générations
    il revient à son état initial. Prouvé via `native_decide`. -/
theorem pulsar_period3 :
    evolveHashlifeFast 3 pulsarGrid = pulsarGrid := by
  native_decide

/-- **Témoin négatif apparié** de `pulsar_period3` : la période n'est pas 1 —
    le Pulsar n'est pas un still life. Sans ce contrôle, `pulsar_period3` seul
    ne dirait rien de la valeur `3`, seulement d'un diviseur de 3. -/
theorem pulsar_period1_negative :
    evolveHashlifeFast 1 pulsarGrid ≠ pulsarGrid := by
  native_decide

/-- **Témoin négatif apparié** : la période n'est pas 2 non plus. Les deux
    négatifs ensemble établissent que la période vaut **exactement** 3. -/
theorem pulsar_period2_negative :
    evolveHashlifeFast 2 pulsarGrid ≠ pulsarGrid := by
  native_decide

/-! ## Théorèmes témoins

Chaque théorème affirme que `evolveHashlifeFastMemo N motif = cible`
pour le pilier correspondant. La preuve est conçue comme un simple
`by native_decide` une fois la mémoïsation en place. -/

/-- **OTCA metapixel** — Brice Due 2006.

    La première métacellule programmable : 2058 × 2058, 64 691 cellules
    vivantes, capable d'émuler tout automate cellulaire life-like — Life
    simulant *lui-même*. Vu de loin, les états ON et OFF de la métacellule
    sont visibles. Le cycle ON→OFF→ON publié dure 35 328 générations
    (source : conwaylife.com/wiki/OTCA_metapixel).

    **Il n'y a toujours pas de témoin de période ici — mais le report
    est désormais mesuré, pas seulement motivé.** Mesure motivante
    (simulateur dense, 1 800 générations) : l'étendue reste strictement
    2058 × 2058, aucune cellule ne quitte la boîte aux relevés, la
    population oscille en [63 955, 64 798] — confinement **observé**
    sur la fenêtre, pas prouvé pour toutes les générations. Le témoin
    `evolveHashlifeFastMemo 35328 otcaInitial = otcaInitial` reste une
    hypothèse ouverte (récurrence éventuelle et retour à l'état initial
    non mesurés) ; il attend (a) la confirmation de la période exacte
    35 328 sur le motif isolé et (b) un test de performance du Hashlife
    mémoïsé sur une grille de 64 691 cellules — dont la tranche 4 a fait
    une **première tentative, non concluante** en 2 h sur cette machine
    (aucun `.olean` produit ; plafond levable sur une machine plus dotée).

    Ce qui est prouvé ici, et **non vacuous**, c'est que la grille chargée
    est réelle : 165 Ko de RLE passés par le même `include_str` +
    `RLE.parseRLE!` que l'UnitCell — la route `evolveHashlifeFastMemo_empty`
    est fermée pour ce motif. -/
theorem otca_initial_population : otcaInitial.length = 64691 := by
  native_decide

/-- La grille OTCA chargée n'est pas vide. Contrôle croisé indépendant :
    la même population (64 691) est mesurée par comptage Python direct des
    runs `o` du RLE source.

    **La preuve est dérivée, pas réévaluée** : la non-vacuité découle de la
    population mesurée par `otca_initial_population` — une population non
    nulle exclut la liste vide. Ce théorème ne porte donc plus d'ancrage
    `native_decide` propre : il hérite de celui de la population, et le
    module perd une certification native indépendante au profit d'une
    déduction arithmétique sur le noyau. -/
theorem otca_initial_nonempty : otcaInitial ≠ ([] : Grid) := by
  intro h
  have hpop := otca_initial_population
  have hl := congrArg List.length h
  simp only [List.length_nil] at hl
  omega

/-- **UnitCell** — Nicolay Beluchenko 2011.

    Une métacellule OTCA-style plus petite, de période **5 760**, environ 9× la
    vitesse de l'OTCA. Le motif utilise une architecture interne différente
    (cœur p5760) le rendant complémentaire de l'OTCA.

    **Il n'y a pas de témoin de période ici, et c'est un résultat, pas un
    oubli.** La période 5 760 n'est pas exprimable dans ce moteur : `Grid` est
    une liste creuse **sans bord** (`evolveHashlifeFastMemo` retombe sur
    `evolve`), et l'UnitCell est un **système ouvert** — il émet des planeurs
    qui s'échappent indéfiniment. Mesure (simulateur creux calibré contre
    `life_synthesize`) : en 8 000 générations la population reste ~4 840 tandis
    que l'étendue passe de 499² à 3 705 × 3 795, et **aucun état ne se répète**
    — donc `evolveHashlifeFastMemo N unitcellInitial = unitcellInitial` n'a
    aucune solution `N`.

    La période est réelle, mais elle appartient à la lecture **pavée** :
    mesurée *sans bord* sur un tore 500 × 500 (première répétition
    gen 11324 == gen 5564, soit 5 760). La formaliser demande un moteur
    torique, qui n'existe pas dans le lac — c'est la suite de cette tranche.

    Ce qui est prouvable ici, et **non vacuous**, c'est que la grille chargée
    est réelle : c'est exactement ce que fermait la route
    `evolveHashlifeFastMemo_empty` utilisée par les trois autres témoins. -/
theorem unitcell_initial_population : unitcellInitial.length = 4761 := by
  native_decide

/-- La grille UnitCell chargée n'est pas vide — la route
    `evolveHashlifeFastMemo_empty` est donc **fermée** pour ce motif, ce qui
    rend le témoin de période impossible *a fortiori*. Contrôle croisé
    indépendant : la même population (4 761) est mesurée par
    `scripts/lean/rle_to_lean_grid.py`.

    **La preuve est dérivée, pas réévaluée** : la non-vacuité découle de la
    population mesurée par `unitcell_initial_population` — une population non
    nulle exclut la liste vide. Ce théorème ne porte donc plus d'ancrage
    `native_decide` propre : il hérite de celui de la population, et le
    module perd une certification native indépendante au profit d'une
    déduction arithmétique sur le noyau. -/
theorem unitcell_initial_nonempty : unitcellInitial ≠ ([] : Grid) := by
  intro h
  have hpop := unitcell_initial_population
  have hl := congrArg List.length h
  simp only [List.length_nil] at hl
  omega

/-! ## Témoin de la machine de Turing

La machine de Turing de Paul Rendell (avril 2000) est le motif le plus
célèbre de la communauté après les quatre piliers : une machine de
Turing dont le programme est écrit dans une grille de Conway. Le
fichier `turingmachine.rle` (104 Ko, boîte 1714 × 1647) est **déjà dans
l'arbre** ; jusqu'ici il n'était qu'un récit dans le tableau de
l'archive de motifs.

Ce qui manquait : un témoin **prouvé**. Le motif est chargé pour de
vrai (`include_str` + `RLE.parseRLE!`, comme l'OTCA et l'UnitCell), et
il reçoit la paire de témoins de chargement (population, non-vacuité)
**plus** un témoin de **dynamisme** : la machine n'est pas inerte.

Le témoin de dynamisme ne peut pas être un témoin de période : une
période exigerait de faire tourner l'évolution complète du motif, et le
moteur de référence `Conway.Life.evolve` est **quadratique** — le test
d'appartenance `isAlive g p = g.elem p` est une recherche linéaire dans
la liste triée, répétée pour chaque cellule candidate, soit environ
`9 × 36 549` cellules candidates à coût `O(n)` chacune. On utilise donc
`Conway.Life.birthSiteNotFixed` : un **site de naissance** — une cellule
morte avec exactement trois voisins de Moore vivants — suffit à prouver
que la grille n'est pas un point fixe, et cette preuve est **locale**. -/

/-- Source RLE de la machine de Turing de Paul Rendell, embarquée à la
    compilation par `include_str` (104 Ko, boîte 1714 × 1647). Le chemin
    est relatif à CE fichier (`Conway/Life/`). -/
def turingmachineRLE : String := include_str "../../patterns/turingmachine.rle"

/-- État initial de la machine de Turing, décodé du RLE par l'analyseur
    **prouvé** du dépôt (`Conway.Life.RLE.parseRLE`). Population mesurée :
    36 549 cellules vivantes. -/
def turingmachineInitial : Grid := RLE.parseRLE! turingmachineRLE

/-- **Faits mesurés** sur la grille Turing chargée, établis par **une seule**
    évaluation `native_decide`.

    Le regroupement n'est pas cosmétique : chaque site `native_decide`
    réévalue `RLE.parseRLE!`, donc reparse la source RLE et retrie les
    36 549 cellules de la grille. Un seul passage suffit à établir les
    quatre faits ; les théorèmes ci-dessous n'en sont que des projections,
    gratuites au niveau du noyau. -/
theorem turingmachine_facts :
    turingmachineInitial.length = 36549 ∧
    (9, 256) ∉ turingmachineInitial ∧
    (9, 256) ∈ turingmachineInitial.flatMap mooreNeighbors ∧
    liveNeighborCount turingmachineInitial (9, 256) = 3 := by
  native_decide

/-- La grille Turing chargée a bien **36 549 cellules vivantes**.
    Contrôle croisé indépendant : la même population est mesurée par le
    moteur Hashlife Python du lac (`scripts/hashlife.py`), dont le tableau
    de mesures (`scripts/README.md`) porte la même valeur pour ce motif. -/
theorem turingmachine_initial_population : turingmachineInitial.length = 36549 :=
  turingmachine_facts.1

/-- La grille Turing chargée n'est pas vide : la route du placeholder
    `([] : Grid)` est **fermée** pour ce motif. -/
theorem turingmachine_initial_nonempty : turingmachineInitial ≠ ([] : Grid) := by
  intro h
  have hlen : turingmachineInitial.length = 0 := by rw [h, List.length_nil]
  have hpop : turingmachineInitial.length = 36549 := turingmachine_facts.1
  rw [hlen] at hpop
  exact absurd hpop (by decide)

/-- La cellule `(9, 256)` est **morte** dans la grille Turing chargée. -/
theorem turingmachine_birth_site_absent : (9, 256) ∉ turingmachineInitial :=
  turingmachine_facts.2.1

/-- La cellule `(9, 256)` est voisine de Moore d'au moins une cellule
    vivante de la grille Turing : elle est donc **candidate** pour
    l'étape suivante. Ses trois voisins vivants sont `(9, 257)`,
    `(10, 256)` et `(10, 257)`. -/
theorem turingmachine_birth_site_adjacent :
    (9, 256) ∈ turingmachineInitial.flatMap mooreNeighbors :=
  turingmachine_facts.2.2.1

/-- La cellule `(9, 256)` a **exactement trois** voisins de Moore vivants
    dans la grille Turing : c'est un **site de naissance** (règle B3). -/
theorem turingmachine_birth_site_count :
    liveNeighborCount turingmachineInitial (9, 256) = 3 :=
  turingmachine_facts.2.2.2

/-- **Témoin de dynamisme de la machine de Turing** : la grille chargée
    n'est pas un point fixe de l'évolution — la machine **exécute** au
    moins une transition de la règle B3/S23 (une cellule naît en
    `(9, 256)`).

    La preuve est locale (un site de naissance), donc applicable à un
    motif de 36 549 cellules dont l'évolution complète n'est pas
    calculable par le moteur de référence.

    **Témoin négatif apparié** : `Conway.Life.emptyGridIsStillLife`
    montre que la grille vide — le placeholder qui remplacerait le motif
    non chargé — est, elle, un point fixe. Sans ce contrôle, le témoin
    ci-dessus ne distinguerait pas le motif chargé d'une grille vide
    remplacée. -/
theorem turingmachine_not_stilllife :
    step turingmachineInitial ≠ turingmachineInitial :=
  birthSiteNotFixed turingmachine_birth_site_absent
    turingmachine_birth_site_adjacent turingmachine_birth_site_count

/-- **Témoin Gemini** — Andrew Wade 2010.

    Le premier constructeur universel auto-répliquant dans Life.
    Gemini crée une copie complète d'elle-même en 33 699 586
    générations à travers un quadtree de niveau 14. C'est le
    **témoin amiral** — il démontre que Life est capable
    d'auto-réplication ouverte, la forme la plus forte
    d'universalité. Nommée d'après la constellation des Gémeaux
    (jumeaux).

    C'est la cible la plus dure : quadtree niveau 14 + 33M
    générations. Phase 3c : `by native_decide` avec Hashlife
    mémoïsé. Actuellement vacuous (grilles placeholder vides,
    voir Statut ci-dessus). -/
theorem gemini_witness :
    evolveHashlifeFastMemo geminiGens geminiInitial = geminiTarget :=
  evolveHashlifeFastMemo_empty geminiGens

/-- **Témoin CPU digital** — Beluchenko / Andy Stearns 2016.

    Un CPU digital programmable construit depuis des OTCA
    metapixels. Il exécute un cycle d'instruction en 1 048 576
    générations (quadtree niveau 12). Démontre que Life peut
    implémenter un calcul arbitraire — pas juste simuler une
    cellule, mais exécuter un programme. Détaillé dans l'analyse
    2016 d'Adam P. Goucher sur le forum conwaylife.com.

    Phase 3c : `by native_decide` avec Hashlife mémoïsé.
    Actuellement vacuous (grilles placeholder vides, voir Statut ci-dessus). -/
theorem cpu_witness :
    evolveHashlifeFastMemo cpuGens cpuInitial = cpuTarget :=
  evolveHashlifeFastMemo_empty cpuGens

end Pillars
end Life
end Conway
