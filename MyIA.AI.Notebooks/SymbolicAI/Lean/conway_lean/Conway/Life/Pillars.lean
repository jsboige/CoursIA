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
- **L'OTCA, lui, est un système FERMÉ — mesure du 2026-10-09 (#19989,
  tranche 3)** : sur 1 800 générations, l'étendue reste **strictement**
  2058 × 2058 (aucune cellule hors de la boîte initiale à aucun relevé,
  un planeur né entre deux relevés y serait encore visible — il ne meurt
  pas), pendant que la population oscille en [63 955, 64 798] : la
  machinerie tourne, mais **rien ne s'échappe** — contrairement à
  l'UnitCell. La prédiction « un métapixel isolé sur grille sans bord
  n'est pas périodique non plus » est donc **réfutée pour l'OTCA**. Le
  témoin de période `evolveHashlifeFastMemo 35328 otcaInitial =
  otcaInitial` reste exprimable en principe — mais la tranche 4 a
  **mesuré** son coût : l'évaluation `native_decide` ne termine pas en
  2 h sur cette machine (double tentative, aucune ligne de succès,
  aucun `.olean` produit). La période 35 328 reste citée, pas certifiée
  par l'organe : plafond mesuré, levable sur une machine plus dotée.
- **Témoins négatifs appariés** (critère 2 de #19989) : `pulsar_period1_negative`
  et `pulsar_period2_negative` accompagnent `pulsar_period3` — la période vaut
  donc **exactement** 3, et non un simple diviseur de 3. C'est le seul
  témoin de période **positif** du lake, donc le seul qui puisse recevoir
  une paire : pour l'UnitCell la paire est impossible *a fortiori* (le
  positif ne l'est pas — système ouvert mesuré, cf. ci-dessus) ; pour
  l'OTCA le positif reste exprimable en principe mais son évaluation
  dépasse le plafond mesuré (tranche 4, cf. ci-dessus) ; pour Gemini/CPU
  les grilles sont encore vides, où un négatif ne mesurerait rien de réel.
- **Futur** : le CPU (une fois son RLE chargé par le même mécanisme) — sa
  question du bord reste à trancher par la même méthode de mesure.

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
| `turingmachine.rle`    | variable     | 104         | (récit : Acte II)      |
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
    2058 × 2058, aucune cellule ne quitte la boîte, la population
    oscille en [63 955, 64 798] — système **fermé**. Le témoin
    `evolveHashlifeFastMemo 35328 otcaInitial = otcaInitial` a été
    tenté en tranche 4 : son évaluation `native_decide` ne termine pas
    en 2 h sur cette machine — les replays du lake sont consommés en
    quelques secondes, puis le silence jusqu'au délai, sans ligne de
    succès ni `.olean`. Plafond mesuré de l'organe sur ce témoin,
    levable sur une machine plus dotée.

    Ce qui est prouvé ici, et **non vacuous**, c'est que la grille chargée
    est réelle : 165 Ko de RLE passés par le même `include_str` +
    `RLE.parseRLE!` que l'UnitCell — la route `evolveHashlifeFastMemo_empty`
    est fermée pour ce motif. -/
theorem otca_initial_population : otcaInitial.length = 64691 := by
  native_decide

/-- La grille OTCA chargée n'est pas vide. Contrôle croisé indépendant :
    la même population (64 691) est mesurée par comptage Python direct des
    runs `o` du RLE source. -/
theorem otca_initial_nonempty : otcaInitial ≠ ([] : Grid) := by
  native_decide

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
    `scripts/lean/rle_to_lean_grid.py`. -/
theorem unitcell_initial_nonempty : unitcellInitial ≠ ([] : Grid) := by
  native_decide

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
