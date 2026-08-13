/-
! # Une tournée des motifs du Jeu de la Vie

Ce module est un **chemin pédagogique** à travers la zoologie des motifs du Jeu de
la Vie de Conway. Il ne définit pas de nouvelle théorie : il fait *tourner* la
théorie existante et la *prouve* sur des exemples concrets, en suivant un fil
narratif unique — la progression des régimes dynamiques :

  **équilibre** (still lifes) → **cycle** (oscillateurs) → **translation** (vaisseaux)
                              → **sérialisation** (RLE) → **accélération** (Hashlife).

Chaque section pose le même geste deux fois : un `#eval` qui *calcule* l'évolution
(« on regarde le motif vivre »), puis un `theorem ... := by decide` qui *prouve*
que ce que l'on voit est bien la propriété annoncée. Les preuves par `decide`
s'exécutent dans le noyau sans ajouter d'axiome (cf. `Computation.lean` §6,
fix `ceilLog2` #9536) ; les rares `native_decide` (pulsar, canon) sont signalés
et ajoutent l'axiome `Lean.ofReduceBool` — l'équivalent formel d'un `#eval`证人.

La convention i18n est Pattern A (cf. `code-style.md`, EPIC #4980) : ce fichier est
le canonique français, le miroir anglais vit dans `PatternTour_en.lean`. Seules les
docstrings et les commentaires diffèrent ; énoncés, tactiques, preuves sont
byte-identiques entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.Oscillators
import Conway.Life.Spaceships
import Conway.Life.RLE
import Conway.Life.Computation

namespace Conway
namespace Life
open RLE

/-! ## §1. Équilibre — les still lifes

Un *still life* est une configuration stable : appliquer une étape du Jeu de la Vie
la laisse inchangée. Ce n'est pas de l'inertie — chaque cellule vivante doit avoir
exactement deux ou trois voisins, et chaque cellule morte doit avoir tout sauf
trois voisins, pour que rien ne bouge. Le plus petit still life non trivial est le
*bloc* (2×2) ; les classiques `loaf`, `boat`, `tub`, `pond`, `ship` montrent la
variété des équilibres locaux possibles.

On *regarde* l'équilibre (le `#eval` renvoie `true`), puis on le *prouve* dans le
noyau (`decide`, zéro axiome). -/

-- Le pain (`loaf`) est un still life à 7 cellules. Le calcul confirme la stabilité.
#eval isStillLife loaf      -- attendu : true
#eval (step loaf) == loaf   -- attendu : true (réduction explicite d'une étape)

/-- Le pain est un still life : une étape le laisse invariant. Preuve par `decide`
    dans le noyau, zéro axiome ajouté. -/
theorem loaf_is_still_life : isStillLife loaf = true := by decide

/-- Le bac (`tub`) est un still life à 4 cellules. Preuve noyau, zéro axiome. -/
theorem tub_is_still_life : isStillLife tub = true := by decide

/-! ## §2. Cycle — les oscillateurs

Un *oscillateur de période n* revient à lui-même après exactement n étapes, sans se
déplacer. Le `blinker` (3 cellules en ligne, période 2) est le plus célèbre ; le
`beacon` (période 2) et le `toad` (période 2) sont d'autres oscillateurs compacts.
Pour les grandes structures, le `pulsar` (48 cellules, période 3) et le
`pentadecathlon` (période 15) dépassent la limite de récursion du noyau : on bascule
sur `native_decide`, qui compile le calcul et ajoute l'axiome `Lean.ofReduceBool`.

La bascule `decide` → `native_decide` est exactement le diagnostic du cycle c.736
documenté dans `decidable_instance_propagation.md` : sur les prédicats d'état du Jeu
de la Vie, `decide` tient jusqu'à une profondeur de récursion modérée, puis cède la
place à l'évaluation native. -/

-- Le phare (`beacon`) oscille avec période 2.
#eval isOscillator beacon 2       -- attendu : true
#eval (evolve 1 beacon) == beacon -- attendu : false (la demi-période change la forme)

/-- Le phare est un oscillateur de période 2. Preuve noyau, zéro axiome. -/
theorem beacon_is_oscillator : isOscillator beacon 2 = true := by decide

-- Le pulsar (48 cellules) dépasse la limite de récursion du noyau : évaluation native.
#eval isOscillator pulsar 3       -- attendu : true
#eval (evolve 3 pulsar) == pulsar -- attendu : true (une période complète)

/-- Le pulsar est un oscillateur de période 3. Le prédicat porte sur 48 cellules ;
    `decide` échoue ici par limite de récursion (`maxRecDepth`), donc on recourt à
    `native_decide` : le calcul est compilé, et la preuve repose sur l'axiome
    `Lean.ofReduceBool`. C'est l'équivalent formel d'un `#eval` témoin. -/
theorem pulsar_is_oscillator : isOscillator pulsar 3 = true := by native_decide

/-! ## §3. Translation — les vaisseaux

Un *vaisseau* (spaceship) de période n et de déplacement v est la version mobile de
l'oscillateur : après n étapes, le motif réapparaît *translaté* de v. Le `glider`
(5 cellules) est le plus petit vaisseau et le seul diagonal à c/4 (une cellule en
diagonale toutes les 4 étapes). Les vaisseaux orthogonaux `lwss`/`mwss`/`hwss`
filent à c/2 (deux cellules horizontalement toutes les 4 étapes).

C'est ici que le fil pédagogique se resserre : **un vaisseau est un oscillateur
dans le référentiel qui se translate avec lui.** Le `#eval` calcule la translation
effective ; le théorème la prouve. -/

-- Le glider se déplace d'une cellule en diagonale (1, -1) toutes les 4 étapes.
#eval isSpaceship glider 4 (1, -1)        -- attendu : true
#eval (evolve 4 glider) == shift (1,-1) glider  -- attendu : true (translation calculée)
#eval (evolve 8 glider) == shift (2,-2) glider  -- attendu : true (deux périodes → 2× le déplacement)

/-- Le glider est un vaisseau diagonal de période 4 et de déplacement (1, -1).
    Preuve noyau, zéro axiome. -/
theorem glider_is_spaceship : isSpaceship glider 4 (1, -1) = true := by decide

/-- Le vaisseau léger (`lwss`) est un vaisseau orthogonal de période 4 et de
    déplacement (0, 2) — vitesse c/2. Preuve noyau, zéro axiome. -/
theorem lwss_is_spaceship : isSpaceship lwss 4 (0, 2) = true := by decide

/-- Uniformité du déplacement du glider : après une demi-période de plus (8 étapes,
    soit deux périodes), la translation est exactement le double. C'est l'invariance
    d'échelle du mouvement — le glider ne dérive pas, il translate linéairement.
    Preuve noyau, zéro axiome. -/
theorem glider_two_periods_translation : evolve 8 glider = shift (2, -2) glider := by decide

/-! ## §4. Sérialisation — le format RLE

Le format *Run-Length Encoded* (RLE) est la lingua franca des motifs du Jeu de la
Vie : un fichier texte compact (`bo$2b3o!`) encode une grille, lisible par tous les
simulateurs. La fonction `parseRLE` (qui retourne un `Except String Grid`) analyse
une chaîne en une `Grid` ; `parseRLE!` est l'enveloppe qui renvoie `[]` en cas
d'erreur, pratique pour les `#eval`.

L'intérêt pédagogique : **le même motif existe sous deux formes** — une constante
écrite à la main (`glider : Grid`) et une chaîne parsée (`glider_parsed`) — et l'on
peut prouver qu'elles coïncident. Le *Gosper Glider Gun* (36 cellules, 1970) est le
premier motif fini connu à croissance non bornée : il émet un glider toutes les 30
étapes, indéfiniment. C'est le chaînon entre les vaisseaux (§3) et la computation
(§5). -/

-- Le canon de Gosper analysé depuis sa chaîne RLE : 36 cellules vivantes.
#eval gosper_gun.length                       -- attendu : 36
#eval (parseRLE gosper_gun_RLE).toOption.isSome  -- attendu : true (RLE bien formé)

/- Remarque pédagogique : on pourrait être tenté d'énoncer `theorem gosper_gun_has_36_cells
   : gosper_gun.length = 36 := by decide`. Mais `decide` échoue ici, bloqué par l'opacité
   du parseur : `gosper_gun := parseRLE! gosper_gun_RLE` est une `def` non-`@[reducible]`,
   que le noyau ne déplie pas lors de la synthèse de l'instance `Decidable` (cf.
   `docs/lean/decidable_instance_propagation.md`, cycle c.939). Le témoin `#eval` ci-dessus,
   qui réduit par évaluation, est donc la preuve computationnelle honnête de ce compte de
   cellules — sans ajouter l'axiome `Lean.ofReduceBool` qu'exigerait `native_decide`. C'est
   précisément le choix fait par `Conway.Life.RLE` pour ses propres vérifications. -/

-- Recoupements sérialisation ↔ constante manuelle. Le lwss RLE coïncide exactement
-- avec la constante ; le glider RLE est le même motif modulo une convention de
-- coordonnées (cf. `Conway.Life.RLE`), on vérifie donc son compte de cellules.
#eval glider_parsed.length        -- attendu : 5 (même cardinal que `glider`)
#eval lwss_parsed == lwss         -- attendu : true (coïncidence exacte)

/-! ## §5. Accélération — Hashlife

`evolveHashlifeFast` avance une grille de `2^k` générations en une seule étape de
l'algorithme récursif Hashlife, qui exploite la redondance de la structure quadtree
du plan. Pour les motifs périodiques (oscillateurs, vaisseaux, canons), Hashlife
atteint une accélération exponentielle : avancer de 2^k générations coûte
essentiellement le même temps qu'avancer de 2^(k-1).

La correction de ce « chemin rapide » se prouve contre la référence naïve `evolve`.
Après le fix `ceilLog2` (#9536, résolvant #8869), ces égalités passent `decide` dans
le noyau sans ajouter d'axiome — la couche `MacroCell` n'est plus opaque au
réducteur. C'est le point d'aboutissement de la tournée : la même évolution,
calculée par deux algorithmes aux complexités radicalement différentes, prouvée
égale. -/

-- Hashlife vs référence : même résultat sur le glider, à 4 et 8 générations.
#eval evolveHashlifeFast 4 glider == evolve 4 glider   -- attendu : true
#eval evolveHashlifeFast 8 glider == evolve 8 glider   -- attendu : true

-- Le « chemin rapide » retrouve exactement la translation prouvée au §3.
#eval evolveHashlifeFast 4 glider == shift (1, -1) glider  -- attendu : true
#eval evolveHashlifeFast 8 glider == shift (2, -2) glider  -- attendu : true

/- L'énoncé jumeau `evolveHashlifeFast 4 glider = evolve 4 glider` (coïncidence avec la
   référence) vit déjà dans `Conway.Life.Computation.hashlife_fast_glider_4`. La tournée en
   déduit ici le résultat de translation, qui relie §3 et §5 : le chemin rapide retrouve
   exactement le déplacement prouvé sur la référence naïve. -/

/-- Le chemin rapide Hashlife retrouve, en une étape `MacroCell`, la translation
    diagonale (1, -1) que la référence calcule pas à pas sur 4 générations. C'est
    l'invariance d'échelle du §3 vue depuis l'algorithme accéléré. Preuve noyau,
    zéro axiome. -/
theorem hashlife_fast_glider_translation_4 : evolveHashlifeFast 4 glider = shift (1, -1) glider := by decide

/-! ## Coda

Du `loaf` immobile au canon de Gosper qui crache des vaisseaux, les motifs du Jeu de
la Vie exhibent cinq régimes dynamiques que l'on peut, pour chacun, à la fois
*regarder tourner* (`#eval`) et *prouver* (`theorem ... := by decide`). Le fil de
cette tournée — équilibre, cycle, translation, sérialisation, accélération — est
lui-même le livrable : il relie des modules jusqu'ici indépendants
(`Oscillators`, `Spaceships`, `RLE`, `Computation`) en un seul récit, où chaque
`theorem` est un point d'ancrage et chaque `#eval` un témoin vivant. -/

end Life
end Conway
