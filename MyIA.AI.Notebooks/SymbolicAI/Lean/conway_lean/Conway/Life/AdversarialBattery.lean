/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Bestiaire adversarial (cribleur c.91) — validation des énoncés universels candidats

Module cribleur (#9568-A) : un **bestiaire de configurations pathologiques** sur
lequel tout énoncé universel candidat — hérité OU nouveau — doit être instancié
AVANT toute itération prover. Généralise le probe c.91 (#9565) qui a tué les trois
lemmes du bras NW de P4 (`p4_nw_overlap_wall` / `p4_nw_g3_bridge` /
`p4_nw_supercell_agree`) : le quantificateur `p : Int × Int` y était libre alors
que le supercell ne représente que la **fenêtre centrale** du parent, et un
contre-exemple trivial (bloc 2×2 au coin absolu NW, `k = 1`) falsifiait l'énoncé
depuis le début. Le test de spécialisation `exact` au site d'appel ne prouvait que
la **suffisance** de l'énoncé (il ferme le but), jamais sa **satisfaisabilité**.

### Deux modes d'usage (sur tout énoncé candidat, avant tout cycle prover)

1. **Falsification** : instancier l'énoncé sur chaque témoin du bestiaire,
   `decide` la conclusion. Hypothèses satisfaites + conclusion fausse ⇒ l'énoncé
   est mort, un théorème de contre-exemple à la `..._counterexample` (#9565) le
   certifie. Ce mode a tué les murs NW/SE/SW (c.91).
2. **Sanité** : l'énoncé restreint au bestiaire doit `decide` à `true` (condition
   **nécessaire**, pas suffisante — un vert du cribleur n'est jamais une preuve,
   mais un rouge est fatal). Les théorèmes `cex*_sanity` ci-dessous garantissent
   que le bestiaire est **bien formé** : chaque témoin a bien la propriété GoL
   qu'il est censé exercer (nature morte, oscillateur, vaisseau, vacuité, mort).

### Contraintes

Toutes les preuves de ce module sont kernel-`decide` pur (réductibilité acquise
par la réécriture `ceilLog2` #9536), **zéro axiome natif**, `native_decide`
interdit, budget compile borné (`k ≤ 2`). EPIC #3846 / #6724. Sans sorry.

### Couche Grid vs couche MacroCell

Le bestiaire fournit les DEUX couches : (a) des **témoins `Grid`** positionnés,
pour cribler les énoncés de localité universels comme `evolve_box_agree` (#9577)
et les réénoncés bornés à venir ; (b) des **témoins `MacroCell`** (généralisation
publique de `p4CexBlock1`/`p4CexEmpty1` de #9565) pour cribler les énoncés
d'assemblage P4 à l'échelle du supercell.
-/

/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
  canonique**, avec son miroir anglais dans le fichier sibling
  `AdversarialBattery_en.lean`. Les énoncés de théorèmes, les tactiques Lean, les
  noms de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ;
  seules les docstrings et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.MacroCell

namespace Conway
namespace Life
open MacroCell

/-! ## Couche Grid — témoins positionnés + sanité (decide)

Configurations canoniques positionnées pour exercer les pathologies de bord :
bloc (nature morte docile) aux quatre coins, blinker à cheval sur une frontière,
glider dirigé hors-fenêtre, univers vide, univers plein (surpopulation).
-/

/-- Témoin : univers vide (vacuité — `evolve` le préserve). -/
def cexEmpty : Grid := []

/-- Témoin : bloc 2×2 (nature morte) au coin absolu NW d'une fenêtre `[0, ...)²`.
    C'est la configuration qui a tué le mur NW (`p4_nw_overlap_wall`, #9565) :
    persiste (LHS `true`) tandis que le RHS évalué en `(-1,-1)` est hors fenêtre
    (`false`). -/
def cexBlockNW : Grid := block

/-- Témoin : bloc 2×2 décalé en `(2, 2)` (coin intérieur — encore dans la fenêtre
    centrale pour `k = 2`, exerçant la frontière de marge). -/
def cexBlockShifted : Grid := shift (2, 2) block

/-- Témoin : blinker horizontal (oscillateur période 2) à l'origine — à cheval
    sur la frontière de fenêtre sous une évolution de 1 pas (le `step` l'étire
    en vertical, débordant la boîte d'origine). -/
def cexBlinker : Grid := blinker_h

/-- Témoin : glider (5 cellules) dirigé vers le coin SE — vaisseau spatial qui
    **sort** de toute fenêtre bornée en 4 pas, exerçant le « bleed off the edge ». -/
def cexGlider : Grid := glider

/-- Témoin : fenêtre 4×4 pleine (`k = 1`) — surpopulation : chaque cellule a 8
    voisines vivantes et meurt en 1 pas (B3/S23 exige 2-3 pour survivre). -/
def cexFull1 : Grid :=
  [(0, 0), (0, 1), (0, 2), (0, 3),
   (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3),
   (3, 0), (3, 1), (3, 2), (3, 3)]

/-- **Sanité** : le témoin vide est une nature morte (vacuité préservée). -/
theorem cexEmpty_stillLife : isStillLife cexEmpty = true := by decide

/-- **Sanité** : le bloc au coin NW est une nature morte (le pattern docile qui a
    tué le mur NW — il persiste, donc LHS = `true`). -/
theorem cexBlockNW_stillLife : isStillLife cexBlockNW = true := by decide

/-- **Sanité** : le bloc décalé reste une nature morte (la translation préserve
    le caractère de nature morte — invariance par `shift`). -/
theorem cexBlockShifted_stillLife : isStillLife cexBlockShifted = true := by decide

/-- **Sanité** : le blinker est un oscillateur de période 2 (exerce le débordement
    de frontière à chaque demi-période). -/
theorem cexBlinker_period2 : isOscillator cexBlinker 2 = true := by decide

/-- **Sanité** : le glider est un vaisseau spatial de période 4 et déplacement
    `(1, -1)` (vecteur canonique `glider_spaceship` de `Life.lean`, exerce le
    « bleed off the edge » — sort de la fenêtre bornée). -/
theorem cexGlider_spaceship : isSpaceship cexGlider 4 (1, -1) = true := by decide

/-- **Sanité** : la fenêtre pleine 4×4 n'est PAS une nature morte (surpopulation —
    le `step` la tue). `false` ici est attendu et confirme le témoin. -/
theorem cexFull1_notStillLife : isStillLife cexFull1 = false := by decide

/-! ## Couche MacroCell — témoins de supercell (généralisation publique de #9565)

Les témoins `p4CexBlock1`/`p4CexEmpty1` de #9565 sont `private` dans
`HashlifeCorrectness` ; cette section en fournit des versions **publiques** et
généralise le bloc au quatre quadrants, pour cribler les réénoncés bornés des
murs/bridges P4 à l'échelle du supercell.
-/

/-- Cellule niveau 1 vide (témoin MacroCell du contre-exemple #9565). -/
def cexEmpty1 : MacroCell :=
  node (leaf false) (leaf false) (leaf false) (leaf false)

/-- Cellule niveau 1 pleine — bloc 2×2, nature morte (témoin MacroCell #9565). -/
def cexBlock1 : MacroCell :=
  node (leaf true) (leaf true) (leaf true) (leaf true)

/-- Cellule niveau 2 (fenêtre 4×4) dont seul le quadrant NW est un bloc 2×2,
    les 3 autres quadrants vides — l'instantiation exacte du contre-exemple
    #9565 (`nw = bloc`, reste vide), rendue publique pour re-cribler les
    réénoncés bornés des murs P4 à l'échelle du supercell. -/
def cexBlockNWcorner2 : MacroCell :=
  node cexBlock1 cexEmpty1 cexEmpty1 cexEmpty1

/-- **Sanité** : `cexBlockNWcorner2` est de niveau 2 (fenêtre 4×4 = 16 cellules,
    2 niveaux de nœuds au-dessus des feuilles). -/
theorem cexBlockNWcorner2_level2 : cexBlockNWcorner2.level = 2 := by decide

end Life
end Conway
