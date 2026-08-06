/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Life-as-Computation (le calcul par la Vie)

Validation croisee de l'algorithme Hashlife par quadtree face au `step` de
reference B3/S23, plus les primitifs de calcul (eaters, composition de
gliders multi-periodes). Ce module fait partie de l'Epic #1647
(Life-as-Computation).

Choix de conception :
- Tous les predicats renvoient `Bool` pour la decidabilite par calcul (`decide`).
- Le `eater1` (fishhook / hamecon) est le primitif d'absorption de signal le
  plus simple, la premiere brique des portes logiques spartiates.
- Les theoremes de coherence `evolveHashlife n g = evolve n g` verifient
  l'algorithme par quadtree face a la reference basee sur les listes pour
  les petites entrees.

Ce module est entierement prouve (aucun gap).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Computation_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.Hashlife

namespace Conway
namespace Life

/-! ## Section 1 : coherence Hashlife / reference

L'algorithme Hashlife (`Conway.Life.Hashlife`) calcule l'evolution par
decomposition en quadtree. L'algorithme de reference (`step`) opere
directement sur `List (Int × Int)`. Les theoremes de coherence ci-dessous
verifient que les deux algorithmes sont d'accord sur les petits patterns
canoniques.

Pour les entrees de niveau 2, `evolveHashlife` passe par `step4x4` (le cas
de base du quadtree). Pour les entrees plus grandes, il retombe sur `step`.
Dans les deux cas, le resultat doit coincider avec `evolve n g`.

### Decidabilite par calcul (`decide`, zero axiome) — #8869 resolu par #9536

Ces theoremes se prouvent par `decide` dans le noyau (zero axiome ajoute).
Le diagnostic anterieur (c.8126, #8749) concluait a une opacite **intrinseque**
de la couche `MacroCell` (et a la non-reductibilite de l'arithmetique `Int`) ;
il a ete **refute** par bisect de sous-expressions (c.847, 2026-08-05). Le seul
point bloquant etait `MacroCell.ceilLog2` (recursion `WellFounded` sur
`(k+2+1)/2`, non structurellement plus petit → opaque au reducteur du noyau),
un niveau plus profond que la couche `MacroCell` / `Int` incriminee. La PR #9536
(mergee) reecrit `ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1`
(recursion structurelle kernel-reductible de Mathlib, memes valeurs, spec
re-prouvee via `Nat.lt_pow_succ_log_self` + `omega`). Apres ce fix, ces
theoremes passent `decide` (noyau, zero axiome), supprimant les axiomes
`native_decide` de la base de confiance. Temoins `#eval` natifs en section 5.
-/

/-- Hashlife et reference sont d'accord sur `block` apres 1 generation.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_block_1 : evolveHashlife 1 block = evolve 1 block := by decide

/-- Hashlife et reference sont d'accord sur `block` apres 4 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_block_4 : evolveHashlife 4 block = evolve 4 block := by decide

/-- Hashlife et reference sont d'accord sur `blinker_h` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_blinker_2 : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by decide

/-- Hashlife et reference sont d'accord sur `glider` apres 4 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_glider_4 : evolveHashlife 4 glider = evolve 4 glider := by decide

/-- Hashlife et reference sont d'accord sur `beacon` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_beacon_2 : evolveHashlife 2 beacon = evolve 2 beacon := by decide

/-- Hashlife et reference sont d'accord sur `toad` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_toad_2 : evolveHashlife 2 toad = evolve 2 toad := by decide

/-! ## Section 2 : Eater 1 (Fishhook) — le puits de calcul le plus simple

L'**eater 1** (aussi appele « fishhook » / hamecon) est une vie stable de
7 cellules decouverte par les membres du groupe de Conway a Cambridge en
1971. C'est le primitif canonique d'absorption de signal dans les
constructions Life-as-Computation : sa frontiere « avale » les gliders
entrants en ~4 generations, revenant a sa forme originale.

Dans la logique spartiate (Rendell 2000, Goucher 2014), les eaters servent
de :
- Puits de signal aux sorties de portes
- Stabilisateurs de frontiere dans la construction des metapixels
- Absorbeurs aux terminaisons de fils

Disposition des coordonnees (haut-gauche = (0,0)) :
```
XX..
X.X.
..X.
..XX
```

### `isStillLife eater1` — prouve par `decide` dans le noyau (zero axiome)

Apres le swap `mergeSort -> insertionSort` (#8895, 2026-07-30), `isStillLife eater1`
se reduit sous `decide` : la verification statique (vie stable, aucune evolution)
n'exerce que le tri `sortDedup` sur une grille fixe, desormais decide-reducible.
`#print axioms Conway.Life.eater1_still_life` est vide (zero axiome) — preuve
purement calculatoire dans le noyau. (Le sondage #8749 du 2026-07-29, anterieur a
#8895, avait correctement constate l'obstruction sous `mergeSort` ; celle-ci est
levee depuis.)

Comme les equivalences `evolveHashlife n g = evolve n g` de la Section 1, le
present theoreme se prouve par `decide` dans le noyau (zero axiome). Historiquement,
`eater1_still_life` est devenu `decide`-reductible des le swap
`mergeSort -> insertionSort` (#8895), tandis que les equivalences de la Section 1
ont necessite en sus la reecriture de `ceilLog2` via `Nat.log 2` (#9536) : tant que
celle-ci etait une recursion `WellFounded` opaque au reducteur, elles restaient
`native_decide`. Le contraste historique pre-#9536 est documente en Section 1.
-/

/-- L'**eater 1** (fishhook), une vie stable de 7 cellules. -/
def eater1 : Grid :=
  [(0, 0), (0, 1),
   (1, 0), (1, 2),
   (2, 2),
   (3, 2), (3, 3)]

#eval s!"Eater 1: {eater1}"
#eval s!"step(eater1) = {step eater1}"
#eval s!"isStillLife eater1 = {isStillLife eater1}"

/-- L'eater 1 est une vie stable. Prouve par `decide` dans le noyau
    (zero axiome, `#print axioms` vide) — `isStillLife` sur grille fixe,
    decide-reducible post-#8895 (critere 2 de #8869). -/
theorem eater1_still_life : isStillLife eater1 = true := by decide

/-! ## Section 3 : composition de gliders par evolution multi-periode

Le glider a une periode 4 et un deplacement de `(1, -1)` par periode. Apres
`4 * k` generations, il doit etre egal a `shift (k, -k) glider`. Cette
composition multi-periode est la base de la propagation des signaux le long
des fils de gliders.

On verifie pour k = 1 (deja dans Life.lean), k = 2 et k = 3.
Le cas k = 2 (8 generations) se verifie aussi via `evolveHashlife`.

### Decidabilite par calcul (`decide`, zero axiome) — #8869 resolu par #9536

Ces theoremes se prouvent par `decide` dans le noyau (zero axiome ajoute).
Le diagnostic anterieur (c.8126, #8749) concluait a une opacite **intrinseque**
de la couche `MacroCell` (et a la non-reductibilite de l'arithmetique `Int`) ;
il a ete **refute** par bisect de sous-expressions (c.847, 2026-08-05). Le seul
point bloquant etait `MacroCell.ceilLog2` (recursion `WellFounded` sur
`(k+2+1)/2`, non structurellement plus petit → opaque au reducteur du noyau),
un niveau plus profond que la couche `MacroCell` / `Int` incriminee. La PR #9536
(mergee) reecrit `ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1`
(recursion structurelle kernel-reductible de Mathlib, memes valeurs, spec
re-prouvee via `Nat.lt_pow_succ_log_self` + `omega`). Apres ce fix, ces
theoremes passent `decide` (noyau, zero axiome), supprimant les axiomes
`native_decide` de la base de confiance. Temoins `#eval` natifs en section 5.
-/

/-- Apres 8 generations (2 periodes), le glider s'est deplace de (2, -2).
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem glider_2periods : evolve 8 glider = shift (2, -2) glider := by decide

/-- Apres 12 generations (3 periodes), le glider s'est deplace de (3, -3).
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem glider_3periods : evolve 12 glider = shift (3, -3) glider := by decide

/-- Hashlife et reference sont d'accord sur le glider apres 8 generations (2 periodes).
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_glider_8 : evolveHashlife 8 glider = evolve 8 glider := by decide

/-! ## Section 4 : verification de l'aller-retour MacroCell

Verification structurelle : l'aller-retour `Grid → MacroCell → Grid`
preserve les cellules vivantes pour les patterns canoniques. Cela verifie
l'encodage/decodage du quadtree a la couche MacroCell (independamment de
step/evolve).

### Decidabilite par calcul (`decide`, zero axiome) — #8869 resolu par #9536

Ces theoremes se prouvent par `decide` dans le noyau (zero axiome ajoute).
Le diagnostic anterieur (c.8126, #8749) concluait a une opacite **intrinseque**
de la couche `MacroCell` (et a la non-reductibilite de l'arithmetique `Int`) ;
il a ete **refute** par bisect de sous-expressions (c.847, 2026-08-05). Le seul
point bloquant etait `MacroCell.ceilLog2` (recursion `WellFounded` sur
`(k+2+1)/2`, non structurellement plus petit → opaque au reducteur du noyau),
un niveau plus profond que la couche `MacroCell` / `Int` incriminee. La PR #9536
(mergee) reecrit `ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1`
(recursion structurelle kernel-reductible de Mathlib, memes valeurs, spec
re-prouvee via `Nat.lt_pow_succ_log_self` + `omega`). Apres ce fix, ces
theoremes passent `decide` (noyau, zero axiome), supprimant les axiomes
`native_decide` de la base de confiance. Temoins `#eval` natifs en section 5.
-/

/-- Le block survive a l'aller-retour MacroCell. `decide` dans le noyau, zero axiome
    — reductible apres le fix `ceilLog2` (#9536, #8869). -/
theorem block_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset block
     mc.toGrid off == block) = true := by decide

/-- Le glider survive a l'aller-retour MacroCell. `decide` dans le noyau, zero axiome
    — reductible apres le fix `ceilLog2` (#9536, #8869). -/
theorem glider_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset glider
     mc.toGrid off == glider) = true := by decide

/-- L'eater 1 survive a l'aller-retour MacroCell. `decide` dans le noyau, zero axiome
    — reductible apres le fix `ceilLog2` (#9536, #8869). -/
theorem eater1_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset eater1
     mc.toGrid off == eater1) = true := by decide

/-! ## Section 5 : temoins diagnostiques #eval

Temoins de calcul plus grands verifies par `#eval` (evaluation par le noyau)
plutot que par `native_decide` (reduction par le noyau). Ils demontrent que
le pipeline Hashlife fonctionne sur des entrees plus grandes et des
evolutions multi-etapes.
-/

-- Le glider rencontre l'eater : apres 8 etapes, la configuration combinee evolue
-- (aucune affirmation sur l'absorption exacte — cela depend de la geometrie precise).
def glider_meets_eater : Grid :=
  sortDedup (glider ++ (eater1.map (fun p => (p.1, p.2 + 6))))

#eval s!"glider + eater combined: {glider_meets_eater.length} cells"
#eval s!"After 4 steps: {(evolve 4 glider_meets_eater).length} cells"
#eval s!"After 8 steps: {(evolve 8 glider_meets_eater).length} cells"

-- Controle croise : Hashlife vs reference sur le glider multi-etapes
#eval evolveHashlife 0 glider == glider
#eval evolveHashlife 1 glider == evolve 1 glider
#eval evolveHashlife 4 glider == evolve 4 glider
#eval evolveHashlife 8 glider == evolve 8 glider

-- Hashlife sur l'eater (vie stable = aucun changement a chaque etape)
#eval evolveHashlife 10 eater1 == eater1

/-! ## Section 6 : validation de l'acceleration exponentielle Hashlife

`evolveHashlifeFast` utilise l'algorithme recursif Hashlife pour avancer
de `2^level` generations en une seule etape MacroCell. Ces theoremes
verifient la correction du chemin rapide face a la reference `evolve` pour
les patterns canoniques.

### Decidabilite par calcul (`decide`, zero axiome) — #8869 resolu par #9536

Ces theoremes se prouvent par `decide` dans le noyau (zero axiome ajoute).
Le diagnostic anterieur (c.8126, #8749) concluait a une opacite **intrinseque**
de la couche `MacroCell` (et a la non-reductibilite de l'arithmetique `Int`) ;
il a ete **refute** par bisect de sous-expressions (c.847, 2026-08-05). Le seul
point bloquant etait `MacroCell.ceilLog2` (recursion `WellFounded` sur
`(k+2+1)/2`, non structurellement plus petit → opaque au reducteur du noyau),
un niveau plus profond que la couche `MacroCell` / `Int` incriminee. La PR #9536
(mergee) reecrit `ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1`
(recursion structurelle kernel-reductible de Mathlib, memes valeurs, spec
re-prouvee via `Nat.lt_pow_succ_log_self` + `omega`). Apres ce fix, ces
theoremes passent `decide` (noyau, zero axiome), supprimant les axiomes
`native_decide` de la base de confiance. Temoins `#eval` natifs en section 5.
-/

/-- `evolveHashlifeFast` coincide avec la reference sur `block` apres 4 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_fast_block_4 : evolveHashlifeFast 4 block = evolve 4 block := by decide

/-- `evolveHashlifeFast` coincide avec la reference sur le glider apres 4 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_fast_glider_4 : evolveHashlifeFast 4 glider = evolve 4 glider := by decide

/-- `evolveHashlifeFast` coincide avec la reference sur le glider apres 8 generations
    (2 periodes completes, deplacement (2, -2)). `decide` dans le noyau, zero axiome — reductible
    apres le fix `ceilLog2` (#9536, #8869). -/
theorem hashlife_fast_glider_8 : evolveHashlifeFast 8 glider = shift (2, -2) glider := by decide

/-- `evolveHashlifeFast` coincide avec la reference sur `blinker` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_fast_blinker_2 : evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by decide

/-- `evolveHashlifeFast` coincide avec la reference sur `beacon` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_fast_beacon_2 : evolveHashlifeFast 2 beacon = evolve 2 beacon := by decide

/-- `evolveHashlifeFast` coincide avec la reference sur `toad` apres 2 generations.
    (`decide` dans le noyau, zero axiome — reductible apres le fix `ceilLog2` #9536, #8869.) -/
theorem hashlife_fast_toad_2 : evolveHashlifeFast 2 toad = evolve 2 toad := by decide

-- temoins #eval pour les sauts plus grands (valide le chemin recursif)
#eval evolveHashlifeFast 16 block == evolve 16 block
#eval evolveHashlifeFast 12 glider == shift (3, -3) glider
#eval evolveHashlifeFast 4 blinker_h == blinker_h  -- periode 2, 4 = 2 periodes
#eval evolveHashlifeFast 10 eater1 == eater1  -- vie stable

end Life
end Conway
