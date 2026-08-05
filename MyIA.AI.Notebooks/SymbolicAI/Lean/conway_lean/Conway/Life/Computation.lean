/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Life-as-Computation (le calcul par la Vie)

Validation croisee de l'algorithme Hashlife par quadtree face au `step` de
reference B3/S23, plus les primitifs de calcul (eaters, composition de
gliders multi-periodes). Ce module fait partie de l'Epic #1647
(Life-as-Computation).

Choix de conception :
- Tous les predicats renvoient `Bool` pour la compatibilite avec `native_decide`.
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

### Pourquoi `native_decide` (et non `decide`) — #8749, refine #8869 c.8126

Ces six theoremes d'equivalence utilisent `native_decide` par **necessite
structurelle**, non par commodite. Le noyau Lean ne peut pas les prouver par
`decide` : avec `set_option maxRecDepth 100000`, chacun echoue par
`reduction got stuck at the Decidable instance` (compilation en erreur,
en quelques secondes) — un echec *definitif*, pas un depassement de temps
que davantage de profondeur de reduction leverait.

**Locus precis de l'obstruction (sondage c.8126, 2026-08-05, PR ouverte)**.
Une investigation en trois sondes a localise la cause **non pas** dans la
liste `Int × Int` (sortDedup, post-#8895) mais dans la **couche
`MacroCell`** :

| Sonde | Enonce | decide ? |
|-------|--------|----------|
| `step block = block` | list-level path | **OUI** (PASS, coherent avec `block_still_life` L231) |
| `mc.toGrid (0,0) = block` | MacroCell → Grid | **NON** (stuck sur `instDecidableEqList` apres unfold) |
| `hashlifeStep1 mc = mc` | MacroCell quadtree | **NON** (stuck sur `instDecidableEqMacroCell.decEq`, recursion 4-quadrants `node nw ne sw se`) |

L'erreur littérale de la sonde `mc.toGrid (0,0) = block` :

```
instDecidableEqList (MacroCell.toGrid (0, 0) (gridToMacroCellWithOffset block).2) block
did not reduce to `isTrue` or `isFalse`.
After unfolding the instance `instDecidableEqList`, reduction got stuck at
the `Decidable` instance
  match MacroCell.toGrid (0, 0) (gridToMacroCellWithOffset block).2 with
  | [] => ... | a :: as => match decEq a b with ...
```

Le reductor unfold `instDecidableEqList` jusqu'au `match` sur la liste,
mais **`MacroCell.toGrid` est une definition recursive** (`sortDedup` ∘
`toCellsAux`, lui-meme recursive sur les 4 quadrants) que le kernel ne
deplie **pas** en squelette littéral. C'est une **limitation structurelle
du reductor**, indépendante de la profondeur de recursion
(`maxRecDepth 1000000` deja applique). La voie `Grid = Nat × Nat`
(autrefois envisagee comme echappatoire a `Int` non-reductible) **ne
resoudrait pas** ce goulot d'etranglement : l'opacite est dans la couche
`MacroCell`, pas dans le type des coordonnees.

Les enonces sont VRAIS (temoins `#eval` natifs en section 5) : c'est
exactement le role de `native_decide` — evaluer le calcul en code natif et
ajouter le resultat a la base de confiance plutot que de le reverifier dans
le noyau. Verifie par-theoreme pour les six declarations de cette section
(sondage #8749, 2026-07-29, puis affine c.8126, 2026-08-05).
-/

/-- Hashlife et reference sont d'accord sur `block` apres 1 generation.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_block_1 : evolveHashlife 1 block = evolve 1 block := by native_decide

/-- Hashlife et reference sont d'accord sur `block` apres 4 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_block_4 : evolveHashlife 4 block = evolve 4 block := by native_decide

/-- Hashlife et reference sont d'accord sur `blinker_h` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_blinker_2 : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by native_decide

/-- Hashlife et reference sont d'accord sur `glider` apres 4 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_glider_4 : evolveHashlife 4 glider = evolve 4 glider := by native_decide

/-- Hashlife et reference sont d'accord sur `beacon` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_beacon_2 : evolveHashlife 2 beacon = evolve 2 beacon := by native_decide

/-- Hashlife et reference sont d'accord sur `toad` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 1, #8749 / refine #8869 c.8126). -/
theorem hashlife_toad_2 : evolveHashlife 2 toad = evolve 2 toad := by native_decide

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

Contraste avec les equivalences `evolveHashlife n g = evolve n g` de la Section 1 :
celles-ci exercent la machinerie quadtree complete sur `Grid = List (Int × Int)` et
restent non-reductibles sous `decide` (`native_decide` requis, voir Section 1).
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

### Pourquoi `native_decide` — #8749, refine #8869 c.8126

Ces trois theoremes (periodicite du glider + coherence hashlife sur 8
generations) ne se reduisent pas sous `decide` (`maxRecDepth 100000` :
chacun stuck a l'instance `Decidable`, EXIT≠0, verifie par-theoreme).
Cause structurelle localisee en c.8126 (2026-08-05) : la couche
`MacroCell` quadtree (`toGrid` recursive + `instDecidableEqMacroCell.decEq`
sur 4-quadrants) est opaque au reductor, PAS la liste `Int × Int` (voir
Section 1 docstring pour le detail des 3 sondes `step` / `toGrid` /
`hashlifeStep1`). Enonces VRAIS (`#eval` section 5) ; `native_decide`
requis.
-/

/-- Apres 8 generations (2 periodes), le glider s'est deplace de (2, -2).
    `native_decide` requis : non-reductible sous `decide` (voir Section 3, #8749 / refine #8869 c.8126). -/
theorem glider_2periods : evolve 8 glider = shift (2, -2) glider := by native_decide

/-- Apres 12 generations (3 periodes), le glider s'est deplace de (3, -3).
    `native_decide` requis : non-reductible sous `decide` (voir Section 3, #8749 / refine #8869 c.8126). -/
theorem glider_3periods : evolve 12 glider = shift (3, -3) glider := by native_decide

/-- Hashlife et reference sont d'accord sur le glider apres 8 generations (2 periodes).
    `native_decide` requis : non-reductible sous `decide` (voir Section 3, #8749 / refine #8869 c.8126). -/
theorem hashlife_glider_8 : evolveHashlife 8 glider = evolve 8 glider := by native_decide

/-! ## Section 4 : verification de l'aller-retour MacroCell

Verification structurelle : l'aller-retour `Grid → MacroCell → Grid`
preserve les cellules vivantes pour les patterns canoniques. Cela verifie
l'encodage/decodage du quadtree a la couche MacroCell (independamment de
step/evolve).

### Pourquoi `native_decide` — #8749, refine #8869 c.8126

Ces trois theoremes d'aller-retour ne se reduisent pas sous `decide`
(`maxRecDepth 100000` : chacun stuck a l'instance `Decidable`, EXIT≠0,
verifie par-theoreme). Cause structurelle localisee en c.8126 (2026-08-05) :
`mc.toGrid` (recursive MacroCell → Grid) est opaque au reductor, comme la
sonde `probe_macrocell_togrid_block_unfolds` l'a verifie (sortie
verbatim dans Section 1 docstring). L'egalite `mc.toGrid off == block`
mobilise la meme instance `instDecidableEqList` non-reductible. Enonces
VRAIS (`#eval` section 5) ; `native_decide` requis.
-/

/-- Le block survive a l'aller-retour MacroCell. `native_decide` requis :
    non-reductible sous `decide` (voir Section 4, #8749 / refine #8869 c.8126). -/
theorem block_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset block
     mc.toGrid off == block) = true := by native_decide

/-- Le glider survive a l'aller-retour MacroCell. `native_decide` requis :
    non-reductible sous `decide` (voir Section 4, #8749 / refine #8869 c.8126). -/
theorem glider_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset glider
     mc.toGrid off == glider) = true := by native_decide

/-- L'eater 1 survive a l'aller-retour MacroCell. `native_decide` requis :
    non-reductible sous `decide` (voir Section 4, #8749 / refine #8869 c.8126). -/
theorem eater1_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset eater1
     mc.toGrid off == eater1) = true := by native_decide

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

### Pourquoi `native_decide` — #8749, refine #8869 c.8126

Ces six theoremes (chemin rapide `evolveHashlifeFast` vs reference) ne se
reduisent pas sous `decide` (`maxRecDepth 100000` : chacun stuck aux
instances `instDecidableEqBool`/`instDecidableEqList`/`instDecidableEqNat`/
`Nat.decLe`, EXIT≠0, verifie par-theoreme). Cause structurelle localisee
en c.8126 (2026-08-05) : la couche `MacroCell` quadtree est opaque au
reductor, comme les sondes l'ont verifie (voir Section 1 docstring) ; le
chemin rapide mobilise la meme arithmetique `MacroCell` recursive que
`evolveHashlife`. Enonces VRAIS (`#eval` section 5) ; `native_decide`
requis.
-/

/-- `evolveHashlifeFast` coincide avec la reference sur `block` apres 4 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_block_4 : evolveHashlifeFast 4 block = evolve 4 block := by native_decide

/-- `evolveHashlifeFast` coincide avec la reference sur le glider apres 4 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_glider_4 : evolveHashlifeFast 4 glider = evolve 4 glider := by native_decide

/-- `evolveHashlifeFast` coincide avec la reference sur le glider apres 8 generations
    (2 periodes completes, deplacement (2, -2)). `native_decide` requis : non-reductible
    sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_glider_8 : evolveHashlifeFast 8 glider = shift (2, -2) glider := by native_decide

/-- `evolveHashlifeFast` coincide avec la reference sur `blinker` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_blinker_2 : evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by native_decide

/-- `evolveHashlifeFast` coincide avec la reference sur `beacon` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_beacon_2 : evolveHashlifeFast 2 beacon = evolve 2 beacon := by native_decide

/-- `evolveHashlifeFast` coincide avec la reference sur `toad` apres 2 generations.
    `native_decide` requis : non-reductible sous `decide` (voir Section 6, #8749 / refine #8869 c.8126). -/
theorem hashlife_fast_toad_2 : evolveHashlifeFast 2 toad = evolve 2 toad := by native_decide

-- temoins #eval pour les sauts plus grands (valide le chemin recursif)
#eval evolveHashlifeFast 16 block == evolve 16 block
#eval evolveHashlifeFast 12 glider == shift (3, -3) glider
#eval evolveHashlifeFast 4 blinker_h == blinker_h  -- periode 2, 4 = 2 periodes
#eval evolveHashlifeFast 10 eater1 == eater1  -- vie stable

end Life
end Conway
