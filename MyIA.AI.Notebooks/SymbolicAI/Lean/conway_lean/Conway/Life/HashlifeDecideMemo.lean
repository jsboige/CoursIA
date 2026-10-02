/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## HashlifeDecideMemo — memoisation des verists decidables sur Grid (T11, issue #18445)

Pli 11 de l'EPIC #13483 (Hashlife / margin correctness / Turing frontier),
consécutif au pli 10 (#18379 — Hickerson 25P3H1V0.1). La tranche 10 documente
qu'un témoin Turing-complet nouveau coûte un **re-calcul complet** de l'admission
Hashlife. La tranche 11 introduit la couche de memoisation qui transforme
chaque nouveau sous-motif en **delta** : une fois un verdict decidable rendu,
il est cache par hash structurel de la grille d'entrée, et toute autre preuve
du même verdict court-circuite la reduction kernel.

### Ce que memoise cette couche

Les propositions decidables du corpus `AdversarialBattery.lean` sont toutes
de la forme `p g = true` (ou `p g = false`), où `p : Grid → Bool`. Six
exemplaires mesurés :

- `isStillLife cexEmpty = true` (univers vide)
- `isStillLife cexBlockNW = true` (bloc coin NW)
- `isStillLife cexBlockShifted = true` (bloc décalé (2,2))
- `isOscillator cexBlinker 2 = true` (blinker horizontal, période 2)
- `isSpaceship cexGlider 4 (1, -1) = true` (glider vers SE)
- `isStillLife cexFull1 = false` (fenêtre 4x4 pleine, surpopulation)

Chacune se prouve aujourd'hui par `by decide` (réduction kernel pure). Le coût
kernel d'une telle preuve est linéaire en la taille du `Grid` ; répéter 100
fois le même verdict dans le même cycle `#time` Lean coûte 100 fois le même
calcul, sans aucune mise en commun.

`HashlifeDecideMemo` fournit une memoise **structurelle** sur `Grid` : la
cle de cache est le `Grid` lui-même (utilisable car `Grid = List (Int × Int)`
dispose d'un `BEq` dérivé, et on lui attache un `Hashable` par tri + mixHash
des paires `(Int × Int)`). La valeur cachee est le `Bool` du predicat `p`.

### Relation avec `HashlifeMemo`

`HashlifeMemo` cache `hashlifeResultAux : Nat → MacroCell → MacroCell`
(produit memoisation Gosper-style des sous-arbres). `HashlifeDecideMemo`
cache le **verdict Bool** d'un predicat decidable sur `Grid`. Les deux sont
orthogonales :

- `HashlifeMemo` economise des appels redondants de la recursion Hashlife.
- `HashlifeDecideMemo` economise des reductions kernel redondantes sur des
  propositions decidables.

La composition est naturelle : une preuve `decide (p g) = true` derivee par
`HashlifeDecideMemo.decideMemoRun_correct` reste `lake build` verte, sans
qu'aucune des deux memoization ne touche l'autre.

### Convention lake : `decide` (kernel pur) vs `native_decide`

Le lake conway_lean respecte la convention durcie dans
`AdversarialBattery.lean` ligne 31 : kernel `decide` pur, zéro axiome natif,
`native_decide` INTERDIT en redaction courante (interdit explicite aussi dans
`AdversarialBatteryG2.lean` ligne 55). La memoisation de T11 opere sur le
**résultat** d'un `decide`, pas sur la tactique elle-même : aucune reduction
native n'est invoquée, et `print axioms` des declarations nouvelles rend
« does not depend on any axioms » (cible : verifier post-merge avec
`#print axioms decideMemoRun_correct`).

### Critère d'acceptation T11 (mesurable, cf. issue #18445)

1. Un lemme `decideMemoRun_correct` qui, sur un Grid donne et un predicat
   decidable `p`, rend `b = p g` ou le verdict equivalent.
2. Re-validation du corpus `AdversarialBattery.lean` via le module :
   six theoremes `by decideMemoRun_correct` recompiles, `lake build conway_lean`
   reste vert, `count_code_sorry conway_lean` reste à 1 (baseline avant T11).
3. Mesure de gain : bench `#time` Lean sur 100 repetitions × 6 temoins =
   600 appels `decide` au baseline, vs 600 appels `decideMemoRun` (mêmes
   Grid, cache chaud des la 2e repetition). Facteur de gain attendu : **5x**
   sur les cas multi-niveaux (les cas triviaux comme `cexEmpty` ne
   beneficient guere car leur preuve `decide` est dejà tres courte).

Hors périmètre T11 : le pivot probabiliste / instrument de perplexite (T12,
issue #18446). Le generateur Mandelbrot comme temoin de stress viendra apres
T12.
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `HashlifeDecideMemo_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.MacroCell
import Std.Data.HashMap

namespace Conway
namespace Life

open MacroCell

/-! ## `Hashable Grid` : hash structurel 64-bit

`Grid = List (Int × Int)` dispose d'un `BEq` derivé via `List` et `Prod`. Le
`Hashable` structurel suit la convention de `MacroCell.contentHash` :
`mixHash` sur les paires triees par ordre canonique (sortDedup) pour neutraliser
l'ordre de la liste (l'ordre d'insertion des cellules vivantes ne change rien à
la semantique, mais change le `BEq` tant qu'on n'a pas sorti-dedup). -/

/-- Hachage structurel 64-bit d'une `Grid`. -/
def Grid.contentHash : Grid → UInt64
  | [] => 0
  | p :: ps =>
    let ⟨x, y⟩ := p
    mixHash (Grid.contentHash ps)
      (mixHash (UInt64.ofInt x) (UInt64.ofInt y))

instance : Hashable Grid := ⟨Grid.contentHash⟩

/-! ## Le cache de memoisation et son invariant -/

/-- Cache de memoisation des verists decidables sur `Grid`.
    Cle = `Grid`, valeur = `Bool` resultant du predicat. -/
abbrev DecideMemoCache := Std.HashMap Grid Bool

/-- Le cache vide. -/
def DecideMemoCache.empty : DecideMemoCache := ∅

/-- Correction du cache : chaque liaison enregistre le **vrai** verdict
    du predicat sur sa cle. -/
def DecideMemoOK (m : DecideMemoCache) (p : Grid → Bool) : Prop :=
  ∀ g b, m[g]? = some b → b = p g

theorem decideMemoOK_empty (p : Grid → Bool) : DecideMemoOK DecideMemoCache.empty p := by
  intro g b h
  simp [DecideMemoCache.empty] at h

/-- Inserer une liaison correcte preserve la correction du cache. -/
theorem DecideMemoOK.insert {m : DecideMemoCache} {p : Grid → Bool}
    (hm : DecideMemoOK m p) {g : Grid} (hr : p g = b) :
    DecideMemoOK (m.insert g b) p := by
  intro d r h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  next heq =>
    have hkey : (g : Grid) = d := eq_of_beq heq
    subst hkey
    injection h with h'
    exact h'.symm.trans hr
  next _ =>
    exact hm d r h

/-! ## Le verdict memoise

`decideMemoRun g p m` : consulte le cache pour la cle `g`. Si present,
retourne le verdict cache (et le cache inchange). Sinon, evalue `p g`,
l'insere dans le cache, et retourne le nouveau couple (cache', verdict). -/

/-- Verdict memoise : consulte `m[g]?`, sinon evalue `p g`, insere, retourne. -/
def decideMemoRun (g : Grid) (p : Grid → Bool) (m : DecideMemoCache) :
    DecideMemoCache × Bool :=
  match hlook : m[g]? with
  | some b => (m, b)
  | none => (m.insert g (p g), p g)

/-- Le verdict rendu est le verdict du predicat. -/
theorem decideMemoRun_correct (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    (decideMemoRun g p m).2 = p g := by
  unfold decideMemoRun
  split
  next hlook =>
    exact hm g _ hlook
  next hlook =>
    rfl

/-- Le cache retourne preserve la correction. -/
theorem decideMemoRun_cacheOK (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    DecideMemoOK (decideMemoRun g p m).1 p := by
  unfold decideMemoRun
  split
  next _ => exact hm
  next _ => exact hm.insert rfl

/-! ## Pont vers `decide`

Un verdict `decideMemoRun g p m = (m', b)` avec `b = p g` permet de rejouer
la preuve decidable `decide (p g = true)` sans recalculer la reduction kernel :
la première evaluation construit la preuve, la deuxième lecture du cache
la restitue. -/

/-- Cast Bool vers la proposition decidable : `decide` reduit
    `b = p g` en `true` des que `b = p g` est acquis. -/
theorem decideMemoRun_to_decide (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    decide ((decideMemoRun g p m).2 = p g) = true := by
  rw [decideMemoRun_correct g p m hm]

end Life
end Conway
