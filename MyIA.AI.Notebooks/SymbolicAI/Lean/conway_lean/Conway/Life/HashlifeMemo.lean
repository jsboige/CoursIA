/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## HashlifeMemo — Hashlife memoise, prouve correct (Phase 3c)

Ce module implemente la couche de memoisation qui rend `hashlifeResult`
faisable sur les temoins communautaires piliers (OTCA 35K gen, UnitCell
4096 gen, Gemini 33M gen, CPU 1M gen). Sans memoisation, l'algorithme
recursif de Hashlife dans `Conway.Life.Hashlife` est `9^k` au pire cas
(chacun des 13 appels subnode engendre d'autres appels jusqu'au cas de
base niveau 2). Avec memoisation (l'astuce canonique de Gosper : cacher
les resultats des sous-arbres identiques), le nombre de sous-arbres
distincts explores sur des patterns realistes tombe a quelques millions,
dans le budget de `native_decide`.

### Conception

- **Cache** : `Std.HashMap (Nat x MacroCell) MacroCell`, cle =
  `(fuel, cell)`. Le fuel fait partie de la cle car `hashlifeResultAux`
  est reellement dependant du fuel (ses branches de repli dependent de
  l'epuisement du fuel), donc cacher par cellule seule serait incorrect
  sur des cellules mal formees.
- **`Hashable MacroCell`** : un hash structurel 64-bit du contenu
  (`MacroCell.contentHash`). `BEq` provient du `DecidableEq` derive
  (done loyal), ce dont les preuves de correction du cache ont besoin.
- **Correction fusionnee** : au lieu de definir la fonction memoisee puis
  la prouver correcte par une induction separee, chaque fonction renvoie
  un sous-type conditionnant la valeur, le cache final, une preuve que
  la valeur egale la reference non memoisee, et une preuve que le cache
  reste correct (`CacheOK`). Chaque appel recursif porte sa propre preuve,
  donc aucune induction globale sur l'arbre de recursion a 13 appels
  n'est requise. Les preuves sont de type `Prop` et completement effacees
  a l'execution.

### Notes d'implementation

- La branche bien formee `node`-de-`node`s deploie ses 16 petits-enfants
  (`a1..a4, b1..b4, c1..c4, d1..d4`) **sans** alias de motif (`c@(...)`) :
  les fvars alias sont syntaxiquement opaques a `rw`/`simp`, ce qui
  casserait le lemme d'unfold `hashlifeResultAux_succ_node` ci-dessous.
- Les branches mal formees dont le calcul de `level` est bloque (par ex.
  `1 + (1 + w1.level)` avec `w1` neutre) renvoient l'expression `ite`
  verbatim de la branche de repli de `hashlifeResultAux` pour que `rfl`
  ferme l'obligation de preuve par unfold definitionnel.
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `HashlifeMemo_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Std.Data.HashMap

namespace Conway
namespace Life

open MacroCell

/-! ## Hachage des `MacroCell`

Un hachage structurel du contenu. Deux cellules égales (selon le `DecidableEq`
dérivé, qui induit le `BEq` en portée) reçoivent des hachages égaux par
construction, donc `LawfulHashable` est automatique. -/

/-- Hachage structurel 64-bit du contenu d'une `MacroCell`. -/
def MacroCell.contentHash : MacroCell → UInt64
  | .leaf b => if b then 1 else 0
  | .node nw ne sw se =>
    mixHash 2 (mixHash (mixHash nw.contentHash ne.contentHash)
                       (mixHash sw.contentHash se.contentHash))

instance : Hashable MacroCell := ⟨MacroCell.contentHash⟩

/-! ## Le cache de mémoïsation et son invariant -/

/-- Cache de mémoïsation : `(fuel, cell) ↦ hashlifeResultAux fuel cell`. -/
abbrev MemoCache := Std.HashMap (Nat × MacroCell) MacroCell

/-- Le cache vide. -/
def MemoCache.empty : MemoCache := ∅

/-- Correction du cache : chaque liaison enregistre le vrai résultat
    Hashlife (non mémoïsé) pour sa clé. -/
def CacheOK (m : MemoCache) : Prop :=
  ∀ fuel c r, m[(fuel, c)]? = some r → r = hashlifeResultAux fuel c

theorem cacheOK_empty : CacheOK MemoCache.empty := by
  intro fuel c r h
  simp [MemoCache.empty] at h

/-- Insérer une liaison correcte préserve la correction du cache. -/
theorem CacheOK.insert {m : MemoCache} (hm : CacheOK m) {fuel : Nat}
    {c r : MacroCell} (hr : r = hashlifeResultAux fuel c) :
    CacheOK (m.insert (fuel, c) r) := by
  intro f d r' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  next heq =>
    have hkey : ((fuel, c) : Nat × MacroCell) = (f, d) := eq_of_beq heq
    injection hkey with h1 h2
    subst h1; subst h2
    injection h with h'
    exact h'.symm.trans hr
  next _ =>
    exact hm f d r' h

/-! ## Lemme d'unfold pour le bras bien formé

`hashlifeResultAux` utilise un alias de motif `c@(node ...)` dans sa
définition, dont la fvar alias bloque la réécriture syntaxique. Ce lemme
reformule le bras bien formé avec des motifs explicites et des `let`
expansés par zéta ; il se prouve par `rfl` (réduction iota + zéta).
Nommage des petits-enfants : `a* = nw.*`, `b* = ne.*`, `c* = sw.*`,
`d* = se.*`, chacun dans l'ordre `nw ne sw se`. -/

private theorem hashlifeResultAux_succ_node (fuel : Nat)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell) :
    hashlifeResultAux (fuel + 1)
      (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
            (node c1 c2 c3 c4) (node d1 d2 d3 d4)) =
    if (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
      step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                    (node c1 c2 c3 c4) (node d1 d2 d3 d4))
    else
      node
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a1 a2 a3 a4))
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node b1 b2 b3 b4))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node c1 c2 c3 c4))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))
          (hashlifeResultAux fuel (node d1 d2 d3 d4)))) := rfl

/-! ## La récursion mémoïsée, fusionnée avec sa preuve de correction

`hashlifeResultMemoAux fuel c m hm` renvoie `(value, cache')` muni des
preuves que `value = hashlifeResultAux fuel c` et `CacheOK cache'`.
Récursion structurelle sur `fuel`. -/

set_option maxHeartbeats 800000 in
/-- Contrepartie mémoïsée de `hashlifeResultAux`, portant son propre
    certificat de correction. Le cache est FILÉ de gauche à droite à
    travers les 13 appels récursifs du bras bien formé. -/
def hashlifeResultMemoAux : (fuel : Nat) → (c : MacroCell) →
    (m : MemoCache) → CacheOK m →
    {p : MacroCell × MemoCache //
      p.1 = hashlifeResultAux fuel c ∧ CacheOK p.2}
  | 0, _, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  | fuel + 1, node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
              (node c1 c2 c3 c4) (node d1 d2 d3 d4), m, hm =>
    match hlook : m[(fuel + 1,
        node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4))]? with
    | some r => ⟨(r, m), hm _ _ _ hlook, hm⟩
    | none =>
      if hl2 : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                     (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
        have hres : step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                                  (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            = hashlifeResultAux (fuel + 1)
                (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                      (node c1 c2 c3 c4) (node d1 d2 d3 d4)) := by
          rw [hashlifeResultAux_succ_node, if_pos hl2]
        ⟨(step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                        (node c1 c2 c3 c4) (node d1 d2 d3 d4)),
          m.insert (fuel + 1,
              node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                   (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            (step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                           (node c1 c2 c3 c4) (node d1 d2 d3 d4)))),
         hres, hm.insert hres⟩
      else
        -- The 9 sub-cells (n1..n9), then the 4 super-cells, threading
        -- the cache (and its `CacheOK` proof) through all 13 calls.
        let p1 := hashlifeResultMemoAux fuel (node a1 a2 a3 a4) m hm
        let p2 := hashlifeResultMemoAux fuel (node a2 b1 a4 b3) p1.1.2 p1.2.2
        let p3 := hashlifeResultMemoAux fuel (node b1 b2 b3 b4) p2.1.2 p2.2.2
        let p4 := hashlifeResultMemoAux fuel (node a3 a4 c1 c2) p3.1.2 p3.2.2
        let p5 := hashlifeResultMemoAux fuel (node a4 b3 c2 d1) p4.1.2 p4.2.2
        let p6 := hashlifeResultMemoAux fuel (node b3 b4 d1 d2) p5.1.2 p5.2.2
        let p7 := hashlifeResultMemoAux fuel (node c1 c2 c3 c4) p6.1.2 p6.2.2
        let p8 := hashlifeResultMemoAux fuel (node c2 d1 c4 d3) p7.1.2 p7.2.2
        let p9 := hashlifeResultMemoAux fuel (node d1 d2 d3 d4) p8.1.2 p8.2.2
        let o1 := hashlifeResultMemoAux fuel
          (node p1.1.1 p2.1.1 p4.1.1 p5.1.1) p9.1.2 p9.2.2
        let o2 := hashlifeResultMemoAux fuel
          (node p2.1.1 p3.1.1 p5.1.1 p6.1.1) o1.1.2 o1.2.2
        let o3 := hashlifeResultMemoAux fuel
          (node p4.1.1 p5.1.1 p7.1.1 p8.1.1) o2.1.2 o2.2.2
        let o4 := hashlifeResultMemoAux fuel
          (node p5.1.1 p6.1.1 p8.1.1 p9.1.1) o3.1.2 o3.2.2
        have hres : node o1.1.1 o2.1.1 o3.1.1 o4.1.1
            = hashlifeResultAux (fuel + 1)
                (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                      (node c1 c2 c3 c4) (node d1 d2 d3 d4)) := by
          rw [hashlifeResultAux_succ_node, if_neg hl2,
              o1.2.1, o2.2.1, o3.2.1, o4.2.1,
              p1.2.1, p2.2.1, p3.2.1, p4.2.1, p5.2.1,
              p6.2.1, p7.2.1, p8.2.1, p9.2.1]
        ⟨(node o1.1.1 o2.1.1 o3.1.1 o4.1.1,
          o4.1.2.insert (fuel + 1,
              node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                   (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            (node o1.1.1 o2.1.1 o3.1.1 o4.1.1)),
         hres, o4.2.2.insert hres⟩
  | fuel + 1, leaf b, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  | fuel + 1, node (leaf x) q2 q3 q4, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  -- Malformed cells whose `level` is a stuck term: return the verbatim
  -- fallback `ite` of `hashlifeResultAux` so that `rfl` closes the goal.
  | fuel + 1, node (node w1 w2 w3 w4) (leaf x) q3 q4, m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (leaf x) q3 q4).level == 0 then deadLeaf
      else emptyOfLevel ((node (node w1 w2 w3 w4) (leaf x) q3 q4).level - 1),
      m), rfl, hm⟩
  | fuel + 1, node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4, m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4).level == 0
      then deadLeaf
      else emptyOfLevel
        ((node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4).level - 1),
      m), rfl, hm⟩
  | fuel + 1, node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
              (node y1 y2 y3 y4) (leaf z), m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
              (node y1 y2 y3 y4) (leaf z)).level == 0
      then deadLeaf
      else emptyOfLevel
        ((node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
               (node y1 y2 y3 y4) (leaf z)).level - 1),
      m), rfl, hm⟩

/-- Hashlife mémoïsé depuis le cache vide : même résultat que
    `hashlifeResult c = hashlifeResultAux c.level c`. -/
def hashlifeResultRunMemo (c : MacroCell) : MacroCell :=
  (hashlifeResultMemoAux c.level c MemoCache.empty cacheOK_empty).1.1

/-- La version mémoïsée coïncide avec la référence non mémoïsée de Phase 3b.
    Immédiat depuis le certificat fusionné. -/
theorem hashlifeResultMemo_correct (c : MacroCell) :
    hashlifeResultRunMemo c = hashlifeResultAux c.level c :=
  (hashlifeResultMemoAux c.level c MemoCache.empty cacheOK_empty).2.1

/-! ## Évolution rapide mémoïsée

`evolveHashlifeFastMemoAux` reflète `evolveHashlifeFastAux`, en routant le
saut Hashlife via `hashlifeResultMemoAux` et en filant le cache à travers
les sauts successifs. Même style de certificat fusionné. -/

/-- Contrepartie mémoïsée d'`evolveHashlifeFastAux`, portant son propre
    certificat de correction. Récursion structurelle sur `fuel`. -/
def evolveHashlifeFastMemoAux : (fuel n : Nat) → (g : Grid) →
    (m : MemoCache) → CacheOK m →
    {p : Grid × MemoCache //
      p.1 = evolveHashlifeFastAux fuel n g ∧ CacheOK p.2}
  | 0, 0, g, m, hm => ⟨(g, m), rfl, hm⟩
  | fuel + 1, 0, g, m, hm => ⟨(g, m), rfl, hm⟩
  | 0, n + 1, g, m, hm => ⟨(g, m), rfl, hm⟩
  | fuel + 1, n + 1, g, m, hm =>
    have heq : evolveHashlifeFastAux (fuel + 1) (n + 1) g =
        if (gridToMacroCellWithOffset g).2.level >= 2
            && n + 1 >= jumpSize (gridToMacroCellWithOffset g).2.level then
          evolveHashlifeFastAux fuel
            (n + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
            ((hashlifeJump (gridToMacroCellWithOffset g).2).toGrid
              (jumpResultOff (gridToMacroCellWithOffset g).1
                (gridToMacroCellWithOffset g).2.level))
        else evolve (n + 1) g := rfl
    if hcond : (gridToMacroCellWithOffset g).2.level >= 2
        && n + 1 >= jumpSize (gridToMacroCellWithOffset g).2.level then
      let pc := padCenter2 (gridToMacroCellWithOffset g).2
      let pr := hashlifeResultMemoAux pc.level pc m hm
      let r2 := evolveHashlifeFastMemoAux fuel
        (n + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
        (pr.1.1.toGrid (jumpResultOff (gridToMacroCellWithOffset g).1
          (gridToMacroCellWithOffset g).2.level))
        pr.1.2 pr.2.2
      ⟨r2.1, by
        rw [heq, if_pos hcond, r2.2.1, pr.2.1]
        -- Residual: `hashlifeResultAux pc.level pc` vs
        -- `hashlifeJump (gridToMacroCellWithOffset g).2` — definitionally
        -- equal after unfolding `hashlifeJump`/`hashlifeResult` and the
        -- local `pc` let.
        rfl, r2.2.2⟩
    else
      ⟨(evolve (n + 1) g, m), by rw [heq, if_neg hcond], hm⟩

/-- Fait évoluer `g` de `n` générations via Hashlife mémoïsé. Mêmes
    sémantiques qu'`evolveHashlifeFast` (cf. le théorème-pont ci-dessous). -/
def evolveHashlifeFastMemo (n : Nat) (g : Grid) : Grid :=
  (evolveHashlifeFastMemoAux n n g MemoCache.empty cacheOK_empty).1.1

/-- Pont vers la Phase 3b : le chemin rapide mémoïsé coïncide avec le
    non mémoïsé. Immédiat depuis le certificat fusionné. -/
theorem evolveHashlifeFastMemo_eq_evolveHashlifeFast (n : Nat) (g : Grid) :
    evolveHashlifeFastMemo n g = evolveHashlifeFast n g :=
  (evolveHashlifeFastMemoAux n n g MemoCache.empty cacheOK_empty).2.1

/-! ## La grille vide est un point fixe

Requis par `Conway.Life.Pillars` tant que les motifs de piliers sont
encore des grilles vides placeholders (chargement RLE en attente). -/

theorem step_empty : step ([] : Grid) = [] := by
  simp [step, candidates, sortDedup]

theorem evolve_empty (n : Nat) : evolve n ([] : Grid) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve_succ, ih, step_empty]

theorem evolveHashlifeFast_empty (n : Nat) :
    evolveHashlifeFast n ([] : Grid) = [] := by
  cases n with
  | zero => rfl
  | succ n =>
    -- On `[]`, `gridFrame` gives level 0, the jump condition is false,
    -- and the fast path falls back to `evolve`.
    show evolveHashlifeFastAux (n + 1) (n + 1) ([] : Grid) = []
    rw [show evolveHashlifeFastAux (n + 1) (n + 1) ([] : Grid)
        = evolve (n + 1) ([] : Grid) from rfl]
    exact evolve_empty (n + 1)

theorem evolveHashlifeFastMemo_empty (n : Nat) :
    evolveHashlifeFastMemo n ([] : Grid) = [] := by
  rw [evolveHashlifeFastMemo_eq_evolveHashlifeFast]
  exact evolveHashlifeFast_empty n

/-! ## Vérifications de cohérence

Les fonctions mémoïsées doivent coïncider avec leurs références sur les
motifs canoniques (ce sont des évaluations compilées, qui complètent les
théorèmes vérifiés par le noyau ci-dessus). -/

#eval hashlifeResultRunMemo (gridToMacroCell glider)
        == hashlifeResult (gridToMacroCell glider)          -- expect true
#eval evolveHashlifeFastMemo 8 glider == evolveHashlifeFast 8 glider  -- true
#eval evolveHashlifeFastMemo 4 blinker_h == evolve 4 blinker_h        -- true
#eval evolveHashlifeFastMemo 3 toad == evolve 3 toad                  -- true

end Life
end Conway
