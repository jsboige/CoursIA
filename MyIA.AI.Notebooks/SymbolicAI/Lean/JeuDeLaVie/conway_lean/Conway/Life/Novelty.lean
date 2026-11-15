/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Borne de nouveaute pour la classe des oscillateurs

Axe EFFICACITE de hashlife (#11162) : la quantite qui fait tenir Golly n'est
pas le confinement (`jumpCaptured`, #11007 — la licence) mais la NOVEAUTE,
c'est-a-dire la stabilite de l'ensemble des etats visites le long de la
trajectoire. Ce module formalise l'invariant de stabilite pour la classe
la plus simple : les oscillateurs.

**Resultat.** Si `evolve p g = g` avec `p > 0` (g est un point fixe de la
p-ieme iteratee — la periode au sens de `isOscillator`), alors la trajectoire
complete `t |-> evolve t g` ne visite que des etats deja apparus dans les `p`
premiers instants (`novelty_bound_of_period`), donc il existe un `Finset` de
cardinal au plus `p` contenant toute la trajectoire
(`trajectory_states_le_of_period`). La nouveaute au niveau grille est bornee
par `p`, independamment de l'horizon : c'est le pendant quantitatif du
constat empirique « Golly est rapide sur les oscillateurs ».

**Portee et limite, documentees.** Deux niveaux de borne sont livres :
GRILLE (`trajectory_states_le_of_period` : au plus `p` etats distincts) et
NOEUDS (`nodes_novelty_bound_of_period` : au plus `p * nodesBound k`
sous-arbres distincts de la trajectoire cadree au niveau `k`). La seconde
est la quantite operationnelle de hashlife — le taux de hit du cache de
memoisation, avec partage de sous-arbres : l'induction sur la structure de
`MacroCell` que ce module declarait hors de portee lors de la livraison
initiale (#11162, ou l'alternative « borne ou diagnostic » avait retenu le
diagnostic) est desormais le contenu de la section dediee ci-dessous. Reste
ouvert, et pour de bon : la caracterisation « quels motifs ont une
nouveaute persistante » est indecidable a la limite (Life est
Turing-complet : une machine de Turing programmee encode la production
infinie de motifs neufs) — les patterns pathologiques (MT, #6724) sont les
temoins de ce plafond.

Ce module est entierement prouve (aucun `sorry`, aucun axiome natif).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Novelty_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de theoreme et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

/-! ## Multiples de la periode

Le lemme d'iteration `evolve_add` (Foundation, P4.4) dit que `evolve` est un
morphisme de l'addition : composer `q` blocs de periode `p` ramene a l'etat
initial. C'est la seule arithmetique dont la borne a besoin. -/

/-- La periode se re-applique en tout point de la trajectoire : si
`evolve p g = g`, alors `evolve p (evolve m g) = evolve m g` pour tout `m`.
C'est la commutativite de l'addition des iteratees qui le donne :
`p + m = m + p`, et le bloc `p` cote droit se reduit par `hp`. -/
theorem evolve_period_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (m : Nat) :
    evolve p (evolve m g) = evolve m g := by
  rw [← evolve_add, Nat.add_comm, evolve_add, hp]

/-- Tout multiple de la periode laisse tout point de la trajectoire invariant :
si `evolve p g = g`, alors `evolve (p * q) (evolve m g) = evolve m g` pour
tous `q`, `m` — le bloc `p * q` se decompose en `q` blocs `p`, chacun se
reduisant par `evolve_period_shift`. -/
theorem evolve_mul_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (q m : Nat) :
    evolve (p * q) (evolve m g) = evolve m g := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, evolve_add, evolve_period_shift g p hp m, ih]

/-- Tout multiple de la periode ramene a l'etat initial : si `evolve p g = g`,
alors `evolve (p * q) g = g` pour tout `q` (cas `m = 0` du shift). -/
theorem evolve_mul_of_period (g : Grid) (p : Nat) (hp : evolve p g = g) (q : Nat) :
    evolve (p * q) g = g := by
  simpa using evolve_mul_shift g p hp q 0

/-! ## Borne de nouveaute (niveau grille)

L'invariant de stabilite : apres `p` instants, la trajectoire ne produit plus
d'etat neuf. Tout ce qui est visite a l'instant `t` est deja apparu a un
instant `r < p`. -/

/-- **Borne de nouveaute pour un oscillateur** : si `evolve p g = g` avec
`p > 0`, alors tout etat visite a un instant quelconque `t` est deja apparu
dans les `p` premiers instants — la trajectoire ne produit jamais d'etat
neuf apres la periode. Le temoin est le reste `t % p`. -/
theorem novelty_bound_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) (t : Nat) :
    ∃ r, r < p ∧ evolve t g = evolve r g := by
  obtain ⟨r, hr, hdecomp⟩ : ∃ r, r < p ∧ t = p * (t / p) + r :=
    ⟨t % p, Nat.mod_lt t hp0, (Nat.div_add_mod t p).symm⟩
  refine ⟨r, hr, ?_⟩
  rw [hdecomp, evolve_add, evolve_mul_shift g p hp (t / p) r]

/-- **Cardinal de la trajectoire** : la trajectoire complete d'un oscillateur
de periode `p` tient dans un `Finset` de cardinal au plus `p`. C'est la
formulation ensembliste de « au plus `p` etats distincts », le pendant
formel du constat empirique « Golly est rapide sur les oscillateurs » :
le taux de hit de la memoisation ne peut pas se degrader avec l'horizon. -/
theorem trajectory_states_le_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) :
    ∃ s : Finset Grid, s.card ≤ p ∧ ∀ t : Nat, evolve t g ∈ s := by
  refine ⟨(Finset.range p).image (fun r => evolve r g),
    Finset.card_image_le.trans_eq (Finset.card_range p), fun t => ?_⟩
  obtain ⟨r, hr, heq⟩ := novelty_bound_of_period g p hp0 hp t
  exact Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, heq.symm⟩

/-! ## Application : le blinker

Le blinker (periode 2, `blinker_period_two` dans `Conway.Life`) visite au
plus 2 etats — l'horizontal et le vertical — quel que soit l'horizon. -/

/-- La trajectoire du blinker horizontal (periode 2) tient dans un `Finset`
de cardinal au plus 2 : deux etats distincts, jamais plus, quel que soit
l'horizon de simulation. -/
theorem blinker_h_trajectory_states_le :
    ∃ s : Finset Grid, s.card ≤ 2 ∧ ∀ t : Nat, evolve t blinker_h ∈ s :=
  trajectory_states_le_of_period _ 2 (by norm_num) (by decide)

open Conway.Life.MacroCell

/-! ## Borne de nouveaute au niveau noeuds (macrocells)

Le diagnostic du preambule est ici leve : l'induction sur la structure de
`MacroCell` y etait declaree hors de portee, elle est le contenu de cette
section. La nouveaute operationnelle de hashlife se mesure au niveau des
NOEUDS du quadtree — les cles du cache de memoisation, avec partage de
sous-arbres. La trajectoire d'un oscillateur, cadree au niveau `k`, ne
visite qu'un nombre borne de sous-arbres distincts, de majorant
`p * nodesBound k` independant de l'horizon : le pendant quantitatif, au
niveau du cache, de la borne grille ci-dessus. -/

/-- Compte les noeuds d'un quadtree parfait de profondeur `k` : la somme
geometrique `1 + 4 + 16 + ... + 4^k = (4^(k+1) - 1) / 3`, definie par sa
recurrence — la forme manipulable en preuve. -/
def nodesBound : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + 4 * nodesBound k

/-- Profondeur structurelle d'une macrocell : la hauteur de l'arbre,
mesuree sur la plus profonde des quatre sous-cellules. Contrairement a
`level` (qui ne regarde que le quadrant nord-ouest), elle ne suppose pas la
bonne formation : c'est le parametre naturel de la borne de cardinal
ci-dessous, valide pour toute macrocell, equilibree ou non. -/
def depth : MacroCell → Nat
  | leaf _ => 0
  | node nw ne sw se =>
      1 + max (depth nw) (max (depth ne) (max (depth sw) (depth se)))

/-- Tous les sous-arbres d'une macrocell, elle-meme incluse. Chaque element
est un noeud du quadtree — une cle potentielle du cache de memoisation de
hashlife. La nouveaute niveau noeuds d'un etat, c'est le cardinal de cet
ensemble. -/
def allSubtrees (c : MacroCell) : Finset MacroCell :=
  match c with
  | leaf _ => {c}
  | node nw ne sw se =>
      insert c (allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw ∪ allSubtrees se)

/-- `nodesBound` croit avec la profondeur. -/
theorem nodesBound_mono {k m : Nat} (h : k ≤ m) : nodesBound k ≤ nodesBound m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = k + n := ⟨m - k, by omega⟩
  clear h
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    calc nodesBound k ≤ nodesBound (k + n) := ih
      _ ≤ 1 + 4 * nodesBound (k + n) := by omega
      _ = nodesBound ((k + n) + 1) := rfl.symm
      _ = nodesBound (k + (n + 1)) := by rw [Nat.add_assoc]

/-- Une macrocell de profondeur `d` porte au plus `nodesBound d` sous-arbres
distincts : l'induction sur la structure de `MacroCell` annoncee en
preambule. L'union peut dedoubler (sous-arbres partages entre quadrants),
jamais grossir — la borne vaut meme pour les arbres non equilibrés. -/
theorem allSubtrees_card (c : MacroCell) : (allSubtrees c).card ≤ nodesBound (depth c) := by
  induction c with
  | leaf b =>
    simp only [allSubtrees, depth, nodesBound]
    simp
  | node nw ne sw se ihnw ihne ihsw ihse =>
    simp only [allSubtrees, depth]
    set M := max (depth nw) (max (depth ne) (max (depth sw) (depth se))) with hM
    have h1 := Finset.card_insert_le (a := node nw ne sw se)
      (s := allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw ∪ allSubtrees se)
    have e1 := Finset.card_union_le (allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw)
      (allSubtrees se)
    have e2 := Finset.card_union_le (allSubtrees nw ∪ allSubtrees ne) (allSubtrees sw)
    have e3 := Finset.card_union_le (allSubtrees nw) (allSubtrees ne)
    have hn : (allSubtrees nw).card ≤ nodesBound M := ihnw.trans (nodesBound_mono (by omega))
    have he : (allSubtrees ne).card ≤ nodesBound M := ihne.trans (nodesBound_mono (by omega))
    have hs : (allSubtrees sw).card ≤ nodesBound M := ihsw.trans (nodesBound_mono (by omega))
    have hd : (allSubtrees se).card ≤ nodesBound M := ihse.trans (nodesBound_mono (by omega))
    have hstep : nodesBound (1 + M) = 1 + 4 * nodesBound M := by
      rw [Nat.add_comm]; rfl
    omega

/-- Le cadrage de niveau `k` d'une grille est un quadtree exactement de
profondeur `k` : `buildFromGrid` construit l'arbre parfait couvrant le
carre, tous les quadrants presents jusqu'aux feuilles. -/
theorem depth_buildFromGrid (g : Grid) (lvl : Nat) (r0 c0 : Int) :
    depth (buildFromGrid g r0 c0 lvl) = lvl := by
  induction lvl generalizing r0 c0 with
  | zero => rfl
  | succ n ih =>
    simp only [buildFromGrid, depth]
    simp only [ih]
    omega

/-- **Borne de nouveaute au niveau noeuds pour un oscillateur** : si
`evolve p g = g` avec `p > 0`, alors la trajectoire complete, cadree au
niveau `k` en `(r0, c0)`, ne visite qu'un nombre borne de noeuds distincts —
au plus `p * nodesBound k` sous-arbres, un majorant independant de
l'horizon. Chaque instant de la trajectoire reduit a l'un des `p` premiers
instants (`novelty_bound_of_period`), et chacun de ces instants contribue
au plus `nodesBound k` noeuds (`allSubtrees_card`, sur un cadrage de
profondeur exactement `k` par `depth_buildFromGrid`). C'est le pendant
quantitatif, au niveau du cache de hashlife, de la borne grille : le taux
de hit de la memoisation ne peut pas se degrader avec l'horizon, sur la
classe des oscillateurs. -/
theorem nodes_novelty_bound_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) (k : Nat) (r0 c0 : Int) :
    ∃ s : Finset MacroCell, s.card ≤ p * nodesBound k ∧
      ∀ t : Nat, ∀ x ∈ allSubtrees (buildFromGrid (evolve t g) r0 c0 k), x ∈ s := by
  refine ⟨(Finset.range p).biUnion
    fun r => allSubtrees (buildFromGrid (evolve r g) r0 c0 k), ?_, ?_⟩
  · calc ((Finset.range p).biUnion
          fun r => allSubtrees (buildFromGrid (evolve r g) r0 c0 k)).card
        ≤ ∑ r ∈ Finset.range p,
            (allSubtrees (buildFromGrid (evolve r g) r0 c0 k)).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ Finset.range p, nodesBound k := Finset.sum_le_sum fun r _ => by
          have h := allSubtrees_card (buildFromGrid (evolve r g) r0 c0 k)
          rw [depth_buildFromGrid] at h
          exact h
      _ = p * nodesBound k := by rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
  · intro t x hx
    obtain ⟨r, hr, heq⟩ := novelty_bound_of_period g p hp0 hp t
    rw [heq] at hx
    exact Finset.mem_biUnion.2 ⟨r, Finset.mem_range.2 hr, hx⟩

/-! ### Application : le blinker, niveau noeuds -/

/-- Le blinker (periode 2), cadre au niveau `k` : au plus
`2 * nodesBound k` noeuds distincts visites sur toute la trajectoire, quel
que soit l'horizon. -/
theorem blinker_h_nodes_novelty_bound (k : Nat) (r0 c0 : Int) :
    ∃ s : Finset MacroCell, s.card ≤ 2 * nodesBound k ∧
      ∀ t : Nat, ∀ x ∈ allSubtrees (buildFromGrid (evolve t blinker_h) r0 c0 k), x ∈ s :=
  nodes_novelty_bound_of_period _ 2 (by norm_num) (by decide) k r0 c0

/-- Temoin numerique exact : le cadre de niveau 2 du blinker porte
exactement 6 noeuds distincts — la racine, trois quadrants distincts (les
deux quadrants Est, vides, s'identifient) et les deux feuilles — pour une
borne generale de `nodesBound 2 = 21` sur un seul etat. -/
theorem blinker_h_level2_nodes_card :
    (allSubtrees (buildFromGrid blinker_h (-1) (-1) 2)).card = 6 := by
  decide

end Life
end Conway
