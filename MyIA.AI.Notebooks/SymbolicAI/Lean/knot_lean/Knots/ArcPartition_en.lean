/-
  Slice 3 (#18397) — Extraction of the `arcPartition` block (and its direct
  tools up to `alexanderRow_sum_zero`) from `Knots/Conway.lean`.
  Verbatim move: no lemma is touched, only the framing changes (minimal
  imports, slice header, `Knots` namespace preserved). The theorem
  `alexanderRow_sum_zero` is included because it consumes `arcPartition`;
  slices 4+ (polynomial computation `alexander_unknot`, `alexander_trefoil`,
  `det_two_aux`/`det_three_aux`) remain in Conway.lean. The FR sibling
  `Knots/ArcPartition.lean` reproduces the body verbatim, translated
  docstrings and comments — i18n convention `code-style.md` (byte-identity
  on the rest).

  Origin: Conway.lean l.65-979 (915 lines), reference commit origin/main
  71514d576. No reformatting, no tactic modified. -/

import Knots.Basic

import Mathlib.Algebra.Polynomial.Basic

namespace Knots

def mergePair (P : List (List Nat)) (x y : Nat) : List (List Nat) :=
  let keep := P.filter (fun C => !C.contains x && !C.contains y)
  let hit := P.filter (fun C => C.contains x || C.contains y)
  keep ++ [hit.flatten.eraseDups]

/-- Les arcs d'un diagramme : partition des étiquettes d'arêtes par la
fermeture des paires de passage-dessus (e2 ~ e4 en chaque croisement). -/
def arcPartition (d : KnotDiagram) : List (List Nat) :=
  let singles := (List.range d.numEdges).map (fun i => [i + 1])
  let pairs := d.crossings.map (fun c => (c.e2, c.e4))
  pairs.foldl (fun P p => mergePair P p.1 p.2) singles

/-- La fusion de classes est symétrique : fusionner selon `(x, y)` ou `(y, x)`
    produit la même partition. Première brique de l'invariance R3
    (issue #16650) : la chirurgie réécrit les paires de passage-dessus du
    triangle avec des orientations qui diffèrent d'un diagramme à l'autre,
    et l'argument de réindexation exige que l'orientation d'une paire ne
    change pas la partition obtenue. -/
theorem mergePair_symm (P : List (List Nat)) (x y : Nat) :
    mergePair P x y = mergePair P y x := by
  simp [mergePair, Bool.and_comm, Bool.or_comm]

/-- La découpe en `take`/cons/`drop` restitue la liste : lecture « liste
    pure » du voisinage de l'indice `i`, prouvée par induction sur la liste. -/
theorem take_cons_drop_eq {α : Type _} (l : List α) (i : Nat)
    (hi : i < l.length) :
    l.take i ++ [l.get ⟨i, hi⟩] ++ l.drop (i + 1) = l := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a as ih =>
    rcases i with _ | n
    · have hget0 : (a :: as).get ⟨0, hi⟩ = a := rfl
      rw [hget0, List.take_zero, List.nil_append]
      simp [List.drop_succ_cons]
    · have hn : n < as.length := by simpa using hi
      have hget : (a :: as).get ⟨n + 1, hi⟩ = as.get ⟨n, hn⟩ := rfl
      rw [List.take_succ_cons, List.drop_succ_cons, hget, List.cons_append]
      exact congrArg (fun t => a :: t) (ih n hn)

/-- Le repli `arcPartition` est insensible à l'orientation d'une paire
    isolée : renverser la paire en position `i` ne change pas la partition
    produite. C'est la traduction au niveau du repli de `mergePair_symm` —
    la chirurgie R3 connexe réécrit les paires du triangle avec des
    orientations qui diffèrent d'un diagramme à l'autre, et ce lemme absorbe
    ces différences (issue #16650, deuxième brique). -/
theorem foldl_mergePair_swap (pairs : List (Nat × Nat)) (i : Nat)
    (hi : i < pairs.length) (P₀ : List (List Nat)) :
    (pairs.take i ++ [(pairs.get ⟨i, hi⟩).swap] ++ pairs.drop (i + 1)).foldl
        (fun P p => mergePair P p.1 p.2) P₀
      = pairs.foldl (fun P p => mergePair P p.1 p.2) P₀ := by
  have hmid : ∀ (m : Nat × Nat),
      (pairs.take i ++ [m] ++ pairs.drop (i + 1)).foldl
          (fun P p => mergePair P p.1 p.2) P₀
        = (pairs.take i ++ [m.swap] ++ pairs.drop (i + 1)).foldl
            (fun P p => mergePair P p.1 p.2) P₀ := by
    intro m
    obtain ⟨a, b⟩ := m
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
      Prod.swap_prod_mk]
    rw [mergePair_symm]
  rw [← hmid, take_cons_drop_eq pairs i hi]

/-! #### Le fait de Fox : la paire de dessus partage une classe d'arcs

La docstring d'`alexanderEntry` avance que « chaque ligne somme à zéro ».
Ce n'est pas une propriété de la ligne seule : c'est la conséquence d'un fait
structurel de `arcPartition` — en chaque croisement, les deux étiquettes de
dessus `e2` et `e4` appartiennent à une même classe. `mergePair` fusionne
précisément cette paire, et le repli ne fait ensuite qu'unir des classes,
jamais en scinder une : c'est la traduction combinatoire de la relation de
Wirtinger. Les lemmes qui suivent l'établissent pour tout diagramme dont les
étiquettes d'arêtes vivent dans la plage `1..numEdges` (cf `EdgesInRange`).
-/

/-- Deux étiquettes d'arêtes partagent une classe de la partition `P`. -/
def SameClass (P : List (List Nat)) (x y : Nat) : Prop :=
  ∃ C ∈ P, x ∈ C ∧ y ∈ C

/-- L'étiquette `z` est portée par au moins une classe de `P`. -/
def Covered (P : List (List Nat)) (z : Nat) : Prop := ∃ C ∈ P, z ∈ C

/-- Étape du repli de `arcPartition` : fusionner la paire de dessus. -/
def mergeStep (P : List (List Nat)) (p : Nat × Nat) : List (List Nat) :=
  mergePair P p.1 p.2

/-- Forme dépliée de `mergePair` : les classes intactes, puis la classe
fusionnée. -/
lemma mergePair_eq (P : List (List Nat)) (x y : Nat) :
    mergePair P x y =
      (P.filter (fun C => !C.contains x && !C.contains y)) ++
      [(P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups] := rfl

/-- La classe fusionnée porte toute étiquette d'une classe du filtre `hit`. -/
lemma mem_merged {P : List (List Nat)} {C : List Nat} {z x y : Nat}
    (hC : C ∈ P) (hz : z ∈ C) (hxy : (C.contains x || C.contains y) = true) :
    z ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  rw [List.mem_eraseDups, List.mem_flatten]
  exact ⟨C, List.mem_filter.mpr ⟨hC, hxy⟩, hz⟩

/-- Une classe qui ne porte ni `x` ni `y` reste intacte dans `keep`. -/
lemma keep_filter {P : List (List Nat)} {C : List Nat} {x y : Nat}
    (hC : C ∈ P) (hmem : ¬(C.contains x || C.contains y) = true) :
    C ∈ (P.filter (fun C => !C.contains x && !C.contains y)) := by
  refine List.mem_filter.mpr ⟨hC, ?_⟩
  simpa using hmem

/-- `mergePair` ne fait pas disparaître une étiquette déjà couverte. -/
lemma covered_mergePair {P : List (List Nat)} {x y z : Nat} (h : Covered P z) :
    Covered (mergePair P x y) z := by
  obtain ⟨C, hC, hz⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC hz hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, hz⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` ne scinde aucune classe : deux étiquettes qui partageaient une
classe continuent de la partager. -/
lemma sameClass_mergePair {P : List (List Nat)} {x y a b : Nat}
    (h : SameClass P a b) : SameClass (mergePair P x y) a b := by
  obtain ⟨C, hC, ha, hb⟩ := h
  by_cases hmem : (C.contains x || C.contains y) = true
  · refine ⟨_, ?_, mem_merged hC ha hmem, mem_merged hC hb hmem⟩
    rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl
  · refine ⟨C, ?_, ha, hb⟩
    rw [mergePair_eq, List.mem_append]; left
    exact keep_filter hC hmem

/-- `mergePair` réunit effectivement `x` et `y` dans une même classe, dès lors
que l'un et l'autre sont couverts (le filtre `hit` n'est alors pas vide et la
classe fusionnée les porte tous les deux). -/
lemma sameClass_mergePair_self {P : List (List Nat)} {x y : Nat}
    (hx : Covered P x) (hy : Covered P y) : SameClass (mergePair P x y) x y := by
  obtain ⟨Cx, hCx, hx'⟩ := hx
  obtain ⟨Cy, hCy, hy'⟩ := hy
  have hmx : (Cx.contains x || Cx.contains y) = true := by
    rw [Bool.or_eq_true]; left; exact List.contains_iff_mem.mpr hx'
  have hmy : (Cy.contains x || Cy.contains y) = true := by
    rw [Bool.or_eq_true]; right; exact List.contains_iff_mem.mpr hy'
  refine ⟨_, ?_, mem_merged hCx hx' hmx, mem_merged hCy hy' hmy⟩
  rw [mergePair_eq, List.mem_append]; right; exact List.mem_singleton.mpr rfl

/-- Le repli préserve l'appartenance partagée. -/
lemma sameClass_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {a b : Nat}
    (h : SameClass P a b) : SameClass (pairs.foldl mergeStep P) a b := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (sameClass_mergePair h)

/-- Toute paire rencontrée pendant le repli finit dans une même classe. -/
lemma sameClass_foldl_of_mem {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hcover : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ∀ q ∈ pairs, SameClass (pairs.foldl mergeStep P) q.1 q.2 := by
  induction pairs generalizing P with
  | nil => intro q hq; simp at hq
  | cons p ps ih =>
      intro q hq
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hq with rfl | hqs
      · exact sameClass_foldl (sameClass_mergePair_self
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).1
          (hcover q (List.mem_cons.mpr (Or.inl rfl))).2)
      · exact ih (P := mergeStep P p)
          (fun r hr => ⟨covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).1,
                        covered_mergePair (hcover r (List.mem_cons.mpr (Or.inr hr))).2⟩)
          q hqs

/-! ### Commutation de deux fusions — la reformulation `SameClass`

Le repli de `arcPartition` applique les paires de dessus dans l'ordre des
croisements. `foldl_mergePair_swap` (ci-dessus) montre qu'un échange
adjacent de paires préserve la liste à un `take`/`drop` près — ce n'est pas
l'égalité des listes : l'ordre d'apparition dans la classe fusionnée
diffère (contre-exemple `P = [[1,3],[2],[4]]`, paires `(1,2)` puis `(3,4)` :
la classe géante est `[4,1,3,2]` dans un ordre et `[2,1,3,4]` dans l'autre
— issue #16650). Ce qui commute exactement, c'est la relation d'équivalence
sous-jacente : deux étiquettes partagent une classe finale dans un ordre
d'application ssi elles en partagent une dans l'autre. Le théorème
`mergePair_mergePair_comm_equiv` l'établit via une caractérisation complète
de `SameClass` après deux fusions (`sameClass_two_merges_iff`), dont la
forme est invariante par échange des deux groupes.
-/

/-- `z` vit dans une classe de `P` qui porte `x` ou `y` : c'est exactement
la condition d'atterrir dans la classe fusionnée de `mergePair P x y`. -/
def Touches (P : List (List Nat)) (x y z : Nat) : Prop :=
  ∃ C ∈ P, z ∈ C ∧ ((C.contains x || C.contains y) = true)

/-- Une même classe de `P` porte une étiquette du groupe `{a, b}` et une du
groupe `{c, d}` : les deux fusions produisent alors une classe unique au
lieu de deux classes séparées. -/
def GroupsLinked (P : List (List Nat)) (a b c d : Nat) : Prop :=
  ∃ C ∈ P, ((C.contains a || C.contains b) = true) ∧
    ((C.contains c || C.contains d) = true)

/-- Un « hit » de classe, lu en appartenances. -/
lemma hit_iff_mem {C : List Nat} {x y : Nat} :
    ((C.contains x || C.contains y) = true) ↔ (x ∈ C ∨ y ∈ C) := by
  rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem]

/-- Appartenance à la classe fusionnée, caractérisée sur `P`. -/
lemma mem_fused_iff {P : List (List Nat)} {x y z : Nat} :
    z ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups ↔
      Touches P x y z := by
  rw [List.mem_eraseDups, List.mem_flatten]
  constructor
  · rintro ⟨C, hC, hz⟩
    obtain ⟨hCP, hcond⟩ := List.mem_filter.mp hC
    exact ⟨C, hCP, hz, hcond⟩
  · rintro ⟨C, hC, hz, hcond⟩
    exact ⟨C, List.mem_filter.mpr ⟨hC, hcond⟩, hz⟩

/-- `GroupsLinked` se lit depuis le groupe `{a, b}` : une classe porte
alors `c` ou `d`. -/
lemma groupsLinked_iff {P : List (List Nat)} {a b c d : Nat} :
    GroupsLinked P a b c d ↔ (Touches P a b c ∨ Touches P a b d) := by
  constructor
  · rintro ⟨C, hC, hab, hcd⟩
    rw [hit_iff_mem] at hcd
    rcases hcd with hc | hd
    · exact Or.inl ⟨C, hC, hc, hab⟩
    · exact Or.inr ⟨C, hC, hd, hab⟩
  · rintro (⟨C, hC, hc, hab⟩ | ⟨C, hC, hd, hab⟩)
    · exact ⟨C, hC, hab, by rw [hit_iff_mem]; exact Or.inl hc⟩
    · exact ⟨C, hC, hab, by rw [hit_iff_mem]; exact Or.inr hd⟩

/-- `GroupsLinked` est symétrique dans l'échange des deux groupes. -/
lemma groupsLinked_symm {P : List (List Nat)} {a b c d : Nat} :
    GroupsLinked P a b c d ↔ GroupsLinked P c d a b := by
  constructor <;> rintro ⟨C, hC, h1, h2⟩ <;> exact ⟨C, hC, h2, h1⟩

/-- Quand les groupes ne sont pas reliés, la classe fusionnée du groupe
`{a, b}` ne porte ni `c` ni `d`. -/
lemma not_mem_fused_of_not_linked {P : List (List Nat)} {a b c d : Nat}
    (h : ¬ GroupsLinked P a b c d) :
    ¬ (c ∈ (P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups ∨
       d ∈ (P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups) :=
  fun hmem => h (groupsLinked_iff.mpr
    (hmem.elim (fun hc => Or.inl (mem_fused_iff.mp hc))
               (fun hd => Or.inr (mem_fused_iff.mp hd))))

/-- `SameClass` après une fusion, caractérisé sur la partition d'origine :
une classe commune laissée intacte, ou deux étiquettes happées toutes deux
par la fusion. -/
lemma sameClass_mergePair_iff {P : List (List Nat)} {x y u v : Nat} :
    SameClass (mergePair P x y) u v ↔
      (∃ C ∈ P, u ∈ C ∧ v ∈ C ∧ ¬((C.contains x || C.contains y) = true)) ∨
      (Touches P x y u ∧ Touches P x y v) := by
  rw [mergePair_eq]
  constructor
  · rintro ⟨D, hD, hu, hv⟩
    rw [List.mem_append] at hD
    rcases hD with hkeep | hF
    · obtain ⟨hDP, hcond⟩ := List.mem_filter.mp hkeep
      exact Or.inl ⟨D, hDP, hu, hv, by simpa using hcond⟩
    · have hDeq : D = (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups :=
        List.mem_singleton.mp hF
      subst hDeq
      exact Or.inr ⟨mem_fused_iff.mp hu, mem_fused_iff.mp hv⟩
  · rintro (⟨C, hC, hu, hv, hcond⟩ | ⟨hu, hv⟩)
    · exact ⟨C, by rw [List.mem_append]; exact Or.inl (keep_filter hC hcond), hu, hv⟩
    · exact ⟨_, by rw [List.mem_append]; exact Or.inr (List.mem_singleton.mpr rfl),
        mem_fused_iff.mpr hu, mem_fused_iff.mpr hv⟩

/-- `Touches` à travers une première fusion `{a, b}` : soit une classe
intacte (hors du groupe `{a, b}`) qui porte `c` ou `d`, soit la classe
fusionnée du groupe `{a, b}` elle-même. -/
lemma touches_mergePair_iff {P : List (List Nat)} {a b c d z : Nat} :
    Touches (mergePair P a b) c d z ↔
      (∃ C ∈ P, z ∈ C ∧ ¬((C.contains a || C.contains b) = true) ∧
        ((C.contains c || C.contains d) = true)) ∨
      (Touches P a b z ∧ (Touches P a b c ∨ Touches P a b d)) := by
  constructor
  · rintro ⟨E, hE, hz, hcd⟩
    rw [mergePair_eq, List.mem_append] at hE
    rcases hE with hkeep | hF
    · obtain ⟨hEP, hcond⟩ := List.mem_filter.mp hkeep
      exact Or.inl ⟨E, hEP, hz, by simpa using hcond, hcd⟩
    · have hEeq : E = (P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups :=
        List.mem_singleton.mp hF
      subst hEeq
      rw [hit_iff_mem] at hcd
      rcases hcd with hc | hd
      · exact Or.inr ⟨mem_fused_iff.mp hz, Or.inl (mem_fused_iff.mp hc)⟩
      · exact Or.inr ⟨mem_fused_iff.mp hz, Or.inr (mem_fused_iff.mp hd)⟩
  · rintro (⟨C, hC, hz, hcond, hcd⟩ | ⟨hz, hcd⟩)
    · exact ⟨C, by rw [mergePair_eq, List.mem_append]; exact Or.inl (keep_filter hC hcond),
        hz, hcd⟩
    · refine ⟨(P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups,
        by rw [mergePair_eq, List.mem_append]; exact Or.inr (List.mem_singleton.mpr rfl),
        mem_fused_iff.mpr hz, ?_⟩
      rw [hit_iff_mem]
      rcases hcd with hc | hd
      · exact Or.inl (mem_fused_iff.mpr hc)
      · exact Or.inr (mem_fused_iff.mpr hd)

/-- Caractérisation complète de `SameClass` après deux fusions `{a, b}`
puis `{c, d}`, lue sur la partition d'origine `P`. Trois voies seulement :
(i) une classe commune — une classe n'est jamais scindée ; ou (ii) `x` et
`y` happés par les fusions, avec soit groupes reliés (une seule classe
géante), soit `x` et `y` happés par le même groupe. La forme est invariante
par échange des deux groupes — c'est elle qui donne la commutation. -/
lemma sameClass_two_merges_iff {P : List (List Nat)} {a b c d x y : Nat} :
    SameClass (mergePair (mergePair P a b) c d) x y ↔
      (∃ C ∈ P, x ∈ C ∧ y ∈ C) ∨
      ((Touches P a b x ∨ Touches P c d x) ∧ (Touches P a b y ∨ Touches P c d y) ∧
        (GroupsLinked P a b c d ∨ (Touches P a b x ∧ Touches P a b y) ∨
          (Touches P c d x ∧ Touches P c d y))) := by
  rw [sameClass_mergePair_iff]
  constructor
  · rintro (⟨E, hE, hx, hy, hncd⟩ | ⟨hTx, hTy⟩)
    · rw [mergePair_eq, List.mem_append] at hE
      rcases hE with hkeep | hF
      · obtain ⟨hEP, _⟩ := List.mem_filter.mp hkeep
        exact Or.inl ⟨E, hEP, hx, hy⟩
      · have hEeq : E = (P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups :=
          List.mem_singleton.mp hF
        subst hEeq
        have htabx : Touches P a b x := mem_fused_iff.mp hx
        have htaby : Touches P a b y := mem_fused_iff.mp hy
        exact Or.inr ⟨Or.inl htabx, Or.inl htaby, Or.inr (Or.inl ⟨htabx, htaby⟩)⟩
    · rw [touches_mergePair_iff] at hTx hTy
      rcases hTx with hKx | ⟨htabx, hGLx⟩
      · rcases hTy with hKy | ⟨htaby, hGLy⟩
        · obtain ⟨C, hC, hxc, _, hcd⟩ := hKx
          obtain ⟨D, hD, hyc, _, hcd2⟩ := hKy
          have htcdx : Touches P c d x := ⟨C, hC, hxc, hcd⟩
          have htcdy : Touches P c d y := ⟨D, hD, hyc, hcd2⟩
          exact Or.inr ⟨Or.inr htcdx, Or.inr htcdy, Or.inr (Or.inr ⟨htcdx, htcdy⟩)⟩
        · obtain ⟨C, hC, hxc, _, hcd⟩ := hKx
          exact Or.inr ⟨Or.inr ⟨C, hC, hxc, hcd⟩, Or.inl htaby,
            Or.inl (groupsLinked_iff.mpr hGLy)⟩
      · rcases hTy with hKy | ⟨htaby, hGLy⟩
        · obtain ⟨D, hD, hyc, _, hcd2⟩ := hKy
          exact Or.inr ⟨Or.inl htabx, Or.inr ⟨D, hD, hyc, hcd2⟩,
            Or.inl (groupsLinked_iff.mpr hGLx)⟩
        · exact Or.inr ⟨Or.inl htabx, Or.inl htaby, Or.inl (groupsLinked_iff.mpr hGLx)⟩
  · rintro (hI | ⟨hx, hy, hinner⟩)
    · obtain ⟨C, hC, hxc, hyc⟩ := hI
      by_cases hab : (C.contains a || C.contains b) = true
      · by_cases hGL : GroupsLinked P a b c d
        · exact Or.inr
            ⟨touches_mergePair_iff.mpr (Or.inr ⟨⟨C, hC, hxc, hab⟩, groupsLinked_iff.mp hGL⟩),
             touches_mergePair_iff.mpr (Or.inr ⟨⟨C, hC, hyc, hab⟩, groupsLinked_iff.mp hGL⟩)⟩
        · left
          refine ⟨(P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups,
            by rw [mergePair_eq, List.mem_append]; exact Or.inr (List.mem_singleton.mpr rfl),
            mem_fused_iff.mpr ⟨C, hC, hxc, hab⟩, mem_fused_iff.mpr ⟨C, hC, hyc, hab⟩, ?_⟩
          rw [hit_iff_mem]
          exact not_mem_fused_of_not_linked hGL
      · by_cases hcd : (C.contains c || C.contains d) = true
        · exact Or.inr
            ⟨touches_mergePair_iff.mpr (Or.inl ⟨C, hC, hxc, hab, hcd⟩),
             touches_mergePair_iff.mpr (Or.inl ⟨C, hC, hyc, hab, hcd⟩)⟩
        · left
          exact ⟨C, by rw [mergePair_eq, List.mem_append]; exact Or.inl (keep_filter hC hab),
            hxc, hyc, hcd⟩
    · rcases hinner with hGL | ⟨htabx, htaby⟩ | ⟨htcdx, htcdy⟩
      · have mk : ∀ z : Nat, (Touches P a b z ∨ Touches P c d z) →
            Touches (mergePair P a b) c d z := by
          rintro z (htab | ⟨C, hC, hzc, hcdz⟩)
          · exact touches_mergePair_iff.mpr (Or.inr ⟨htab, groupsLinked_iff.mp hGL⟩)
          · by_cases habC : (C.contains a || C.contains b) = true
            · exact touches_mergePair_iff.mpr (Or.inr ⟨⟨C, hC, hzc, habC⟩,
                groupsLinked_iff.mp ⟨C, hC, habC, hcdz⟩⟩)
            · exact touches_mergePair_iff.mpr (Or.inl ⟨C, hC, hzc, habC, hcdz⟩)
        exact Or.inr ⟨mk x hx, mk y hy⟩
      · by_cases hGL : GroupsLinked P a b c d
        · exact Or.inr
            ⟨touches_mergePair_iff.mpr (Or.inr ⟨htabx, groupsLinked_iff.mp hGL⟩),
             touches_mergePair_iff.mpr (Or.inr ⟨htaby, groupsLinked_iff.mp hGL⟩)⟩
        · left
          refine ⟨(P.filter (fun C => C.contains a || C.contains b)).flatten.eraseDups,
            by rw [mergePair_eq, List.mem_append]; exact Or.inr (List.mem_singleton.mpr rfl),
            mem_fused_iff.mpr htabx, mem_fused_iff.mpr htaby, ?_⟩
          rw [hit_iff_mem]
          exact not_mem_fused_of_not_linked hGL
      · obtain ⟨C, hC, hxc, hcdx⟩ := htcdx
        obtain ⟨D, hD, hyc, hcdy⟩ := htcdy
        by_cases habC : (C.contains a || C.contains b) = true
        · have hGLC : GroupsLinked P a b c d := ⟨C, hC, habC, hcdx⟩
          by_cases habD : (D.contains a || D.contains b) = true
          · exact Or.inr
              ⟨touches_mergePair_iff.mpr (Or.inr ⟨⟨C, hC, hxc, habC⟩,
                 groupsLinked_iff.mp hGLC⟩),
               touches_mergePair_iff.mpr (Or.inr ⟨⟨D, hD, hyc, habD⟩,
                 groupsLinked_iff.mp ⟨D, hD, habD, hcdy⟩⟩)⟩
          · exact Or.inr
              ⟨touches_mergePair_iff.mpr (Or.inr ⟨⟨C, hC, hxc, habC⟩,
                 groupsLinked_iff.mp hGLC⟩),
               touches_mergePair_iff.mpr (Or.inl ⟨D, hD, hyc, habD, hcdy⟩)⟩
        · by_cases habD : (D.contains a || D.contains b) = true
          · exact Or.inr
              ⟨touches_mergePair_iff.mpr (Or.inl ⟨C, hC, hxc, habC, hcdx⟩),
               touches_mergePair_iff.mpr (Or.inr ⟨⟨D, hD, hyc, habD⟩,
                 groupsLinked_iff.mp ⟨D, hD, habD, hcdy⟩⟩)⟩
          · exact Or.inr
              ⟨touches_mergePair_iff.mpr (Or.inl ⟨C, hC, hxc, habC, hcdx⟩),
               touches_mergePair_iff.mpr (Or.inl ⟨D, hD, hyc, habD, hcdy⟩)⟩

/-- La forme caractérisante de `sameClass_two_merges_iff` est invariante
par échange des deux groupes. -/
lemma sameClass_two_merges_comm_form {P : List (List Nat)} {a b c d x y : Nat} :
    ((∃ C ∈ P, x ∈ C ∧ y ∈ C) ∨
      ((Touches P a b x ∨ Touches P c d x) ∧ (Touches P a b y ∨ Touches P c d y) ∧
        (GroupsLinked P a b c d ∨ (Touches P a b x ∧ Touches P a b y) ∨
          (Touches P c d x ∧ Touches P c d y)))) ↔
    ((∃ C ∈ P, x ∈ C ∧ y ∈ C) ∨
      ((Touches P c d x ∨ Touches P a b x) ∧ (Touches P c d y ∨ Touches P a b y) ∧
        (GroupsLinked P c d a b ∨ (Touches P c d x ∧ Touches P c d y) ∨
          (Touches P a b x ∧ Touches P a b y)))) := by
  constructor
  · rintro (hI | ⟨hx, hy, hL | hab | hcd⟩)
    · exact Or.inl hI
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inl (groupsLinked_symm.mp hL)⟩
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inr (Or.inr hab)⟩
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inr (Or.inl hcd)⟩
  · rintro (hI | ⟨hx, hy, hL | hcd | hab⟩)
    · exact Or.inl hI
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inl (groupsLinked_symm.mpr hL)⟩
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inr (Or.inr hcd)⟩
    · exact Or.inr ⟨hx.symm, hy.symm, Or.inr (Or.inl hab)⟩

/-- **Commutation de deux fusions** : l'ordre d'application des paires
`{a, b}` puis `{c, d}` ne change pas la relation « partager une classe ».
Les listes produites diffèrent (ordre d'apparition dans la classe
fusionnée — contre-exemple documenté sur l'issue #16650), mais la partition
vue comme relation d'équivalence est la même. C'est la reformulation
correcte du lemme de commutation cherché : la commutation vit au niveau de
`SameClass`, pas de l'égalité des listes. -/
theorem mergePair_mergePair_comm_equiv (P : List (List Nat)) (a b c d x y : Nat) :
    SameClass (mergePair (mergePair P a b) c d) x y ↔
    SameClass (mergePair (mergePair P c d) a b) x y := by
  rw [sameClass_two_merges_iff, sameClass_two_merges_comm_form,
      ← sameClass_two_merges_iff (a := c) (b := d) (c := a) (d := b)]

/-- `Touches` lu en `SameClass` : une étiquette est happée par la fusion
    `{x, y}` exactement quand elle partage une classe avec `x` ou avec `y`.
    C'est la cle qui rend la caractérisation de `SameClass` après fusion
    transportable d'une partition à une autre. -/
lemma touches_iff_sameClass {P : List (List Nat)} {x y z : Nat} :
    Touches P x y z ↔ (SameClass P x z ∨ SameClass P y z) := by
  constructor
  · rintro ⟨C, hC, hz, hcond⟩
    rw [hit_iff_mem] at hcond
    rcases hcond with hx | hy
    · exact Or.inl ⟨C, hC, hx, hz⟩
    · exact Or.inr ⟨C, hC, hy, hz⟩
  · rintro (⟨C, hC, hx, hz⟩ | ⟨C, hC, hy, hz⟩)
    · exact ⟨C, hC, hz, by rw [hit_iff_mem]; exact Or.inl hx⟩
    · exact ⟨C, hC, hz, by rw [hit_iff_mem]; exact Or.inr hy⟩

/-- Caractérisation pure de `SameClass` après une fusion : une classe
    commune conservée, ou deux étiquettes toutes deux happées — lu
    entièrement en `SameClass` de la partition d'origine. C'est cette forme
    qui fait du repli une congruence pour `SameClass`. -/
lemma sameClass_mergePair_pure {P : List (List Nat)} {x y u v : Nat} :
    SameClass (mergePair P x y) u v ↔
      SameClass P u v ∨
        ((SameClass P x u ∨ SameClass P y u) ∧
          (SameClass P x v ∨ SameClass P y v)) := by
  rw [sameClass_mergePair_iff, touches_iff_sameClass, touches_iff_sameClass]
  constructor
  · rintro (⟨C, hC, hu, hv, _⟩ | h)
    · exact Or.inl ⟨C, hC, hu, hv⟩
    · exact Or.inr h
  · rintro (⟨C, hC, hu, hv⟩ | h)
    · by_cases hcond : ((C.contains x || C.contains y) = true)
      · rw [hit_iff_mem] at hcond
        rcases hcond with hx | hy
        · exact Or.inr ⟨Or.inl ⟨C, hC, hx, hu⟩, Or.inl ⟨C, hC, hx, hv⟩⟩
        · exact Or.inr ⟨Or.inr ⟨C, hC, hy, hu⟩, Or.inr ⟨C, hC, hy, hv⟩⟩
      · exact Or.inl ⟨C, hC, hu, hv, hcond⟩
    · exact Or.inr h

/-- **Congruence du repli** : si deux partitions sont indiscernables par
    `SameClass`, le repli d'une même liste de paires les laisse
    indiscernables. Le repli ne voit jamais la forme des listes de classes,
    seulement qui partage une classe. -/
lemma foldl_mergeStep_congr {Q₁ Q₂ : List (List Nat)}
    (h : ∀ w z, SameClass Q₁ w z ↔ SameClass Q₂ w z)
    (pairs : List (Nat × Nat)) :
    ∀ w z, SameClass (pairs.foldl mergeStep Q₁) w z ↔
           SameClass (pairs.foldl mergeStep Q₂) w z := by
  induction pairs generalizing Q₁ Q₂ with
  | nil => exact h
  | cons p rest ih =>
    refine ih ?_
    intro w z
    show SameClass (mergePair Q₁ p.1 p.2) w z ↔ SameClass (mergePair Q₂ p.1 p.2) w z
    rw [sameClass_mergePair_pure, sameClass_mergePair_pure,
        h w z, h p.1 w, h p.2 w, h p.1 z, h p.2 z]

/-- **Le repli est insensible à la permutation de deux paires adjacentes** :
    échanger les positions `i` et `i + 1` de la liste de paires ne change
    pas la relation `SameClass` du résultat du repli. Troisième brique de
    l'invariance R3 (issue #16650) : la chirurgie R3 connexe déplace les
    croisements réécrits dans la liste du repli, `foldl_mergePair_swap`
    absorbe l'orientation, `mergePair_mergePair_comm_equiv` la commutation
    des deux fusions, et la congruence `foldl_mergeStep_congr` transporte
    l'équivalence à travers le reste du repli. Ensemble, elles fondent la
    préservation de la partition d'arcs sur le témoin du lake. -/
theorem foldl_mergePair_permute_adjacent (pairs : List (Nat × Nat)) (i : Nat)
    (hi : i + 1 < pairs.length) (P₀ : List (List Nat)) (w z : Nat) :
    SameClass
      ((pairs.take i ++ [pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩,
                          pairs.get ⟨i + 1, hi⟩] ++ pairs.drop (i + 2)).foldl
          mergeStep P₀) w z ↔
      SameClass
      ((pairs.take i ++ [pairs.get ⟨i + 1, hi⟩,
                          pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩] ++ pairs.drop
            (i + 2)).foldl mergeStep P₀) w z := by
  have hfold : ∀ (r s : Nat × Nat),
      ((pairs.take i ++ [r, s] ++ pairs.drop (i + 2)).foldl mergeStep P₀)
        = (pairs.drop (i + 2)).foldl mergeStep
            (mergeStep (mergeStep ((pairs.take i).foldl mergeStep P₀) r) s) := by
    intro r s
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
        List.foldl_nil]
  rw [hfold (pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩) (pairs.get ⟨i + 1, hi⟩),
      hfold (pairs.get ⟨i + 1, hi⟩) (pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩)]
  exact foldl_mergeStep_congr
    (mergePair_mergePair_comm_equiv ((pairs.take i).foldl mergeStep P₀)
      (pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩).1
      (pairs.get ⟨i, Nat.lt_of_succ_lt hi⟩).2
      (pairs.get ⟨i + 1, hi⟩).1
      (pairs.get ⟨i + 1, hi⟩).2)
    (pairs.drop (i + 2)) w z

/-- Toute étiquette de la plage `1..n` est couverte par les singletons initiaux. -/
lemma covered_singles {n z : Nat} (h1 : 1 ≤ z) (h2 : z ≤ n) :
    Covered ((List.range n).map (fun i => [i + 1])) z := by
  refine ⟨[z], ?_, by simp⟩
  rw [List.mem_map]
  exact ⟨z - 1, by rw [List.mem_range]; omega, by simp only [Nat.sub_add_cancel h1]⟩

/-- Les quatre étiquettes d'arête de chaque croisement vivent dans la plage
`1..numEdges` du diagramme. -/
def EdgesInRange (d : KnotDiagram) : Prop :=
  ∀ c ∈ d.crossings, 1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
    1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
    1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧
    1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges

/-- Le repli de `arcPartition` en forme de `foldl` sur `mergeStep`. -/
lemma arcPartition_eq (d : KnotDiagram) :
    arcPartition d = (d.crossings.map (fun c => (c.e2, c.e4))).foldl mergeStep
      ((List.range d.numEdges).map (fun i => [i + 1])) := rfl

/-- **Le fait de Fox** : en chaque croisement d'un diagramme à étiquettes en
plage, les deux étiquettes de dessus appartiennent à une même classe de la
partition d'arcs. C'est ce fait — et non la seule garde de cardinal de
`alexanderPolynomialAux` — qui porte la somme de ligne nulle de la matrice
d'Alexander (cf `alexanderEntry_sum_zero` ci-dessous). -/
theorem arcPartition_sameClass_overStrand (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    SameClass (arcPartition d) c.e2 c.e4 := by
  rw [arcPartition_eq]
  have hcover : ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨c', hc', rfl⟩ := hq
    obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
    exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩
  exact sameClass_foldl_of_mem hcover (c.e2, c.e4) (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Contrôle : la partition d'arcs du code Conway corrigé — 11 arcs couvrant
les 22 arêtes (condition de non-dégénérescence du mineur d'Alexander : la
garde `arcs'.length = rest.length + 1` de `alexanderPolynomialAux` passe).
Le code non connexe précédent produisait un arc isolé {21, 22} absorbé par
la colonne éliminée du mineur désigné → déterminant 0. -/
theorem conway_arcPartition :
    arcPartition conwayKnotDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [20, 21], [10, 11, 12],
       [18, 19], [14, 15], [16, 17]] := by
  decide

/-- Contrôle : partition d'arcs du code KT corrigé — 11 arcs, structure
partagée avec Conway sur les croisements 1-5, divergente au-delà. -/
theorem kinoshitaTerasaka_arcPartition :
    arcPartition kinoshitaTerasakaDiagram =
      [[13], [22], [3, 4], [1, 2], [5, 6], [9, 7, 8], [14, 15], [10, 11, 12],
       [18, 19], [20, 21], [16, 17]] := by
  decide

/-- Entrée de la matrice d'Alexander : ligne du croisement `c`, colonne de
l'arc `C`. Convention positive (Fox de la relation de Wirtinger) : `+t`
(arc entrant du dessous), `−1` (arc sortant du dessous), `1−t` (arc du
dessus) — chaque ligne somme à zéro, condition qui garantit que deux
mineurs (n−1)×(n−1) diffèrent d'une unité ±t^k. Le code PD ne code pas la
chiralité du croisement, aussi les deux conventions différeraient-elles
d'un facteur unité — la présente est désignée. -/
noncomputable def alexanderEntry (c : PDCrossing) (C : List Nat) : Polynomial ℤ :=
  (if C.contains c.e1 then Polynomial.X else 0)
    + (if C.contains c.e3 then -(1 : Polynomial ℤ) else 0)
    + (if C.contains c.e2 || C.contains c.e4 then 1 - Polynomial.X else 0)

/-! #### Les lignes d'Alexander somment à zéro

Sous les hypothèses d'unicité — chaque étiquette du dessous portée par
exactement une classe, la paire de dessus rencontrant exactement une classe —
chaque ligne de la matrice d'Alexander somme à zéro : `t − 1 + (1 − t) = 0`.
C'est ce fait qui rend le mineur (n−1)×(n−1) indépendant, à un signe près, du
choix de la colonne frappée : l'affirmation normative de la docstring
d'`alexanderEntry` devient ici un théorème. `arcPartition_sameClass_overStrand`
fournit la moitié combinatoire (la paire de dessus partage une classe) ;
la vérification que `arcPartition` satisfait les hypothèses d'unicité
(`countP` = 1 par étiquette) est établie dans la section suivante
(`arcPartition_countP_label`).
-/

/-- Somme d'une carte indicatrice : le `w` est compté une fois par classe
porteuse. -/
lemma sum_map_indicator (P : List (List Nat)) (p : List Nat → Bool) (w : Polynomial ℤ) :
    (P.map (fun C => if p C then w else 0)).sum = w * (P.countP p : Polynomial ℤ) := by
  induction P with
  | nil => simp
  | cons D Ps ih =>
      by_cases hD : p D = true
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, if_true]
        push_cast
        ring
      · simp only [List.map_cons, List.sum_cons, ih, List.countP_cons, hD, Bool.false_eq_true,
          if_false]
        push_cast
        ring

/-- La somme d'une carte à trois termes se distribue sur les trois sommes. -/
lemma sum_map_three (P : List (List Nat)) (f g h : List Nat → Polynomial ℤ) :
    (P.map (fun C => f C + g C + h C)).sum =
      (P.map f).sum + (P.map g).sum + (P.map h).sum := by
  induction P with
  | nil => simp
  | cons D Ps ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- **Somme de ligne nulle** : si chaque étiquette du dessous est portée par
exactement une classe et si la paire de dessus rencontre exactement une
classe, alors la ligne d'`alexanderEntry` somme à zéro. C'est le fait de Fox
qui rend le mineur (n−1)×(n−1) indépendant, à un signe près, du choix de la
colonne frappée — le socle demandé par See #14962 avant toute correction de
normalisation. -/
theorem alexanderEntry_sum_zero (P : List (List Nat)) (c : PDCrossing)
    (h1 : P.countP (fun C => C.contains c.e1) = 1)
    (h3 : P.countP (fun C => C.contains c.e3) = 1)
    (h24 : P.countP (fun C => C.contains c.e2 || C.contains c.e4) = 1) :
    (P.map (alexanderEntry c)).sum = 0 := by
  have hmap : (P.map (alexanderEntry c)) = P.map (fun C : List Nat =>
      ((if C.contains c.e1 then (Polynomial.X : Polynomial ℤ) else 0)
        + (if C.contains c.e3 then (-(1 : Polynomial ℤ)) else 0)
        + (if C.contains c.e2 || C.contains c.e4 then (1 : Polynomial ℤ) - Polynomial.X
           else 0))) := by
    congr 1
  rw [hmap, sum_map_three, sum_map_indicator, h1, sum_map_indicator, h3, sum_map_indicator, h24]
  push_cast
  ring

/-! #### `arcPartition` est une partition : l'unicité `countP` = 1

La section précédente reposait sur des hypothèses d'unicité (`countP` = 1).
Cette section les établit pour la vraie `arcPartition` : les classes sont deux
à deux disjointes (un invariant que `mergePair` préserve), sans doublon, et
couvrent toute la plage `1..numEdges`. Il en découle que chaque ligne de la
matrice d'Alexander somme à zéro sans hypothèse additionnelle — le résiduel
nommé sur See #14962 est levé. -/

/-- Deux classes distinctes de `P` sont disjointes. -/
def ClassesDisjoint (P : List (List Nat)) : Prop :=
  ∀ C ∈ P, ∀ D ∈ P, C ≠ D → ∀ z, z ∈ C → z ∉ D

/-- Les singletons initiaux sont deux à deux disjoints. -/
lemma classesDisjoint_singles {n : Nat} :
    ClassesDisjoint ((List.range n).map (fun i => [i + 1])) := by
  intro C hC D hD hne z hzC hzD
  rw [List.mem_map] at hC hD
  obtain ⟨i, hi, rfl⟩ := hC
  obtain ⟨j, hj, rfl⟩ := hD
  simp only [List.mem_singleton] at hzC hzD
  exact hne (by congr 1; omega)

/-- Le filtre `keep` (classes ne portant ni `x` ni `y`) ne rencontre jamais le
bloc fusionné : un `z` d'une classe intacte n'appartient à aucune classe touchée. -/
lemma not_mem_merged_of_keep {P : List (List Nat)} {C : List Nat} {x y z : Nat}
    (hP : ClassesDisjoint P)
    (hC : C ∈ P) (hkeep : (C.contains x || C.contains y) ≠ true) :
    z ∈ C → z ∉ (P.filter (fun D => D.contains x || D.contains y)).flatten.eraseDups := by
  intro hz hmem
  rw [List.mem_eraseDups, List.mem_flatten] at hmem
  obtain ⟨D, hD, hzD⟩ := hmem
  rw [List.mem_filter] at hD
  obtain ⟨hDP, hDhit⟩ := hD
  have hne : C ≠ D := by
    intro heq; subst heq; exact hkeep hDhit
  exact hP C hC D hDP hne z hz hzD

/-- `mergePair` préserve la disjonction des classes. -/
lemma classesDisjoint_mergePair {P : List (List Nat)} {x y : Nat}
    (hP : ClassesDisjoint P) : ClassesDisjoint (mergePair P x y) := by
  intro C hC D hD hne z hzC hzD
  rw [mergePair_eq, List.mem_append] at hC hD
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · rw [List.mem_filter] at hC hD
    exact hP C hC.1 D hD.1 hne z hzC hzD
  · rw [List.mem_filter] at hC
    rw [List.mem_singleton] at hD
    subst hD
    refine not_mem_merged_of_keep hP hC.1 ?_ hzC hzD
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  · rw [List.mem_filter] at hD
    rw [List.mem_singleton] at hC
    subst hC
    refine not_mem_merged_of_keep hP hD.1 ?_ hzD hzC
    cases hA : D.contains x <;> cases hB : D.contains y <;> simp_all
  · rw [List.mem_singleton] at hC hD
    exact hne (hC.trans hD.symm)

/-- La disjonction des classes survit au repli complet. -/
lemma classesDisjoint_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (h : ClassesDisjoint P) : ClassesDisjoint (pairs.foldl mergeStep P) := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (classesDisjoint_mergePair h)

/-- Les singletons initiaux sont deux à deux distincts. -/
lemma pairwise_singles {n : Nat} :
    ((List.range n).map (fun i => [i + 1])).Pairwise (fun C D => C ≠ D) :=
  List.Pairwise.map (fun i => [i + 1])
    (fun a b h heq => by
      injection heq with h1
      exact h (by omega))
    List.nodup_range

/-- Une étiquette couverte reste dans le bloc fusionné. -/
lemma mem_merged_of_covered {P : List (List Nat)} {x y : Nat} (hx : Covered P x) :
    x ∈ (P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups := by
  obtain ⟨C, hCP, hx'⟩ := hx
  refine List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨C, ?_, hx'⟩)
  refine List.mem_filter.mpr ⟨hCP, ?_⟩
  rw [Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr hx')

/-- `mergePair` préserve l'absence de doublon : le bloc fusionné, qui porte `x`,
ne peut pas être une classe intacte, qui ne porte pas `x`. -/
lemma pairwise_mergePair {P : List (List Nat)} {x y : Nat}
    (hnd : P.Pairwise (fun C D => C ≠ D)) (hx : Covered P x) :
    (mergePair P x y).Pairwise (fun C D => C ≠ D) := by
  rw [mergePair_eq, List.pairwise_append]
  have hkeep : (P.filter (fun C => !C.contains x && !C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  refine ⟨hkeep, List.pairwise_singleton _ _, ?_⟩
  intro C hC D hDm
  rw [List.mem_filter] at hC
  obtain ⟨hCP, hcond⟩ := hC
  have hfx : C.contains x = false := by
    cases hA : C.contains x <;> cases hB : C.contains y <;> simp_all
  rw [List.mem_singleton] at hDm
  intro heq
  subst heq
  subst hDm
  have h1 : ((P.filter (fun C => C.contains x || C.contains y)).flatten.eraseDups).contains x = true :=
    List.contains_iff_mem.mpr (mem_merged_of_covered hx)
  rw [h1] at hfx
  exact Bool.noConfusion hfx

/-- Les deux invariants de partition traversent le repli complet. -/
lemma foldl_partition_inv {pairs : List (Nat × Nat)} {P : List (List Nat)}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D))
    (hcov : ∀ q ∈ pairs, Covered P q.1 ∧ Covered P q.2) :
    ClassesDisjoint (pairs.foldl mergeStep P) ∧
      (pairs.foldl mergeStep P).Pairwise (fun C D => C ≠ D) := by
  induction pairs generalizing P with
  | nil => exact ⟨hd, hnd⟩
  | cons p ps ih =>
      rw [List.foldl_cons]
      refine ih (classesDisjoint_mergePair hd)
        (pairwise_mergePair hnd (hcov p (List.mem_cons_self ..)).1) ?_
      intro q hq
      have hc := hcov q (List.mem_cons_of_mem _ hq)
      exact ⟨covered_mergePair hc.1, covered_mergePair hc.2⟩

/-- La couverture d'une étiquette survit au repli complet. -/
lemma covered_foldl {pairs : List (Nat × Nat)} {P : List (List Nat)} {z : Nat}
    (h : Covered P z) : Covered (pairs.foldl mergeStep P) z := by
  induction pairs generalizing P with
  | nil => exact h
  | cons p ps ih => rw [List.foldl_cons]; exact ih (covered_mergePair h)

/-- Une liste deux-à-deux distincte dont tous les éléments valent `a` est de
longueur au plus un. -/
lemma pairwise_all_eq_length_le_one {α : Type} {l : List α} {a : α}
    (hnd : l.Pairwise (fun x y => x ≠ y)) (hall : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons b t =>
      cases t with
      | nil => simp
      | cons c t' =>
          exfalso
          have hbc : b = c := (hall b (by simp)).trans (hall c (by simp)).symm
          cases hnd with
          | cons hhead _ => exact absurd hbc (hhead c (by simp))

/-- Pont `countP`/`filter`, autonome. -/
lemma countP_length_filter {α : Type} {p : α → Bool} (l : List α) :
    l.countP p = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases h : p a = true
      · simp [h, ih]
      · simp [h, ih]

/-- **Unicité sous-strand** : dans une partition sans doublon, une étiquette
couverte appartient à exactement une classe. -/
lemma countP_contains_eq_one {P : List (List Nat)} {z : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hcov : Covered P z) :
    P.countP (fun C => C.contains z) = 1 := by
  obtain ⟨C₀, hC₀P, hz₀⟩ := hcov
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains z) :=
    List.mem_filter.mpr ⟨hC₀P, List.contains_iff_mem.mpr hz₀⟩
  have hall : ∀ D ∈ P.filter (fun C => C.contains z), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, hzD⟩ := hD
    rw [List.contains_iff_mem] at hzD
    by_contra hne
    exact hd C₀ hC₀P D hDP (Ne.symm hne) z hz₀ hzD
  have hndf : (P.filter (fun C => C.contains z)).Pairwise (fun C D => C ≠ D) :=
    List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains z)).length := List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains z)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- **Unicité over-strand** : si `x` et `y` partagent une classe d'une partition
sans doublon, exactement une classe porte `x` ou `y`. -/
lemma countP_over_eq_one {P : List (List Nat)} {x y : Nat}
    (hd : ClassesDisjoint P) (hnd : P.Pairwise (fun C D => C ≠ D)) (hsc : SameClass P x y) :
    P.countP (fun C => C.contains x || C.contains y) = 1 := by
  obtain ⟨C₀, hC₀P, hx₀, hy₀⟩ := hsc
  have hfC₀ : C₀ ∈ P.filter (fun C => C.contains x || C.contains y) := by
    refine List.mem_filter.mpr ⟨hC₀P, ?_⟩
    rw [Bool.or_eq_true]
    exact Or.inl (List.contains_iff_mem.mpr hx₀)
  have hall : ∀ D ∈ P.filter (fun C => C.contains x || C.contains y), D = C₀ := by
    intro D hD
    rw [List.mem_filter] at hD
    obtain ⟨hDP, horD⟩ := hD
    rw [Bool.or_eq_true] at horD
    rcases horD with hxD | hyD
    · rw [List.contains_iff_mem] at hxD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) x hx₀ hxD
    · rw [List.contains_iff_mem] at hyD
      by_contra hne
      exact hd C₀ hC₀P D hDP (Ne.symm hne) y hy₀ hyD
  have hndf : (P.filter (fun C => C.contains x || C.contains y)).Pairwise
      (fun C D => C ≠ D) := List.Pairwise.filter _ hnd
  have hge : 0 < (P.filter (fun C => C.contains x || C.contains y)).length :=
    List.length_pos_of_mem hfC₀
  have hle : (P.filter (fun C => C.contains x || C.contains y)).length ≤ 1 :=
    pairwise_all_eq_length_le_one hndf hall
  rw [countP_length_filter]
  omega

/-- Chaque paire du repli est couverte par les singletons initiaux. -/
lemma crossings_covered_singles {d : KnotDiagram} (h : EdgesInRange d) :
    ∀ q ∈ d.crossings.map (fun c => (c.e2, c.e4)),
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.1 ∧
      Covered ((List.range d.numEdges).map (fun i => [i + 1])) q.2 := by
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨c', hc', rfl⟩ := hq
  obtain ⟨_, _, h2lo, h2hi, _, _, h4lo, h4hi⟩ := h c' hc'
  exact ⟨covered_singles h2lo h2hi, covered_singles h4lo h4hi⟩

/-- Toute étiquette de la plage `1..numEdges` est couverte par la partition. -/
lemma arcPartition_covered {d : KnotDiagram} {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    Covered (arcPartition d) z := by
  rw [arcPartition_eq]
  exact covered_foldl (covered_singles hz1 hz2)

/-- **`arcPartition` est une partition** : classes disjointes, sans doublon. -/
theorem arcPartition_classes (d : KnotDiagram) (h : EdgesInRange d) :
    ClassesDisjoint (arcPartition d) ∧
      (arcPartition d).Pairwise (fun C D => C ≠ D) := by
  rw [arcPartition_eq]
  exact foldl_partition_inv classesDisjoint_singles pairwise_singles
    (crossings_covered_singles h)

/-- **L'hypothèse `h1`/`h3` est un théorème** : chaque étiquette de la plage
est portée par exactement une classe de `arcPartition`. -/
theorem arcPartition_countP_label (d : KnotDiagram) (h : EdgesInRange d) {z : Nat}
    (hz1 : 1 ≤ z) (hz2 : z ≤ d.numEdges) :
    (arcPartition d).countP (fun C => C.contains z) = 1 := by
  obtain ⟨hd, hnd⟩ := arcPartition_classes d h
  exact countP_contains_eq_one hd hnd (arcPartition_covered hz1 hz2)

/-- **Somme de ligne inconditionnelle** : pour tout diagramme à étiquettes en
plage, chaque ligne de la matrice d'Alexander somme à zéro — la boucle entre
le fait de Fox et la somme nulle se referme, sans hypothèse d'unicité restée
à la main du lecteur. -/
theorem alexanderRow_sum_zero (d : KnotDiagram) (h : EdgesInRange d)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    ((arcPartition d).map (alexanderEntry c)).sum = 0 := by
  obtain ⟨h1lo, h1hi, _, _, h3lo, h3hi, _, _⟩ := h c hc
  exact alexanderEntry_sum_zero (arcPartition d) c
    (arcPartition_countP_label d h h1lo h1hi)
    (arcPartition_countP_label d h h3lo h3hi)
    (countP_over_eq_one (arcPartition_classes d h).1 (arcPartition_classes d h).2
      (arcPartition_sameClass_overStrand d h hc))
