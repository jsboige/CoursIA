/-
# DeuxMinima — les deux minima dans la paire profonde (pli 5h de #18706)

Le pli précédent (`min_to_bottom`) a amené UN poids minimal dans la paire de
sœurs à la profondeur maximale. Le théorème d'optimalité (pli suivant) en veut
davantage : **les DEUX plus petits poids** doivent y vivre — c'est la paire que
la construction de Huffman fusionne en premier. Ce pli en livre la seconde
moitié : `both_mins_to_bottom` amène le second minimum aux côtés du premier,
toujours sans augmenter le coût et en conservant le multi-ensemble des feuilles.

La difficulté est celle des **multiplicités** : sur la maille du carnet 02, le
trie compte deux 1 — les « deux plus petits poids » sont le même nombre porté
par deux feuilles distinctes. Un lemme énoncé sur « la feuille de poids w » ne
saurait alors désigner la bonne ; le pli précédent a déjà répondu par l'adresse
positionnel, ce pli y ajoute le comptage :

* `count_two_positions` — deux positions distinctes portant le même poids
  forcent deux occurrences dans le multi-ensemble des feuilles ;
* `exists_leafPos_ne` — réciproquement, un poids compté au moins deux fois a
  une seconde position, divergente de la première ;
* `both_mins_to_bottom` — la paire (premier minimum, occupant droit) du pli
  précédent reçoit le second minimum par UN échange positionnel : soit il y
  est déjà (l'occupant EST le second minimum), soit la facture
  `costW_exchPos_le` plafonne le coût au produit des écarts.

Ancre du carnet `Compression-02` : sur l'arbre déséquilibré de la maille 21,
le pli précédent rend 19 (premier 1 descendu) ; échanger le second 1
(profondeur 2) contre le 4 de la paire profonde rend
19 − (4−1)·(3−2) = 16.
-/
import Descente

namespace CompressionLean

/-! ## Compter les occurrences positionnelles -/

/-- **Deux positions distinctes portant le même poids y sont deux
occurrences.** La réciproque positionnelle de l'appartenance : non seulement
chaque position de `w` atteste `w ∈ leafWeights t` (c'est `subtreeAt_mem`),
mais deux positions distinctes attestent une multiplicité — le compte dans le
multi-ensemble des feuilles monte à deux. Cas croisés (une occurrence de chaque
côté d'un nœud) par `count_append`, même côté par récurrence. -/
theorem count_two_positions : ∀ (t : WTree) (π₁ π₂ : List Bool) (w : ℕ),
    subtreeAt t π₁ = some (.leaf w) → subtreeAt t π₂ = some (.leaf w) → π₁ ≠ π₂ →
    2 ≤ List.count w (leafWeights t) := by
  intro t
  induction t with
  | leaf w' =>
      intro π₁ π₂ w h1 h2 hne
      cases π₁ with
      | nil =>
          cases π₂ with
          | nil => exact absurd rfl hne
          | cons g2 q2 => simp [subtreeAt] at h2
      | cons g1 q1 => simp [subtreeAt] at h1
  | node l r ihl ihr =>
      intro π₁ π₂ w h1 h2 hne
      cases π₁ with
      | nil => simp [subtreeAt] at h1
      | cons g1 q1 =>
          cases π₂ with
          | nil => simp [subtreeAt] at h2
          | cons g2 q2 =>
              cases g1 with
              | true =>
                  cases g2 with
                  | true =>
                      -- même côté gauche : récurrence, l'autre côté n'ajoute que du compte
                      simp only [subtreeAt] at h1 h2
                      simp only [leafWeights, List.count_append]
                      refine Nat.le_trans (ihl q1 q2 w h1 h2 ?_) (Nat.le_add_right _ _)
                      intro he
                      exact hne (by rw [he])
                  | false =>
                      -- occurrences croisées : une de chaque côté, chaque côté en porte au moins une
                      simp only [subtreeAt] at h1 h2
                      simp only [leafWeights, List.count_append]
                      have hl : 1 ≤ List.count w (leafWeights l) :=
                        List.count_pos_iff.mpr (subtreeAt_mem l q1 w h1)
                      have hr : 1 ≤ List.count w (leafWeights r) :=
                        List.count_pos_iff.mpr (subtreeAt_mem r q2 w h2)
                      omega
              | false =>
                  cases g2 with
                  | true =>
                      simp only [subtreeAt] at h1 h2
                      simp only [leafWeights, List.count_append]
                      have hl : 1 ≤ List.count w (leafWeights l) :=
                        List.count_pos_iff.mpr (subtreeAt_mem l q2 w h2)
                      have hr : 1 ≤ List.count w (leafWeights r) :=
                        List.count_pos_iff.mpr (subtreeAt_mem r q1 w h1)
                      omega
                  | false =>
                      simp only [subtreeAt] at h1 h2
                      simp only [leafWeights, List.count_append]
                      refine Nat.le_trans (ihr q1 q2 w h1 h2 ?_) (Nat.le_add_left _ _)
                      intro he
                      exact hne (by rw [he])

/-! ## Une seconde position pour un poids répété -/

/-- **Un poids compté au moins deux fois a une seconde position, divergente
de la première.** La réciproque de `count_two_positions` : depuis le compte
(multiplicité), retrouver une géométrie — une autre feuille de même poids,
dont le chemin diverge du premier (aucun n'est prolongement de l'autre), la
garde qu'exigera `subtreeAt_replaceAt_ne` pour l'échange final. Quand la
multiplicité vit d'un seul côté, la récurrence la suit ; sinon elle traverse
le nœud et la divergence est structurelle (premier cran opposé). -/
theorem exists_leafPos_ne : ∀ (t : WTree) (πa : List Bool) (w : ℕ),
    subtreeAt t πa = some (.leaf w) → 2 ≤ List.count w (leafWeights t) →
    ∃ πb : List Bool, subtreeAt t πb = some (.leaf w) ∧ πa ≠ πb ∧
      (∀ q, πa ++ q ≠ πb) ∧ (∀ q, πb ++ q ≠ πa) := by
  intro t
  induction t with
  | leaf w' =>
      intro πa w hπa hcount
      cases πa with
      | nil =>
          -- une feuille seule porte son poids une fois : le compte ≥ 2 est impossible
          simp only [subtreeAt, Option.some.injEq, WTree.leaf.injEq] at hπa
          subst hπa
          simp only [leafWeights, List.count_cons_self, List.count_nil] at hcount
          omega
      | cons ga qa => simp [subtreeAt] at hπa
  | node l r ihl ihr =>
      intro πa w hπa hcount
      cases πa with
      | nil => simp [subtreeAt] at hπa
      | cons ga qa =>
          simp only [leafWeights, List.count_append] at hcount
          cases ga with
          | true =>
              simp only [subtreeAt] at hπa
              by_cases hcl : 2 ≤ List.count w (leafWeights l)
              · -- la multiplicité vit à gauche : la récurrence fournit la seconde position
                obtain ⟨πb, hπb, hne, hd1, hd2⟩ := ihl qa w hπa hcl
                refine ⟨true :: πb, hπb, ?_, ?_, ?_⟩
                · intro he
                  simp only [List.cons.injEq] at he
                  exact hne he.2
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact hd1 q hq.2
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact hd2 q hq.2
              · -- au moins une occurrence vit à droite : premier cran opposé
                have hcr : 1 ≤ List.count w (leafWeights r) := by omega
                obtain ⟨πb, hπb⟩ := exists_leafPos r w (List.count_pos_iff.mp hcr)
                refine ⟨false :: πb, hπb, ?_, ?_, ?_⟩
                · intro he
                  simp only [List.cons.injEq] at he
                  exact absurd he.1 (by decide)
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact absurd hq.1 (by decide)
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact absurd hq.1 (by decide)
          | false =>
              simp only [subtreeAt] at hπa
              by_cases hcr : 2 ≤ List.count w (leafWeights r)
              · obtain ⟨πb, hπb, hne, hd1, hd2⟩ := ihr qa w hπa hcr
                refine ⟨false :: πb, hπb, ?_, ?_, ?_⟩
                · intro he
                  simp only [List.cons.injEq] at he
                  exact hne he.2
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact hd1 q hq.2
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact hd2 q hq.2
              · have hcl : 1 ≤ List.count w (leafWeights l) := by omega
                obtain ⟨πb, hπb⟩ := exists_leafPos l w (List.count_pos_iff.mp hcl)
                refine ⟨true :: πb, hπb, ?_, ?_, ?_⟩
                · intro he
                  simp only [List.cons.injEq] at he
                  exact absurd he.1 (by decide)
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact absurd hq.1 (by decide)
                · intro q hq
                  simp only [List.cons_append, List.cons.injEq] at hq
                  exact absurd hq.1 (by decide)

/-! ## La seconde moitié du lemme des sœurs -/

/-- **Les deux plus petits poids peuvent vivre ensemble dans la paire de
sœurs à la profondeur maximale, sans augmenter le coût.** Suite directe de
`min_to_bottom` (pli 5g) : la paire (premier minimum `w₁`, occupant droit `c`)
que ce pli garantit reçoit le second minimum `w₂` par UN échange positionnel.
Trois lectures :

* si l'occupant droit EST le second minimum (`w₂ = c`), la paire du pli 5g
  est déjà la bonne — aucun échange ;
* si le second minimum est un poids distinct (`w₂ ≠ w₁`), une position
  quelconque de `w₂` suffit : l'échange la remplace par `c`, la facture
  `costW_exchPos_le` plafonne le coût au produit des écarts `w₂ ≤ c` ;
* si le trie compte DEUX fois le premier minimum (`w₂ = w₁` — la maille du
  carnet 02), le comptage prend le relais de l'égalité des poids :
  `exists_leafPos_ne` désigne la seconde occurrence, distincte de la première
  feuille de la paire.

Le multi-ensemble des feuilles est conservé (double `leafWeights_replaceAt`
refermé par `perm_double_exch`), la hauteur aussi — la paire finale vit
exactement à la profondeur maximale de l'arbre initial. -/
theorem both_mins_to_bottom : ∀ (t : WTree), (∃ l r, t = WTree.node l r) → ∀ (w₁ w₂ : ℕ),
    (∀ v ∈ leafWeights t, w₁ ≤ v) → w₁ ∈ leafWeights t →
    (∀ v ∈ (leafWeights t).erase w₁, w₂ ≤ v) → w₂ ∈ (leafWeights t).erase w₁ →
    ∃ (t' : WTree) (π : List Bool),
      List.Perm (leafWeights t') (leafWeights t) ∧
      costW t' ≤ costW t ∧
      subtreeAt t' π = some (WTree.node (.leaf w₁) (.leaf w₂)) ∧
      π.length + 1 = maxDepth t' := by
  intro t hnode w₁ w₂ hmin₁ hw₁ hmin₂ hw₂
  obtain ⟨t₁, π, c, hperm₁, hcost₁, hpair, hdepth⟩ :=
    min_to_bottom t hnode w₁ hmin₁ hw₁
  have hπL : subtreeAt t₁ (π ++ [true]) = some (.leaf w₁) := by
    rw [subtreeAt_congr t₁ π [true] (WTree.node (.leaf w₁) (.leaf c)) hpair]
    rfl
  have hπR : subtreeAt t₁ (π ++ [false]) = some (.leaf c) := by
    rw [subtreeAt_congr t₁ π [false] (WTree.node (.leaf w₁) (.leaf c)) hpair]
    rfl
  -- l'occupant droit de la paire vit dans l'effacé du premier minimum
  -- (le second minimum lui est donc comparable)
  have hc_mem : c ∈ (leafWeights t).erase w₁ := by
    by_cases hne_c : c ≠ w₁
    · exact (List.mem_erase_of_ne hne_c).mpr
        ((hperm₁.mem_iff).mp (subtreeAt_mem t₁ (π ++ [false]) c hπR))
    · -- c = w₁ : le minimum occupe les DEUX positions de la paire
      push Not at hne_c
      rw [hne_c] at hπR
      have hneLR : π ++ [true] ≠ π ++ [false] := by
        intro he
        have h2 : [true] = [false] := (List.append_right_inj π).mp he
        simp at h2
      have hcount₂ := count_two_positions t₁ (π ++ [true]) (π ++ [false]) w₁ hπL hπR hneLR
      have hpc := (List.perm_iff_count.mp hperm₁) w₁
      have hcs : List.count w₁ ((leafWeights t).erase w₁)
          = List.count w₁ (leafWeights t) - 1 := List.count_erase_self
      rw [hne_c]
      exact List.count_pos_iff.mp (by omega)
  have hle : w₂ ≤ c := hmin₂ c hc_mem
  by_cases hwc : w₂ = c
  · -- la paire produite par le pli 5g est déjà (w₁, w₂)
    exact ⟨t₁, π, hperm₁, hcost₁, by rw [hwc]; exact hpair, hdepth⟩
  · -- échange du second minimum contre l'occupant droit de la paire
    obtain ⟨π₂, hπ₂, hneL⟩ : ∃ π₂ : List Bool,
        subtreeAt t₁ π₂ = some (.leaf w₂) ∧ π ++ [true] ≠ π₂ := by
      by_cases hw2w1 : w₂ = w₁
      · -- la maille compte deux fois le premier minimum : comptage positionnel
        rw [hw2w1] at hw₂ ⊢
        have hc1 : 1 ≤ List.count w₁ (leafWeights t) := List.count_pos_iff.mpr hw₁
        have hc2 : 1 ≤ List.count w₁ ((leafWeights t).erase w₁) :=
          List.count_pos_iff.mpr hw₂
        have hcs : List.count w₁ ((leafWeights t).erase w₁)
            = List.count w₁ (leafWeights t) - 1 := List.count_erase_self
        have hcount₁ : 2 ≤ List.count w₁ (leafWeights t₁) := by
          have hpc := (List.perm_iff_count.mp hperm₁) w₁
          omega
        obtain ⟨πb, hπb, hneb, _, _⟩ :=
          exists_leafPos_ne t₁ (π ++ [true]) w₁ hπL hcount₁
        exact ⟨πb, hπb, hneb⟩
      · -- poids distinct : n'importe quelle position de w₂ convient
        have hw2_mem : w₂ ∈ leafWeights t := List.mem_of_mem_erase hw₂
        obtain ⟨π₂₀, hπ₂₀⟩ := exists_leafPos t₁ w₂ ((hperm₁.mem_iff).mpr hw2_mem)
        refine ⟨π₂₀, hπ₂₀, ?_⟩
        intro he
        rw [← he] at hπ₂₀
        exact hw2w1 (WTree.leaf.inj (Option.some.inj (hπL.symm.trans hπ₂₀))).symm
    have hneR : π ++ [false] ≠ π₂ := by
      intro he
      rw [he] at hπR
      exact hwc (WTree.leaf.inj (Option.some.inj (hπR.symm.trans hπ₂))).symm
    have hneR2 : π₂ ≠ π ++ [false] := fun he => hneR he.symm
    -- divergences entre la position de w₂ et la feuille droite de la paire
    have hdivR2A : ∀ q, (π ++ [false]) ++ q ≠ π₂ :=
      fun q hq => hneR (leafPos_prefix t₁ (π ++ [false]) π₂ c (.leaf w₂) hπR hπ₂ q hq)
    have hdivR2B : ∀ q, π₂ ++ q ≠ (π ++ [false]) :=
      fun q hq => hneR2 (leafPos_prefix t₁ π₂ (π ++ [false]) w₂ (.leaf c) hπ₂ hπR q hq)
    have hπ₂' : subtreeAt (replaceAt t₁ (π ++ [false]) w₂) π₂ = some (.leaf w₂) :=
      (subtreeAt_replaceAt_ne t₁ (π ++ [false]) π₂ c w₂ hπR hneR2 hdivR2A hdivR2B).trans hπ₂
    -- divergences entre la position de w₂ et le PARENT de la paire
    have hneA : π ≠ π₂ := by
      intro he
      rw [he] at hpair
      exact WTree.noConfusion (Option.some.inj (hpair.symm.trans hπ₂))
    have hdivA : ∀ q, π₂ ++ q ≠ π :=
      fun q hq =>
        hneA (leafPos_prefix t₁ π₂ π w₂ (WTree.node (.leaf w₁) (.leaf c)) hπ₂ hpair q hq).symm
    have hdivB : ∀ q, π ++ q ≠ π₂ := by
      intro q hq
      rw [← hq, subtreeAt_congr t₁ π q (WTree.node (.leaf w₁) (.leaf c)) hpair] at hπ₂
      cases q with
      | nil => exact hneA (by simpa only [List.append_nil] using hq)
      | cons go q' =>
          cases go with
          | true =>
              cases q' with
              | nil => exact hneL hq
              | cons g2 q'' => simp [subtreeAt] at hπ₂
          | false =>
              cases q' with
              | nil => exact hneR hq
              | cons g2 q'' => simp [subtreeAt] at hπ₂
    -- l'échange ne touche ni le parent, ni (après coup) la nouvelle feuille droite
    have hkeepπ : subtreeAt (replaceAt (replaceAt t₁ (π ++ [false]) w₂) π₂ c) π
        = subtreeAt (replaceAt t₁ (π ++ [false]) w₂) π :=
      subtreeAt_replaceAt_ne (replaceAt t₁ (π ++ [false]) w₂) π₂ π w₂ c hπ₂' hneA hdivA hdivB
    have memc : c ∈ leafWeights t₁ := subtreeAt_mem t₁ (π ++ [false]) c hπR
    have hlen : π₂.length ≤ (π ++ [false]).length := by
      have h1 := pathLen_le_maxDepth t₁ π₂ (.leaf w₂) hπ₂
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hp1' := leafWeights_replaceAt t₁ (π ++ [false]) c w₂ hπR
    have hp2' := leafWeights_replaceAt (replaceAt t₁ (π ++ [false]) w₂) π₂ w₂ c hπ₂'
    have hmd1 := maxDepth_replaceAt t₁ (π ++ [false]) c w₂ hπR
    have hmd2 := maxDepth_replaceAt (replaceAt t₁ (π ++ [false]) w₂) π₂ w₂ c hπ₂'
    refine ⟨exchPos t₁ (π ++ [false]) π₂ c w₂, π, ?_, ?_, ?_, ?_⟩
    · exact (hp2'.trans ((List.Perm.append_right [c] (hp1'.erase w₂)).trans
        (perm_double_exch (leafWeights t₁) c w₂ memc))).trans hperm₁
    · exact Nat.le_trans
        (costW_exchPos_le t₁ (π ++ [false]) π₂ c w₂ hπR hπ₂ hneR2.symm hle hlen) hcost₁
    · simp only [exchPos]
      rw [hkeepπ]
      exact subtreeAt_parent_right t₁ π c w₂ (.leaf w₁) hpair
    · simp only [exchPos]
      omega

/-! ## Ancres du carnet 02 : la maille 21 → 19 → 16 -/

/- Le pli 5g a rendu 19 (premier 1 descendu) ; le second 1 de la maille
(profondeur 2) échange sa place contre le 4 de la paire profonde :
la facture positionnelle rend 19 − (4−1)·(3−2) = 16. -/
#eval costW (exchPos (exchPos desequilibre [false, false, true] [true] 2 1)
    [false, false, false] [false, true] 4 1)
-- 16

example : costW (exchPos (exchPos desequilibre [false, false, true] [true] 2 1)
    [false, false, false] [false, true] 4 1) = 16 := by
  decide

/-- Le théorème vit sur la maille du carnet : un arbre de coût ≤ 21, mêmes
feuilles, porte LES DEUX minima (la maille compte deux 1) dans une paire de
sœurs à la profondeur maximale. -/
example : ∃ (t' : WTree) (π : List Bool),
    List.Perm (leafWeights t') (leafWeights desequilibre) ∧
    costW t' ≤ costW desequilibre ∧
    subtreeAt t' π = some (WTree.node (.leaf 1) (.leaf 1)) ∧
    π.length + 1 = maxDepth t' := by
  exact both_mins_to_bottom desequilibre ⟨_, _, rfl⟩ 1 1 (by decide) (by decide)
    (by decide) (by decide)

end CompressionLean
