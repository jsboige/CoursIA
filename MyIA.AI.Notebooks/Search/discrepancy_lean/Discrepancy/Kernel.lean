import Discrepancy.Basic

/-!
# b1 — Noyau dimensionnel de Beck-Fiala

Première boute du grignotage de la « noix » `BeckFialaClassic` (`disc ≤ 2k−1`),
voir `FORMAL_STATUS.md`. Le geste central de la preuve classique de Beck-Fiala
est un argument de **double comptage dimensionnel** : tant qu'il reste des
variables flottantes (non figées à `±1`), les lignes « dangereuses » — celles
qui portent **plus de `k`** flottants — sont moins nombreuses que les
flottants eux-mêmes. La matrice d'incidence `D × X` est donc large : elle
possède un **noyau non trivial**, c'est-à-dire une direction de déplacement
non nulle qui préserve exactement la somme colorée de chaque ligne dangereuse.
C'est ce degré de liberté qui permet de « figer » un nouveau flottant à chaque
phase sans jamais déranger les lignes déjà sous contrôle (b2, b3, b4).

## Seuil « dangereux » : `> k`, pas `≥ k`

Le seuil correct est **strictement supérieur à `k`** flottants. C'est ce qui
rend l'inégalité de double comptage **stricte** :

* chaque ligne dangereuse porte `≥ k+1` flottants, donc `(k+1)·|D| ≤` nombre
  d'incidences `(S, x)` avec `S ∈ D`, `x ∈ X ∩ S` ;
* chaque flottant `x` a un degré `≤ k` dans toute la famille, donc a fortiori
  dans `D` : le nombre d'incidences est `≤ k·|X|` ;
* d'où `(k+1)·|D| ≤ k·|X| < (k+1)·|X|` dès que `X ≠ ∅`, donc `|D| < |X|`.

Avec un seuil `≥ k` on n'obtiendrait que `|D| ≤ |X|` — égalité possible, pas
de noyau garanti. C'est la raison d'être du `k+1` ci-dessous, et de la borne
finale `2k−1` (les lignes quittent le statut dangereux avec `≤ k` flottants,
chacun à distance `< 2` de sa valeur finale `±1`, sur une somme entière).
-/

namespace Discrepancy

section DoubleCounting

variable {α : Type*} [DecidableEq α]

/-- Expansion d'un cardinal d'intersection en somme d'indicateurs sur `X` :
la brique d'échange des sommations du double comptage. -/
private theorem card_inter_eq_sum_ite (X : Finset α) (S : Finset α) :
    (S ∩ X).card = ∑ x ∈ X, if x ∈ S then (1 : ℕ) else 0 := by
  classical
  have hset : X.filter (fun x => x ∈ S) = S ∩ X := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  calc (S ∩ X).card = (X.filter (fun x => x ∈ S)).card := by rw [hset]
    _ = ∑ x ∈ X, if x ∈ S then (1 : ℕ) else 0 := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- **Double comptage dimensionnel (b1, étape 1)** : si `X` est un ensemble
non vide de flottants, chacun de degré `≤ k` dans la famille `F`, alors les
lignes dangereuses — celles contenant plus de `k` éléments de `X` — sont en
nombre **strictement** inférieur aux flottants. -/
theorem card_dangerous_lt_card_floating (F : Finset (Finset α)) (X : Finset α) (k : ℕ)
    (hX : X.Nonempty) (hk : ∀ x ∈ X, degree F x ≤ k) :
    (F.filter fun S => k < (S ∩ X).card).card < X.card := by
  classical
  set D := F.filter fun S => k < (S ∩ X).card with hDdef
  -- Borne inférieure : chaque ligne dangereuse porte au moins k+1 flottants.
  have hlb : (k + 1) * D.card ≤ ∑ S ∈ D, (S ∩ X).card := by
    have hterm : ∀ S ∈ D, (k : ℕ) + 1 ≤ (S ∩ X).card := fun S hS =>
      (Finset.mem_filter.mp hS).2
    calc (k + 1) * D.card = ∑ _S ∈ D, (k + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ S ∈ D, (S ∩ X).card := Finset.sum_le_sum fun S hS => hterm S hS
  -- Échange des sommations (double comptage des incidences).
  have e2 : ∀ x : α, (D.filter fun S => x ∈ S).card
      = ∑ S ∈ D, if x ∈ S then (1 : ℕ) else 0 := by
    intro x
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hswap : ∑ S ∈ D, (S ∩ X).card = ∑ x ∈ X, (D.filter fun S => x ∈ S).card := by
    simp only [card_inter_eq_sum_ite X, e2]
    exact Finset.sum_comm
  -- Borne supérieure : chaque flottant appartient à au plus k lignes de D.
  have hsum : ∑ S ∈ D, (S ∩ X).card ≤ k * X.card := by
    have hDF : D ⊆ F := Finset.filter_subset _ _
    have hub : ∀ x ∈ X, (D.filter fun S => x ∈ S).card ≤ degree F x := fun x _ =>
      Finset.card_le_card (Finset.filter_subset_filter (p := fun S => x ∈ S) hDF)
    calc ∑ S ∈ D, (S ∩ X).card = ∑ x ∈ X, (D.filter fun S => x ∈ S).card := hswap
      _ ≤ ∑ x ∈ X, degree F x := Finset.sum_le_sum hub
      _ ≤ ∑ _x ∈ X, k := Finset.sum_le_sum fun x hx => hk x hx
      _ = k * X.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Assemblage : (k+1)·|D| ≤ k·|X| < (k+1)·|X| donc |D| < |X|.
  have hstrict : k * X.card < (k + 1) * X.card := by
    have hpos : 0 < X.card := Finset.card_pos.2 hX
    rw [Nat.succ_mul]
    omega
  exact Nat.lt_of_mul_lt_mul_left
    (lt_of_le_of_lt (le_trans hlb hsum) hstrict)

end DoubleCounting

section KernelVector

variable {α : Type*} [DecidableEq α]

/-- **b1, étape 2 — existence d'une direction de noyau.** Si les lignes
dangereuses sont moins nombreuses que les flottants (étape 1), la carte
linéaire « sommes des lignes dangereuses » de `ℚ^X` vers `ℚ^D` ne peut être
injective : son noyau contient un vecteur non nul. C'est la direction de
déplacement qui préserve exactement la somme colorée de chaque ligne
dangereuse — le degré de liberté que les phases de Beck-Fiala consomment
une à une (b2, b3). -/
theorem exists_dangerous_kernel_vec (F : Finset (Finset α)) (X : Finset α) (k : ℕ)
    (hX : X.Nonempty) (hk : ∀ x ∈ X, degree F x ≤ k) :
    ∃ v : α → ℚ, (∃ x ∈ X, v x ≠ 0) ∧
      ∀ S ∈ F.filter fun S => k < (S ∩ X).card,
        ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * v x = 0 := by
  classical
  set D := F.filter fun S => k < (S ∩ X).card with hDdef
  -- La carte linéaire « sommes des lignes dangereuses » : (X → ℚ) →ₗ (D → ℚ).
  let f : (X → ℚ) →ₗ[ℚ] (D → ℚ) :=
    { toFun := fun v S => ∑ p ∈ X.attach,
        (if (p : α) ∈ (S : Finset α) then (1 : ℚ) else 0) * v p
      map_add' := by
        intro v w
        funext S
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      map_smul' := by
        intro c v
        funext S
        simp only [Pi.smul_apply, Finset.smul_sum, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring }
  -- Par l'absurde : si 0 est le seul vecteur de somme nulle, f est injective.
  by_contra hno
  push_neg at hno
  have hkerbot : LinearMap.ker f = ⊥ := by
    by_contra hbot
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hbot
    obtain ⟨p, hp⟩ : ∃ p : ↥X, v p ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv0 (funext hall)
    set vext : α → ℚ := fun a => if h : a ∈ X then v ⟨a, h⟩ else 0 with hvext
    have hvX : ∃ x ∈ X, vext x ≠ 0 := ⟨p, p.2, by simp [hvext, hp]⟩
    obtain ⟨S, hSD, hSne⟩ := hno vext hvX
    have hvalext : ∀ p : ↥X, vext ↑p = v p := fun p => by simp [hvext]
    have hsum0 : ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * vext x = 0 := by
      have h0sum : ∑ p ∈ X.attach, (if (p : α) ∈ S then (1 : ℚ) else 0) * v p = 0 :=
        congrFun (LinearMap.mem_ker.mp hv) ⟨S, hSD⟩
      rw [← Finset.sum_attach]
      exact Eq.trans (Finset.sum_congr rfl fun p _ => by rw [hvalext p]) h0sum
    exact hSne hsum0
  have hle := LinearMap.finrank_le_finrank_of_injective
    (LinearMap.ker_eq_bot.mp hkerbot)
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, Fintype.card_coe] at hle
  exact absurd hle (Nat.not_le.mpr (card_dangerous_lt_card_floating F X k hX hk)).elim

end KernelVector

end Discrepancy
