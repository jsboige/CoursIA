import Mathlib

/-!
# Fonction objectif MIMO — Phase 2 : Lemme 11.1 (coût d'un flip), avec Mathlib

Ce module instancie la fonction objectif du détecteur MIMO à flips
(Papailiopoulos, 2026 — issue #10984) et prouve le **Lemme 11.1** :
le coût d'un flip de coordonnée admet une forme fermée

    f(1⁽ⁱ⁾) − f(1) = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫)

où `s = ρ/N`, `hᵢ` est la i-ème colonne du canal (l'image du i-ème
vecteur de base par l'application linéaire du canal) et `w` le bruit.

Architecture du fichier :

1. `norm_add_sq_two` — Pythagore réel : `‖x + y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`
   (re-dérivé des lemmes de base de Mathlib pour l'autonomie pédagogique) ;
2. `flip_cost` — le cœur géométrique **générique** : dans tout espace de Hilbert
   réel, `‖w + 2√s•h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h,w⟫)` — c'est le Lemme 11.1
   débarrassé de la structure MIMO ;
3. `mimoObj` / `flipAt` — la fonction objectif concrète sur
   `EuclideanSpace ℝ (Fin N)` (canal = application linéaire) et le vecteur de
   déviation d'un flip ;
4. `mimo_flip_cost` — **Lemme 11.1** instancié ;
5. `flip_accepted_iff` — la boucle de contrôle de l'algorithme : un flip est
   accepté ssi le terme `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` est strictement négatif —
   exactement l'hypothèse `hstrict` que consomme la Proposition 9.1 de la
   Phase 1 (`Descent.lean`).

Le Lemme 5.1 (erreur LMMSE `E‖b − x*‖² = E tr(B_ρ)`) et la converse §11
arrivent avec la Phase 3 (lake externe SLT, concentration gaussienne).
-/

namespace Mimo

open InnerProductSpace

section Geometrie

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Pythagore réel** : `‖x + y‖² = ‖x‖² + 2·⟪x, y⟫_ℝ + ‖y‖²`. Redérivé des
lemmes fondamentaux (`inner_add_left/right`, `real_inner_comm`) plutôt
qu'invoqué — chaque étape est lisible par un étudiant. -/
theorem norm_add_sq_two (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h : ∀ z : E, ‖z‖ ^ 2 = ⟪z, z⟫_ℝ := fun z => (real_inner_self_eq_norm_sq z).symm
  rw [h (x + y), h x, h y, inner_add_left, inner_add_right,
    inner_add_right, real_inner_comm y x]
  ring

/-- **Cœur géométrique du Lemme 11.1 (forme générique).** Pour un bruit `w`,
une direction de colonne `h` et un SNR par antenne `s ≥ 0`, le coût du flip
le long de `h` est

    ‖w + 2√s • h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h, w⟫_ℝ).

La quantité entre parenthèses est exactement le **score de flip** : négatif
⟺ le flip diminue strictement la fonction objectif. -/
theorem flip_cost (w h : E) {s : ℝ} (hs : 0 ≤ s) :
    ‖w + (2 * √s) • h‖ ^ 2 - ‖w‖ ^ 2 = 4 * (s * ‖h‖ ^ 2 + √s * ⟪h, w⟫_ℝ) := by
  have key := norm_add_sq_two w ((2 * √s) • h)
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs] at key
  rw [key, mul_pow, sq_abs, mul_pow, Real.sq_sqrt hs]
  rw [real_inner_comm w h]
  ring

end Geometrie

section MIMO

variable {N M : ℕ}

/-- Fonction objectif du détecteur : `obj A w s u = ‖w + √s • A u‖²` où
`A` est l'application linéaire du canal (de l'espace signal `(Fin N → ℝ)`
vers l'espace de mesure `EuclideanSpace ℝ (Fin M)`), `w` le bruit,
`s = ρ/N` le SNR par antenne, et `u` le **vecteur de déviation** par
rapport au point de départ (`u = 1 − x` : zéro = point de départ,
`2eᵢ` = i-ème coordonnée flippée). -/
noncomputable def mimoObj (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) (s : ℝ) (u : Fin N → ℝ) : ℝ :=
  ‖w + √s • A u‖ ^ 2

/-- Le vecteur de déviation du flip de la i-ème coordonnée : `2·eᵢ`
dans l'espace signal. -/
def flipAt (i : Fin N) : Fin N → ℝ :=
  (2 : ℝ) • Pi.single i 1

/-- **Lemme 11.1 (Papailiopoulos 2026) — coût d'un flip.** Passer de la
configuration de départ à la configuration flippée en i change l'objectif de

    Δf = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫_ℝ)

où `hᵢ = A eᵢ` est la i-ème colonne du canal. Forme fermée exacte — la
preuve est l'instanciation du lemme géométrique générique `flip_cost`. -/
theorem mimo_flip_cost (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) - mimoObj A w s 0
      = 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
             + √s * ⟪A (Pi.single i 1), w⟫_ℝ) := by
  have hA : A (flipAt i) = (2 : ℝ) • A (Pi.single i 1) :=
    LinearMap.map_smul A 2 _
  show ‖w + √s • A (flipAt i)‖ ^ 2 - ‖w + √s • A 0‖ ^ 2 = _
  rw [hA, smul_smul, LinearMap.map_zero, smul_zero, add_zero, mul_comm √s 2]
  exact flip_cost w (A (Pi.single i 1)) hs

/-- **Boucle de contrôle de l'algorithme.** Un flip de la i-ème coordonnée
est **accepté** (diminue strictement l'objectif) si et seulement si le score
de flip `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` est strictement négatif. C'est l'hypothèse
`hstrict` que consomme la Proposition 9.1 de la Phase 1 (`Descent.lean`) :
seuls les flips à score négatif sont acceptés, donc le coût décroît
strictement le long du run. -/
theorem flip_accepted_iff (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) < mimoObj A w s 0 ↔
      s * ‖A (Pi.single i 1)‖ ^ 2
        + √s * ⟪A (Pi.single i 1), w⟫_ℝ < 0 := by
  constructor
  · intro hlt
    have h4 : mimoObj A w s (flipAt i) - mimoObj A w s 0 < 0 := sub_neg.mpr hlt
    rw [mimo_flip_cost A w hs i] at h4
    linarith
  · intro hlt
    have h4 : 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
        + √s * ⟪A (Pi.single i 1), w⟫_ℝ) < 0 := by linarith
    rw [← mimo_flip_cost A w hs i] at h4
    exact sub_neg.mp h4

end MIMO

end Mimo
