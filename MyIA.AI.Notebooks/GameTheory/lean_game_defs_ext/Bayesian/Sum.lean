/-
  Sommes finies sur `Fin n` (Lean 4 core uniquement, sans Mathlib)
  ==============================================================

  Infrastructure de sommation minimale pour les utilités espérées des
  jeux bayésiens. Le `Finset.sum` de Mathlib n'est pas disponible (projet
  core-only), donc nous définissons une récursion structurelle et prouvons
  les trois lemmes dont le développement de théorie des jeux a besoin :
  monotonie, multiplication scalaire et congruence.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 1).

  ---
  English:
  Finite sums over `Fin n` (core Lean 4 only, no Mathlib)
  =======================================================

  Minimal summation infrastructure for Bayesian game expected utilities.
  Mathlib's `Finset.sum` is not available (core-only project), so we
  define a structural recursion and prove the three lemmas the game
  theory development needs: monotonicity, scalar multiplication, and
  congruence.

  See #2610 (GT-Lean formalization, Bayesian phase 1).
-/

/-- Somme de `f` sur tout `Fin n`, par récursion structurelle sur `n`.
    English: Sum of `f` over all of `Fin n`, by structural recursion on `n`. -/
def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f i.succ)

@[simp] theorem sumFin_zero (f : Fin 0 → Int) : sumFin 0 f = 0 := rfl

@[simp] theorem sumFin_succ (n : Nat) (f : Fin (n + 1) → Int) :
    sumFin (n + 1) f = f 0 + sumFin n (fun i => f i.succ) := rfl

/-- La somme de la fonction nulle s'annule.
    English: The sum of the zero function vanishes. -/
@[simp] theorem sumFin_zero_fun (n : Nat) :
    sumFin n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

/-- La domination point par point se transmet aux sommes.
    English: Pointwise dominance transfers to the sums. -/
theorem sumFin_mono {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    sumFin n f ≤ sumFin n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    exact Int.add_le_add (h 0) (ih (fun i => h i.succ))

/-- Des fonctions égales point par point ont des sommes égales.
    English: Pointwise equal functions have equal sums. -/
theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [h 0, ih (fun i => h i.succ)]

/-- Un facteur constant se distribue hors de la somme.
    English: A constant factor distributes out of the sum. -/
theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [ih, Int.mul_add]

/-- Les sommes se distribuent sur l'addition point par point.
    English: Sums distribute over pointwise addition. -/
theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [ih]
    omega

/-- Les doubles sommes commutent (Fubini pour les sommes finies).
    English: Double sums commute (Fubini for finite sums). -/
theorem sumFin_comm {n m : Nat} (F : Fin n → Fin m → Int) :
    sumFin n (fun i => sumFin m (fun j => F i j)) =
    sumFin m (fun j => sumFin n (fun i => F i j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [ih (fun i j => F i.succ j), ← sumFin_add]

/-- Un `if` dont la condition ne dépend pas de l'indice sort de la somme
    (la branche `else 0` correspond à la somme vide).
    English: An `if` whose condition does not depend on the index pulls out of
    the sum (the `else 0` branch matches the empty sum). -/
theorem sumFin_if_distrib {n : Nat} (c : Prop) [Decidable c] (f : Fin n → Int) :
    sumFin n (fun i => if c then f i else 0) = if c then sumFin n f else 0 := by
  by_cases h : c <;> simp [h]

/-- Sommer un indicateur d'un point unique sélectionne la valeur de ce point.
    English: Summing an indicator of a single point picks out that point's value. -/
theorem sumFin_single : ∀ {n : Nat} (c : Fin n) (x : Fin n → Int),
    sumFin n (fun j => if c = j then x j else 0) = x c
  | 0, c, _ => c.elim0
  | n + 1, c, x => by
    cases c using Fin.cases with
    | zero =>
      have htail : ∀ i : Fin n, (if (0 : Fin (n + 1)) = i.succ then x i.succ else 0) = 0 :=
        fun i => if_neg (fun h => Fin.succ_ne_zero i h.symm)
      simp only [sumFin_succ]
      rw [sumFin_congr htail, sumFin_zero_fun, Int.add_zero]
      simp
    | succ j =>
      simp only [sumFin_succ]
      rw [if_neg (Fin.succ_ne_zero j), Int.zero_add]
      have hcond : ∀ i : Fin n,
          (if j.succ = i.succ then x i.succ else 0) =
          (if j = i then x i.succ else 0) := by
        intro i
        by_cases h : j = i
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (fun hs => h (Fin.succ_inj.mp hs)), if_neg h]
      rw [sumFin_congr hcond, sumFin_single j (fun i => x i.succ)]

/-- Décompose une somme sur les états en groupes indexés par la valeur d'une
    application de classification (double comptage fini).
    English: Decompose a sum over states into groups indexed by the value of a
    classifying map (finite double counting). -/
theorem sumFin_partition {n m : Nat} (σ : Fin n → Fin m) (f : Fin n → Int) :
    sumFin n f = sumFin m (fun k => sumFin n (fun s => if σ s = k then f s else 0)) := by
  rw [sumFin_comm]
  exact (sumFin_congr (fun s => sumFin_single (σ s) (fun _ => f s))).symm
