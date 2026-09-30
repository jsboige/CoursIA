import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# L'anneau des entiers de Q(ζ₁₃) est principal

Ce module prouve que si `K` est un corps tel que `IsCyclotomicExtension {13} ℚ K`
(c'est-à-dire `K = ℚ(ζ₁₃)`, le 13-ième corps cyclotomique), alors son anneau
d'entiers `⸜ K = ℤ[ζ₁₃]` est un anneau principal (PID).

**Adaptation pédagogique** : ce fichier est un port du dépôt
`anthropics/fermats-last-theorem` (fichier
`P2M/Sol/S_IsCyclotomicExtension_Rat_thirteen_pid.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`). Les énoncés et preuves sont
repris tels quels ; la documentation pédagogique et le sibling anglais
`ThirteenPid_en.lean` sont des additions CoursIA. La licence Apache-2.0 est
préservée (voir `NOTICE.md`). Les deux sous-namespaces de l'amont
(`M3dS11`, `M3aS12`) sont conservés pour isoler les deux `Fact (Nat.Prime 13)`
homonymes.

## La stratégie

Comme pour `seven_pid` et `eleven_pid`, la borne de Minkowski vaut ici
`⌊M K⌋₊ < 307` (lemmes `crazy13` / `M13` : approximations de `π` à 20
décimales et encadrement de `√1792160394037` par `norm_num`), et le critère
de Marcus `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_...`
réduit la question aux premiers `p ∈ {2, …, 306}` : pour chacun, il faut un
idéal premier `P` au-dessus de `p` tel que `⌊M K⌋₊ < p ^ f` (où `f` est le
degré d'inertie) **ou** `P` principal.

1. **`p = 3`** (lemme `isPrincipal_of_liesOver_three`) : le corps `F₂₇ =
   AdjoinRoot (X³ - X - 1)` sur `ZMod 3` fournit le morphisme `⸜ K → F₂₇`
   envoyant `ζ₁₃` sur une racine de `X³ - X - 1` ; son noyau est
   `span {α}` avec `α = 1 + ζ - ζ³`, via l'identité `α * β = 3` et un
   argument galoisien (`exists_smul_eq_of_isGaloisGroup`) ;
2. **`p ∈ {13, 53, 79, 131, 157}`** : le certificat générique
   `span_mem_primesOver_of_cert` exhibe pour chacun un générateur explicite
   (image de `ζ₁₃` dans `ZMod q`, polynôme `A` et témoins `b`, `c` avec
   `α * b = q` et `α * c = ζ - r`) ;
3. **les autres `p`** : leur degré d'inertie (ordre de `p` dans
   `(ZMod 13)ˣ`, lemme `exists_primesOver_lt`) donne `p ^ f ≥ p² > 306`
   dans chaque tranche — les lemmes `dispatchA`/`dispatchB`/`dispatchC`/
   `dispatchD` épuisent les quatre tranches `{2, …, 80}`, `{81, …, 160}`,
   `{161, …, 240}`, `{241, …, 306}` par `interval_cases`.
-/

set_option autoImplicit false

namespace CyclotomicPID

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
open NumberField.RingOfIntegers Finset IsCyclotomicExtension.Rat Polynomial
open Real.Polynomial Polynomial.cyclotomic Ideal NumberField.Ideal

open scoped NumberField NumberField.InfinitePlace.NumberField Pointwise
namespace M3dS11

/-- `13` est premier, en instance `Fact` pour les lemmes de Mathlib. -/
scoped instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- Le polynôme `X³ - X - 1` sur `ZMod 3` : irréductible, il définit le corps
`F₂₇` dans lequel `ζ₁₃` s'envoie sur une racine. -/
noncomputable def g3 : Polynomial (ZMod 3) := X ^ 3 - X - 1

theorem g3_natDegree : g3.natDegree = 3 := by
  rw [g3]; compute_degree!

theorem g3_irreducible : Irreducible g3 := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [g3_natDegree]; decide) ?_
  intro x hx
  rw [IsRoot.def, g3, eval_sub, eval_sub, eval_pow, eval_X, eval_one] at hx
  fin_cases x <;> revert hx <;> decide

scoped instance fact_irreducible_g3 : Fact (Irreducible g3) := ⟨g3_irreducible⟩

/-- Le corps à 27 éléments, construit comme `AdjoinRoot g3` : l'image de
`ζ₁₃` pour le premier `p = 3`. -/
abbrev F27 : Type := AdjoinRoot g3

theorem F27_root : (AdjoinRoot.root g3) ^ 3 - AdjoinRoot.root g3 - 1 = 0 := by
  have := AdjoinRoot.eval₂_root g3
  rw [g3, eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_one] at this
  exact this

theorem F27_three : (3 : F27) = 0 := by
  have h : (3 : ZMod 3) = 0 := rfl
  rw [← map_ofNat (algebraMap (ZMod 3) F27) 3, h, map_zero]

scoped instance F27_charP : CharP F27 3 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 3) F27).injective 3

variable {K : Type*} [Field K] [NumberField K] [hK : IsCyclotomicExtension {13} ℚ K]

/-- Tout idéal premier de `⸜ K` au-dessus de `3` est principal : son
générateur est l'image galoisienne de `α = 1 + ζ - ζ³`, qui engendre le noyau
du morphisme `⸜ K → F₂₇` envoyant `ζ₁₃` sur la racine de `X³ - X - 1`. -/
theorem isPrincipal_of_liesOver_three (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    [hP3 : P.LiesOver (span {(3 : ℤ)})] : Submodule.IsPrincipal P := by
  have hζ := hK.zeta_spec
  set z : 𝓞 K := hζ.toInteger with hz

  have hrel : z ^ 12 + z ^ 11 + z ^ 10 + z ^ 9 + z ^ 8 + z ^ 7 + z ^ 6 + z ^ 5 + z ^ 4 + z ^ 3
      + z ^ 2 + z + 1 = 0 := by
    have h := hζ.geom_sum_eq_zero (by norm_num : 1 < 13)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero] at h
    have hzK : algebraMap (𝓞 K) K z = IsCyclotomicExtension.zeta 13 ℚ K := by
      rw [hz]; rfl
    refine (map_eq_zero_iff (algebraMap (𝓞 K) K) (RingOfIntegers.coe_injective)).mp ?_
    simp only [map_add, map_pow, map_one, hzK]
    linear_combination h

  set r : F27 := AdjoinRoot.root g3 with hr
  have hgr : r ^ 3 - r - 1 = 0 := F27_root
  let pb := hζ.integralPowerBasis
  have hgen : pb.gen = z := by rw [hz]; exact hζ.integralPowerBasis_gen
  have hmin : minpoly ℤ pb.gen = cyclotomic 13 ℤ := by
    rw [hgen, hz, cyclotomic_eq_minpoly hζ (by norm_num)]
    exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hζ.toInteger).symm
  have hrΦ : aeval r (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]

    linear_combination (r ^ 9 + r ^ 8 + 2 * r ^ 7 + 3 * r ^ 6 + 4 * r ^ 5 + 6 * r ^ 4 + 8 * r ^ 3
      + 11 * r ^ 2 + 15 * r + 20) * hgr + (9 * r ^ 2 + 12 * r + 7) * F27_three
  let f : 𝓞 K →ₐ[ℤ] F27 := pb.lift r hrΦ
  have hfz : f z = r := by rw [← hgen]; exact pb.lift_gen r hrΦ

  set P₀ : Ideal (𝓞 K) := RingHom.ker f.toRingHom with hP₀
  haveI hP₀prime : P₀.IsPrime := RingHom.ker_isPrime _
  haveI hP₀over : P₀.LiesOver (span {(3 : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_def, hP₀, RingHom.comap_ker]
    have : f.toRingHom.comp (algebraMap ℤ (𝓞 K)) = Int.castRingHom F27 := RingHom.ext_int _ _
    rw [this]
    ext n
    rw [RingHom.mem_ker, Int.coe_castRingHom, CharP.intCast_eq_zero_iff F27 3,
      Ideal.mem_span_singleton]
    norm_num

  set α : 𝓞 K := 1 + z - z ^ 3 with hα
  set β : 𝓞 K := -3 * z ^ 10 + z ^ 9 - 2 * z ^ 8 - z ^ 7 - 2 * z ^ 5 - z ^ 3 - z ^ 2 - 1 with hβ
  have hαβ : α * β = 3 := by
    rw [hα, hβ]; linear_combination (3 * z - 4) * hrel

  have hP₀eq : P₀ = span {α} := by
    apply le_antisymm
    · intro x hx
      have hx0 : f x = 0 := hx
      obtain ⟨b, rfl⟩ := pb.exists_eq_aeval' x
      rw [pb.lift_aeval r hrΦ] at hx0

      set G : ℤ[X] := X ^ 3 - X - 1 with hG
      have hGm : G.Monic := by rw [hG]; monicity!
      have hGdeg : G.degree = 3 := by rw [hG]; compute_degree!
      set ρ : ℤ[X] := b %ₘ G with hρ
      set t : ℤ[X] := b /ₘ G with ht
      have hb : b = G * t + ρ := by rw [hρ, ht, add_comm, modByMonic_add_div b G]
      have hρdeg : ρ.degree < 3 := by rw [hρ, ← hGdeg]; exact degree_modByMonic_lt b hGm

      have hGr : aeval r G = 0 := by
        rw [hG]; simp only [map_sub, map_pow, aeval_X, map_one]; exact hgr
      have hρr : aeval r ρ = 0 := by
        rw [hb, map_add, map_mul, hGr, zero_mul, zero_add] at hx0; exact hx0

      have hρbar : ρ.map (Int.castRingHom (ZMod 3)) = 0 := by
        have h1 : aeval r (ρ.map (algebraMap ℤ (ZMod 3))) = 0 := by
          rw [aeval_map_algebraMap]; exact hρr
        rw [hr, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h1
        refine Polynomial.eq_zero_of_dvd_of_degree_lt h1 ?_
        calc (ρ.map (Int.castRingHom (ZMod 3))).degree ≤ ρ.degree := degree_map_le
          _ < 3 := hρdeg
          _ = g3.degree := by rw [show g3.degree = 3 from by rw [g3]; compute_degree!]
      have hρ3 : C (3 : ℤ) ∣ ρ := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (fun q => q.coeff i) hρbar
        simp only [coeff_map, Int.coe_castRingHom, coeff_zero] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
      obtain ⟨ρ', hρ'⟩ := hρ3

      have ex : aeval pb.gen b = (z ^ 3 - z - 1) * aeval z t + 3 * aeval z ρ' := by
        rw [hgen, hb, hρ', map_add, map_mul, map_mul, aeval_C, map_ofNat, hG]
        simp only [map_sub, map_pow, aeval_X, map_one]
      rw [ex]
      refine Ideal.mem_span_singleton'.mpr ⟨-aeval z t + β * aeval z ρ', ?_⟩
      rw [hα]
      linear_combination (aeval z ρ') * hαβ
    · rw [span_le, Set.singleton_subset_iff]
      show f α = 0
      rw [hα]
      simp only [map_add, map_sub, map_pow, map_one, hfz]
      linear_combination (-1 : F27) * hgr

  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {(13 : ℕ)} ℚ K
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (span {(3 : ℤ)}) P₀ P Gal(K/ℚ)
  refine ⟨⟨σ • α, ?_⟩⟩
  rw [← hσ, hP₀eq, Ideal.submodule_span_eq, Ideal.smul_closure, Set.smul_set_singleton]

end M3dS11

/-- Reformulation : tout idéal de `primesOver 3` est principal. -/
theorem isPrincipal_of_mem_primesOver_three (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {13} ℚ K] (P : Ideal (𝓞 K))
    (hP : P ∈ primesOver (Ideal.span {((3 : ℕ) : ℤ)}) (𝓞 K)) : Submodule.IsPrincipal P := by
  have h3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
  haveI := hP.1
  haveI : P.LiesOver (span {(3 : ℤ)}) := by rw [← h3]; exact hP.2
  exact M3dS11.isPrincipal_of_liesOver_three P

/-- Il existe un idéal au-dessus de `3`, et il est principal. -/
theorem exists_primesOver_three_isPrincipal (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K] : ∃ P ∈ primesOver (Ideal.span {((3 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
  have h3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
  haveI : (Ideal.span {((3 : ℕ) : ℤ)}).IsPrime := by
    rw [h3, Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_three
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) (Ideal.span {((3 : ℕ) : ℤ)})
  exact ⟨P, hP, isPrincipal_of_mem_primesOver_three K P hP⟩

namespace M3aS12
section cert

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  {ζ : K}

/-- **Certificat d'idéal premier principal.** Si `q` est premier, `Φₙ(r) ≡ 0
mod q` et `A(r) ≡ 0 mod q`, et si dans `⸜ K` on sait écrire `α * b = q` et
`α * c = ζ - r` (avec `α = A(ζ)`), alors `span {α}` est un idéal premier
au-dessus de `q` — donc un idéal principal de `primesOver q`. C'est le
mécanisme des cinq certificats explicites de `thirteen_pid`. -/
theorem span_mem_primesOver_of_cert (hζ : IsPrimitiveRoot ζ n) (q : ℕ) [hq : Fact q.Prime]
    (r : ℤ) (hr : (q : ℤ) ∣ (cyclotomic n ℤ).eval r)
    (A : ℤ[X]) (hA : (q : ℤ) ∣ A.eval r) (b c : 𝓞 K)
    (hB : aeval hζ.toInteger A * b = (q : 𝓞 K))
    (hC : aeval hζ.toInteger A * c = hζ.toInteger - (r : 𝓞 K)) :
    Ideal.span {aeval hζ.toInteger A} ∈ primesOver (Ideal.span {(q : ℤ)}) (𝓞 K) := by
  classical
  set θ := hζ.toInteger with hθdef
  let pb := hζ.integralPowerBasis
  have hgen : pb.gen = θ := hζ.integralPowerBasis_gen
  have hmin : minpoly ℤ pb.gen = cyclotomic n ℤ := by
    rw [hgen, ← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ]
    exact (cyclotomic_eq_minpoly hζ (NeZero.pos n)).symm
  have hcast : ((r : ℤ) : ZMod q) = algebraMap ℤ (ZMod q) r := (eq_intCast _ r).symm
  have hy : aeval ((r : ℤ) : ZMod q) (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, hcast, aeval_algebraMap_apply_eq_algebraMap_eval, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hr
  let toZMod : 𝓞 K →ₐ[ℤ] ZMod q := pb.lift _ hy
  have htoZModθ : toZMod θ = (r : ZMod q) := by rw [← hgen]; exact pb.lift_gen _ hy
  have htoZModq : ∀ F : ℤ[X], toZMod (aeval θ F) = 0 ↔ (q : ℤ) ∣ F.eval r := fun F ↦ by
    rw [← aeval_algHom_apply, htoZModθ, hcast, aeval_algebraMap_apply_eq_algebraMap_eval, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  set α := aeval θ A with hαdef
  have hqα : (q : 𝓞 K) ∈ Ideal.span {α} :=
    Ideal.mem_span_singleton'.mpr ⟨b, by rw [mul_comm]; exact hB⟩
  have hθα : θ - (r : 𝓞 K) ∈ Ideal.span {α} :=
    Ideal.mem_span_singleton'.mpr ⟨c, by rw [mul_comm]; exact hC⟩
  have hker : RingHom.ker toZMod = Ideal.span {α} := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      obtain ⟨F, rfl⟩ := pb.exists_eq_aeval' x
      rw [hgen] at hx ⊢
      obtain ⟨m, hm⟩ := (htoZModq F).mp hx
      have hdec : F = C (F.eval r) + (X - C r) * (F /ₘ (X - C r)) := by
        conv_lhs => rw [← modByMonic_add_div F (X - C r), modByMonic_X_sub_C_eq_C_eval]
      rw [hdec, hm]
      simp only [map_add, map_mul, map_sub, aeval_C, aeval_X]
      simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hqα) (Ideal.mul_mem_right _ _ hθα)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact (htoZModq A).mpr hA
  have hprime : (Ideal.span {α}).IsPrime := by rw [← hker]; exact RingHom.ker_isPrime _
  refine ⟨hprime, ⟨?_⟩⟩
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq.out).irreducible
  refine hmax.eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  show algebraMap ℤ (𝓞 K) q ∈ Ideal.span {α}
  rw [map_natCast]
  exact hqα

/-- Si l'ordre de `p` dans `(ZMod n)ˣ` est au moins `k` et que `N < p ^ k`,
alors tout idéal au-dessus de `p` a un degré d'inertie `f` avec `N < p ^ f` :
le lemme sert à éliminer les premiers dont aucun idéal au-dessus n'est
contraint par la borne de Minkowski. -/
theorem exists_primesOver_lt (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [hp : Fact p.Prime] (hpn : ¬ p ∣ n) (N k : ℕ)
    (hN : N < p ^ k) (hk : ∀ j < k, 0 < j → (p : ZMod n) ^ j ≠ 1) :
    ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      N < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := this.isPrime
  obtain ⟨⟨P, hP⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, hP, Or.inl ?_⟩
  haveI := hP.1
  haveI := hP.2
  have hf := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P (m := n) hpn
  have hpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hkle : k ≤ P.inertiaDeg ℤ := by
    by_contra h
    push Not at h
    exact hk _ h hpos (by rw [hf]; exact pow_orderOf_eq_one _)
  calc N < p ^ k := hN
    _ ≤ p ^ _ := Nat.pow_le_pow_right hp.out.pos hkle

end cert

section thirteen

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- Encadrement numérique : la borne de Minkowski de `ℚ(ζ₁₃)` est `< 307`
(`π` approché à 20 décimales, `√1792160394037 < 1338718`). -/
lemma crazy13 : ⌊(4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037)⌋₊ < 307 := by
  rw [Nat.floor_lt (by positivity)]
  calc
    _ < (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
      gcongr; exact pi_gt_d20
    _ ≤ (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * 1338718) := by
      gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
    _ < 307 := by norm_num

/-- `13` est premier, en instance `Fact` pour les lemmes de Mathlib. -/
scoped instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K]

/-- La partie entière de la borne de Minkowski de `ℚ(ζ₁₃)` est `< 307`
(discriminant `13^11 = 1792160394037`, rang 12, 6 places complexes). -/
theorem M13 : ⌊(M K)⌋₊ < 307 := by
  rw [discr_prime 13 K, IsCyclotomicExtension.finrank (n := 13) K
    (cyclotomic.irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 13, totient_prime
      (p := 13) (by norm_num)]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, one_mul, Int.cast_ofNat, abs_ofNat]
  exact crazy13

/-- Tranche `{1, …, 80}` : seuls `3`, `13`, `53` et `79` exigent un idéal
principal ; les autres premiers ont un degré d'inertie suffisant. -/
theorem dispatchA (N : ℕ) (hN : N < 307) (h3 : ∃ P ∈ primesOver (Ideal.span {((3 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P) (h13 : ∃ P ∈ primesOver (Ideal.span {((13 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P) (h53 : ∃ P ∈ primesOver (Ideal.span {((53 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P) (h79 : ∃ P ∈ primesOver (Ideal.span {((79 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P)
    (p : ℕ) [hpF : Fact p.Prime] (hp1 : 1 ≤ p) (hp2 : p ≤ 80) :
    ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      N < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have hpp : p.Prime := hpF.out
  interval_cases p
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 9 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · exact let ⟨P, hP, hpr⟩ := h3; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 4 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 3 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 3 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact let ⟨P, hP, hpr⟩ := h13; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 3 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact let ⟨P, hP, hpr⟩ := h53; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact let ⟨P, hP, hpr⟩ := h79; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp

/-- Tranche `{81, …, 160}` : seuls `131` et `157` exigent un idéal principal. -/
theorem dispatchB (N : ℕ) (hN : N < 307) (h131 : ∃ P ∈ primesOver (Ideal.span {((131 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P) (h157 : ∃ P ∈ primesOver (Ideal.span {((157 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P)
    (p : ℕ) [hpF : Fact p.Prime] (hp1 : 81 ≤ p) (hp2 : p ≤ 160) :
    ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      N < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have hpp : p.Prime := hpF.out
  interval_cases p
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact let ⟨P, hP, hpr⟩ := h131; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact let ⟨P, hP, hpr⟩ := h157; ⟨P, hP, Or.inr hpr⟩
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp

/-- Tranche `{161, …, 240}` : aucun premier n'exige d'idéal principal. -/
theorem dispatchC (N : ℕ) (hN : N < 307)
    (p : ℕ) [hpF : Fact p.Prime] (hp1 : 161 ≤ p) (hp2 : p ≤ 240) :
    ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      N < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have hpp : p.Prime := hpF.out
  interval_cases p
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp

/-- Tranche `{241, …, 306}` : aucun premier n'exige d'idéal principal. -/
theorem dispatchD (N : ℕ) (hN : N < 307)
    (p : ℕ) [hpF : Fact p.Prime] (hp1 : 241 ≤ p) (hp2 : p ≤ 306) :
    ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      N < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have hpp : p.Prime := hpF.out
  interval_cases p
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · exact exists_primesOver_lt 13 K _ (by norm_num) _ 2 (lt_of_lt_of_le hN (by norm_num)) (by decide)
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp
  · norm_num at hpp

/-- **`ℤ[ζ₁₃]` est un anneau principal.** Le critère de Marcus
(`isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_...`) réduit la
question aux premiers `p < 307` : `3` par le lemme `F₂₇`, `13` (le ramifié),
`53`, `79`, `131` et `157` par certificats explicites
(`span_mem_primesOver_of_cert`), tous les autres par degré d'inertie
(`exists_primesOver_lt`, dispatch A-D). -/
theorem thirteen_pid : IsPrincipalIdealRing (𝓞 K) := by
  haveI := IsCyclotomicExtension.isGalois {13} ℚ K
  have hζ := IsCyclotomicExtension.zeta_spec 13 ℚ K
  set θ : 𝓞 K := hζ.toInteger with hθ
  have hΦ : 1 + θ + θ ^ 2 + θ ^ 3 + θ ^ 4 + θ ^ 5 + θ ^ 6 + θ ^ 7 + θ ^ 8 + θ ^ 9 + θ ^ 10 + θ ^ 11 + θ ^ 12 = 0 := by
    have h := hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by norm_num : 1 < 13)
    simpa [Finset.sum_range_succ, ← hθ] using h
  have h3 := exists_primesOver_three_isPrincipal K
  have h13 : ∃ P ∈ primesOver (Ideal.span {((13 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    refine ⟨_, span_mem_primesOver_of_cert hζ 13 1 ?_ (X - 1) ?_
      (-12 - 11 * θ - 10 * θ ^ 2 - 9 * θ ^ 3 - 8 * θ ^ 4 - 7 * θ ^ 5 - 6 * θ ^ 6 - 5 * θ ^ 7 - 4 * θ ^ 8 - 3 * θ ^ 9 - 2 * θ ^ 10 - θ ^ 11)
      (1) ?_ ?_, ⟨_, rfl⟩⟩
    · rw [cyclotomic_prime, eval_finsetSum]
      simp
    · simp only [eval_sub, eval_X, eval_one]
      norm_num
    · simp only [map_sub, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (-1) * hΦ
    · simp only [map_sub, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (0) * hΦ
  have h53 : ∃ P ∈ primesOver (Ideal.span {((53 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
    haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    refine ⟨_, span_mem_primesOver_of_cert hζ 53 36 ?_ (X ^ 3 + X + 1) ?_
      (1 - 24 * θ - 35 * θ ^ 2 - 25 * θ ^ 3 - 10 * θ ^ 4 - 14 * θ ^ 5 - 20 * θ ^ 6 - 29 * θ ^ 7 - 16 * θ ^ 8 - 23 * θ ^ 9 - 7 * θ ^ 10 - 36 * θ ^ 11)
      (17 * θ + 24 * θ ^ 2 + 17 * θ ^ 3 + 7 * θ ^ 4 + 10 * θ ^ 5 + 14 * θ ^ 6 + 20 * θ ^ 7 + 11 * θ ^ 8 + 16 * θ ^ 9 + 5 * θ ^ 10 + 25 * θ ^ 11) ?_ ?_, ⟨_, rfl⟩⟩
    · rw [cyclotomic_prime, eval_finsetSum]
      simp only [eval_pow, eval_X, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · simp only [eval_add, eval_pow, eval_X, eval_one]
      norm_num
    · simp only [map_add, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (-52 + 29 * θ - 36 * θ ^ 2) * hΦ
    · simp only [map_add, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (36 - 20 * θ + 25 * θ ^ 2) * hΦ
  have h79 : ∃ P ∈ primesOver (Ideal.span {((79 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
    haveI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    refine ⟨_, span_mem_primesOver_of_cert hζ 79 52 ?_ (X ^ 4 + X ^ 2 + X + 1) ?_
      (-15 - 32 * θ - 46 * θ ^ 2 - 25 * θ ^ 3 - 17 * θ ^ 4 - 29 * θ ^ 5 - 11 * θ ^ 6 - 38 * θ ^ 7 - 37 * θ ^ 8 + θ ^ 9 - 56 * θ ^ 10 - 10 * θ ^ 11)
      (10 + 21 * θ + 30 * θ ^ 2 + 16 * θ ^ 3 + 11 * θ ^ 4 + 19 * θ ^ 5 + 7 * θ ^ 6 + 25 * θ ^ 7 + 24 * θ ^ 8 - θ ^ 9 + 37 * θ ^ 10 + 6 * θ ^ 11) ?_ ?_, ⟨_, rfl⟩⟩
    · rw [cyclotomic_prime, eval_finsetSum]
      simp only [eval_pow, eval_X, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · simp only [eval_add, eval_pow, eval_X, eval_one]
      norm_num
    · simp only [map_add, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (-94 + 47 * θ - 46 * θ ^ 2 - 10 * θ ^ 3) * hΦ
    · simp only [map_add, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (62 - 32 * θ + 31 * θ ^ 2 + 6 * θ ^ 3) * hΦ
  have h131 : ∃ P ∈ primesOver (Ideal.span {((131 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
    haveI : Fact (Nat.Prime 131) := ⟨by norm_num⟩
    refine ⟨_, span_mem_primesOver_of_cert hζ 131 113 ?_ (-X ^ 3 + X ^ 2 + 1) ?_
      (-13 - 5 * θ - 20 * θ ^ 2 - 41 * θ ^ 3 - 18 * θ ^ 4 - 12 * θ ^ 5 - 56 * θ ^ 6 - 39 * θ ^ 7 + 11 * θ ^ 8 - 50 * θ ^ 9 - 83 * θ ^ 10 + 28 * θ ^ 11)
      (11 + 4 * θ + 17 * θ ^ 2 + 35 * θ ^ 3 + 15 * θ ^ 4 + 10 * θ ^ 5 + 48 * θ ^ 6 + 33 * θ ^ 7 - 10 * θ ^ 8 + 43 * θ ^ 9 + 71 * θ ^ 10 - 25 * θ ^ 11) ?_ ?_, ⟨_, rfl⟩⟩
    · rw [cyclotomic_prime, eval_finsetSum]
      simp only [eval_pow, eval_X, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · simp only [eval_add, eval_neg, eval_pow, eval_X, eval_one]
      norm_num
    · simp only [map_add, map_neg, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (-144 + 139 * θ - 28 * θ ^ 2) * hΦ
    · simp only [map_add, map_neg, map_pow, aeval_X, map_one, ← hθ]
      push_cast
      linear_combination (124 - 121 * θ + 25 * θ ^ 2) * hΦ
  have h157 : ∃ P ∈ primesOver (Ideal.span {((157 : ℕ) : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
    haveI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    refine ⟨_, span_mem_primesOver_of_cert hζ 157 39 ?_ (X ^ 4 + X ^ 3 + 2 * X ^ 2 + 2 * X + 1) ?_
      (-76 - 86 * θ - 46 * θ ^ 2 - 49 * θ ^ 3 - 37 * θ ^ 4 - 85 * θ ^ 5 - 50 * θ ^ 6 - 33 * θ ^ 7 - 101 * θ ^ 8 + 14 * θ ^ 9 - 132 * θ ^ 10 - 19 * θ ^ 11)
      (19 + 21 * θ + 11 * θ ^ 2 + 12 * θ ^ 3 + 9 * θ ^ 4 + 21 * θ ^ 5 + 12 * θ ^ 6 + 8 * θ ^ 7 + 25 * θ ^ 8 - 4 * θ ^ 9 + 33 * θ ^ 10 + 4 * θ ^ 11) ?_ ?_, ⟨_, rfl⟩⟩
    · rw [cyclotomic_prime, eval_finsetSum]
      simp only [eval_pow, eval_X, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · simp only [eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
      norm_num
    · simp only [map_add, map_mul, map_pow, aeval_X, map_one, map_ofNat, ← hθ]
      push_cast
      linear_combination (-233 - 5 * θ - 132 * θ ^ 2 - 19 * θ ^ 3) * hΦ
    · simp only [map_add, map_mul, map_pow, aeval_X, map_one, map_ofNat, ← hθ]
      push_cast
      linear_combination (58 + 33 * θ ^ 2 + 4 * θ ^ 3) * hΦ
  have hM := M13 K
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    (fun p hp hpp ↦ ?_)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp306 : p ≤ 306 := by have := (Finset.mem_Icc.mp hp).2; omega
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp).1
  by_cases hA : p ≤ 80
  · exact dispatchA K _ hM h3 h13 h53 h79 p hp1 hA
  by_cases hB : p ≤ 160
  · exact dispatchB K _ hM h131 h157 p (by omega) hB
  by_cases hC : p ≤ 240
  · exact dispatchC K _ hM p (by omega) hC
  · exact dispatchD K _ hM p (by omega) hp306
end thirteen
end M3aS12

end CyclotomicPID
