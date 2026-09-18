/-
  Cible de calibration : espaces de Schwartz — décroissance et régularité
  =======================================================================

  L'espace de Schwartz est l'espace des fonctions lisses dont TOUTES les
  dérivées décroissent plus vite que n'importe quelle puissance de `‖x‖`. Sa
  capacité distinctive est double, et c'est cette dualité que ce module
  enseigne :

  * la RÉGULARITÉ — la lissité `C^∞`, portée par le champ `smooth'` ;
  * la DÉCROISSANCE — le champ `decay'`, qui majore uniformément
    `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` par une constante.

  La famille de seminormes `SchwartzMap.seminorm 𝕜 k n` mesure les deux d'un
  seul geste : `k` indexe la décroissance, `n` l'ordre de dérivation. C'est la
  structure qui rend l'espace muni d'une topologie localement convexe, et
  c'est ce que les théorèmes ci-dessous rendent manipulable.

  Le module instancie l'API Mathlib réellement pinnée par le lake
  (`Mathlib.Analysis.Distribution.SchwartzSpace.Basic`) — aucune définition
  n'est réinventée, aucune preuve n'est laissée en `sorry`.

  Chemins du harnais exercés :
  - Cible S1 (exists_decay_bound) : P3 — le prouveur doit découvrir le lemme
    nommé `SchwartzMap.decay` ; un `simp` nu ne le trouve pas.
  - Cible S2 (seminorm_bounds_decay) : P3 — le lemme nommé
    `SchwartzMap.le_seminorm`, à ne pas confondre avec sa réciproque.
  - Cible S3 (seminorm_le_of_pointwise_bound) : P1 — le pont inverse
    `SchwartzMap.seminorm_le_bound`, avec son hypothèse de positivité.
  - Cible S4 (seminorm_smul) : P3 — l'homogénéité sort du lemme générique
    `SeminormClass.map_smul_eq_mul`, pas de `simp`.
  - Cible S5 (seminorm_add_le) : P1 — la sous-additivité via le champ
    `Seminorm.add_le'`.
  - Cible S6 (norm_le_seminorm_div_pow) : P2 — la décroissance polynômiale
    RÉELLE se déduit de la seminorme ; requiert `le_div_iff₀` puis une
    commutation `mul_comm` (preuve en deux temps, l'erreur est distante).
  - Cible S7 (exists_schwartzMap_of_compactSupport) : P2 — l'énoncé de
    clôture `HasCompactSupport.toSchwartzMap`, avec l'égalité de la fonction
    sous-jacente.

  Difficulté visée : zone de Goldilocks (3-10 itérations du prouveur).
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic

open scoped SchwartzMap ContDiff Topology

namespace Calibration.Distribution

/-! ## 1. Le contrat : décroissance contrôlée par une constante -/

section Decay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Décroissance brute (cible S1).** Pour toute fonction de Schwartz `f` et
tout couple d'indices `(k, n)`, il existe une constante strictement positive
`C` qui majore `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` pour tout `x`.

C'est le champ `decay'` de la structure, raffiné par le lemme `decay` qui
garantit en plus `0 < C` (utile pour diviser). -/
theorem exists_decay_bound (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
  f.decay k n

/-- **Régularité (la première moitié du contrat).** Toute fonction de Schwartz
est lisse à l'ordre infini : c'est le champ `smooth'`, ici lu comme un énoncé
public sur la fonction sous-jacente. -/
theorem smooth_of_schwartz (f : 𝓢(E, F)) : ContDiff ℝ ∞ (f : E → F) :=
  f.smooth'

/-- **La décroissance entraîne l'annulation à l'infini.** C'est le sens
concret de « décroît plus vite que toute puissance » : `f` tend vers `0`
le long du filtre `cocompact`. -/
theorem tendsto_zero_atInfty [ProperSpace E] (f : 𝓢(E, F)) :
    Filter.Tendsto (f : E → F) (Filter.cocompact E) (𝓝 0) :=
  f.tendsto_cocompact

end Decay

/-! ## 2. Les seminormes : mesurer décroissance et régularité d'un seul geste

`SchwartzMap.seminorm 𝕜 k n` est la meilleure constante de l'estimation
`‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C`. Le théorème `le_seminorm` dit qu'elle
la réalise (c'est un majorant), `seminorm_le_bound` qu'elle en est le plus
petit (toute constante qui marche la majore) : les deux moitiés de la
définition par infimum, prises par les deux bouts. -/

section Seminorm

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **La seminorme réalise l'estimation (cible S2).** Pour tout point `x`,
l'estimation de Schwartz est majorée par la seminorme d'indices `(k, n)`.

C'est la moitié « la seminorme est un majorant ». -/
theorem seminorm_bounds_decay (f : 𝓢(E, F)) (k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
  SchwartzMap.le_seminorm 𝕜 k n f x

/-- **La seminorme est le plus petit majorant (cible S3).** Réciproque du
théorème précédent : borner l'estimation en TOUT point par une constante `M`
borne la seminorme par `M`. L'hypothèse `hMp : 0 ≤ M` est indispensable (sans
elle, une constante strictement négative bornerait tout). -/
theorem seminorm_le_of_pointwise_bound (f : 𝓢(E, F)) (k n : ℕ) {M : ℝ}
    (hMp : 0 ≤ M)
    (hM : ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) :
    SchwartzMap.seminorm 𝕜 k n f ≤ M :=
  SchwartzMap.seminorm_le_bound 𝕜 k n f hMp hM

/-- **Homogénéité (cible S4).** Le scalaire sort multiplicativement, en norme,
de la seminorme. C'est l'axiome `SMul` de `Seminorm`, lu par le lemme
générique `SeminormClass.map_smul_eq_mul`. -/
theorem seminorm_smul (c : 𝕜) (f : 𝓢(E, F)) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n (c • f) = ‖c‖ * SchwartzMap.seminorm 𝕜 k n f :=
  map_smul_eq_mul (SchwartzMap.seminorm 𝕜 k n) c f

/-- **Sous-additivité (cible S5).** Une seminorme n'est pas additive, elle est
sous-additive : l'inégalité triangulaire est un axiome de la structure, lu par
le champ `Seminorm.add_le'`. -/
theorem seminorm_add_le (f g : 𝓢(E, F)) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n (f + g) ≤
      SchwartzMap.seminorm 𝕜 k n f + SchwartzMap.seminorm 𝕜 k n g :=
  (SchwartzMap.seminorm 𝕜 k n).add_le' f g

/-- **Décroissance polynômiale effective (cible S6).** La seminorme d'indices
`(k, 0)` — décroissance d'ordre `k`, aucune dérivée — fournit une décroissance
POLYNÔMIALE de la fonction elle-même : hors de l'origine,

  `‖f x‖ ≤ C_k / ‖x‖^k`.

La preuve déplace `‖x‖^k` au dénominateur (`le_div_iff₀`, l'hypothèse
`0 < ‖x‖` est ce qui l'autorise), puis commute les deux facteurs pour
retomber sur `norm_pow_mul_le_seminorm`. -/
theorem norm_le_seminorm_div_pow (f : 𝓢(E, F)) (k : ℕ) {x : E} (hx : 0 < ‖x‖) :
    ‖f x‖ ≤ SchwartzMap.seminorm 𝕜 k 0 f / ‖x‖ ^ k := by
  rw [le_div_iff₀ (pow_pos hx k)]
  exact (mul_comm _ _).trans_le (SchwartzMap.norm_pow_mul_le_seminorm 𝕜 f k x)

/-- **La seminorme `(0, 0)` majore la norme uniforme.** Cas particulier
`k = 0` du théorème précédent, sans hypothèse : partout,
`‖f x‖ ≤ seminorm 𝕜 0 0 f`. C'est la seminorme qui contrôle le sup de `f`. -/
theorem norm_le_seminorm_zero (f : 𝓢(E, F)) (x : E) :
    ‖f x‖ ≤ SchwartzMap.seminorm 𝕜 0 0 f :=
  SchwartzMap.norm_le_seminorm 𝕜 f x

end Seminorm

/-! ## 3. Clôture : le support compact fabrique des fonctions de Schwartz -/

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Une fonction lisse à support compact est de Schwartz (cible S7).** La
clôture de la classe est un fait du support compact : hors du support, la
fonction est nulle, donc la décroissance est gagnée sans hypothèse.

La conclusion témoigne EN PLUS de la préservation de la fonction sous-jacente
— `toSchwartzMap` ne change pas la fonction, il l'habille du contrat. -/
theorem exists_schwartzMap_of_compactSupport {f : E → F}
    (hsupp : HasCompactSupport f) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ g : 𝓢(E, F), (g : E → F) = f :=
  ⟨hsupp.toSchwartzMap hsmooth, rfl⟩

end CompactSupport

end Calibration.Distribution
