import Mathlib

/-!
# Coherence.Basic — événements, prix, tickets (de Finetti)

Fondations de l'argument du Dutch Book. Un agent qui parie attribue un prix unitaire
`q A` à chaque événement `A` (un ticket qui paie 1 € si `A` se réalise) ; l'agent
achète ET vend au même prix `q A` (pas de spread bid–ask). Le théorème de de Finetti
(cas fini) dit que des prix violant les axiomes de probabilité exposent l'agent à un
*Dutch Book* — un livret de paris garantissant une perte sûre. Voir `DutchBook.lean`.

C'est la fondation conceptuelle du *pourquoi* des probabilités (additives, normalisées)
plutôt que des fonctions de croyance arbitraires : la cohérence *force* les axiomes
de Kolmogorov. Pédagogiquement, ce module répond à la question fondatrice de toute la
série Probas : « pourquoi `P(A∪B) = P(A) + P(B) − P(A∩B)` ? » — parce que sinon, un
arbitragiste construit un pari à perte sûre.

Références croisées :
- Infer-14 (Infer.NET) : espérance d'utilité bayésienne sous incertitude sur la postérieure.
- PyMC-14 (PyMC) : estimation d'utilité espérée par échantillonnage postérieur.
-/

namespace Coherence

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Un événement est un ensemble fini d'états du monde. -/
abbrev Event (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Finset Ω

/-- Une fonction de prix (quotient de pari) : `q A` est le prix unitaire (en €) d'un
    ticket payant 1 € si l'événement `A` se réalise. L'agent achète et vend au même
    prix `q A` (pas de spread) — le cadre standard de de Finetti. -/
abbrev Price (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Event Ω → ℝ

/-- L'indicatrice `𝟙_{ω ∈ A}` comme un réel (1 si l'état `ω` réalise `A`, 0 sinon). -/
def ind (A : Event Ω) (ω : Ω) : ℝ := if ω ∈ A then 1 else 0

/-- Identité d'inclusion–exclusion pour les indicatrices :
    `𝟙_A + 𝟙_B − 𝟙_{A∩B} − 𝟙_{A∪B} = 0` en tout état `ω`.

    C'est la clé de voûte du Dutch Book : elle rend le gain des quatre tickets
    déterministe (indépendant de l'état réalisé). Voir `DutchBook.lean`.

    **Preuve** : disjonction sur l'appartenance `(ω ∈ A, ω ∈ B)` (4 cas) ; dans chaque
    cas, l'identité se réduit à une équation arithmétique triviale. -/
lemma ind_inclusion_exclusion (A B : Event Ω) (ω : Ω) :
    ind A ω + ind B ω - ind (A ∩ B) ω - ind (A ∪ B) ω = 0 := by
  unfold ind
  simp only [Finset.mem_inter, Finset.mem_union]
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

end Coherence
