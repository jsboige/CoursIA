/-
Reduction parallele et lemme du losange pour S/K/I.

Preuve de style Tait / Martin-Lof, adaptee aux combinateurs (sans
lieurs) : la reduction parallele `par` contracte simultanement une
famille de redexes disjoints. Le lemme du losange (`diamond`) est
etabli par induction forte sur la taille du terme — les cas
d'affrontement congruence/redex exigent le losange sur des
sous-termes stricts, pas seulement sur les fils — et il a exactement
la forme que l'organe `Relation.church_rosser` consomme.

Literature : Takahashi, "Parallel Reductions in λ-Calculus" (1995) ;
Nipkow, "More Church-Rosser Proofs (in Isabelle/HOL)" (1996), section
combinatory logic.
-/

import Combinators.Term
import Mathlib.Tactic

namespace Combinators

open Term

/-- Reduction parallele : contraction simultanee de redexes disjoints.
Reflexive par construction (constructeur `refl`), contient `step`,
et satisfait le losange local — contrairement a `step` qui ne l'a pas
(les deux contractions d'un meme `K ⊙ x ⊙ y` depuis des redex
imbriques ne se rejoignent pas en un pas). -/
inductive par : Term → Term → Prop
  | refl (t : Term) : par t t
  | congr {x x' y y' : Term} (hx : par x x') (hy : par y y') :
      par (x ⊙ y) (x' ⊙ y')
  | S {x x' y y' z z' : Term} (hx : par x x') (hy : par y y') (hz : par z z') :
      par (S ⊙ x ⊙ y ⊙ z) (x' ⊙ z' ⊙ (y' ⊙ z'))
  | K {x x' y y' : Term} (hx : par x x') (hy : par y y') :
      par (K ⊙ x ⊙ y) x'
  | I {x x' : Term} (hx : par x x') : par (I ⊙ x) x'

/-! ### Lemmes de forme

La reduction parallele ne cree pas de redex au sommet : un terme dont
la tete est un atome la garde — sauf pour la regle I, qui absorbe sa
tete (`I ⊙ u → u'`). C'est pourquoi les lemmes de forme a tete fixe
sont enonces pour S et K seulement, avec la tete syntactique dans
l'enonce : la tete ne peut alors ni migrer ni disparaitre. Ces lemmes
portent tous les cas d'affrontement du losange. -/

/-- Un atome ne se reduit parallelement qu'en lui-meme. -/
theorem par_atom {t s : Term} (ht : t = S ∨ t = K ∨ t = I)
    (h : par t s) : s = t := by
  cases h with
  | refl => rfl
  | congr => rcases ht with h | h | h <;> simp at h
  | S => rcases ht with h | h | h <;> simp at h
  | K => rcases ht with h | h | h <;> simp at h
  | I => rcases ht with h | h | h <;> simp at h

/-- Un spine `S ⊙ p` garde sa tete S : seul l'argument se reduit.
(La regle S exige trois arguments, `S ⊙ p` n'en a qu'un : elle ne
peut pas se declencher au sommet.) -/
theorem par_Shead {p s : Term} (h : par (S ⊙ p) s) :
    ∃ p', s = S ⊙ p' ∧ par p p' := by
  cases h with
  | refl => exact ⟨p, rfl, par.refl p⟩
  | congr h1 h2 =>
      have hs := par_atom (Or.inl rfl) h1
      subst hs
      exact ⟨_, rfl, h2⟩

/-- Un spine `K ⊙ p` garde sa tete K : seul l'argument se reduit.
(La regle K exige deux arguments, `K ⊙ p` n'en a qu'un.) -/
theorem par_Khead {p s : Term} (h : par (K ⊙ p) s) :
    ∃ p', s = K ⊙ p' ∧ par p p' := by
  cases h with
  | refl => exact ⟨p, rfl, par.refl p⟩
  | congr h1 h2 =>
      have hs := par_atom (Or.inr (Or.inl rfl)) h1
      subst hs
      exact ⟨_, rfl, h2⟩

/-- La reduction parallele ne contracte pas un redex partiel : un
spine `S ⊙ p ⊙ q` garde sa tete et ses deux arguments. -/
theorem par_S2 {p q s : Term} (h : par (S ⊙ p ⊙ q) s) :
    ∃ p' q', s = S ⊙ p' ⊙ q' ∧ par p p' ∧ par q q' := by
  cases h with
  | refl => exact ⟨p, q, rfl, par.refl p, par.refl q⟩
  | congr h1 h2 =>
      obtain ⟨p', hx', hp'⟩ := par_Shead h1
      exact ⟨p', _, by rw [hx'], hp', h2⟩

/-! ### Lemme du losange -/

/-- **Lemme du losange pour la reduction parallele** : deux reductions
paralleles d'un meme terme se rejoignent en une reduction parallele
chacune.

L'induction est forte sur la taille du terme : dans les cas
d'affrontement (une congruence contre un redex de tete), le losange
est requis sur des sous-termes stricts (les arguments du redex), que
l'hypotenuse `n` fournit.

Cas d'affrontement typique, `h1` congruence et `h2` regle S sur
`a = (S ⊙ p ⊙ q) ⊙ r` : la congruence reduit `S ⊙ p ⊙ q` en
`S ⊙ p₂ ⊙ q₂` (lemme `par_S2` — la tete S ne peut pas disparaitre),
puis le redex residuel se contracte, et le rejoint est
`u ⊙ w ⊙ (v ⊙ w)` ou `u, v, w` sont les rejoints de `p, q, r` — la
regle S duplique son **troisieme** argument `r`, c'est donc `w` (le
rejoint de `r`) qui apparait deux fois dans le terme final. -/
theorem diamond (n : Nat) (a b c : Term) (hn : Term.size a ≤ n)
    (h1 : par a b) (h2 : par a c) : ∃ d, par b d ∧ par c d := by
  induction n generalizing a b c with
  | zero => exact absurd hn (by have := Term.size_pos a; omega)
  | succ n ih =>
    cases h1 with
    | refl => exact ⟨c, h2, par.refl c⟩
    | @congr x x' y y' hx hy =>
        have hxn : Term.size x ≤ n := by
          have := Term.size_pos x
          simp only [Term.size] at hn ⊢
          omega
        have hyn : Term.size y ≤ n := by
          simp only [Term.size] at hn
          omega
        cases h2 with
        | refl => exact ⟨x' ⊙ y', par.refl _, par.congr hx hy⟩
        | congr hu hv =>
            obtain ⟨w₁, hw₁, hw₂⟩ := ih _ _ _ hxn hx hu
            obtain ⟨w₂, hw₃, hw₄⟩ := ih _ _ _ hyn hy hv
            exact ⟨_, par.congr hw₁ hw₃, par.congr hw₂ hw₄⟩
        | S hp hq hr =>
            -- h2 : a = (S ⊙ ?P ⊙ ?Q) ⊙ ?R ; hx : par (S ⊙ ?P ⊙ ?Q) x'
            obtain ⟨p₂, q₂, hx_eq, hp₂, hq₂⟩ := par_S2 hx
            subst hx_eq
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ (by simp only [Term.size] at hn; omega) hp₂ hp
            obtain ⟨v, hv₁, hv₂⟩ := ih _ _ _ (by simp only [Term.size] at hn; omega) hq₂ hq
            obtain ⟨w, hw₁, hw₂⟩ := ih _ _ _ (by simp only [Term.size] at hn; omega) hy hr
            exact ⟨u ⊙ w ⊙ (v ⊙ w), par.S hu₁ hv₁ hw₁,
              par.congr (par.congr hu₂ hw₂) (par.congr hv₂ hw₂)⟩
        | K hp hq =>
            -- h2 : a = (K ⊙ ?P) ⊙ ?Q ; hx : par (K ⊙ ?P) x'
            obtain ⟨p₂, hx_eq, hp₂⟩ := par_Khead hx
            subst hx_eq
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ (by simp only [Term.size] at hn; omega) hp₂ hp
            exact ⟨u, par.K hu₁ (par.refl y'), hu₂⟩
        | I hp =>
            -- h2 : a = I ⊙ ?P ; hx : par I x', donc x' = I
            have hxI := par_atom (Or.inr (Or.inr rfl)) hx
            subst hxI
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ (by simp only [Term.size] at hn; omega) hy hp
            exact ⟨u, par.I hu₁, hu₂⟩
    | @S p p' q q' r r' hp hq hr =>
        have hpn : Term.size p ≤ n := by simp only [Term.size] at hn; omega
        have hqn : Term.size q ≤ n := by simp only [Term.size] at hn; omega
        have hrn : Term.size r ≤ n := by simp only [Term.size] at hn; omega
        cases h2 with
        | refl => exact ⟨p' ⊙ r' ⊙ (q' ⊙ r'), par.refl _, par.S hp hq hr⟩
        | congr hu hv =>
            -- hu : par (S ⊙ p ⊙ q) ?u', la tete S ne peut pas disparaitre
            obtain ⟨p₂, q₂, hu_eq, hp₂, hq₂⟩ := par_S2 hu
            subst hu_eq
            obtain ⟨w₁, hw₁, hw₂⟩ := ih _ _ _ hpn hp hp₂
            obtain ⟨w₂, hw₃, hw₄⟩ := ih _ _ _ hqn hq hq₂
            obtain ⟨w₃, hw₅, hw₆⟩ := ih _ _ _ hrn hr hv
            exact ⟨w₁ ⊙ w₃ ⊙ (w₂ ⊙ w₃),
              par.congr (par.congr hw₁ hw₅) (par.congr hw₃ hw₅),
              par.S hw₂ hw₄ hw₆⟩
        | S hp₂ hq₂ hr₂ =>
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ hpn hp hp₂
            obtain ⟨v, hv₁, hv₂⟩ := ih _ _ _ hqn hq hq₂
            obtain ⟨w, hw₁, hw₂⟩ := ih _ _ _ hrn hr hr₂
            exact ⟨u ⊙ w ⊙ (v ⊙ w),
              par.congr (par.congr hu₁ hw₁) (par.congr hv₁ hw₁),
              par.congr (par.congr hu₂ hw₂) (par.congr hv₂ hw₂)⟩
    | @K p p' q q' hp hq =>
        have hpn : Term.size p ≤ n := by simp only [Term.size] at hn; omega
        cases h2 with
        | refl => exact ⟨b, par.refl b, par.K hp hq⟩
        | congr hu hv =>
            -- hu : par (K ⊙ p) ?u', la tete K ne peut pas disparaitre
            obtain ⟨p₂, hu_eq, hp₂⟩ := par_Khead hu
            subst hu_eq
            obtain ⟨w, hw₁, hw₂⟩ := ih _ _ _ hpn hp hp₂
            exact ⟨w, hw₁, par.K hw₂ (par.refl _)⟩
        | K hp₂ hq₂ =>
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ hpn hp hp₂
            exact ⟨u, hu₁, hu₂⟩
    | @I p p' hp =>
        have hpn : Term.size p ≤ n := by simp only [Term.size] at hn; omega
        cases h2 with
        | refl => exact ⟨b, par.refl b, par.I hp⟩
        | congr hu hv =>
            -- hu : par I ?u', donc ?u' = I
            have huI := par_atom (Or.inr (Or.inr rfl)) hu
            subst huI
            obtain ⟨w, hw₁, hw₂⟩ := ih _ _ _ hpn hp hv
            exact ⟨w, hw₁, par.I hw₂⟩
        | I hp₂ =>
            obtain ⟨u, hu₁, hu₂⟩ := ih _ _ _ hpn hp hp₂
            exact ⟨u, hu₁, hu₂⟩

/-- Forme sans la borne de taille, pour consommation directe. -/
theorem diamond' (a b c : Term) (h1 : par a b) (h2 : par a c) :
    ∃ d, par b d ∧ par c d :=
  diamond (Term.size a) a b c (Nat.le_refl _) h1 h2

end Combinators
