import Mathlib
import Argumentation.Basic
import Argumentation.Extensions

/-!
# Fundamental Lemma de Dung (1995)

> **Fundamental Lemma (Dung, Proposition 6).** Soit `S` admissible et `a`, `b`
> deux arguments **défendus** par `S`. Alors (i) `S ∪ {a}` est admissible, et
> (ii) `b` est défendu par `S ∪ {a}`.

Ce lemme est la **pierre angulaire** de la théorie de Dung : il garantit que la
défense est *robuste* à l'adjonction d'arguments défendus, et sous-tend
l'existence des extensions complètes/grounded/preferred. Il est prouvé ici **sans
aucun `sorry`**, par un raisonnement du premier ordre :

- **Conflit interne de `S ∪ {a}`** : un attaquant interne `x` d'un membre `y`
  déclenche (selon les 4 cas `x,y ∈ {a} ∪ S`) une chaîne de contre-attaques qui
  contredit l'absence de conflat de `S` combinée au fait que `S` défend `a`.
- **Défense des membres** : `S ∪ {a}` défend `a` (donné) et chaque `s ∈ S`
  (par admissibilité de `S`), car `S ⊆ S ∪ {a}` et la défense est monotone.
- **(ii)** : immédiat par monotonie (`S ⊆ S ∪ {a}`).

Référence : Dung, *On the Acceptability of Arguments and its Fundamental Role in
Nonmonotonic Reasoning, Logic Programming and n-Person Games*, Artificial
Intelligence 77 (1995), Proposition 6.
-/

namespace Argumentation

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- **Dung Fundamental Lemma (i)** : si `S` est admissible et défend `a`, alors
`S ∪ {a}` est admissible. -/
theorem fundamental_lemma {S : Set α} {a : α}
    (hS : af.Admissible S) (ha : af.defends S a) :
    af.Admissible (insert a S) := by
  refine ⟨?_, ?_⟩
  · -- (1) S ∪ {a} est sans conflat : analyse 2×2 des positions de x,y ∈ {a}∪S.
    rintro x hx y hy hxy
    obtain hxa | hxS := Set.mem_insert_iff.1 hx
    · -- x = a : a attaque y.
      obtain hya | hyS := Set.mem_insert_iff.1 hy
      · -- a attaque a : S défend a ⇒ ∃ c ∈ S attaque a ; mais aucun membre de S
        -- n'attaque a (cf. `no_internal_attack_on_defended`). Contradiction.
        subst x; subst y
        obtain ⟨c, hcS, hca⟩ := ha a hxy
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha c hcS hca
      · -- a attaque y ∈ S : S défend y ⇒ ∃ c ∈ S attaque a ; aucun membre de S
        -- n'attaque a. Contradiction.
        subst x
        obtain ⟨c, hcS, hca⟩ := hS.2 y hyS a hxy
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha c hcS hca
    · -- x ∈ S : x attaque y.
      obtain hya | hyS := Set.mem_insert_iff.1 hy
      · -- x ∈ S attaque a : impossible (aucun membre de S n'attaque a).
        subst y
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha x hxS hxy
      · -- x ∈ S attaque y ∈ S : contredit l'absence de conflat de S.
        exact hS.1 hxS hyS hxy
  · -- (2) S ∪ {a} défend chacun de ses membres (par monotonie : S ⊆ S ∪ {a}).
    rintro y hy
    obtain hya | hyS := Set.mem_insert_iff.1 hy
    · -- défendre a : S défend a, et S ⊆ S ∪ {a}.
      subst y
      exact af.defends_mono (Set.subset_insert a S) ha
    · -- défendre y ∈ S : S (admissible) défend y, et S ⊆ S ∪ {a}.
      exact af.defends_mono (Set.subset_insert a S) (hS.2 y hyS)

/-- **Dung Fundamental Lemma (ii)** : si `S` (admissible) défend `a` et `b`,
alors `S ∪ {a}` défend encore `b`. Immédiat par monotonie de la défense
(`S ⊆ S ∪ {a}`). -/
theorem fundamental_lemma_defends {S : Set α} {a b : α}
    (hS : af.Admissible S) (ha : af.defends S a) (hb : af.defends S b) :
    af.defends (insert a S) b :=
  af.defends_mono (Set.subset_insert a S) hb

/-- **Corollaire** : si `S` est admissible et défend `a`, alors `a` est défendu
par `S ∪ {a}` (cas particulier de (ii) avec `b = a`). -/
theorem fundamental_lemma_defends_self {S : Set α} {a : α}
    (hS : af.Admissible S) (ha : af.defends S a) :
    af.defends (insert a S) a :=
  af.defends_mono (Set.subset_insert a S) ha

end AF

end Argumentation
