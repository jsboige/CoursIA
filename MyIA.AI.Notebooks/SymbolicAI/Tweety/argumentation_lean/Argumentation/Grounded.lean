import Mathlib
import Argumentation.Basic
import Argumentation.Characteristic
import Argumentation.Extensions

/-!
# Extension grounded — point fixe et propriétés (Knaster–Tarski)

L'extension **grounded** de Dung est définie comme le **plus petit point fixe** de
la fonction caractéristique `F` :
```
grounded = F.lfp   (Knaster–Tarski sur le treillis complet (Set α, ⊆))
```
Mathlib fournit `OrderHom.map_lfp` (`F.lfp` est un point fixe), `OrderHom.lfp_le`
(`F.lfp` majore tout pré-point-fixe) — que nous exploitons pour prouver, **sans
aucun `sorry`**, les identités caractérisant le grounded :

- `grounded_fixed` : `F(grounded) = grounded` (c'est bien un point fixe).
- `grounded_defends_iff_mem` : `a ∈ grounded ⇔ grounded défend a`
  (caractérisation par défense, cœur de la sémantique grounded).
- `grounded_least_complete` : toute extension complète contient `grounded`
  (le grounded est la **plus petite** extension complète — `lfp_le`).

Plus le lemme-clé de Dung **`F_preserves_admissible`** : la fonction
caractéristique préserve l'admissibilité (`Admissible S ⇒ Admissible (F S)`),
pierre angulaire de l'existence des extensions complètes.

### Jalon OPEN (documenté, NON sorry-backed)

La preuve que `grounded` est **elle-même** une extension complète (donc sans
conflat) est le résultat substantiel de Dung (Proposition 11). Elle requiert, pour
un cadre fini, la **stabilisation finie** de la suite itérée
`∅ ⊂ F(∅) ⊂ F²(∅) ⊂ …` vers le `lfp` (chaque itéré est admissible via
`F_preserves_admissible` ; la chaîne se stabilise en `|α|` étapes). Cette connexion
itération-finie↔`lfp` est délibérément **non énoncée comme un `sorry`** : la
bibliothèque actuelle reste entièrement `sorry`-free, livrant les identités de
point fixe, la plus-petite-complétude, la hiérarchie des sémantiques et la
Fundamental Lemma.
-/

namespace Argumentation

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- `grounded` est un **point fixe** de la fonction caractéristique
(`F(grounded) = grounded`). Identité de Knaster–Tarski via `OrderHom.map_lfp`. -/
theorem grounded_fixed :
    af.characteristic af.grounded = af.grounded :=
  af.characteristic.map_lfp

/-- Caractérisation par défense : `a ∈ grounded` **si et seulement si** `grounded`
défend `a`. Conséquence immédiate du point fixe et de la définition de `F`. -/
theorem grounded_defends_iff_mem (a : α) :
    af.defends af.grounded a ↔ a ∈ af.grounded := by
  constructor
  · intro h
    rw [← af.grounded_fixed]
    exact (af.mem_characteristic_iff af.grounded a).mpr h
  · intro h
    rw [← af.grounded_fixed] at h
    exact (af.mem_characteristic_iff af.grounded a).mp h

/-- Le `grounded` est la **plus petite extension complète** : toute extension
complète `T` contient `grounded`. Preuve via `OrderHom.lfp_le` appliqué au
pré-point-fixe `F(T) ⊆ T` (une extension complète contient tout ce qu'elle
défend). -/
theorem grounded_least_complete (T : Set α) (h : af.Complete T) :
    af.grounded ⊆ T := by
  have hFT : af.characteristic T ⊆ T := by
    rintro a ha
    exact h.2 a ((af.mem_characteristic_iff T a).mp ha)
  show af.characteristic.lfp ⊆ T
  exact af.characteristic.lfp_le hFT

/-!
## Lemme-clé de Dung : `F` préserve l'admissibilité
-/

/-- La fonction caractéristique **préserve l'absence de conflat** :
si `S` est sans conflat, alors `F(S)` l'est aussi. -/
theorem F_preserves_conflictFree {S : Set α} (hcf : af.conflictFree S) :
    af.conflictFree (af.characteristic S) := by
  rintro a ha b hb hab
  -- a,b ∈ F(S) ⟹ S défend a et b ; a attaque b ⟹ chaîne de contre-attaques
  -- dans S ⟹ contredit l'absence de conflat de S.
  obtain ⟨c, hcS, hca⟩ := hb a hab
  obtain ⟨d, hdS, hdc⟩ := ha c hca
  exact hcf hdS hcS hdc

/-- **Lemme de Dung (Proposition 7)** : la fonction caractéristique préserve
l'admissibilité — `Admissible S ⇒ Admissible (F S)`. C'est le fait fondamental qui
garantit l'existence d'extensions complètes par itération depuis `∅`. -/
theorem F_preserves_admissible {S : Set α} (h : af.Admissible S) :
    af.Admissible (af.characteristic S) := by
  refine ⟨af.F_preserves_conflictFree h.1, ?_⟩
  rintro a ha b hb
  obtain ⟨c, hcS, hcb⟩ := ha b hb
  refine ⟨c, ?_, hcb⟩
  exact (af.mem_characteristic_iff S c).mpr (h.2 c hcS)

end AF

end Argumentation
