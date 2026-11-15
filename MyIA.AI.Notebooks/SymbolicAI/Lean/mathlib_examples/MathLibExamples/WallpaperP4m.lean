import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs

/-!
# Le groupe ponctuel du pavage p4m

Les matrices rationnelles ci-dessous sont celles des générateurs du moteur
`scripts/symmetry/wallpaper.py`. Le groupe ponctuel est fini ; le pavage
contient aussi toutes les translations entières. Ce fichier ne prétend pas
classifier les 17 groupes de pavage.
-/

namespace WallpaperP4m

open DihedralGroup

abbrev Mat := Matrix (Fin 2) (Fin 2) ℚ

def rotation : Mat := !![0, -1; 1, 0]
def reflection : Mat := !![1, 0; 0, -1]

def rotations (i : ZMod 4) : Mat :=
  if i = 0 then 1 else if i = 1 then rotation else
    if i = 2 then !![-1, 0; 0, -1] else !![0, 1; -1, 0]

def representation : DihedralGroup 4 → Mat
  | .r i => rotations i
  | .sr i => reflection * rotations i

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
 theorem representation_mul (a b : DihedralGroup 4) :
    representation (a * b) = representation a * representation b := by
  revert a b
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
 theorem representation_injective : Function.Injective representation := by
  decide +kernel

theorem rotation_generator : representation (.r 1) = rotation := by decide +kernel

theorem horizontal_mirror_generator : representation (.sr 0) = reflection := by
  decide +kernel

theorem vertical_mirror_generator :
    representation (.sr 2) = !![-1, 0; 0, 1] := by decide +kernel

theorem point_group_card : Fintype.card (DihedralGroup 4) = 8 := by
  simpa using (DihedralGroup.card (n := 4))

theorem rotation_order : (DihedralGroup.r 1 : DihedralGroup 4) ^ 4 = 1 := by decide

theorem reflection_order : (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 := by decide

theorem reflection_conjugates_rotation :
    (DihedralGroup.sr 0 : DihedralGroup 4) * DihedralGroup.r 1 * DihedralGroup.sr 0 =
      (DihedralGroup.r 1)⁻¹ := by decide

/-- Translation par un vecteur entier du réseau carré. -/
def translation (v : ℤ × ℤ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (p.1 + v.1, p.2 + v.2)

theorem translation_add (v w : ℤ × ℤ) (p : ℚ × ℚ) :
    translation (v + w) p = translation v (translation w p) := by
  simp [translation, Int.cast_add, add_comm, add_left_comm]

theorem translation_injective : Function.Injective translation := by
  intro v w h
  have h0 := congrFun h (0, 0)
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [translation, zero_add] at h1 h2
  exact Prod.ext (Int.cast_injective h1) (Int.cast_injective h2)

/-- Il existe une infinité de translations distinctes dans le pavage. -/
theorem infinitely_many_translations : Set.Infinite (Set.range translation) :=
  Set.infinite_range_of_injective translation_injective

end WallpaperP4m
