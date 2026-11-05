module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingCylinder.Contraction.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderContraction_inl {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s t : I) :
    mappingCylinderContraction f n (mappingCylinderMk f n (.inl (x,s)),t) =
      mappingCylinderMk f n (.inl (x,max s t)) := rfl

@[simp] theorem mappingCylinderContraction_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (z : mappingCylinderLevel f n) : mappingCylinderContraction f n (z,0) = z := by
  obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases a with ⟨x,s⟩ | y
  · rw [mappingCylinderContraction_inl,max_eq_left (show (0 : I) ≤ s from s.property.1)]
  · rfl

@[simp] theorem mappingCylinderContraction_one {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (z : mappingCylinderLevel f n) : mappingCylinderContraction f n (z,1) =
      (mappingCylinderSection f).level n ((mappingCylinderProjection f).level n z) := by
  obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases a with ⟨x,s⟩ | y
  · rw [mappingCylinderContraction_inl,max_eq_right (show s ≤ (1 : I) from s.property.2),mappingCylinderMk_top]
    rfl
  · rfl

@[simp] theorem mappingCylinderContraction_point {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (s : I) :
    mappingCylinderContraction f n ((mappingCylinderLevel f n).point,s) =
      (mappingCylinderLevel f n).point := rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
