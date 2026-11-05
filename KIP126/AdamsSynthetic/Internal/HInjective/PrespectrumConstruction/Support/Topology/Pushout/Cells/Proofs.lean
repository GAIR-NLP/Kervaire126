module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.Topology.Pushout.RealFunctions.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- A cell point away from the attaching boundary acquires no additional
identifications in the actual pushout. -/
theorem pushout_cell_eq_of_outside_boundary
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    {x y : A} (hx : x ∉ Set.range i) (hxy : a x = a y) : x = y := by
  by_contra hne
  obtain ⟨g,hg⟩ := pushout_distinct_cell_points_real_separation h hi x y hx hne
  exact hg (congrArg g hxy)

end KIP126.Topology
