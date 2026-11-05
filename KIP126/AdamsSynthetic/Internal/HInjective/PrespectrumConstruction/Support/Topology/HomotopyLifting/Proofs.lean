module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Topology.HomotopyLifting.Predicates

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {E : Type u} {B : Type v} {Z : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]

theorem cubeCylinderHomeomorph_boundary (n : ℕ) (z : I × (Fin n → I)) :
    z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) ↔
      cubeCylinderHomeomorph n z ∈ _root_.Cube.boundary (Fin (n + 1)) := by
  constructor
  · rintro (h | h | ⟨i,hi⟩)
    · exact ⟨0,Or.inl h⟩
    · exact ⟨0,Or.inr h⟩
    · exact ⟨i.succ,hi⟩
  · rintro ⟨i,hi⟩
    induction i using Fin.cases with
    | zero => exact hi.elim Or.inl (fun h => Or.inr (Or.inl h))
    | succ i => exact Or.inr (Or.inr ⟨i,hi⟩)

end KIP126.Topology.HomotopyLifting
