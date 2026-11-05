module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingCylinder.Contraction.Proofs
import all KIP126.AdamsSynthetic.Internal.Prespectrum.Path.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.Prespectrum.HomotopyGroup.Map.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified deformation gives a relative homotopy of every actual based loop. -/
theorem mappingCylinder_loop_deformation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((mappingCylinder f).level n) ((mappingCylinder f).level n).point) :
    GenLoop.Homotopic p
      ⟨((mappingCylinderSection f).level n).comp
        (((mappingCylinderProjection f).level n).comp p.val), by
        intro t ht
        change (mappingCylinderSection f).level n ((mappingCylinderProjection f).level n (p t)) = _
        exact (congrArg (fun z => (mappingCylinderSection f).level n
          ((mappingCylinderProjection f).level n z)) (p.property t ht)).trans
          (by rw [(mappingCylinderProjection f).point,(mappingCylinderSection f).point])⟩ := by
  refine ⟨{ toFun := fun z => mappingCylinderContraction f n (p z.2,z.1)
            continuous_toFun := (mappingCylinderContraction f n).continuous.comp
              ((p.val.continuous.comp continuous_snd).prodMk continuous_fst)
            map_zero_left := fun t => mappingCylinderContraction_zero f n (p t)
            map_one_left := fun t => mappingCylinderContraction_one f n (p t)
            prop' := ?_ }⟩
  intro s t ht
  change mappingCylinderContraction f n (p t,s) = p t
  exact (congrArg (fun z => mappingCylinderContraction f n (z,s)) (p.property t ht)).trans
    ((mappingCylinderContraction_point f n s).trans (p.property t ht).symm)

/-- The actual mapping-cylinder projection is always a stable equivalence. -/
theorem mappingCylinderProjection_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (mappingCylinderProjection f) := by
  apply stableEquivalence_of_levelwise_loops
  · intro n r p q hpq
    exact (mappingCylinder_loop_deformation f n r p).trans
      ((hpq.comp_continuousMap ((mappingCylinderSection f).level n)).trans
        (mappingCylinder_loop_deformation f n r q).symm)
  · intro n r p
    refine ⟨⟨((mappingCylinderSection f).level n).comp p.val, ?_⟩, ?_⟩
    · intro t ht
      change (mappingCylinderSection f).level n (p t) = _
      exact (congrArg ((mappingCylinderSection f).level n) (p.property t ht)).trans
        ((mappingCylinderSection f).point n)
    · exact GenLoop.Homotopic.refl p

/-- Factoring an actual stable equivalence by this cylinder produces
another actual stable equivalence on the source side. -/
theorem mappingCylinderInclusion_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (mappingCylinderInclusion f) := by
  intro d
  have hc (x : StableHomotopy X d) :
      stableHomotopyMap (mappingCylinderProjection f) d
        (stableHomotopyMap (mappingCylinderInclusion f) d x) = stableHomotopyMap f d x := by
    induction x using Quot.inductionOn with
    | h p => rfl
  have hq := mappingCylinderProjection_stableEquivalence f d
  constructor
  · intro x y h
    apply (hf d).injective
    rw [← hc x,← hc y,h]
  · intro z
    obtain ⟨x,hx⟩ := (hf d).surjective (stableHomotopyMap (mappingCylinderProjection f) d z)
    exact ⟨x,hq.injective ((hc x).trans hx)⟩

end KIP126.AdamsSynthetic.Source.Prespectrum
