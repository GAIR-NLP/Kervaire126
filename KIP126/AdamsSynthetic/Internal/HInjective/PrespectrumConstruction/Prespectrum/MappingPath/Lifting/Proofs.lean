module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingPath.Lifting.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {A X Y : Prespectrum.{u}} (f : X ⟶ Y)
  (u : A ⟶ mappingPath f) (H : A ⟶ pathPrespectrum Y)
  (h : u ≫ mappingPathProjection f = H ≫ pathEvaluation Y 0)

/-- At time zero the constructed lift is exactly the prescribed original lift. -/
@[simp] theorem mappingPathLift_zero :
    mappingPathLift f u H h ≫ pathEvaluation (mappingPath f) 0 = u := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    classical
    change (if (1+(0 : ℝ))*(t : ℝ) ≤ 1 then
      (u.level n a).val.2 (mappingPathLiftFirst (0,t)) else
        (H.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (0,t))) = (u.level n a).val.2 t
    simp only [add_zero,one_mul,t.property.2,ite_true,mappingPathLiftFirst_zero]

/-- At every time the lift projects exactly to the prescribed base homotopy. -/
@[simp] theorem mappingPathLift_projection (s : I) :
    mappingPathLift f u H h ≫ pathEvaluation (mappingPath f) s ≫ mappingPathProjection f =
      H ≫ pathEvaluation Y s := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  classical
  change (if (1+(s : ℝ))*(1 : ℝ) ≤ 1 then
    (u.level n a).val.2 (mappingPathLiftFirst (s,1)) else
      (H.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,1))) = (H.level n a : C(I,Y.level n)).toFun s
  split_ifs with hs
  · have hs0 : s = 0 := by
      apply Subtype.ext
      change (s : ℝ) = 0
      nlinarith [s.property.1]
    subst s
    rw [mappingPathLiftFirst_zero]
    exact congrArg (fun k : A ⟶ Y => k.level n a) h
  · rw [mappingPathLiftSecond_end]

end KIP126.AdamsSynthetic.Source.Prespectrum
