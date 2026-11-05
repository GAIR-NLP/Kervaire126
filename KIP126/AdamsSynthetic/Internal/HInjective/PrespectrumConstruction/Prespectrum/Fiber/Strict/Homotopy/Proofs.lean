module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Strict.Homotopy.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Strict.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B : Prespectrum.{u}} (p : A ⟶ B)
  (L : fiber p ⟶ pathPrespectrum A)
  (hp : ∀ s : I, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s)

@[simp] theorem strictFiberTailHomotopy_zero
    (hzero : L ≫ pathEvaluation A 0 = fiberProjection p) :
    strictFiberTailHomotopy p L hp ≫ pathEvaluation (fiber p) 0 = 𝟙 (fiber p) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun k : fiber p ⟶ A => k.level n z) hzero
  · apply ContinuousMap.ext; intro t
    change z.val.2 (Set.Icc.convexComb 0 1 t) = z.val.2 t
    rw [Set.Icc.convexComb_zero_one]

@[simp] theorem strictFiberTailHomotopy_one :
    strictFiberTailHomotopy p L hp ≫ pathEvaluation (fiber p) 1 =
      strictFiberRetraction p L hp ≫ strictFiberInclusion p := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext; intro t
    change z.val.2 (Set.Icc.convexComb 1 1 t) = (B.level n).point
    rw [Set.Icc.convexComb_eq]
    exact z.property.2

@[simp] theorem strictFiberKernelHomotopy_zero
    (hzero : L ≫ pathEvaluation A 0 = fiberProjection p) :
    strictFiberKernelHomotopy p L hp ≫ pathEvaluation (strictFiber p) 0 = 𝟙 (strictFiber p) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun k : fiber p ⟶ A => k.level n ((strictFiberInclusion p).level n z)) hzero
  · rfl

@[simp] theorem strictFiberKernelHomotopy_one :
    strictFiberKernelHomotopy p L hp ≫ pathEvaluation (strictFiber p) 1 =
      strictFiberInclusion p ≫ strictFiberRetraction p L hp := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim (α := PUnit) _ _

end KIP126.AdamsSynthetic.Source.Prespectrum
