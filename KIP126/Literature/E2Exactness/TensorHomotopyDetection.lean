module
import all KIP126.Literature.E2Exactness.ActualHModuleDecomposition
import all KIP126.Literature.E2Exactness.HModuleGeneratorNatural

@[expose] section
namespace KIP126.Literature.Standard.HModuleDetection
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.HModuleDecomposition
open KIP126.Literature.Standard.HModuleGenerator
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual coefficient tensor map is zero when its action on every
ordinary stable homotopy group is zero. The natural μ-action extensions,
chosen in the actual coefficient basis wedge, are used essentially here. -/
private theorem coefficient_tensor_map_zero_of_homotopy_zero {X Y : Spectrum}
    (f : X ⟶ Y)
    (hf : ∀ (d : ℤ) (a : HomotopyGroup d (coefficients.object ⊗ X)),
      inducedMap (coefficients.object ◁ f) d a = 0) :
    coefficients.object ◁ f = 0 := by
  letI := coefficientTensorWedgeMap_isIso X
  apply (cancel_epi (coefficientTensorWedgeMap X)).mp
  rw [comp_zero]
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, coefficientTensorWedgeMap_inclusion, comp_zero]
  exact generatorExtension_annihilated f j.1 _ (hf j.1 _)

end
end KIP126.Literature.Standard.HModuleDetection
end
