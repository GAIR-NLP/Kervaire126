module
import all KIP126.Literature.E2Exactness.CoefficientUnit
import all KIP126.Literature.E2Exactness.CoefficientSplit

@[expose] section
namespace KIP126.Literature.Standard.HUnitConsequences
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def multiplication : coefficients.object ⊗ coefficients.object ⟶ coefficients.object :=
  HUnitCore.coefficientSelfUnit_retraction.choose

private theorem multiplication_left_unit :
    ((λ_ coefficients.object).inv ≫ coefficients.unit ▷ coefficients.object) ≫
      multiplication = 𝟙 coefficients.object :=
  HUnitCore.coefficientSelfUnit_retraction.choose_spec

private theorem coefficient_unit_detects_endomorphisms
    (f g : coefficients.object ⟶ coefficients.object)
    (hfg : coefficients.unit ≫ f = coefficients.unit ≫ g) : f = g := by
  let T := Triangle.mk coefficients.unit (HasFunctorialCofiber.cofibι coefficients.unit)
    (HasFunctorialCofiber.cofibδ coefficients.unit)
  exact HUnitCore.coefficient_map_eq_of_cover T (HasFunctorialCofiber.cofib_distinguished _)
    sphere_connected HUnitCore.coefficient_connected HUnitCore.coefficient_unit_pi0_surjective f g hfg

private theorem multiplication_right_unit :
    ((ρ_ coefficients.object).inv ≫ coefficients.object ◁ coefficients.unit) ≫
      multiplication = 𝟙 coefficients.object :=
  HModuleSplit.right_unit_of_left_unit_and_detection coefficients.object coefficients.unit
    multiplication multiplication_left_unit coefficient_unit_detects_endomorphisms

/-- The actual fixed coefficient kills every adjacent map of any actual
    coefficient-unit Adams tower, for arbitrary spectra. -/
private theorem actual_adams_step_tensor_zero {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℕ) :
    coefficients.object ◁ T.map (Nat.le_succ s) = 0 :=
  HModuleSplit.adams_step_tensor_zero closedBackground coefficients.object coefficients.unit
    multiplication multiplication_right_unit T s

private theorem actual_adams_step_homology_zero {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℕ) :
    ZeroOnModTwoHomology coefficients (T.map (Nat.le_succ s)) :=
  HModuleSplit.adams_step_homology_zero closedBackground coefficients
    multiplication multiplication_right_unit T s

private theorem actual_coefficient_tensor_extension (Y : Spectrum)
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hz : coefficients.object ◁ T.mor₁ = 0)
    (g : T.obj₂ ⟶ coefficients.object ⊗ Y) :
    ∃ lift : T.obj₃ ⟶ coefficients.object ⊗ Y, T.mor₂ ≫ lift = g :=
  HModuleSplit.coefficient_tensor_extension coefficients.object Y coefficients.unit
    multiplication multiplication_left_unit T hT hz g

end
end KIP126.Literature.Standard.HUnitConsequences
end
