module
import all KIP126.Literature.E2Exactness.CoefficientConsequences
import Mathlib.CategoryTheory.Shift.CommShift

@[expose] section
namespace KIP126.Literature.Standard.HModuleGenerator
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated CategoryTheory.BraidedCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem coefficient_unit_add_self : coefficients.unit + coefficients.unit = 0 := by
  have h : coefficients.pi0Equiv.symm 1 + coefficients.pi0Equiv.symm 1 = 0 := by
    apply coefficients.pi0Equiv.injective
    simp only [map_add, AddEquiv.apply_symm_apply, map_zero]
    decide
  change (shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ coefficients.pi0Equiv.symm 1 +
    (shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ coefficients.pi0Equiv.symm 1 = 0
  rw [← Preadditive.comp_add, h, comp_zero]

/-- Characteristic two is a statement about the identity of the actual fixed H. -/
private theorem coefficient_two_id_zero :
    (2 : ℕ) • (𝟙 coefficients.object) = 0 := by
  have h : (𝟙 coefficients.object) + (𝟙 coefficients.object) = 0 := by
    apply HUnitConsequences.coefficient_unit_detects_endomorphisms
    simp only [Preadditive.comp_add, Category.comp_id, comp_zero]
    exact coefficient_unit_add_self
  simpa only [two_nsmul] using h

/-- The same identity holds on the actual coefficient tensor of every spectrum. -/
private theorem coefficient_tensor_two_id_zero (X : Spectrum) :
    (2 : ℕ) • (𝟙 (coefficients.object ⊗ X)) = 0 := by
  letI := closedBackground.tensorShift X
  letI := closedBackground.tensorExact X
  have h := congrArg ((tensorRight X).map) coefficient_two_id_zero
  simp only [Functor.map_nsmul, Functor.map_zero] at h
  rw [(tensorRight X).map_id] at h
  exact h

private theorem coefficient_tensor_unit_split :
    coefficients.object ◁ coefficients.unit ≫
      (HUnitConsequences.multiplication ≫ (ρ_ coefficients.object).inv) =
        𝟙 (coefficients.object ⊗ SphereSpectrum) := by
  have h := HUnitConsequences.multiplication_right_unit
  apply (cancel_epi (ρ_ coefficients.object).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp] using
    congrArg (fun f => f ≫ (ρ_ coefficients.object).inv) h

/-- Transport an actual tensor-unit splitting through a supplied coherent
shift comparison, natural only in the source object. -/
private theorem coefficient_tensor_shift_unit_split (d : ℤ) :
    ∃ r : coefficients.object ⊗ coefficients.object⟦d⟧ ⟶
        coefficients.object ⊗ SphereSpectrum⟦d⟧,
      coefficients.object ◁ ((shiftFunctor Spectrum d).map coefficients.unit) ≫ r = 𝟙 _ := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI : (tensorLeft coefficients.object).CommShift ℤ :=
    Functor.CommShift.ofIso (tensorLeftIsoTensorRight coefficients.object).symm ℤ
  let F := tensorLeft coefficients.object
  let q := HUnitConsequences.multiplication ≫ (ρ_ coefficients.object).inv
  refine ⟨(F.commShiftIso d).hom.app coefficients.object ≫
    (shiftFunctor Spectrum d).map q ≫ (F.commShiftIso d).inv.app SphereSpectrum, ?_⟩
  change F.map ((shiftFunctor Spectrum d).map coefficients.unit) ≫ _ = _
  rw [← Category.assoc, F.commShiftIso_hom_naturality]
  simp only [Category.assoc]
  erw [← (shiftFunctor Spectrum d).map_comp_assoc]
  change (F.commShiftIso d).hom.app SphereSpectrum ≫
    (shiftFunctor Spectrum d).map (coefficients.object ◁ coefficients.unit ≫ q) ≫ _ = _
  erw [coefficient_tensor_unit_split, (shiftFunctor Spectrum d).map_id, Category.id_comp]
  exact (F.commShiftIso d).hom_inv_id_app SphereSpectrum

/-- Every actual sphere class in H⊗X extends over the actual shifted unit.
The proof uses the cofiber of that very shifted unit and the existing μ laws. -/
private theorem coefficient_generator_extension (X : Spectrum) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X)) :
    ∃ f : coefficients.object⟦d⟧ ⟶ coefficients.object ⊗ X,
      (shiftFunctor Spectrum d).map coefficients.unit ≫ f = a := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  letI : (tensorLeft coefficients.object).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (tensorLeftIsoTensorRight coefficients.object).symm
  let u := (shiftFunctor Spectrum d).map coefficients.unit
  let T := (Triangle.mk u (HasFunctorialCofiber.cofibι u)
    (HasFunctorialCofiber.cofibδ u)).invRotate
  have hT : T ∈ distTriang Spectrum :=
    inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished u)
  have hz : coefficients.object ◁ T.mor₁ = 0 := by
    obtain ⟨r,hr⟩ := coefficient_tensor_shift_unit_split d
    have hzero := congrArg ((tensorLeft coefficients.object).map)
      (comp_distTriang_mor_zero₁₂ T hT)
    change coefficients.object ◁ (T.mor₁ ≫ u) = _ at hzero
    rw [whiskerLeft_comp, Functor.map_zero] at hzero
    calc
      coefficients.object ◁ T.mor₁ = coefficients.object ◁ T.mor₁ ≫
          (coefficients.object ◁ u ≫ r) := by
            rw [hr]
            exact (Category.comp_id _).symm
      _ = 0 := by rw [← Category.assoc, hzero, zero_comp]
  exact HUnitConsequences.actual_coefficient_tensor_extension X T hT hz a

end
end KIP126.Literature.Standard.HModuleGenerator
end
