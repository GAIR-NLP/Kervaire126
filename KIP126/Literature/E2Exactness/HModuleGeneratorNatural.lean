module
import all KIP126.Literature.E2Exactness.HModuleGenerator

@[expose] section
namespace KIP126.Literature.Standard.HModuleGenerator
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated CategoryTheory.BraidedCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A single fixed retraction for each integer degree. Its choice depends
only on d and the fixed coefficient data, never on X or its sphere class. -/
private def shiftedUnitTensorRetraction (d : ℤ) :
    coefficients.object ⊗ coefficients.object⟦d⟧ ⟶
      coefficients.object ⊗ SphereSpectrum⟦d⟧ :=
  (coefficient_tensor_shift_unit_split d).choose

private theorem shiftedUnitTensorRetraction_spec (d : ℤ) :
    coefficients.object ◁ ((shiftFunctor Spectrum d).map coefficients.unit) ≫
      shiftedUnitTensorRetraction d = 𝟙 _ :=
  (coefficient_tensor_shift_unit_split d).choose_spec

/-- The action on H⊗X induced by μ. -/
private def coefficientAction (X : Spectrum) :
    coefficients.object ⊗ (coefficients.object ⊗ X) ⟶ coefficients.object ⊗ X :=
  (α_ coefficients.object coefficients.object X).inv ≫
    HUnitConsequences.multiplication ▷ X

/-- Extend every actual degree-d sphere class using the same fixed
unit retraction and the actual μ action. -/
private def generatorExtension (X : Spectrum) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X)) :
    coefficients.object⟦d⟧ ⟶ coefficients.object ⊗ X :=
  HModuleSplit.eta coefficients.object (coefficients.object⟦d⟧) coefficients.unit ≫
    shiftedUnitTensorRetraction d ≫ coefficients.object ◁ a ≫ coefficientAction X

private theorem generatorExtension_unit (X : Spectrum) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X)) :
    (shiftFunctor Spectrum d).map coefficients.unit ≫ generatorExtension X d a = a := by
  dsimp only [generatorExtension]
  rw [← Category.assoc ((shiftFunctor Spectrum d).map coefficients.unit),
    ← HModuleSplit.eta_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (coefficients.object ◁ ((shiftFunctor Spectrum d).map coefficients.unit)),
    shiftedUnitTensorRetraction_spec, Category.id_comp]
  exact HModuleSplit.coefficient_tensor_factor coefficients.object X coefficients.unit
    HUnitConsequences.multiplication HUnitConsequences.multiplication_left_unit a

private theorem coefficientAction_natural {X Y : Spectrum} (f : X ⟶ Y) :
    coefficientAction X ≫ coefficients.object ◁ f =
      coefficients.object ◁ (coefficients.object ◁ f) ≫ coefficientAction Y := by
  dsimp only [coefficientAction]
  simp only [Category.assoc]
  rw [← whisker_exchange]
  rw [← associator_inv_naturality_right_assoc]

private theorem generatorExtension_natural {X Y : Spectrum} (f : X ⟶ Y) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X)) :
    generatorExtension X d a ≫ coefficients.object ◁ f =
      generatorExtension Y d (a ≫ coefficients.object ◁ f) := by
  dsimp only [generatorExtension]
  simp only [Category.assoc, coefficientAction_natural, whiskerLeft_comp]

private theorem generatorExtension_zero (X : Spectrum) (d : ℤ) :
    generatorExtension X d (0 : HomotopyGroup d (coefficients.object ⊗ X)) = 0 := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  letI : (tensorLeft coefficients.object).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (tensorLeftIsoTensorRight coefficients.object).symm
  dsimp only [generatorExtension]
  change _ ≫ _ ≫ (tensorLeft coefficients.object).map 0 ≫ _ = _
  rw [Functor.map_zero, zero_comp, comp_zero, comp_zero]

/-- Annihilation of the chosen canonical generator extensions. -/
private theorem generatorExtension_annihilated {X Y : Spectrum} (f : X ⟶ Y) (d : ℤ)
    (a : HomotopyGroup d (coefficients.object ⊗ X))
    (ha : a ≫ coefficients.object ◁ f = 0) :
    generatorExtension X d a ≫ coefficients.object ◁ f = 0 := by
  rw [generatorExtension_natural, ha, generatorExtension_zero]

end
end KIP126.Literature.Standard.HModuleGenerator
end
