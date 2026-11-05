module
import all KIP126.Literature.E2Exactness.CoefficientConsequences
import KIP126.AdamsSynthetic.Tower
import KIP126.SpectralSequence.ModuleSubobject.Proofs
import Mathlib.CategoryTheory.Shift.CommShift

@[expose] section
namespace KIP126.Literature.Standard.E2MapComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated CategoryTheory.BraidedCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private def coefficientShiftIso (Y : Spectrum) (n : ℤ) :
    (coefficients.object ⊗ Y)⟦n⟧ ≅ coefficients.object ⊗ Y⟦n⟧ := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI : (tensorLeft coefficients.object).CommShift ℤ :=
    Functor.CommShift.ofIso (tensorLeftIsoTensorRight coefficients.object).symm ℤ
  exact ((tensorLeft coefficients.object).commShiftIso n).symm.app Y

private theorem shifted_tensor_zero {A B : Spectrum} (f : A ⟶ B)
    (hf : coefficients.object ◁ f = 0) (n : ℤ) :
    coefficients.object ◁ (shiftFunctor Spectrum n).map f = 0 := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI : (tensorLeft coefficients.object).CommShift ℤ :=
    Functor.CommShift.ofIso (tensorLeftIsoTensorRight coefficients.object).symm ℤ
  let F := tensorLeft coefficients.object
  apply (cancel_mono ((F.commShiftIso n).hom.app B)).mp
  rw [zero_comp]
  change F.map ((shiftFunctor Spectrum n).map f) ≫ _ = 0
  rw [F.commShiftIso_hom_naturality]
  change _ ≫ (shiftFunctor Spectrum n).map (coefficients.object ◁ f) = 0
  rw [hf, Functor.map_zero, comp_zero]

private theorem tensor_annihilates {A B : Spectrum} (f : A ⟶ B)
    (hf : coefficients.object ◁ f = 0) (Y : Spectrum)
    (g : B ⟶ coefficients.object ⊗ Y) : f ≫ g = 0 :=
  HModuleSplit.coefficient_tensor_annihilates coefficients.object Y coefficients.unit
    HUnitConsequences.multiplication HUnitConsequences.multiplication_left_unit f hf g

private theorem shifted_tensor_annihilates {A B : Spectrum} (f : A ⟶ B)
    (hf : coefficients.object ◁ f = 0) (Y : Spectrum) (n : ℤ)
    (g : B ⟶ (coefficients.object ⊗ Y)⟦n⟧) : f ≫ g = 0 := by
  apply (cancel_mono (coefficientShiftIso Y n).hom).mp
  simpa only [Category.assoc, zero_comp] using
    tensor_annihilates f hf (Y⟦n⟧) (g ≫ (coefficientShiftIso Y n).hom)

private def stepTriangle {X : Spectrum} (T : AbstractAdamsTower coefficients.unit X)
    (s : ℕ) : Triangle Spectrum :=
  Triangle.mk (T.map (Nat.le_succ s)) (HasFunctorialCofiber.cofibι (T.map (Nat.le_succ s)))
    (HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ s)))

private theorem shifted_layer_annihilates {A B X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℕ) (n : ℤ)
    (f : A ⟶ B) (hf : coefficients.object ◁ f = 0)
    (g : B ⟶ ((stepTriangle T s).obj₃)⟦n⟧) : f ≫ g = 0 := by
  apply (cancel_mono ((shiftFunctor Spectrum n).map (T.layerIso s).hom)).mp
  simpa only [Category.assoc, zero_comp] using
    shifted_tensor_annihilates f hf (T.stage s) n
      (g ≫ (shiftFunctor Spectrum n).map (T.layerIso s).hom)

private theorem layer_negative_isZero {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) (hs : s < 0) :
    IsZero (T.layer s) := by
  let f := T.mapAt (show s ≤ s+1 by omega)
  have hf : IsIso f := by
    have hi (m n : ℕ) (h : m ≤ n) (he : m = n) : IsIso (T.map h) := by
      subst n
      rw [T.map_self]
      infer_instance
    exact hi _ _ _ (by omega)
  exact Triangle.isZero₃_of_isIso₁ _ (HasFunctorialCofiber.cofib_distinguished f) hf

end
end KIP126.Literature.Standard.E2MapComparison
end
