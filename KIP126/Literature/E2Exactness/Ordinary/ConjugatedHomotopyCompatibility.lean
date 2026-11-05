module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ConjugatedAugmentation
import all KIP126.Literature.E2Exactness.Ordinary.ShiftedHomotopyCochain

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.Standard.FixedTensorE2
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def conjugatedTensorCochainMap {X Y : Spectrum} (f : X ⟶ Y) (t : ℤ) :
    cochain (tensorTower coefficients.unit X) t ⟶ cochain (tensorTower coefficients.unit Y) t :=
  (tensorTowerCochainIso X t).hom ≫ tensorHomotopyCochainMap baseTensorTower t f ≫
    (tensorTowerCochainIso Y t).inv

/-- Two descriptions of the transported strict map agree before taking homology. -/
private theorem conjugatedTensorCochainMap_shifted {X Y : Spectrum} (f : X ⟶ Y) (t : ℤ) :
    conjugatedTensorCochainMap f t ≫
      (shiftedHomotopyCochainIso (tensorTower coefficients.unit Y) t).hom =
    (shiftedHomotopyCochainIso (tensorTower coefficients.unit X) t).hom ≫
      homotopyCochainMap (conjugatedShiftedCochainMap f) t := by
  ext s a
  change homShiftEquiv _ _ _ _ _
      ((homShiftEquiv _ _ _ _ _).symm
        (((homShiftEquiv _ _ _ _ _ a ≫ (shiftedLayerTensorIso coefficients.unit X s).hom) ≫
          (baseTensorTower.layer s)⟦s⟧ ◁ f) ≫
          (shiftedLayerTensorIso coefficients.unit Y s).inv)) =
    homShiftEquiv _ _ _ _ _ a ≫
      ((shiftedLayerTensorIso coefficients.unit X s).hom ≫
        (baseTensorTower.layer s)⟦s⟧ ◁ f ≫ (shiftedLayerTensorIso coefficients.unit Y s).inv)
  simp only [LinearEquiv.apply_symm_apply, Category.assoc]

end
end KIP126.Literature.Standard.TensorNormalization
