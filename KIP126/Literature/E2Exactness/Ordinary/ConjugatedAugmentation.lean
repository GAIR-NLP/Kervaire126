module
import all KIP126.Literature.E2Exactness.Ordinary.ConjugatedShiftedComplex
import all KIP126.Literature.E2Exactness.Ordinary.ShiftedTowerCochainMap

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.Standard.FixedTensorE2
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The transported strict map and the actual chosen tower map extend the same augmentation. -/
private theorem conjugatedShiftedCochainMap_same_augmentation {X Y : Spectrum} (f : X ⟶ Y) :
    (shiftFunctor Spectrum (0:ℤ)).map
      (HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit X).mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      (conjugatedShiftedCochainMap f).f 0 =
    (shiftFunctor Spectrum (0:ℤ)).map
      (HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit X).mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      (shiftedLayerComplexMap (tensorTowerMap coefficients.unit f)).f 0 := by
  rw [conjugatedShiftedCochainMap_augmentation_zero,
    shiftedLayerComplexMap_augmentation, ← Functor.map_comp]
  rfl

end
end KIP126.Literature.Standard.TensorNormalization
