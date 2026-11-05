module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ConjugatedHomotopyCompatibility
import all KIP126.Literature.E2Exactness.Ordinary.ActualAugmentedComparison
import all KIP126.Literature.E2Exactness.Ordinary.ComparisonHomology

@[expose] section
namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.E2AugmentedComparison
open KIP126.Literature.Standard.E2TowerComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The objectwise normalization retains the original chosen tower maps on
cohomology, using the same degree-zero augmentation. -/
private theorem tensorTowerCochainIso_homology_natural
    {X Y : Spectrum} (f : X ⟶ Y) (t s : ℤ) :
    homologyMap (cochainMap (tensorTowerMap coefficients.unit f) t) s ≫
        homologyMap (tensorTowerCochainIso Y t).hom s =
      homologyMap (tensorTowerCochainIso X t).hom s ≫
        homologyMap (tensorHomotopyCochainMap baseTensorTower t f) s := by
  have he : homologyMap (conjugatedTensorCochainMap f t) s =
      homologyMap (cochainMap (tensorTowerMap coefficients.unit f) t) s :=
    homologyMap_eq_of_shifted_conjugation
      (tensorTower coefficients.unit X) (tensorTower coefficients.unit Y) t s
      (conjugatedTensorCochainMap f t) (cochainMap (tensorTowerMap coefficients.unit f) t)
      (conjugatedShiftedCochainMap f) (shiftedLayerComplexMap (tensorTowerMap coefficients.unit f))
      (conjugatedTensorCochainMap_shifted f t)
      (shiftedHomotopyCochainIso_natural (tensorTowerMap coefficients.unit f) t)
      (actual_homotopyCochain_homologyMap_eq _ _ _ _
        (conjugatedShiftedCochainMap_same_augmentation f) t s)
  rw [← he, ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  simp only [conjugatedTensorCochainMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
end KIP126.Literature.Standard.TensorNormalization
end
