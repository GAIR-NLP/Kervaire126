module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ComparisonHomology
import all KIP126.Literature.E2Exactness.Ordinary.ActualAugmentedComparison
import all KIP126.Literature.E2Exactness.Ordinary.TensorCochainNormalization

@[expose] section
namespace KIP126.Literature.Standard.E2TowerComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.E2AugmentedComparison
open KIP126.Literature.Standard.TensorNormalization
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.BocksteinComparison.Stages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {X Y : Spectrum}

private theorem comparison_cochain_homology_square
    {T T' : AbstractAdamsTower coefficients.unit X}
    {U U' : AbstractAdamsTower coefficients.unit Y} {f : X ⟶ Y}
    (φ : TowerMap coefficients.unit T U f) (ψ : TowerMap coefficients.unit T' U' f)
    (cT : TowerMap coefficients.unit T T' (𝟙 X))
    (cU : TowerMap coefficients.unit U U' (𝟙 Y)) (t s : ℤ) :
    homologyMap (cochainMap φ t) s ≫ homologyMap (cochainMap cU t) s =
      homologyMap (cochainMap cT t) s ≫ homologyMap (cochainMap ψ t) s := by
  rw [← homologyMap_comp, ← homologyMap_comp]
  apply homologyMap_eq_of_shifted_conjugation T U' t s _ _
    (shiftedLayerComplexMap φ ≫ shiftedLayerComplexMap cU)
    (shiftedLayerComplexMap cT ≫ shiftedLayerComplexMap ψ)
    (shiftedHomotopyCochainIso_composite φ cU t)
    (shiftedHomotopyCochainIso_composite cT ψ t)
  exact actual_homotopyCochain_homologyMap_eq T U' _ _
    (comparison_square_same_augmentation φ ψ cT cU) t s

private theorem fixedTowerCochainIso_homology_natural
    {T : AbstractAdamsTower coefficients.unit X} {U : AbstractAdamsTower coefficients.unit Y}
    {f : X ⟶ Y} (φ : TowerMap coefficients.unit T U f) (t s : ℤ) :
    homologyMap (cochainMap φ t) s ≫ homologyMap (fixedTowerCochainIso U t).hom s =
      homologyMap (fixedTowerCochainIso T t).hom s ≫
        homologyMap (cochainMap (tensorTowerMap coefficients.unit f) t) s := by
  exact comparison_cochain_homology_square φ (tensorTowerMap coefficients.unit f)
    (comparisonMap T (tensorTower coefficients.unit X) (Iso.refl X))
    (comparisonMap U (tensorTower coefficients.unit Y) (Iso.refl Y)) t s

end
end KIP126.Literature.Standard.E2TowerComparison
end
