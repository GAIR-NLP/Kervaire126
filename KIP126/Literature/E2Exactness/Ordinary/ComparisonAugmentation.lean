module
import all KIP126.Literature.E2Exactness.Ordinary.ShiftedTowerCochainMap

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X Y : C} {unit : SphereSpectrum ⟶ H}
  {T T' : AbstractAdamsTower unit X} {U U' : AbstractAdamsTower unit Y} {f : X ⟶ Y}

private theorem comparison_square_stage_zero
    (φ : TowerMap unit T U f) (ψ : TowerMap unit T' U' f)
    (cT : TowerMap unit T T' (𝟙 X)) (cU : TowerMap unit U U' (𝟙 Y)) :
    φ.stage 0 ≫ cU.stage 0 = cT.stage 0 ≫ ψ.stage 0 := by
  apply (cancel_mono U'.zeroIso.hom).mp
  simp only [Category.assoc, cU.zero, ψ.zero, Category.comp_id]
  rw [φ.zero, ← Category.assoc, cT.zero, Category.comp_id]

private theorem comparison_square_same_augmentation
    (φ : TowerMap unit T U f) (ψ : TowerMap unit T' U' f)
    (cT : TowerMap unit T T' (𝟙 X)) (cU : TowerMap unit U U' (𝟙 Y)) :
    (shiftFunctor C (0:ℤ)).map
      (HasFunctorialCofiber.cofibι (T.mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      ((shiftedLayerComplexMap φ) ≫ (shiftedLayerComplexMap cU)).f 0 =
    (shiftFunctor C (0:ℤ)).map
      (HasFunctorialCofiber.cofibι (T.mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      ((shiftedLayerComplexMap cT) ≫ (shiftedLayerComplexMap ψ)).f 0 := by
  change _ ≫ ((shiftedLayerComplexMap φ).f 0 ≫ (shiftedLayerComplexMap cU).f 0) =
    _ ≫ ((shiftedLayerComplexMap cT).f 0 ≫ (shiftedLayerComplexMap ψ).f 0)
  rw [← Category.assoc, ← Category.assoc,
    shiftedLayerComplexMap_augmentation, shiftedLayerComplexMap_augmentation]
  rw [Category.assoc, Category.assoc,
    shiftedLayerComplexMap_augmentation, shiftedLayerComplexMap_augmentation]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    comparison_square_stage_zero φ ψ cT cU]
  simp only [Functor.map_comp]
end
end KIP126.Literature.Standard.FixedTensorE2
end
