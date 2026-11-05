module
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorComplex

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X Y : C} {unit : SphereSpectrum ⟶ H}
  {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}

private theorem layerBoundary_natural (φ : TowerMap unit T U f) (s : ℤ) :
    φ.layer s ≫ layerBoundary U s =
      layerBoundary T s ≫ (shiftFunctor C (1:ℤ)).map (φ.layer (s+1)) := by
  dsimp only [layerBoundary]
  rw [← Category.assoc]
  erw [HasFunctorialCofiber.cofibMap_δ]
  rw [Category.assoc, ← Functor.map_comp]
  rw [HasFunctorialCofiber.cofibMap_ι
    (T.mapAt (show s+1 ≤ (s+1)+1 by omega))
    (U.mapAt (show s+1 ≤ (s+1)+1 by omega))
    (φ.stage ((s+1)+1).toNat) (φ.stage (s+1).toNat) (φ.natural _)]
  rw [Functor.map_comp, Category.assoc]
  rfl

private theorem shiftedLayerDifferential_natural (φ : TowerMap unit T U f) (s : ℤ) :
    (shiftFunctor C s).map (φ.layer s) ≫ shiftedLayerDifferential U s =
      shiftedLayerDifferential T s ≫ (shiftFunctor C (s+1)).map (φ.layer (s+1)) := by
  dsimp only [shiftedLayerDifferential]
  rw [← Category.assoc, ← Functor.map_comp, layerBoundary_natural, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg ((shiftFunctor C s).map (layerBoundary T s) ≫ ·)
    ((shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.naturality (φ.layer (s+1)))

private def shiftedLayerComplexMap (φ : TowerMap unit T U f) :
    shiftedLayerComplex T ⟶ shiftedLayerComplex U :=
  CochainComplex.ofHom (fun s => (shiftFunctor C s).map (φ.layer s)) (fun s => by
    rw [shiftedLayerComplex_d, shiftedLayerComplex_d]
    exact shiftedLayerDifferential_natural φ s)

private theorem shiftedLayerComplexMap_f (φ : TowerMap unit T U f) (s : ℤ) :
    (shiftedLayerComplexMap φ).f s = (shiftFunctor C s).map (φ.layer s) := rfl

private theorem shiftedLayerComplexMap_augmentation (φ : TowerMap unit T U f) :
    (shiftFunctor C (0:ℤ)).map
      (HasFunctorialCofiber.cofibι (T.mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      (shiftedLayerComplexMap φ).f 0 =
    (shiftFunctor C (0:ℤ)).map (φ.stage 0) ≫
      (shiftFunctor C (0:ℤ)).map
        (HasFunctorialCofiber.cofibι (U.mapAt (show (0:ℤ) ≤ 0+1 by omega))) := by
  rw [shiftedLayerComplexMap_f, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (HasFunctorialCofiber.cofibMap_ι _ _ _ _ _).symm
end
end KIP126.Literature.Standard.FixedTensorE2
end
