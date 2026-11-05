module
import all KIP126.Literature.E2Exactness.Ordinary.TensorFiniteIntervals

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.FiniteBoundaryStage22
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)
  [∀ A : C, (tensorRight A).CommShift ℤ] [∀ A : C, (tensorRight A).IsTriangulated]

private def layerBoundary {Y : C} (T : AbstractAdamsTower unit Y) (s : ℤ) :
    T.layer s ⟶ (T.layer (s+1))⟦(1:ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega)) ≫
    (shiftFunctor C (1:ℤ)).map
      (HasFunctorialCofiber.cofibι (T.mapAt (show s+1 ≤ (s+1)+1 by omega)))

/-- The natural-interval comparison includes equal endpoints and hence every integer layer. -/
private def layerTensorIso (X : C) (s : ℤ) :
    (tensorTower unit X).layer s ≅ (tensorTower unit SphereSpectrum).layer s ⊗ X :=
  intervalCofiberIso unit X s.toNat (s+1).toNat (by omega)

private theorem layerTensorIso_inclusion (X : C) (s : ℤ) :
    HasFunctorialCofiber.cofibι ((tensorTower unit X).mapAt (show s ≤ s+1 by omega)) ≫
      (layerTensorIso unit X s).hom =
    (stageTensorIso unit X s.toNat).inv ≫
      (HasFunctorialCofiber.cofibι
        ((tensorTower unit SphereSpectrum).mapAt (show s ≤ s+1 by omega)) ▷ X) :=
  intervalCofiberIso_inclusion unit X s.toNat (s+1).toNat (by omega)

private theorem layerTensorIso_boundary (X : C) (s : ℤ) :
    (layerTensorIso unit X s).hom ≫
      (HasFunctorialCofiber.cofibδ
        ((tensorTower unit SphereSpectrum).mapAt (show s ≤ s+1 by omega)) ▷ X) ≫
      ((tensorRight X).commShiftIso (1:ℤ)).hom.app
        ((tensorTower unit SphereSpectrum).stageAt (s+1)) =
    HasFunctorialCofiber.cofibδ ((tensorTower unit X).mapAt (show s ≤ s+1 by omega)) ≫
      (shiftFunctor C (1:ℤ)).map (stageTensorIso unit X (s+1).toNat).inv :=
  intervalCofiberIso_boundary unit X s.toNat (s+1).toNat (by omega)

private theorem layerTensorIso_layerBoundary (X : C) (s : ℤ) :
    (layerTensorIso unit X s).hom ≫
      (layerBoundary unit (tensorTower unit SphereSpectrum) s ▷ X) ≫
      ((tensorRight X).commShiftIso (1:ℤ)).hom.app
        ((tensorTower unit SphereSpectrum).layer (s+1)) =
    layerBoundary unit (tensorTower unit X) s ≫
      (shiftFunctor C (1:ℤ)).map (layerTensorIso unit X (s+1)).hom := by
  dsimp only [layerBoundary]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  have hn := (tensorRight X).commShiftIso_hom_naturality
    (HasFunctorialCofiber.cofibι
      ((tensorTower unit SphereSpectrum).mapAt (show s+1 ≤ (s+1)+1 by omega))) (1:ℤ)
  change ((shiftFunctor C (1:ℤ)).map _ ▷ X) ≫ _ =
    ((tensorRight X).commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor C (1:ℤ)).map (_ ▷ X) at hn
  erw [hn]
  erw [reassoc_of% (layerTensorIso_boundary unit X s)]
  rw [← Functor.map_comp]
  erw [← layerTensorIso_inclusion unit X (s+1)]
  rw [Functor.map_comp]

end
end KIP126.Literature.Standard.TensorNormalization
