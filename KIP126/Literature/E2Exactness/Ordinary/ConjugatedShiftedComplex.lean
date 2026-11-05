module
import all KIP126.Literature.E2Exactness.Ordinary.ConjugatedTensorMap

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.FiniteBoundaryStage22
open KIP126.Literature.Standard.FixedTensorE2
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v

/-- Transport of the strict parameter map through the fixed objectwise comparisons. -/
private def conjugatedShiftedCochainMap {X Y : Spectrum} (f : X ⟶ Y) :
    shiftedLayerComplex (tensorTower coefficients.unit X) ⟶
      shiftedLayerComplex (tensorTower coefficients.unit Y) :=
  CochainComplex.ofHom (fun s =>
    (shiftedLayerTensorIso coefficients.unit X s).hom ≫
      (baseTensorTower.layer s)⟦s⟧ ◁ f ≫
      (shiftedLayerTensorIso coefficients.unit Y s).inv) (fun s => by
        rw [shiftedLayerComplex_d, shiftedLayerComplex_d]
        apply (cancel_mono (shiftedLayerTensorIso coefficients.unit Y (s+1)).hom).mp
        simp only [Category.assoc]
        rw [← shiftedLayerTensorIso_d]
        simp only [Iso.inv_hom_id_assoc]
        erw [whisker_exchange]
        rw [← Category.assoc]
        rw [shiftedLayerTensorIso_d]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)

private theorem conjugatedShiftedCochainMap_f {X Y : Spectrum} (f : X ⟶ Y) (s : ℤ) :
    (conjugatedShiftedCochainMap f).f s =
      (shiftedLayerTensorIso coefficients.unit X s).hom ≫
        (baseTensorTower.layer s)⟦s⟧ ◁ f ≫
        (shiftedLayerTensorIso coefficients.unit Y s).inv := rfl

section Zero
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [∀ A : C, (tensorRight A).CommShift ℤ]

/-- The shift-zero law forces the needed tensor-parameter compatibility at degree zero. -/
private theorem tensor_commShift_zero_parameter (L : C) {X Y : C} (f : X ⟶ Y) :
    ((tensorRight X).commShiftIso (0:ℤ)).inv.app L ≫
      L⟦(0:ℤ)⟧ ◁ f ≫ ((tensorRight Y).commShiftIso (0:ℤ)).hom.app L =
    (shiftFunctor C (0:ℤ)).map (L ◁ f) := by
  simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
    Functor.CommShift.isoZero_hom_app]
  change ((shiftFunctorZero C ℤ).hom.app (L ⊗ X) ≫
      ((shiftFunctorZero C ℤ).inv.app L ▷ X)) ≫ L⟦(0:ℤ)⟧ ◁ f ≫
      ((shiftFunctorZero C ℤ).hom.app L ▷ Y) ≫
      (shiftFunctorZero C ℤ).inv.app (L ⊗ Y) = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc]
  simp only [Iso.inv_hom_id_app, id_whiskerRight, Category.id_comp]
  exact NatIso.naturality_2 (shiftFunctorZero C ℤ) (L ◁ f)
end Zero

section Generic
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)
  [∀ A : C, (tensorRight A).CommShift ℤ] [∀ A : C, (tensorRight A).IsTriangulated]

private theorem layerTensorIso_parameter_inclusion {X Y : C} (f : X ⟶ Y) (s : ℤ) :
    HasFunctorialCofiber.cofibι ((tensorTower unit X).mapAt (show s ≤ s+1 by omega)) ≫
      (layerTensorIso unit X s).hom ≫ (tensorTower unit SphereSpectrum).layer s ◁ f =
    (stageFunctor unit s.toNat).map f ≫
      HasFunctorialCofiber.cofibι ((tensorTower unit Y).mapAt (show s ≤ s+1 by omega)) ≫
      (layerTensorIso unit Y s).hom := by
  rw [reassoc_of% (layerTensorIso_inclusion unit X s), layerTensorIso_inclusion unit Y s]
  erw [← whisker_exchange]
  have hn : (stageTensorIso unit X s.toNat).inv ≫
      tensorStage unit SphereSpectrum s.toNat ◁ f =
      (stageFunctor unit s.toNat).map f ≫ (stageTensorIso unit Y s.toNat).inv := by
    apply (cancel_mono (stageTensorIso unit Y s.toNat).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [stageTensorIso_natural]
    simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc]

private theorem shiftedLayerTensorIso_zero_parameter {X Y : C} (f : X ⟶ Y) :
    (shiftedLayerTensorIso unit X 0).hom ≫
      ((tensorTower unit SphereSpectrum).layer 0)⟦(0:ℤ)⟧ ◁ f ≫
      (shiftedLayerTensorIso unit Y 0).inv =
    (shiftFunctor C (0:ℤ)).map
      ((layerTensorIso unit X 0).hom ≫ (tensorTower unit SphereSpectrum).layer 0 ◁ f ≫
        (layerTensorIso unit Y 0).inv) := by
  change ((shiftFunctor C (0:ℤ)).map (layerTensorIso unit X 0).hom ≫
      ((tensorRight X).commShiftIso (0:ℤ)).inv.app _) ≫
      _ ◁ f ≫ ((tensorRight Y).commShiftIso (0:ℤ)).hom.app _ ≫
      (shiftFunctor C (0:ℤ)).map (layerTensorIso unit Y 0).inv = _
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% (tensor_commShift_zero_parameter ((tensorTower unit SphereSpectrum).layer 0) f)]
end Generic

private theorem conjugatedShiftedCochainMap_augmentation_zero {X Y : Spectrum} (f : X ⟶ Y) :
    (shiftFunctor Spectrum (0:ℤ)).map
      (HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit X).mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫
      (conjugatedShiftedCochainMap f).f 0 =
    (shiftFunctor Spectrum (0:ℤ)).map
      ((stageFunctor coefficients.unit 0).map f ≫
        HasFunctorialCofiber.cofibι
          ((tensorTower coefficients.unit Y).mapAt (show (0:ℤ) ≤ 0+1 by omega))) := by
  rw [conjugatedShiftedCochainMap_f]
  change (shiftFunctor Spectrum (0:ℤ)).map _ ≫
      ((shiftedLayerTensorIso coefficients.unit X 0).hom ≫
        ((tensorTower coefficients.unit SphereSpectrum).layer 0)⟦(0:ℤ)⟧ ◁ f ≫
        (shiftedLayerTensorIso coefficients.unit Y 0).inv) = _
  rw [shiftedLayerTensorIso_zero_parameter, ← Functor.map_comp]
  apply congrArg ((shiftFunctor Spectrum (0:ℤ)).map)
  erw [reassoc_of% (layerTensorIso_parameter_inclusion coefficients.unit f 0)]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rfl

end
end KIP126.Literature.Standard.TensorNormalization
