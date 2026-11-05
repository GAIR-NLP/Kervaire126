module
import all KIP126.Literature.E2Exactness.Ordinary.TensorCochainNormalization

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual unshifted layer map induced by transporting the strict parameter map. -/
private def conjugatedLayerMap {X Y : Spectrum} (f : X ⟶ Y) (s : ℤ) :
    (tensorTower coefficients.unit X).layer s ⟶ (tensorTower coefficients.unit Y).layer s :=
  (shiftFunctor Spectrum s).preimage
    ((shiftedLayerTensorIso coefficients.unit X s).hom ≫
      (baseTensorTower.layer s)⟦s⟧ ◁ f ≫ (shiftedLayerTensorIso coefficients.unit Y s).inv)

private theorem conjugatedLayerMap_shift {X Y : Spectrum} (f : X ⟶ Y) (s : ℤ) :
    (shiftFunctor Spectrum s).map (conjugatedLayerMap f s) =
      (shiftedLayerTensorIso coefficients.unit X s).hom ≫
        (baseTensorTower.layer s)⟦s⟧ ◁ f ≫ (shiftedLayerTensorIso coefficients.unit Y s).inv :=
  (shiftFunctor Spectrum s).map_preimage _

private theorem tensorFirstPageEquiv_conjugated {X Y : Spectrum} (f : X ⟶ Y)
    (t s : ℤ) (a : (tensorTower coefficients.unit X).FirstPage (s,t)) :
    tensorFirstPageEquiv coefficients.unit Y t s (a ≫ conjugatedLayerMap f s) =
      tensorFirstPageEquiv coefficients.unit X t s a ≫ (baseTensorTower.layer s)⟦s⟧ ◁ f := by
  change homShiftEquiv _ _ _ _ _ (a ≫ conjugatedLayerMap f s) ≫
      (shiftedLayerTensorIso coefficients.unit Y s).hom =
    (homShiftEquiv _ _ _ _ _ a ≫ (shiftedLayerTensorIso coefficients.unit X s).hom) ≫ _
  rw [homShiftEquiv_postcomp, conjugatedLayerMap_shift]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Exact residual equation for applying same-inclusion uniqueness. -/
private theorem conjugatedLayerMap_inclusion_iff {X Y : Spectrum} (f : X ⟶ Y) (s : ℤ) :
    (HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit X).mapAt (show s ≤ s+1 by omega)) ≫
      conjugatedLayerMap f s =
    (stageFunctor coefficients.unit s.toNat).map f ≫
      HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit Y).mapAt (show s ≤ s+1 by omega))) ↔
    (shiftFunctor Spectrum s).map (HasFunctorialCofiber.cofibι
        ((tensorTower coefficients.unit X).mapAt (show s ≤ s+1 by omega))) ≫
      (shiftedLayerTensorIso coefficients.unit X s).hom ≫
      (baseTensorTower.layer s)⟦s⟧ ◁ f =
    (shiftFunctor Spectrum s).map
      ((stageFunctor coefficients.unit s.toNat).map f ≫
        HasFunctorialCofiber.cofibι
          ((tensorTower coefficients.unit Y).mapAt (show s ≤ s+1 by omega))) ≫
      (shiftedLayerTensorIso coefficients.unit Y s).hom := by
  rw [← (shiftFunctor Spectrum s).map_injective.eq_iff,
    ← cancel_mono (shiftedLayerTensorIso coefficients.unit Y s).hom]
  rw [Functor.map_comp, conjugatedLayerMap_shift]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
end KIP126.Literature.Standard.TensorNormalization
