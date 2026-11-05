module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.DifferentialNormalization
import all KIP126.Literature.E2Exactness.Ordinary.FunctorShiftNormalization
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorComplex

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.Standard.FixedTensorE2
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def postcomposeHomEquiv {A B : C} (e : A ≅ B) (P : C) : (P ⟶ A) ≃ₗ[ℤ] (P ⟶ B) :=
  (show (P ⟶ A) ≃+ (P ⟶ B) from
    { toFun := fun a => a ≫ e.hom
      invFun := fun a => a ≫ e.inv
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_add' := fun a b => Preadditive.add_comp _ _ _ a b e.hom }).toIntLinearEquiv

variable [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)
  [∀ A : C, (tensorRight A).CommShift ℤ] [∀ A : C, (tensorRight A).IsTriangulated]

private def shiftedLayerTensorIso (X : C) (s : ℤ) :
    ((tensorTower unit X).layer s)⟦s⟧ ≅ ((tensorTower unit SphereSpectrum).layer s)⟦s⟧ ⊗ X :=
  (shiftFunctor C s).mapIso (layerTensorIso unit X s) ≪≫
    ((tensorRight X).commShiftIso s).symm.app ((tensorTower unit SphereSpectrum).layer s)

private theorem shiftedLayerTensorIso_d (X : C) (s : ℤ) :
    (shiftedLayerTensorIso unit X s).hom ≫
      (shiftedLayerDifferential (tensorTower unit SphereSpectrum) s ▷ X) =
    shiftedLayerDifferential (tensorTower unit X) s ≫
      (shiftedLayerTensorIso unit X (s+1)).hom := by
  exact shifted_boundary_transport (tensorRight X)
    (layerBoundary unit (tensorTower unit SphereSpectrum) s)
    (layerBoundary unit (tensorTower unit X) s)
    (layerTensorIso unit X s).hom (layerTensorIso unit X (s+1)).hom
    (layerTensorIso_layerBoundary unit X s) s

private def tensorFirstPageEquiv (X : C) (t s : ℤ) :
    (tensorTower unit X).FirstPage (s,t) ≃ₗ[ℤ]
      HomotopyGroup t (((tensorTower unit SphereSpectrum).layer s)⟦s⟧ ⊗ X) :=
  (homShiftEquiv ((tensorTower unit X).layer s) (t-s) s t (by omega)).trans
    (postcomposeHomEquiv (shiftedLayerTensorIso unit X s) (Sphere t))

private theorem tensorFirstPageEquiv_d (X : C) (t s : ℤ)
    (a : (tensorTower unit X).FirstPage (s,t)) :
    tensorFirstPageEquiv unit X t (s+1) (cochainDifferential (tensorTower unit X) t s a) =
      tensorFirstPageEquiv unit X t s a ≫
        (shiftedLayerDifferential (tensorTower unit SphereSpectrum) s ▷ X) := by
  change homShiftEquiv _ _ _ _ _ (cochainDifferential _ _ _ a) ≫
      (shiftedLayerTensorIso unit X (s+1)).hom =
    (homShiftEquiv _ _ _ _ _ a ≫ (shiftedLayerTensorIso unit X s).hom) ≫ _
  rw [cochainDifferential_shift]
  change (homShiftEquiv _ _ _ _ _ a ≫ shiftedLayerDifferential (tensorTower unit X) s) ≫
      (shiftedLayerTensorIso unit X (s+1)).hom = _
  rw [Category.assoc, ← shiftedLayerTensorIso_d, ← Category.assoc]

section Actual
open KIP126.AdamsSynthetic.Completed
private instance tensorRightCommShift (X : Spectrum) : (tensorRight X).CommShift ℤ :=
  closedBackground.tensorShift X
private instance tensorRightExact (X : Spectrum) : (tensorRight X).IsTriangulated :=
  closedBackground.tensorExact X

private def baseTensorTower : AbstractAdamsTower coefficients.unit (SphereSpectrum : Spectrum) :=
  tensorTower coefficients.unit SphereSpectrum

/-- Objectwise chain isomorphism at the specified tensor parameter. -/
private def tensorTowerCochainIso (X : Spectrum) (t : ℤ) :
    cochain (tensorTower coefficients.unit X) t ≅
      tensorHomotopyCochain baseTensorTower t X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s => (tensorFirstPageEquiv coefficients.unit X t s).toModuleIso) (by
      intro s r h
      have hr : s+1=r := h
      subst r
      rw [cochain_d, tensorHomotopyCochain_d]
      ext a
      exact (tensorFirstPageEquiv_d coefficients.unit X t s a).symm)

private def tensorHomotopyCochainIso (X : Spectrum) (t : ℤ) :
    tensorHomotopyCochain baseTensorTower t X ≅
      cochain (tensorTower coefficients.unit X) t :=
  (tensorTowerCochainIso X t).symm

end Actual
end
end KIP126.Literature.Standard.TensorNormalization
