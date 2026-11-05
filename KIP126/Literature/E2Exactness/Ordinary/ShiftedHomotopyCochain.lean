module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.HomotopyComplex
import all KIP126.Literature.E2Exactness.Ordinary.ShiftedTowerCochainMap
import all KIP126.Literature.E2Exactness.Ordinary.DifferentialNormalization

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.Standard.TensorNormalization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X Y : C} {unit : SphereSpectrum ⟶ H}

private def shiftedHomotopyCochainIso (T : AbstractAdamsTower unit X) (t : ℤ) :
    cochain T t ≅ homotopyCochain (shiftedLayerComplex T) t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s => (homShiftEquiv (T.layer s) (t-s) s t (by omega)).toModuleIso) (by
      intro s r h
      have hr : s+1=r := h
      subst r
      rw [cochain_d]
      change _ ≫ (homotopyModuleFunctor t).map ((shiftedLayerComplex T).d s (s+1)) = _
      rw [shiftedLayerComplex_d]
      ext a
      change homShiftEquiv _ _ _ _ _ a ≫ shiftedLayerDifferential T s =
        homShiftEquiv _ _ _ _ _ (cochainDifferential T t s a)
      exact (cochainDifferential_shift T t s a).symm)

private theorem shiftedHomotopyCochainIso_natural
    {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}
    (φ : TowerMap unit T U f) (t : ℤ) :
    cochainMap φ t ≫ (shiftedHomotopyCochainIso U t).hom =
      (shiftedHomotopyCochainIso T t).hom ≫ homotopyCochainMap (shiftedLayerComplexMap φ) t := by
  ext s a
  change homShiftEquiv _ _ _ _ _ (a ≫ φ.layer s) =
    homShiftEquiv _ _ _ _ _ a ≫ (shiftFunctor C s).map (φ.layer s)
  exact homShiftEquiv_postcomp _ _ _ _ _ _
end
end KIP126.Literature.Standard.FixedTensorE2
end
