module
import all KIP126.Literature.E2Exactness.Ordinary.ShiftNormalization
import all KIP126.Literature.E2Exactness.Ordinary.LayerTensorComparison
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private theorem desuspend_postcomp {Y Z : C} (f : Y ⟶ Z) (m : ℤ)
    (a : HomotopyGroup m (Y⟦(1:ℤ)⟧)) :
    AbstractAdamsTower.desuspend Z m (a ≫ (shiftFunctor C (1:ℤ)).map f) =
      AbstractAdamsTower.desuspend Y m a ≫ f := by
  dsimp [AbstractAdamsTower.desuspend]
  simp only [Functor.map_comp, Category.assoc]
  have h := (shiftFunctorCompIsoId C (1:ℤ) (-1) (by omega)).hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [h]

variable [HasFunctorialCofiber (C := C)] {H Y : C} {unit : SphereSpectrum ⟶ H}

private theorem cochainDifferential_shift (T : AbstractAdamsTower unit Y) (t s : ℤ)
    (a : T.FirstPage (s,t)) :
    homShiftEquiv (T.layer (s+1)) (t-(s+1)) (s+1) t (by omega)
      (cochainDifferential T t s a) =
    homShiftEquiv (T.layer s) (t-s) s t (by omega) a ≫
      (shiftFunctor C s).map (layerBoundary unit T s) ≫
      (shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app (T.layer (s+1)) := by
  change homShiftEquiv _ _ _ _ _
    (homotopyDegreeEquiv _ (by omega : t-s-1=t-(s+1))
      (AbstractAdamsTower.desuspend _ (t-s)
        (a ≫ HasFunctorialCofiber.cofibδ (T.mapAt _))) ≫
      HasFunctorialCofiber.cofibι (T.mapAt _)) = _
  rw [← homotopyDegreeEquiv_postcomp, homShiftEquiv_degreeCast,
    ← desuspend_postcomp, homShiftEquiv_desuspend_shift, homShiftEquiv_postcomp]
  all_goals try omega
  rw [homShiftEquiv_postcomp]
  simp only [layerBoundary, Functor.map_comp, Category.assoc]
  rfl

end
end KIP126.Literature.Standard.TensorNormalization
