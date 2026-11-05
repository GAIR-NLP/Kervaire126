module

import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.ShiftedCoefficients

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.HModuleDecomposition
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def homShiftEquiv (Y : C) (m n k : ℤ) (h : m+n=k) :
    HomotopyGroup m Y ≃ₗ[ℤ] HomotopyGroup k (Y⟦n⟧) :=
  ((shiftMapAddEquiv n (Sphere m) Y).trans
    (precomposeAddEquiv ((shiftFunctorAdd' C m n k h).app SphereSpectrum) _)).toIntLinearEquiv

private theorem homShiftEquiv_apply (Y : C) (m n k : ℤ) (h : m+n=k)
    (a : HomotopyGroup m Y) :
    homShiftEquiv Y m n k h a =
      (shiftFunctorAdd' C m n k h).hom.app SphereSpectrum ≫ (shiftFunctor C n).map a := rfl

private theorem homShiftEquiv_postcomp {Y Z : C} (f : Y ⟶ Z)
    (m n k : ℤ) (h : m+n=k) (a : HomotopyGroup m Y) :
    homShiftEquiv Z m n k h (a ≫ f) =
      homShiftEquiv Y m n k h a ≫ (shiftFunctor C n).map f := by
  simp only [homShiftEquiv_apply, Functor.map_comp, Category.assoc]

private theorem homShiftEquiv_comp (Y : C) (a b c ab bc abc : ℤ)
    (hab : a+b=ab) (hbc : b+c=bc) (habc : a+b+c=abc) (x : HomotopyGroup a Y) :
    homShiftEquiv (Y⟦b⟧) ab c abc (by omega) (homShiftEquiv Y a b ab hab x) =
      homShiftEquiv Y a bc abc (by omega) x ≫ (shiftFunctorAdd' C b c bc hbc).hom.app Y := by
  simp only [homShiftEquiv_apply, Functor.map_comp]
  rw [← Category.assoc, shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc habc]
  rw [Category.assoc]
  have hn := (shiftFunctorAdd' C b c bc hbc).hom.naturality x
  change (shiftFunctor C bc).map x ≫ (shiftFunctorAdd' C b c bc hbc).hom.app Y =
    (shiftFunctorAdd' C b c bc hbc).hom.app (Sphere a) ≫
      (shiftFunctor C c).map ((shiftFunctor C b).map x) at hn
  rw [← hn, Category.assoc]

private theorem homShiftEquiv_desuspend (Y : C) (m : ℤ)
    (x : HomotopyGroup m (Y⟦(1:ℤ)⟧)) :
    homShiftEquiv Y (m-1) 1 m (by omega) (AbstractAdamsTower.desuspend Y m x) = x := by
  simp only [homShiftEquiv_apply, AbstractAdamsTower.desuspend, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc,
    shiftFunctorAdd'_assoc_hom_app m (-1) 1 (m-1) 0 m (by omega) (by omega) (by omega)]
  rw [shiftFunctorAdd'_add_zero_hom_app]
  rw [Category.assoc]
  have hn := (shiftFunctorAdd' C (-1:ℤ) 1 0 (by omega)).hom.naturality x
  change (shiftFunctor C (0:ℤ)).map x ≫
      (shiftFunctorAdd' C (-1:ℤ) 1 0 (by omega)).hom.app (Y⟦(1:ℤ)⟧) =
    (shiftFunctorAdd' C (-1:ℤ) 1 0 (by omega)).hom.app (Sphere m) ≫
      (shiftFunctor C (1:ℤ)).map ((shiftFunctor C (-1:ℤ)).map x) at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [shift_shiftFunctorCompIsoId_hom_app (1:ℤ) (-1) (by omega) Y]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc]
  exact NatIso.naturality_1 (shiftFunctorZero C ℤ) x

private theorem homShiftEquiv_degreeCast (Y : C) (m m' n k : ℤ)
    (e : m=m') (h : m+n=k) (x : HomotopyGroup m Y) :
    homShiftEquiv Y m' n k (by omega)
      (CochainCoordinates.homotopyDegreeEquiv Y e x) = homShiftEquiv Y m n k h x := by
  subst m'
  rfl

private theorem homShiftEquiv_desuspend_shift (Y : C) (m s k : ℤ) (h : m+s=k)
    (x : HomotopyGroup m (Y⟦(1:ℤ)⟧)) :
    homShiftEquiv Y (m-1) (s+1) k (by omega) (AbstractAdamsTower.desuspend Y m x) =
      homShiftEquiv (Y⟦(1:ℤ)⟧) m s k h x ≫
        (shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app Y := by
  have hc := homShiftEquiv_comp Y (m-1) 1 s m (s+1) k
    (by omega) (by omega) (by omega) (AbstractAdamsTower.desuspend Y m x)
  rw [homShiftEquiv_desuspend] at hc
  apply (cancel_mono ((shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).hom.app Y)).mp
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact hc.symm

end
end KIP126.Literature.Standard.TensorNormalization
