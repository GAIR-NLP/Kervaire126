module
import KIP126.AdamsSynthetic.Context
import Mathlib.CategoryTheory.Shift.CommShift

namespace KIP126.Literature.Standard.TensorNormalization
open CategoryTheory
open KIP126.StableHomotopy
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {D : Type u'} [StableHomotopyCategory.{u',v'} D]
  (F : C ⥤ D) [F.CommShift ℤ]

private theorem shiftComm_add_inv (Y : C) (s : ℤ) :
    (shiftFunctor D s).map ((F.commShiftIso (1:ℤ)).inv.app Y) ≫
      (F.commShiftIso s).inv.app (Y⟦(1:ℤ)⟧) ≫
      F.map ((shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app Y) =
    (shiftFunctorAdd' D (1:ℤ) s (s+1) (by omega)).inv.app (F.obj Y) ≫
      (F.commShiftIso (s+1)).inv.app Y := by
  rw [F.commShiftIso_add' (show (1:ℤ)+s=s+1 by omega)]
  simp only [Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc]

private theorem shifted_boundary_transport {A B : C} {A' B' : D}
    (f : A ⟶ B⟦(1:ℤ)⟧) (g : A' ⟶ B'⟦(1:ℤ)⟧)
    (a : A' ⟶ F.obj A) (b : B' ⟶ F.obj B)
    (h : a ≫ F.map f ≫ (F.commShiftIso (1:ℤ)).hom.app B =
      g ≫ (shiftFunctor D (1:ℤ)).map b) (s : ℤ) :
    ((shiftFunctor D s).map a ≫ (F.commShiftIso s).inv.app A) ≫
      F.map ((shiftFunctor C s).map f ≫
        (shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app B) =
    ((shiftFunctor D s).map g ≫
      (shiftFunctorAdd' D (1:ℤ) s (s+1) (by omega)).inv.app B') ≫
      (shiftFunctor D (s+1)).map b ≫ (F.commShiftIso (s+1)).inv.app B := by
  have h' : a ≫ F.map f = g ≫ (shiftFunctor D (1:ℤ)).map b ≫
      (F.commShiftIso (1:ℤ)).inv.app B := by
    apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app B)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact h
  simp only [F.map_comp, Category.assoc]
  rw [← F.commShiftIso_inv_naturality_assoc f s, ← Functor.map_comp_assoc, h']
  simp only [Functor.map_comp, Category.assoc]
  rw [shiftComm_add_inv]
  rw [← Category.assoc ((shiftFunctor D s).map ((shiftFunctor D (1:ℤ)).map b))]
  have hn := (shiftFunctorAdd' D (1:ℤ) s (s+1) (by omega)).inv.naturality b
  change (shiftFunctor D s).map ((shiftFunctor D (1:ℤ)).map b) ≫
      (shiftFunctorAdd' D (1:ℤ) s (s+1) (by omega)).inv.app (F.obj B) =
    (shiftFunctorAdd' D (1:ℤ) s (s+1) (by omega)).inv.app B' ≫
      (shiftFunctor D (s+1)).map b at hn
  rw [hn, Category.assoc]

end
end KIP126.Literature.Standard.TensorNormalization
