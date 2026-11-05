module

import all KIP126.Literature.E2Exactness.GradedBasisCofan
import all KIP126.Literature.E2Exactness.ShiftedCoefficients
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

namespace KIP126.AdamsSynthetic.HModuleDecomposition
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual map defined by extensions of a homotopy basis induces an
isomorphism in each degree whose hom functor preserves its chosen coproduct. -/
private theorem basisCoproduct_inducedMap_bijective
    {C : Type u} [StableHomotopyCategory.{u, 0} C] [HasCoproducts.{0} C]
    (H : ModTwoCoefficients C) (Y : C)
    [∀ d : ℤ, Module (ZMod 2) (HomotopyGroup d Y)]
    (J : ℤ → Type) (b : ∀ d, Module.Basis (J d) (ZMod 2) (HomotopyGroup d Y))
    (e : ∀ j : Σ d, J d, H.object⟦j.1⟧ ⟶ Y)
    (he : ∀ j : Σ d, J d, (shiftFunctor C j.1).map H.unit ≫ e j = b j.1 j.2)
    (d : ℤ)
    [PreservesColimit (Discrete.functor (fun j : Σ n, J n => H.object⟦j.1⟧))
      (preadditiveCoyoneda.obj (Opposite.op (Sphere (C := C) d)))] :
    Function.Bijective (inducedMap (Sigma.desc e) d) := by
  let F := preadditiveCoyoneda.obj (Opposite.op (Sphere (C := C) d))
  let A (j : Σ n, J n) := H.object⟦j.1⟧
  let c : Cofan (fun j => F.obj (A j)) :=
    Cofan.mk (F.obj (∐ A)) (fun j => F.map (Sigma.ι A j))
  have hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit F A
  let t : Cofan (fun j => F.obj (A j)) :=
    Cofan.mk (F.obj Y) (fun j => F.map (e j))
  have ht : IsColimit t := by
    change IsColimit (Cofan.mk (AddCommGrpCat.of (HomotopyGroup d Y))
      (fun j => AddCommGrpCat.ofHom (inducedMap (e j) d)))
    apply gradedBasisCofan_isColimit d (AddCommGrpCat.of (HomotopyGroup d Y)) (b d)
      (fun j => F.obj (A j)) (fun _ => coefficientDiagonalEquiv H d)
      (fun j hj => shiftedCoefficient_vanishes H d j.1 (Ne.symm hj))
      (fun j => inducedMap (e j) d)
    intro j x
    apply zmodTwo_map_eq_smul (coefficientDiagonalEquiv H d)
      (inducedMap (e ⟨d, j⟩) d) (b d j) _ x
    rw [coefficientDiagonalEquiv_symm_one]
    exact he ⟨d, j⟩
  have heq : F.map (Sigma.desc e) = (hc.coconePointUniqueUpToIso ht).hom := by
    apply hc.hom_ext
    rintro ⟨j⟩
    change F.map (Sigma.ι A j) ≫ F.map (Sigma.desc e) = _
    rw [← F.map_comp, Sigma.ι_desc]
    exact (hc.comp_coconePointUniqueUpToIso_hom ht ⟨j⟩).symm
  have hi : IsIso (F.map (Sigma.desc e)) := by
    rw [heq]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective (F.map (Sigma.desc e))).mp hi


end KIP126.AdamsSynthetic.HModuleDecomposition
