module

import KIP126.AdamsSynthetic.Context
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace KIP126.AdamsSynthetic.HModuleDecomposition
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy
universe u v
set_option backward.isDefEq.respectTransparency false

private noncomputable def precomposeAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}
    (e : X ≅ Y) (Z : C) : (Y ⟶ Z) ≃+ (X ⟶ Z) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := Preadditive.comp_add _ _ _ _ _ _

private noncomputable def shiftMapAddEquiv
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (n : ℤ) (X Y : C) : (X ⟶ Y) ≃+ (X⟦n⟧ ⟶ Y⟦n⟧) where
  toEquiv := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).homEquiv
  map_add' _ _ := (shiftFunctor C n).map_add

private noncomputable def shiftedHomotopyEquiv
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (X : C) (d n : ℤ) :
    HomotopyGroup (d - n) X ≃+ HomotopyGroup d (X⟦n⟧) :=
  (shiftMapAddEquiv n (Sphere (d - n)) X).trans
    (precomposeAddEquiv
      ((shiftFunctorAdd' C (d - n) n d (sub_add_cancel d n)).app SphereSpectrum) _)

private theorem shiftedCoefficient_vanishes
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (H : ModTwoCoefficients C) (d n : ℤ) (h : d ≠ n) :
    Subsingleton (HomotopyGroup d (H.object⟦n⟧)) := by
  letI := H.homotopy_vanishes (d - n) (sub_ne_zero.mpr h)
  exact (shiftedHomotopyEquiv H.object d n).symm.injective.subsingleton

private noncomputable def coefficientDiagonalEquiv
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (H : ModTwoCoefficients C) (d : ℤ) :
    HomotopyGroup d (H.object⟦d⟧) ≃+ ZMod 2 :=
  (shiftMapAddEquiv d SphereSpectrum H.object).symm.trans
    ((precomposeAddEquiv ((shiftFunctorZero C ℤ).app SphereSpectrum) H.object).trans
      H.pi0Equiv)

private theorem coefficientDiagonalEquiv_unit
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (H : ModTwoCoefficients C) (d : ℤ) :
    coefficientDiagonalEquiv H d ((shiftFunctor C d).map H.unit) = 1 := by
  change H.pi0Equiv ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫
    (shiftMapAddEquiv d SphereSpectrum H.object).symm
      ((shiftMapAddEquiv d SphereSpectrum H.object) H.unit)) = 1
  rw [AddEquiv.symm_apply_apply]
  simp [ModTwoCoefficients.unit]

private theorem coefficientDiagonalEquiv_symm_one
    {C : Type u} [StableHomotopyCategory.{u, v} C]
    (H : ModTwoCoefficients C) (d : ℤ) :
    (coefficientDiagonalEquiv H d).symm 1 = (shiftFunctor C d).map H.unit := by
  apply (coefficientDiagonalEquiv H d).injective
  rw [AddEquiv.apply_symm_apply, coefficientDiagonalEquiv_unit]


end KIP126.AdamsSynthetic.HModuleDecomposition
