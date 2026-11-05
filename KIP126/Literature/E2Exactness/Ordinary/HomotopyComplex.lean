module
import KIP126.AdamsSynthetic.Tower
import Mathlib.Algebra.Homology.Homotopy

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def homotopyModuleFunctor (t : ℤ) : C ⥤ ModuleCat.{v} ℤ where
  obj X := ModuleCat.of ℤ (HomotopyGroup t X)
  map f := ModuleCat.ofHom (inducedMap f t).toIntLinearMap
  map_id X := by ext a; exact Category.comp_id a
  map_comp f g := by ext a; exact (Category.assoc a f g).symm

private instance homotopyModuleFunctor_additive (t : ℤ) :
    (homotopyModuleFunctor (C := C) t).Additive where
  map_add {X Y f g} := by
    ext a
    change a ≫ (f + g) = a ≫ f + a ≫ g
    rw [Preadditive.comp_add]

private def homotopyCochain (K : CochainComplex C ℤ) (t : ℤ) :
    CochainComplex (ModuleCat.{v} ℤ) ℤ :=
  ((homotopyModuleFunctor t).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

private def homotopyCochainMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (t : ℤ) :
    homotopyCochain K t ⟶ homotopyCochain L t :=
  ((homotopyModuleFunctor t).mapHomologicalComplex (ComplexShape.up ℤ)).map f

private def homotopyCochainIso {K L : CochainComplex C ℤ} (e : K ≅ L) (t : ℤ) :
    homotopyCochain K t ≅ homotopyCochain L t :=
  ((homotopyModuleFunctor t).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e

private def homotopyCochainHomotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (h : Homotopy f g) (t : ℤ) : Homotopy (homotopyCochainMap f t) (homotopyCochainMap g t) :=
  (homotopyModuleFunctor t).mapHomotopy h
end
end KIP126.Literature.Standard.FixedTensorE2
end
