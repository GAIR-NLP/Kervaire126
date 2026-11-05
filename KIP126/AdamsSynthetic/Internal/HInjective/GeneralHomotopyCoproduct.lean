module
import all KIP126.AdamsSynthetic.Internal.HInjective.GeneralSourceWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.RecognitionHomotopy
import all KIP126.AdamsSynthetic.Internal.HInjective.TargetCoproduct
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Actual homotopy preserves arbitrary ordinary small coproducts, using the
same source recognition and the original chosen target inclusions. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open Prespectrum
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,0} C]
  {H : ModTwoCoefficients C} (R : SourceRecognition C H)

include R in
private theorem recognizedSmallCoproducts : HasCoproducts.{0} C :=
  fun _ => Adjunction.hasColimitsOfShape_of_equivalence R.equivalence.inverse

variable [HasCoproducts.{0} C]

private def recognizedCoproductIso {J : Type} (X : J → C) :
    R.equivalence.functor.obj (∐ fun j => R.equivalence.inverse.obj (X j)) ≅ ∐ X :=
  PreservesCoproduct.iso R.equivalence.functor (fun j => R.equivalence.inverse.obj (X j)) ≪≫
    Sigma.mapIso (fun j => R.equivalence.counitIso.app (X j))

private theorem recognizedCoproductIso_inclusion {J : Type} (X : J → C) (j : J) :
    R.equivalence.functor.map (Sigma.ι (fun j => R.equivalence.inverse.obj (X j)) j) ≫
      (recognizedCoproductIso R X).hom =
        (R.equivalence.counitIso.app (X j)).hom ≫ Sigma.ι X j := by
  let E := R.equivalence.functor
  let S (j : J) := R.equivalence.inverse.obj (X j)
  have hp : E.map (Sigma.ι S j) ≫ (PreservesCoproduct.iso E S).hom =
      Sigma.ι (fun j => E.obj (S j)) j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit E S) (colimit.isColimit _) ⟨j⟩
  change E.map (Sigma.ι S j) ≫ ((PreservesCoproduct.iso E S).hom ≫
    (Sigma.mapIso (fun j => R.equivalence.counitIso.app (X j))).hom) = _
  rw [← Category.assoc, hp, Sigma.ι_mapIso_hom]
  rfl

include R in
private theorem recognized_homotopy_finite_support {J : Type}
    (X : J → C) (d : ℤ) (a : HomotopyGroup d (∐ X)) :
    ∃ (s : Finset J) (b : HomotopyGroup d (∐ fun j : (s : Set J) => X j.val)),
      b ≫ Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val) = a := by
  classical
  let S (j : J) := R.equivalence.inverse.obj (X j)
  let e := recognizedCoproductIso R X
  obtain ⟨s,b,hb⟩ := source_coproduct_finite_support S d
    (R.localizedHomotopyEquiv d (∐ S) (a ≫ e.inv))
  let Y (j : (s : Set J)) := X j.val
  let es := recognizedCoproductIso R Y
  let t := Sigma.desc (fun j : (s : Set J) => Sigma.ι S j.val)
  have hc : es.hom ≫ Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val) =
      R.equivalence.functor.map t ≫ e.hom := by
    apply (isColimitOfHasCoproductOfPreservesColimit R.equivalence.functor
      (fun j : (s : Set J) => S j.val)).hom_ext
    rintro ⟨j⟩
    change R.equivalence.functor.map (Sigma.ι (fun j : (s : Set J) => S j.val) j) ≫
      (es.hom ≫ _) = R.equivalence.functor.map (Sigma.ι (fun j : (s : Set J) => S j.val) j) ≫ _
    rw [← Category.assoc, recognizedCoproductIso_inclusion, Category.assoc, Sigma.ι_desc]
    rw [← Category.assoc, ← R.equivalence.functor.map_comp]
    dsimp only [t]
    rw [Sigma.ι_desc, recognizedCoproductIso_inclusion]
  refine ⟨s, (R.localizedHomotopyEquiv d (∐ fun j : (s : Set J) => S j.val)).symm b ≫ es.hom, ?_⟩
  rw [Category.assoc, hc, ← Category.assoc,
    ← R.localizedHomotopyEquiv_symm_natural d t b]
  rw [hb, Equiv.symm_apply_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include R in
private theorem recognized_homotopy_preserves_coproduct {J : Type}
    (X : J → C) (d : ℤ) :
    PreservesColimit (Discrete.functor X)
      (preadditiveCoyoneda.obj (Opposite.op (Sphere (C := C) d))) :=
  KIP126.AdamsSynthetic.TargetCoproduct.coyoneda_preservesCoproduct_of_finite_support
    (Sphere d) X (recognized_homotopy_finite_support R X d)

include R in
private def recognized_homotopy_coproduct_isColimit {J : Type}
    (X : J → C) (d : ℤ) :
    IsColimit (Cofan.mk
      ((preadditiveCoyoneda.obj (Opposite.op (Sphere (C := C) d))).obj (∐ X))
      (fun j => (preadditiveCoyoneda.obj (Opposite.op (Sphere (C := C) d))).map (Sigma.ι X j))) := by
  letI := recognized_homotopy_preserves_coproduct R X d
  exact isColimitOfHasCoproductOfPreservesColimit
    (preadditiveCoyoneda.obj (Opposite.op (Sphere d))) X

end
end KIP126.AdamsSynthetic.Source
end
