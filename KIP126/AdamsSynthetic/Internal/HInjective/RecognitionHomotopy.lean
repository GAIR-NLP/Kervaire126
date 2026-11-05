module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Recognition
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Functor.Proofs
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Yoneda

@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory TypeCat KIP126.StableHomotopy
universe u v

/-- Forgetting the genuine source group structure preserves the same actual
map on every localization morphism. -/
theorem sourceStableHomotopyAddFunctor_forget (d : ℤ) :
    sourceStableHomotopyAddFunctor.{u} d ⋙ forget AddCommGrpCat =
      sourceStableHomotopyFunctor d := by
  apply Localization.Construction.uniq _ _
  rw [← Functor.assoc, sourceStableHomotopyAddFunctor_fac, sourceStableHomotopyFunctor_fac]
  rfl

theorem sourceStableHomotopyAddFunctor_forget_map {A B : SourceCategory.{u}}
    (f : A ⟶ B) (d : ℤ) :
    (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor d).map f) =
      (sourceStableHomotopyFunctor d).map f := by
  have h : ∀ (F G : SourceCategory.{u} ⥤ Type u),
      F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h (sourceStableHomotopyAddFunctor d ⋙ forget AddCommGrpCat)
    (sourceStableHomotopyFunctor d) (sourceStableHomotopyAddFunctor_forget d))

namespace SourceRecognition
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C} (R : SourceRecognition C H)

/-- The actual homotopy functor in the fixed target category. -/
def targetHomotopyFunctor (d : ℤ) : C ⥤ Type v :=
  coyoneda.obj (Opposite.op (Sphere d))

/-- The given strict-map recognition, with the unique universe lift needed
for the arbitrary target hom universe. -/
noncomputable def strictHomotopyIso (d : ℤ) :
    sourceLocalization ⋙ (R.equivalence.functor ⋙ targetHomotopyFunctor d) ≅
      sourceLocalization ⋙ (sourceStableHomotopyFunctor d ⋙ uliftFunctor.{v,0}) :=
  NatIso.ofComponents (fun X => ((R.homotopy X d).trans Equiv.ulift.symm).toIso) (by
    intro X Y f
    ext a
    change ULift.up (R.homotopy Y d (a ≫ R.equivalence.functor.map
      (sourceLocalization.map f))) = ULift.up
        ((sourceStableHomotopyFunctor d).map (sourceLocalization.map f) (R.homotopy X d a))
    rw [sourceStableHomotopyFunctor_map]
    exact congrArg ULift.up (R.homotopy_natural f d a))

/-- The same recognition extends to every morphism of the actual stable
localization; the only input naturality is the fixed strict-map field. -/
noncomputable def localizedHomotopyIso (d : ℤ) :
    R.equivalence.functor ⋙ targetHomotopyFunctor d ≅
      sourceStableHomotopyFunctor d ⋙ uliftFunctor.{v,0} where
  hom := Localization.Construction.natTransExtension (R.strictHomotopyIso d).hom
  inv := Localization.Construction.natTransExtension (R.strictHomotopyIso d).inv
  hom_inv_id := by
    apply Localization.natTrans_ext sourceLocalization Prespectrum.stableEquivalences
    intro X
    simp only [NatTrans.comp_app, NatTrans.id_app,
      Localization.Construction.natTransExtension_app,
      Localization.Construction.NatTransExtension.app_eq]
    exact (R.strictHomotopyIso d).hom_inv_id_app X
  inv_hom_id := by
    apply Localization.natTrans_ext sourceLocalization Prespectrum.stableEquivalences
    intro X
    simp only [NatTrans.comp_app, NatTrans.id_app,
      Localization.Construction.natTransExtension_app,
      Localization.Construction.NatTransExtension.app_eq]
    exact (R.strictHomotopyIso d).inv_hom_id_app X

/-- The recognized source stable class of an actual target homotopy class,
for an arbitrary object of the source localization. -/
noncomputable def localizedHomotopyEquiv (d : ℤ) (A : SourceCategory.{0}) :
    HomotopyGroup d (R.equivalence.functor.obj A) ≃
      (sourceStableHomotopyFunctor d).obj A :=
  ((R.localizedHomotopyIso d).app A).toEquiv.trans Equiv.ulift

/-- Endpoint naturality for every actual localization morphism. -/
theorem localizedHomotopyEquiv_natural (d : ℤ) {A B : SourceCategory.{0}}
    (f : A ⟶ B) (a : HomotopyGroup d (R.equivalence.functor.obj A)) :
    R.localizedHomotopyEquiv d B (a ≫ R.equivalence.functor.map f) =
      (sourceStableHomotopyFunctor d).map f (R.localizedHomotopyEquiv d A a) := by
  have h := congrArg (fun k => k a) ((R.localizedHomotopyIso d).hom.naturality f)
  exact congrArg ULift.down h

/-- On every original object, this is the specified recognition equivalence. -/
@[simp] theorem localizedHomotopyEquiv_strict (d : ℤ) (X : Prespectrum.{0})
    (a : HomotopyGroup d (R.equivalence.functor.obj (sourceLocalization.obj X))) :
    R.localizedHomotopyEquiv d (sourceLocalization.obj X) a = R.homotopy X d a := by
  change ((Localization.Construction.natTransExtension (R.strictHomotopyIso d).hom).app
    (sourceLocalization.obj X) a).down = _
  rw [Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq]
  rfl
/-- The endpoint formula directly consumable by the genuine additive source
homotopy functor; no target/source additivity of recognition is assumed. -/
theorem localizedHomotopyEquiv_natural_addFunctor (d : ℤ) {A B : SourceCategory.{0}}
    (f : A ⟶ B) (a : HomotopyGroup d (R.equivalence.functor.obj A)) :
    R.localizedHomotopyEquiv d B (a ≫ R.equivalence.functor.map f) =
      (sourceStableHomotopyAddFunctor d).map f (R.localizedHomotopyEquiv d A a) := by
  have h := R.localizedHomotopyEquiv_natural d f a
  rw [← sourceStableHomotopyAddFunctor_forget_map] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary localized morphisms between specified point-set endpoints use
exactly the original recognition fields. -/
theorem homotopy_natural_source (d : ℤ) {X Y : Prespectrum.{0}}
    (f : sourceLocalization.obj X ⟶ sourceLocalization.obj Y)
    (a : HomotopyGroup d (R.equivalence.functor.obj (sourceLocalization.obj X))) :
    R.homotopy Y d (a ≫ R.equivalence.functor.map f) =
      (sourceStableHomotopyAddFunctor d).map f (R.homotopy X d a) := by
  simpa only [localizedHomotopyEquiv_strict] using
    R.localizedHomotopyEquiv_natural_addFunctor d f a

/-- The inverse equivalence transports an actual source factorization to
composition with the same target morphism. -/
theorem localizedHomotopyEquiv_symm_natural (d : ℤ) {A B : SourceCategory.{0}}
    (f : A ⟶ B) (b : (sourceStableHomotopyAddFunctor d).obj A) :
    (R.localizedHomotopyEquiv d B).symm ((sourceStableHomotopyAddFunctor d).map f b) =
      (R.localizedHomotopyEquiv d A).symm b ≫ R.equivalence.functor.map f := by
  apply (R.localizedHomotopyEquiv d B).injective
  rw [Equiv.apply_symm_apply, localizedHomotopyEquiv_natural_addFunctor,
    Equiv.apply_symm_apply]

end SourceRecognition
end KIP126.AdamsSynthetic.Source
