module

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs

/-! A full integer shift from an autoequivalence. We first replace the category
by its skeleton, where the given equivalence is bijective on objects and hence
has a strict inverse. Integer powers of the resulting strict automorphism
satisfy strict group laws. The shift is then transported back along the
skeleton equivalence, including all coherence laws. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelFoundation
open CategoryTheory CategoryTheory.Functor
universe u v
variable {C : Type u} [Category.{v} C]

/-- A strict category automorphism yields a strict family of integer powers. -/
noncomputable def strictAutPower (a : Aut (Cat.of C)) (n : ℤ) : C ⥤ C :=
  (a ^ n).hom.toFunctor

lemma strictAutPower_zero (a : Aut (Cat.of C)) : strictAutPower a 0 = 𝟭 C := by
  rw [strictAutPower, zpow_zero]
  rfl

lemma strictAutPower_add (a : Aut (Cat.of C)) (n m : ℤ) :
    strictAutPower a (n + m) = strictAutPower a n ⋙ strictAutPower a m := by
  rw [add_comm n m, strictAutPower, zpow_add]
  rfl

/-- All shift coherence follows from the strict group equalities. -/
noncomputable def strictAutShiftCore (a : Aut (Cat.of C)) : ShiftMkCore C ℤ where
  F := strictAutPower a
  zero := eqToIso (strictAutPower_zero a)
  add n m := eqToIso (strictAutPower_add a n m)
  assoc_hom_app n m k X := by
    simp [eqToHom_map, eqToHom_app]
  zero_add_hom_app n X := by
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
  add_zero_hom_app n X := by
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans]

/-- The complete shift structure associated to a strict category automorphism. -/
@[implicit_reducible]
noncomputable def strictAutHasShift (a : Aut (Cat.of C)) : HasShift C ℤ :=
  hasShiftMk C ℤ (strictAutShiftCore a)

variable (E : C ≌ C)

instance skeletonEquivalenceIsIso : E.functor.mapSkeleton.IsIso where
  bijective_obj := ⟨E.functor.mapSkeleton_injective, E.functor.mapSkeleton_surjective⟩

/-- On the skeleton an autoequivalence becomes a strict automorphism. -/
noncomputable def skeletonAutomorphism : Aut (Cat.of (Skeleton C)) where
  hom := E.functor.mapSkeleton.toCatHom
  inv := E.functor.mapSkeleton.strictInv.toCatHom
  hom_inv_id := Cat.ext (E.functor.mapSkeleton.asIsomorphism.unit_eq.symm)
  inv_hom_id := Cat.ext E.functor.mapSkeleton.asIsomorphism.counit_eq

/-- The transported integer powers on the original category. -/
noncomputable def equivalenceShiftFunctor (n : ℤ) : C ⥤ C :=
  toSkeletonFunctor C ⋙ strictAutPower (skeletonAutomorphism E) n ⋙ fromSkeleton C

/-- Comparison used to transport the full shift structure along the fully
faithful inclusion into the skeleton. -/
noncomputable def equivalenceShiftComparison (n : ℤ) :
    equivalenceShiftFunctor E n ⋙ toSkeletonFunctor C ≅
      toSkeletonFunctor C ⋙ strictAutPower (skeletonAutomorphism E) n :=
  (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft _ ((Functor.associator _ _ _) ≪≫
      isoWhiskerLeft _ (skeletonEquivalence C).unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- Every autoequivalence induces a coherent shift by all integers. -/
@[implicit_reducible]
noncomputable def constructedHasShift : HasShift C ℤ := by
  letI : HasShift (Skeleton C) ℤ := strictAutHasShift (skeletonAutomorphism E)
  exact (skeletonEquivalence C).fullyFaithfulInverse.hasShift
    (equivalenceShiftFunctor E) (equivalenceShiftComparison E)

/-- The induced shift by one is the specified autoequivalence, up to the
explicit skeleton comparison. -/
noncomputable def constructedShiftOneIso :
    letI := constructedHasShift E
    shiftFunctor C (1 : ℤ) ≅ E.functor := by
  change equivalenceShiftFunctor E 1 ≅ E.functor
  simp only [equivalenceShiftFunctor, strictAutPower, zpow_one]
  change (toSkeletonFunctor C ⋙
      (fromSkeleton C ⋙ E.functor ⋙ toSkeletonFunctor C) ⋙ fromSkeleton C) ≅ E.functor
  simpa only [Functor.assoc, skeletonEquivalence_functor, skeletonEquivalence_inverse] using
    (isoWhiskerRight (skeletonEquivalence C).counitIso
        (E.functor ⋙ toSkeletonFunctor C ⋙ fromSkeleton C) ≪≫
      Functor.leftUnitor _ ≪≫
        isoWhiskerLeft E.functor (skeletonEquivalence C).counitIso ≪≫
          Functor.rightUnitor _)

/-- A complete coherent integer shift exists with the given autoequivalence
as its shift by one. All coherence has already been constructed above. -/
private theorem existsShiftFromEquivalence :
    ∃ S : HasShift C ℤ, letI := S; Nonempty (shiftFunctor C (1 : ℤ) ≅ E.functor) :=
  ⟨constructedHasShift E, ⟨constructedShiftOneIso E⟩⟩

/-- A complete integer shift constructed from the given autoequivalence. -/
@[implicit_reducible]
public noncomputable def hasShiftFromEquivalence : HasShift C ℤ :=
  Classical.choose (show ∃ S : HasShift C ℤ,
      letI := S; Nonempty (shiftFunctor C (1 : ℤ) ≅ E.functor) from by
    exact existsShiftFromEquivalence E)

/-- The chosen shift by one is naturally isomorphic to the specified
 autoequivalence, without any additional coherence assumptions. -/
public noncomputable def shiftOneIsoFromEquivalence :
    letI := hasShiftFromEquivalence E
    shiftFunctor C (1 : ℤ) ≅ E.functor :=
  Classical.choice (by exact Classical.choose_spec (existsShiftFromEquivalence E))


end KIP126.StableHomotopy.ModelFoundation
