module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Proofs
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory

universe u

/-- The original map of stable cubical classes, with its additive structure. -/
noncomputable def Prespectrum.stableHomotopyAddHom {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) : X.StableHomotopy d →+ Y.StableHomotopy d where
  toFun := Prespectrum.stableHomotopyMap f d
  map_zero' := Prespectrum.stableHomotopyMap_zero f d
  map_add' := Prespectrum.stableHomotopyMap_add f d

/-- Actual integer-graded stable homotopy as an abelian-group-valued functor. -/
noncomputable def Prespectrum.stableHomotopyAddFunctor (d : ℤ) :
    Prespectrum.{u} ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (X.StableHomotopy d)
  map f := AddCommGrpCat.ofHom (Prespectrum.stableHomotopyAddHom f d)
  map_id X := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl
  map_comp f g := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl

/-- Descend the actual abelian stable groups through the fixed ordinary
localization at stable equivalences. -/
noncomputable def sourceStableHomotopyAddFunctor (d : ℤ) :
    SourceCategory.{u} ⥤ AddCommGrpCat.{u} :=
  Localization.Construction.lift (Prespectrum.stableHomotopyAddFunctor d)
    (fun _ _ _ hf => (ConcreteCategory.isIso_iff_bijective _).mpr (hf d))

end KIP126.AdamsSynthetic.Source
