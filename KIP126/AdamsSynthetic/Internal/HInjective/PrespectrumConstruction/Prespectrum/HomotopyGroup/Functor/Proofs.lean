module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Functor.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory

universe u

@[simp] theorem sourceStableHomotopyAddFunctor_fac (d : ℤ) :
    sourceLocalization ⋙ sourceStableHomotopyAddFunctor.{u} d =
      Prespectrum.stableHomotopyAddFunctor d :=
  Localization.Construction.fac _ _

@[simp] theorem sourceStableHomotopyAddFunctor_map {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) :
    (sourceStableHomotopyAddFunctor d).map (sourceLocalization.map f) =
      AddCommGrpCat.ofHom (Prespectrum.stableHomotopyAddHom f d) := by
  have h : ∀ (F G : Prespectrum.{u} ⥤ AddCommGrpCat.{u}),
      F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h _ _ (sourceStableHomotopyAddFunctor_fac d))

end KIP126.AdamsSynthetic.Source
