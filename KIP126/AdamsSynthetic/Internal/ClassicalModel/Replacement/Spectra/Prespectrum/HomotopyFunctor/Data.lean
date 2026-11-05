module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Replacement.Spectra.Prespectrum
import Mathlib.CategoryTheory.Types.Basic

@[expose] section

/-! The actual cubical stable quotient, as a functor on prespectra and
on their specified ordinary stable localization. -/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory TypeCat

universe u

/-- Integer stable homotopy before localization, using exactly the
point-set cubical representatives and their displayed relations. -/
def Prespectrum.stableHomotopyFunctor (d : ℤ) : Prespectrum.{u} ⥤ Type u where
  obj X := X.StableHomotopy d
  map f := ofHom (Prespectrum.stableHomotopyMap f d)
  map_id X := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl
  map_comp f g := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl

/-- Stable homotopy of the ordinary source localization, induced by the quotient
functor. -/
noncomputable def sourceStableHomotopyFunctor (d : ℤ) : SourceCategory.{u} ⥤ Type u :=
  Localization.Construction.lift (Prespectrum.stableHomotopyFunctor d)
    (fun _ _ _ hf => (bijective_iff_isIso_ofHom _).mp (hf d))

/-- An ordinary source isomorphism gives an equivalence of the actual
stable cubical quotients in each integer degree. -/
noncomputable def Prespectrum.stableHomotopyEquivOfSourceIso
    {X Y : Prespectrum.{u}} (e : sourceLocalization.obj X ≅ sourceLocalization.obj Y)
    (d : ℤ) : X.StableHomotopy d ≃ Y.StableHomotopy d :=
  ((sourceStableHomotopyFunctor d).mapIso e).toEquiv

end KIP126.AdamsSynthetic.Source
