module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

/-- A morphism in the original ordinary stable localization is represented
by a strict span with its left leg a stable equivalence. -/
def sourceHasRoof : MorphismProperty SourceCategory.{u} := fun X Y h =>
  ∃ (A : Prespectrum.{u}) (s : A ⟶ X.as.obj) (t : A ⟶ Y.as.obj),
    stableEquivalences s ∧ sourceLocalization.map s ≫ h = sourceLocalization.map t

end KIP126.AdamsSynthetic.Source.Prespectrum
