module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Prespectrum.Zero.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Support.CategoryTheory.Localization.Zero.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory CategoryTheory.Limits Topology
universe u

/-- Pointwise uniqueness proves the actual zero-object universal property. -/
theorem zeroPrespectrum_isZero : IsZero zeroPrespectrum.{u} := by
  constructor
  · intro Y
    refine ⟨{default := zeroMap _ Y,uniq := ?_}⟩
    intro f
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    cases x
    exact f.point n
  · intro Y
    refine ⟨{default := zeroMap Y _,uniq := ?_}⟩
    intro f
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    change (f.level n x : PUnit) = PUnit.unit
    cases f.level n x
    rfl

/-- The ordinary stable localization has the image of the actual zero spectrum as a zero object. -/
theorem source_zeroPrespectrum_isZero : IsZero (sourceLocalization.obj zeroPrespectrum.{u}) :=
  KIP126.Foundation.localization_isZero stableEquivalences zeroPrespectrum zeroPrespectrum_isZero

end KIP126.AdamsSynthetic.Source.Prespectrum
