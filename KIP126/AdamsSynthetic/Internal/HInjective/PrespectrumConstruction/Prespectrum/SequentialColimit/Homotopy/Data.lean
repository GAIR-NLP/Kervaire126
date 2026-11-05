module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.SequentialColimit.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyFunctor.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The cocone on the original stable cubical quotients induced by the actual
sequential prespectrum inclusions. -/
noncomputable def sequentialStableHomotopyCocone (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    Cocone (F ⋙ stableHomotopyFunctor d) :=
  (stableHomotopyFunctor d).mapCocone (sequentialColimitCocone F)

end KIP126.AdamsSynthetic.Source.Prespectrum
