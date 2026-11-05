module

public import KIP126.Main.DifferentialCriterion
import all KIP126.Main.Internal.Moore.PermanenceFromSurvival
/-! Nonzero permanent survival of the standard square h₆²
in the fixed sphere Adams spectral sequence. -/

@[expose] section
namespace KIP126.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

public theorem eta_extension_excluded_of_d6_vanishes : Stem126D6Vanishes → ¬ EtaExtensionDetection :=
  Internal.Moore.moore_eta_extension_excluded

private theorem fixed_h6_sq_permanent :
    NonzeroSurvival background.classical.sphere (2,128)
      background.standardClasses.standardH6Square := by
  exact Internal.Moore.moore_h6_sq_permanent

/-- LWX Theorem 7.1 for any nonzero standard-class family on the fixed actual
sphere E₂ page, retaining a common Z∞ representative and nonzero E∞ image. -/
public theorem h6_sq_permanent
    (H : KIP126.Classical.Adams.StandardSphereClasses
      background.classical background.sphereAlgebra) :
    NonzeroSurvival background.classical.sphere (2,128)
      (background.sphereAlgebra.product (1,64) (1,64) (H.standardH6) (H.standardH6)) := by
  have hh : H.standardH6 = KIP126.Computation.Standard.h6 := by
    rcases KIP126.Computation.Standard.h6_exhaustive (H.standardH6) with h | h
    · exact (H.hi_ne_zero 6 (by decide) h).elim
    · exact h
  rw [hh]
  exact fixed_h6_sq_permanent

/-- Every standard generator in the main theorem is nonzero on the actual
sphere E₂ page. The standard class family is defined only for indices ≤ 7. -/
public theorem standard_hi_ne_zero
    (H : KIP126.Classical.Adams.StandardSphereClasses
      background.classical background.sphereAlgebra)
    (i : ℕ) (hiBound : i ≤ 7) :
    (H.standardHi i hiBound : background.classical.sphere.Page 2
      (1, ((2 ^ i : ℕ) : ℤ))) ≠ 0 :=
  H.hi_ne_zero i hiBound

/-- The square is nonzero on E₂ in bidegree (2,128), by the E₂ computation. -/
public theorem h6_square_e2_nonzero
    (H : KIP126.Classical.Adams.StandardSphereClasses
      background.classical background.sphereAlgebra) :
    (background.sphereAlgebra.product (1,64) (1,64) H.standardH6 H.standardH6 :
      background.classical.sphere.Page 2 (2,128)) ≠ 0 := by
  have hh : H.standardH6 = KIP126.Computation.Standard.h6 := by
    rcases KIP126.Computation.Standard.h6_exhaustive H.standardH6 with hz | heq
    · exact (standard_hi_ne_zero H 6 (by decide) hz).elim
    · exact heq
  rw [hh]
  exact KIP126.Computation.Standard.square_nonzero

end KIP126.Main
