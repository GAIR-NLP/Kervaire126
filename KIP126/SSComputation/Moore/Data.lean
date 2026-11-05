module

public import KIP126.AdamsComputation.E2
public import KIP126.SpectralSequence.Computation.Predicates
import all KIP126.SSComputation.Internal.Certification

/-! The d₄ and d₇ equations from the finite coordinate input table. -/

namespace KIP126.SSComputation.Moore
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

/-- The zero d₄ equation for the bottom-cell image of sphere basis[0]
on the completed Moore spectrum in degree (8,132). -/
public theorem bottom_source_d4_zero :
    HasDifferential KIP126.AdamsComputation.Moore.sequence 4 (8,132) (12,135)
      KIP126.AdamsComputation.Moore.bottomSource 0 := by
  exact KIP126.SSComputation.Internal.Certification.bottom_source_d4_zero

/-- The zero d₇ equation on the fixed sphere Adams sequence
for the selected class V in degree (9,132). -/
public theorem v_d7_zero :
    HasDifferential background.classical.sphere 7 (9,132) (16,138)
      KIP126.Computation.Standard.V 0 := by
  exact KIP126.SSComputation.Internal.Certification.v_d7_zero

end KIP126.SSComputation.Moore
