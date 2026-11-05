module

import all KIP126.ProofTools.CrossingCounterexample.Right
import all KIP126.ProofTools.CrossingCounterexample.ZeroLength

/-! The actual sphere/Moore(4) counterexample to unrestricted finite crossing
comparison. All constructions are internal to the proof of the public negation. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Completed

private theorem candidate_no_crossing :
    ¬ FiniteHasCrossing background candidateAdamsObject candidateAdamsObject
      matrixMap 4 2 1 1 :=
  candidate_not_finite_crossing candidate_length_one_not_essential
    candidate_zero_length_two_boundary candidate_zero_length_three_boundary

end KIP126.ProofTools.Internal.CrossingCounterexample
