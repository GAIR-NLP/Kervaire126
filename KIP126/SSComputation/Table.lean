module

public import KIP126.AdamsComputation.Table.D2
public import KIP126.SSComputation.Table.Data
import all KIP126.SSComputation.Internal.Certification

/-! SS propagation records, including derived d2 equations and later-page claims. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

public theorem result (c : Raw.Claim) (hc : c ∈ Raw.claims) : Statement c := by
  exact KIP126.SSComputation.Internal.Certification.table_result c hc

end
end KIP126.Computation.Table
