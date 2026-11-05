module
public import KIP126.SSComputation.Table
public import KIP126.AdamsComputation.Table.Dimensions

@[expose] section
namespace KIP126.Computation.Table

/-- Two finite staircase states with representatives on page 1000. -/
public def staircaseClaims : List Raw.Claim := [
  ⟨.sphere,.reaches,1000,14,138,[2],14,138,[]⟩,
  ⟨.sphere,.reaches,1000,15,139,[1,3],15,139,[]⟩
]

public theorem staircase_result (c : Raw.Claim) (hc : c ∈ staircaseClaims) :
    Statement c := by
  sorry

end KIP126.Computation.Table
