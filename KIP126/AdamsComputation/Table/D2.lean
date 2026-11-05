module

public import KIP126.AdamsComputation.Table
public import KIP126.AdamsComputation.Table.ClaimSyntax

/-! The selected records exported directly from the Adams E2-basis d2 column.
These four direct records form a separate input collection from SS propagation. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed
noncomputable section

/-- Successful decoding and page-specific mathematical claims, including
refutations as negated equations. -/
public def Statement (c : Raw.Claim) : Prop :=
  ∃ x, decode c.spectrum c.s c.t c.x = some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        ¬ HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y

namespace Raw
/-- Direct Adams d₂ equations in the fixed coordinates. -/
public def directD2Claims : List Claim := [
  ⟨.sphere, .equation, 2, 7, 70, [2], 9, 71, [0]⟩,
  ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2]⟩,
  ⟨.sphere, .equation, 2, 11, 137, [0], 13, 138, [3]⟩,
  ⟨.sphere, .equation, 2, 11, 137, [3], 13, 138, [4]⟩
]
end Raw

/-- Actual-sphere statements for precisely the four direct Adams d2 records. -/
public theorem direct_d2_result (c : Raw.Claim) (hc : c ∈ Raw.directD2Claims) : Statement c := by
  sorry

end
end KIP126.Computation.Table
