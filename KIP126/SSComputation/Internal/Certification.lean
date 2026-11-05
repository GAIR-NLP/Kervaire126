module

import KIP126.AdamsComputation.Moore.E2
import KIP126.AdamsComputation.Table.Values
import KIP126.SSComputation.Table.Data
import KIP126.SpectralSequence.Computation.Predicates
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Finite coordinate statements, with Moore coordinates interpreted by the
bottom-cell map. -/

@[expose] section
namespace KIP126.SSComputation.Internal.Certification
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

open KIP126.SSComputation.Input

noncomputable section
set_option backward.isDefEq.respectTransparency false
open KIP126.Computation.Table

private def decodeMoore (s t : ℕ) (indices : List ℕ) :=
  (decode .sphere s t indices).map (KIP126.AdamsComputation.Moore.bottomPageMap s t)

private def Statement (c : Claim) : Prop :=
  match c.toRaw? with
  | some row => KIP126.Computation.Table.Statement row
  | none =>
      ∃ x, decodeMoore c.s c.t c.x = some x ∧
        match c.kind with
        | .reaches => ReachesPage KIP126.AdamsComputation.Moore.sequence c.r (c.s,c.t) x
        | .boundaryBy => IsBoundaryBy KIP126.AdamsComputation.Moore.sequence c.r (c.s,c.t) x
        | .equation => ∃ y, decodeMoore c.ts c.tt c.y = some y ∧
            HasDifferential KIP126.AdamsComputation.Moore.sequence c.r
              (c.s,c.t) (c.ts,c.tt) x y
        | .refutation => ∃ y, decodeMoore c.ts c.tt c.y = some y ∧
            ¬ HasDifferential KIP126.AdamsComputation.Moore.sequence c.r
              (c.s,c.t) (c.ts,c.tt) x y

/-- Pending certification of the 200 finite coordinate statements. -/
private theorem certified_result (c : Claim) (hc : c ∈ claims) : Statement c := by
  sorry

private theorem table_result (c : KIP126.Computation.Table.Raw.Claim)
    (hc : c ∈ KIP126.Computation.Table.Raw.claims) :
    KIP126.Computation.Table.Statement c := by
  obtain ⟨row, hrow, heq⟩ := List.mem_filterMap.mp hc
  simpa only [Statement, heq] using certified_result row hrow

private theorem bottom_source_d4_zero :
    HasDifferential KIP126.AdamsComputation.Moore.sequence 4 (8,132) (12,135)
      KIP126.AdamsComputation.Moore.bottomSource 0 := by
  have h := certified_result ⟨.moore, .equation, 4, 8, 132, [0], 12, 135, []⟩
    (List.mem_of_getElem? (i := 198) (by rfl))
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [] = true := rfl
  simp only [Statement, Claim.toRaw?, decodeMoore, decode, vx, vy, if_true,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Option.map, Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, hd⟩ := h
  rw [← hx, ← hy] at hd
  simp only [Nat.cast_ofNat] at hd
  have hz : KIP126.AdamsComputation.Moore.bottomPageMap 12 135 0 = 0 := map_zero _
  rw [hz] at hd
  simpa only [KIP126.AdamsComputation.Moore.bottomSource] using hd

private theorem v_d7_zero :
    HasDifferential background.classical.sphere 7 (9,132) (16,138)
      KIP126.Computation.Standard.V 0 := by
  have h := table_result ⟨.sphere, .equation, 7, 9, 132, [0, 1], 16, 138, []⟩
    (List.mem_of_getElem? (i := 198) (by rfl))
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [] = true := rfl
  simp only [KIP126.Computation.Table.Statement, decode, vx, vy, if_true,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, hd⟩ := h
  rw [← hx, ← hy] at hd
  have h0 := basis_value ⟨.named .x_123_9, 0⟩ (by decide)
  have h1 := basis_value ⟨.mul (.named .h0) (.named .x_123_8), 1⟩ (by decide)
  change basis .sphere 9 132 0 = KIP126.Computation.Standard.atom .x_123_9 at h0
  change basis .sphere 9 132 1 = KIP126.Computation.Standard.product (r := (9,132))
    (KIP126.Computation.Standard.atom .h0) (KIP126.Computation.Standard.atom .x_123_8) at h1
  rw [h0, h1, KIP126.Computation.Standard.atom_h0] at hd
  exact hd

end
end KIP126.SSComputation.Internal.Certification
end
