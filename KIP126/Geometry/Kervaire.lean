module

public import KIP126.Literature
import KIP126.Main

/-! AimPaper Theorem 1.1 and Corollary 1.2, using the geometric objects,
Kervaire invariant and Browder comparison supplied by Literature. -/

@[expose] section
namespace KIP126.Geometry
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)
open KIP126.Literature.Geometry

private theorem square_survives_iff (j : ℕ) (hjBound : j ≤ 7) :
    NonzeroSurvival background.classical.sphere (2, ((2 ^ (j + 1) : ℕ) : ℤ))
      (background.standardClasses.standardHiSquare j) ↔ j ≤ 6 := by
  constructor
  · intro h
    by_contra hn
    exact KIP126.Literature.Standard.high_hi_squares_not_permanent j (by omega) hjBound h
  · intro hj
    by_cases hlow : j ≤ 3
    · exact KIP126.Literature.Standard.low_hi_squares_permanent j hlow
    · have cases : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases cases with rfl | rfl | rfl
      · exact KIP126.Literature.Standard.h4_square_permanent
      · exact KIP126.Literature.Standard.h5Square_permanent
      · exact KIP126.Main.h6_sq_permanent background.standardClasses

private theorem admissible_dimensions (n : ℕ) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ 6 ∧ n = 2 ^ (j + 1) - 2) ↔
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  constructor
  · rintro ⟨j, hj, hj', rfl⟩
    interval_cases j <;> norm_num
  · intro hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨3, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨5, by decide, by decide, by decide⟩
    · exact ⟨6, by decide, by decide, by decide⟩

/-- AimPaper Theorem 1.1: a closed smooth stably framed manifold of
Kervaire invariant one exists in dimension 126. -/
public theorem kervaire_invariant_one_126 : KervaireInvariantOneExists 126 := by
  exact (browder_iff 126 (by decide)).mpr
    ⟨6, by decide, by decide, by decide, KIP126.Main.h6_sq_permanent background.standardClasses⟩

/-- AimPaper Corollary 1.2: precisely the six stated dimensions admit a
closed smooth stably framed manifold of Kervaire invariant one. -/
public theorem kervaire_invariant_one_iff (n : ℕ) :
    KervaireInvariantOneExists n ↔
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  by_cases hn : n ≤ 254
  · rw [browder_iff n hn, ← admissible_dimensions]
    constructor
    · rintro ⟨j, hjBound, hj, hn, hs⟩
      exact ⟨j, hj, (square_survives_iff j hjBound).mp hs, hn⟩
    · rintro ⟨j, hj, hs, hn⟩
      exact ⟨j, by omega, hj, hn, (square_survives_iff j (by omega)).mpr hs⟩
  · constructor
    · intro h
      exact (kervaire_invariant_one_not_exists_of_ge_254 n (by omega) h).elim
    · intro h
      omega

end KIP126.Geometry
