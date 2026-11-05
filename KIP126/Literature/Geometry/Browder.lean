module

public import KIP126.Literature.Geometry.KervaireInvariant
public import KIP126.AdamsSynthetic

/-! Browder's geometric criterion, as used in AimPaper Theorem 1.3.
The comparison concerns stable framings and the fixed 2-completed sphere
Adams spectral sequence, including integral framed cobordism and the
specified h_j classes. The geometric dimension convention is 4k+2, so j≥1. -/

@[expose] section
namespace KIP126.Literature.Geometry
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

open CategoryTheory KIP126.StableHomotopy
open KIP126.AdamsSynthetic
noncomputable section
/-- Pontryagin--Thom of the actual manifold with its chosen framing lands
in the ordinary sphere, before any completion. -/
public def pontryaginThom {n : ℕ} (M : ClosedStablyFramedManifold n) :
    HomotopyGroup (n : ℤ) (SphereSpectrum (C := Ordinary.Spectrum)) := by sorry
/-- The comparison uses the actual completion functor on this same class. -/
public def completedPontryaginThom {n : ℕ} (M : ClosedStablyFramedManifold n) :
    HomotopyGroup (n : ℤ) (SphereSpectrum (C := Completed.Spectrum)) :=
  (Completed.completionSphereShiftIso (n : ℤ)).inv ≫
    Completed.completion.map (pontryaginThom M) ≫ Completed.completionSphereIso.hom

/-- Browder's criterion (AimPaper Theorem 1.3) for positive indices and
nonzero survival of the standard square on the fixed sphere. -/
public theorem browder_iff (n : ℕ) (hn : n ≤ 254) :
    KervaireInvariantOneExists n ↔
      ∃ (j : ℕ) (hjBound : j ≤ 7), 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧
        NonzeroSurvival background.classical.sphere (2, ((2 ^ (j + 1) : ℕ) : ℤ))
          (background.standardClasses.standardHiSquare j) := by
  sorry

/-- HHR high-dimensional nonexistence for stably framed manifolds. -/
public theorem kervaire_invariant_one_not_exists_of_ge_254 (n : ℕ) (hn : 254 ≤ n) :
    ¬ KervaireInvariantOneExists n := by
  sorry

end
end KIP126.Literature.Geometry
