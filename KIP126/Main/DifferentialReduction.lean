module
import all KIP126.Main.ClassicalReduction

public import KIP126.Main.H6SquarePermanent
import all KIP126.Main.Internal.PageCalculus

/-! Differential consequences of Theorem 7.1 on the fixed sphere Adams system. -/

@[expose] section
namespace KIP126.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

/-- No nonzero differential leaves the standard product h6*h6. -/
private theorem h6_square_no_outgoing (r : ℤ) (hr : 2 ≤ r)
    (q : ℤ × ℤ) (y : background.classical.sphere.Page 2 q) :
    ¬ HasNonzeroDifferential background.classical.sphere r (2,128) q
      background.standardClasses.standardH6Square y := by
  intro hd
  apply Internal.nonzero_differential_not_permanent (E := background.classical.sphere)
    (by rw [background.classical.firstPage KIP126.StableHomotopy.SphereSpectrum]; exact hr)
    hd (h6_sq_permanent background.standardClasses)

/-- Differential reduction deduced from permanence on the fixed standard system. -/
private theorem only_d12_differential_reduction :
    (∀ (r : ℤ), 2 ≤ r → r ≠ 12 →
      ∀ y : background.classical.sphere.Page 2 (2+r,127+r),
        ¬ HasNonzeroDifferential background.classical.sphere r (2,128) (2+r,127+r)
          background.standardClasses.standardH6Square y) ∧
    ((∃ y : background.classical.sphere.Page 2 (14,139),
      HasNonzeroDifferential background.classical.sphere 12 (2,128) (14,139)
        background.standardClasses.standardH6Square y) ↔ H6SquareSupportsD12) ∧
    (¬ H6SquareSupportsD12 ↔ H6SquarePermanent) := by
  have hn : ¬ H6SquareSupportsD12 := fun hd =>
    (d12_necessary hd).1 (h6_sq_permanent background.standardClasses)
  refine ⟨fun r hr _ y => h6_square_no_outgoing r hr _ y, ?_, ?_⟩
  · constructor
    · rintro ⟨y, hy⟩
      exact False.elim (h6_square_no_outgoing 12 (by decide) _ y hy)
    · intro hd
      exact False.elim (hn hd)
  · exact ⟨fun _ => h6_sq_permanent background.standardClasses, fun _ => hn⟩

end KIP126.Main
