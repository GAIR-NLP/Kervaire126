module

public import KIP126.Literature.Geometry.Manifolds
public import Mathlib.Data.ZMod.Basic

/-! The geometric invariant used in AimPaper Theorems 1.1 and 1.3: the Arf
invariant of the quadratic refinement of the middle-dimensional mod-two
intersection pairing induced by the chosen stable framing.
See the Literature Blueprint for provenance.
-/

@[expose] section
namespace KIP126.Literature.Geometry

/-- The Kervaire invariant of this particular closed, stably framed smooth
(4k+2)-manifold: the Arf invariant of the canonical framing-induced quadratic
refinement of its middle-dimensional intersection pairing.
The manifold and its chosen framing are both retained as input data. -/
public noncomputable def kervaireInvariant (k : ℕ)
    (M : ClosedStablyFramedManifold (4 * k + 2)) : ZMod 2 := by
  sorry

/-- Geometric existence, defined through actual closed smooth manifolds with
specified stable framings. Dimensions outside 4k+2 are excluded by definition. -/
public def KervaireInvariantOneExists (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 4 * k + 2 ∧
    ∃ M : ClosedStablyFramedManifold (4 * k + 2), kervaireInvariant k M = 1

end KIP126.Literature.Geometry
