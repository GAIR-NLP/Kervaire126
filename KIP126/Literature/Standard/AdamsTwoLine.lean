module

public import KIP126.Literature.Standard
public import KIP126.Literature.Geometry.Browder

/-! Classical inputs for AimPaper Corollary 1.5 on the fixed sphere Adams
sequence, with the comparisons used in the second-line classification. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

/-- The actual product of the two specified standard one-line classes. -/
public noncomputable def hiProduct (i j : ℕ)
    (hiBound : i ≤ 7 := by omega) (hjBound : j ≤ 7 := by omega) :
    ActualE2At background.classical (hiDegree i + hiDegree j) :=
  background.sphereAlgebra.product (hiDegree i) (hiDegree j)
    (background.standardClasses.standardHi i) (background.standardClasses.standardHi j)

/-- May's three exceptional low-dimensional mixed products. -/
public theorem exceptional_hi_products_permanent (i j : ℕ)
    (h : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4))
    (hiBound : i ≤ 7 := by omega) (hjBound : j ≤ 7 := by omega) :
    NonzeroSurvival background.classical.sphere (hiDegree i + hiDegree j) (hiProduct i j) := by
  sorry

/-- The low Kervaire squares, including the degree-zero class h₀². -/
public theorem low_hi_squares_permanent (j : ℕ) (hj : j ≤ 3) :
    NonzeroSurvival background.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (background.standardClasses.standardHiSquare j) := by
  sorry

/-- Mahowald--Tangora's 30-stem Kervaire class. -/
public theorem h4_square_permanent :
    NonzeroSurvival background.classical.sphere (2,32)
      (background.standardClasses.standardHiSquare 4) := by
  sorry

/-- Mahowald, Theorem 1', restricted to the family needed by Corollary 1.5. -/
public theorem h1_hi_product_permanent (j : ℕ) (hj : 3 ≤ j) (hjBound : j ≤ 7 := by omega) :
    NonzeroSurvival background.classical.sphere (hiDegree 1 + hiDegree j) (hiProduct 1 j) := by
  sorry

/-- Mahowald--Tangora's differential on h₂h₅, with its target degree. -/
public theorem h2_h5_supports_nonzero_d3 :
    ∃ y : background.classical.sphere.Page 2 (5,38),
      HasNonzeroDifferential background.classical.sphere 3 (2,36) (5,38) (hiProduct 2 5) y := by
  sorry

/-- Mahowald--Tangora's nonzero d₄ on h₃h₅. -/
public theorem h3_h5_supports_nonzero_d4 :
    ∃ y : background.classical.sphere.Page 2 (6,43),
      HasNonzeroDifferential background.classical.sphere 4 (2,40) (6,43) (hiProduct 3 5) y := by
  sorry

/-- IWX's nonzero classical d₃ on h₃h₆. -/
public theorem h3_h6_supports_nonzero_d3 :
    ∃ y : background.classical.sphere.Page 2 (5,74),
      HasNonzeroDifferential background.classical.sphere 3 (2,72) (5,74) (hiProduct 3 6) y := by
  sorry

/-- IWX's nonzero classical d₃ on h₀h₄. This class reaches E₃ and must
therefore be retained by d₂-stage screening before this later exclusion. -/
public theorem h0_h4_supports_nonzero_d3 :
    ∃ y : background.classical.sphere.Page 2 (5,19),
      HasNonzeroDifferential background.classical.sphere 3 (2,17) (5,19) (hiProduct 0 4) y := by
  sorry

/-- HHR's nonexistence theorem transported to the specified standard squares. -/
public theorem high_hi_squares_not_permanent (j : ℕ) (hj : 7 ≤ j) (hjBound : j ≤ 7 := by omega) :
    ¬ NonzeroSurvival background.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (background.standardClasses.standardHiSquare j) := by
  have heq : j = 7 := by omega
  subst j
  intro hs
  apply KIP126.Literature.Geometry.kervaire_invariant_one_not_exists_of_ge_254 254 (by decide)
  exact (KIP126.Literature.Geometry.browder_iff 254 (by decide)).mpr
    ⟨7, by decide, by decide, by decide, hs⟩

/-- Every nonzero homogeneous second-line element through internal degree 256
is a standard product. This finite specialization of Adams's second-line
theorem is independent of the bounded computation archive and later pages. -/
public theorem two_line_exhaustive (t : ℤ) (x : background.classical.sphere.Page 2 (2,t))
    (hx : x ≠ 0) (ht : t ≤ 256) :
    ∃ (i j : ℕ) (hiBound : i ≤ 7) (hjBound : j ≤ 7), i ≤ j ∧
      ∃ degree : hiDegree i + hiDegree j = (2,t),
        x = (eqToHom (congrArg (ActualE2At background.classical) degree))
          (KIP126.Literature.Standard.hiProduct i j) := by
  sorry

end KIP126.Literature.Standard
