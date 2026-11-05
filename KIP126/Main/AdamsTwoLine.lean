module

public import KIP126.Main.H6SquarePermanent
public import KIP126.Literature
public import KIP126.AdamsComputation
public import KIP126.SSComputation
import all KIP126.Main.Internal.PageCalculus

/-! The finite-range specialization of AimPaper Corollary 1.5 on the actual sphere E₂ page.
The classification combines the classical literature, E₂ basis, and d₂-stage inputs. -/

@[expose] section
namespace KIP126.Main
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background)

/-- The list in Corollary 1.5, with equality in the actual E₂ module.
The degree equation prevents heterogeneous identifications between stems.
Indices are natural numbers, so the square branch includes h₀². -/
public def AdamsTwoLineListed (t : ℤ) (x : background.classical.sphere.Page 2 (2,t)) : Prop :=
  ∃ (i j : ℕ) (hiBound : i ≤ 7) (hjBound : j ≤ 7),
    ((i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6)) ∧
    ∃ degree : hiDegree i + hiDegree j = (2,t),
      x = (eqToHom (congrArg (ActualE2At background.classical) degree))
        (background.sphereAlgebra.product (hiDegree i) (hiDegree j)
          (background.standardClasses.standardHi i) (background.standardClasses.standardHi j))

/-- Exhaustive classification target through internal degree 256, specializing
AimPaper Corollary 1.5. Survival
retains a common Z∞ representative and a nonzero E∞ image. -/
public def AdamsTwoLineClassification : Prop :=
  ∀ (t : ℤ), t ≤ 256 → ∀ (x : background.classical.sphere.Page 2 (2,t)),
    NonzeroSurvival background.classical.sphere (2,t) x ↔ AdamsTwoLineListed t x

private theorem square_listed (j : ℕ) (hj : j ≤ 6) :
    AdamsTwoLineListed ((2 ^ (j+1) : ℕ) : ℤ)
      (background.standardClasses.standardHiSquare j) := by
  refine ⟨j,j,by omega,by omega,Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hj⟩))),?_,?_⟩
  · ext <;> simp [hiDegree, pow_succ, mul_two]
  · rfl

/-- The two square cases j=5 and j=6. The first uses Literature.h5Square_permanent;
the second uses the main theorem. The other listed classes and exhaustiveness
are separate assertions. -/
public theorem adams_two_line_known_squares (j : ℕ) (hj : j = 5 ∨ j = 6) :
    NonzeroSurvival background.classical.sphere (2,((2 ^ (j+1) : ℕ) : ℤ))
      (background.standardClasses.standardHiSquare j) ∧
    AdamsTwoLineListed ((2 ^ (j+1) : ℕ) : ℤ)
      (background.standardClasses.standardHiSquare j) := by
  rcases hj with rfl | rfl
  · exact ⟨KIP126.Literature.Standard.h5Square_permanent, square_listed 5 (by decide)⟩
  · exact ⟨h6_sq_permanent background.standardClasses, square_listed 6 (by decide)⟩

/-- In stem 126 the only nonzero surviving E₂ class is h₆².
The classification uses the fixed exhaustive E₂ basis. -/
public theorem adams_two_line_stem126 (x : background.classical.sphere.Page 2 (2,128)) :
    NonzeroSurvival background.classical.sphere (2,128) x ↔
      x = background.standardClasses.standardH6Square := by
  constructor
  · intro hx
    rcases KIP126.Computation.Standard.square_exhaustive x with hz | he
    · obtain ⟨z,hz',hnz⟩ := hx
      let D := background.classical.sphere.ssData (2,128)
      have h := D.infinity_projection_eq_of_page_projection_eq
        (↑(2-background.classical.sphere.r₀).toNat) z 0
        (by simpa only [map_zero] using hz'.trans hz)
      exact False.elim (hnz (by simpa only [map_zero] using h))
    · exact he
  · rintro rfl
    exact h6_sq_permanent background.standardClasses

private theorem survival_regrade {p q : ℤ × ℤ} (h : p = q)
    (x : ActualE2At background.classical p) :
    NonzeroSurvival background.classical.sphere q
      ((eqToHom (congrArg (ActualE2At background.classical) h)) x) ↔
    NonzeroSurvival background.classical.sphere p x := by
  subst q
  rfl

private theorem square_survival_iff (j : ℕ) (hjBound : j ≤ 7) :
    NonzeroSurvival background.classical.sphere (hiDegree j + hiDegree j)
      (KIP126.Literature.Standard.hiProduct j j) ↔
    NonzeroSurvival background.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (background.standardClasses.standardHiSquare j) := by
  have hd : hiDegree j + hiDegree j = (2,((2^(j+1) : ℕ) : ℤ)) := by
    ext <;> simp [hiDegree,pow_succ,mul_two]
  have hs : background.standardClasses.standardHiSquare j =
      (eqToHom (congrArg (ActualE2At background.classical) hd))
        (KIP126.Literature.Standard.hiProduct j j) := rfl
  rw [hs]
  exact (survival_regrade hd _).symm

private theorem survival_nonzero {p : ℤ × ℤ}
    {x : background.classical.sphere.Page 2 p}
    (hx : NonzeroSurvival background.classical.sphere p x) : x ≠ 0 := by
  intro hzero
  obtain ⟨z,hz,hnz⟩ := hx
  let D := background.classical.sphere.ssData p
  have h := D.infinity_projection_eq_of_page_projection_eq
    (↑(2-background.classical.sphere.r₀).toNat) z 0
    (by simpa only [map_zero] using hz.trans hzero)
  exact hnz (by simpa only [map_zero] using h)

private theorem survival_reaches_three {p : ℤ × ℤ}
    {x : background.classical.sphere.Page 2 p}
    (hx : NonzeroSurvival background.classical.sphere p x) :
    ReachesPage background.classical.sphere 3 p x := by
  obtain ⟨z,hz,_⟩ := hx
  let D := background.classical.sphere.ssData p
  let zr := (Subobject.ofLE (D.Z ⊤) (D.Z ↑(3-background.classical.sphere.r₀).toNat)
    (D.Z_anti le_top)) z
  refine ⟨D.pageπ _ zr,by decide,zr,?_,rfl⟩
  dsimp only [zr]
  rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem listed_pair_survives (i j : ℕ)
    (hiBound : i ≤ 7) (hjBound : j ≤ 7)
    (h : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6)) :
    NonzeroSurvival background.classical.sphere (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j) := by
  rcases h with h02 | h03 | h24 | ⟨rfl,hj⟩ | ⟨heq,hj⟩
  · exact KIP126.Literature.Standard.exceptional_hi_products_permanent i j (Or.inl h02)
  · exact KIP126.Literature.Standard.exceptional_hi_products_permanent i j (Or.inr (Or.inl h03))
  · exact KIP126.Literature.Standard.exceptional_hi_products_permanent i j (Or.inr (Or.inr h24))
  · exact KIP126.Literature.Standard.h1_hi_product_permanent j hj
  · subst i
    apply (square_survival_iff j (by omega)).mpr
    by_cases hlow : j ≤ 3
    · exact KIP126.Literature.Standard.low_hi_squares_permanent j hlow
    · have hcases : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact KIP126.Literature.Standard.h4_square_permanent
      · exact KIP126.Literature.Standard.h5Square_permanent
      · exact h6_sq_permanent background.standardClasses

private theorem surviving_pair_listed (i j : ℕ) (hij : i ≤ j)
    (hiBound : i ≤ 7) (hjBound : j ≤ 7)
    (hx : NonzeroSurvival background.classical.sphere (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j)) :
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6) := by
  have hc := KIP126.SSComputation.two_line_d2_candidates i j hij hiBound hjBound
    (survival_nonzero hx) (survival_reaches_three hx)
  rcases hc with h02 | h03 | h24 | heta | hsq | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩
  · exact Or.inl h02
  · exact Or.inr (Or.inl h03)
  · exact Or.inr (Or.inr (Or.inl h24))
  · exact Or.inr (Or.inr (Or.inr (Or.inl heta)))
  · subst i
    have hj : j ≤ 6 := by
      by_contra hn
      exact KIP126.Literature.Standard.high_hi_squares_not_permanent j (by omega) hjBound
        ((square_survival_iff j (by omega)).mp hx)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hj⟩)))
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.h2_h5_supports_nonzero_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [background.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.h3_h5_supports_nonzero_d4
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [background.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.h3_h6_supports_nonzero_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [background.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.h0_h4_supports_nonzero_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [background.classical.firstPage]; decide) hy hx)

/-- AimPaper Corollary 1.5: the second-line classification through internal degree 256 on the fixed
sphere. -/
public theorem adams_two_line_classification : AdamsTwoLineClassification := by
  intro t ht x
  constructor
  · intro hx
    obtain ⟨i,j,hiBound,hjBound,hij,degree,heq⟩ := KIP126.Literature.Standard.two_line_exhaustive t x
      (survival_nonzero hx) ht
    have hp := (survival_regrade degree (KIP126.Literature.Standard.hiProduct i j)).mp
      (heq ▸ hx)
    exact ⟨i,j,hiBound,hjBound,surviving_pair_listed i j hij hiBound hjBound hp,degree,heq⟩
  · rintro ⟨i,j,hiBound,hjBound,hij,degree,heq⟩
    rw [heq]
    exact (survival_regrade degree (KIP126.Literature.Standard.hiProduct i j)).mpr
      (listed_pair_survives i j hiBound hjBound hij)

end KIP126.Main
