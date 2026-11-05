module

public import KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.SteenrodExt
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.Module.Basic

/-! The complete statement of Theorem 3.6 on the fixed synthetic Adams
spectral sequence. The total E₂ comparison retains the actual grading,
deformation map, classical Ext identification and homotopy filtration. -/

@[expose] section
set_option autoImplicit false
noncomputable section

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background PaperSpectrum)

namespace SyntheticAdamsTheorem

/-- The classical page of this very paper spectrum. -/
public abbrev classical (X : PaperSpectrum) :=
  background.classical.obj (X.adamsObject.obj background.auxiliary)

/-- The synthetic sequence of the same spectrum under the fixed ν functor. -/
public abbrev synthetic (X : PaperSpectrum) :=
  background.family.nu background.nu (X.adamsObject.obj background.auxiliary)

public abbrev classicalE2 (X : PaperSpectrum) (p : ℤ × ℤ) :=
  ((classical X).Page 2 p : Type)

public abbrev page (X : PaperSpectrum) (r : ℤ) (i : Tridegree) :=
  ((synthetic X).Page r i : Type)

/-- Finite sums of homogeneous elements of the actual page. -/
public abbrev totalPage (X : PaperSpectrum) (r : ℤ) :=
  DirectSum Tridegree (page X r)

/-- On every homogeneous summand, this is the actual deformation map. -/
public def totalLambda (X : PaperSpectrum) (r : ℤ) :
    totalPage X r →+ totalPage X r :=
  DirectSum.toAddMonoid (fun i =>
    (DirectSum.of (page X r) (i.1,i.2.1,i.2.2-1)).comp
      (pageLambda X.adamsObject r i.1 i.2.1 i.2.2).hom.toAddMonoidHom)

/-- Polynomial coefficients in each classical bidegree. A monomial λ^k
on the (s,t) summand has tridegree (s,t,t-k). -/
public abbrev polynomialE2 (X : PaperSpectrum)
    [∀ p, Module (ZMod 2) (classicalE2 X p)] :=
  DirectSum (ℤ × ℤ) (fun p => PolynomialModule (ZMod 2) (classicalE2 X p))

/-- All clauses use the fixed pages and maps. The additive total E₂
equivalence is F₂-linear and intertwines polynomial multiplication by λ
with the actual total deformation map, which equivalently makes it an
F₂[λ]-linear equivalence. The monomial equation fixes its trigrading. -/
public structure Data (X : PaperSpectrum) where
  classicalScalar : ∀ p, Module (ZMod 2) (classicalE2 X p)
  syntheticScalar : ∀ i, Module (ZMod 2) (page X 2 i)
  e2 :
    letI := classicalScalar
    polynomialE2 X ≃+ totalPage X 2
  e2_scalar :
    letI := classicalScalar
    letI := syntheticScalar
    ∀ (c : ZMod 2) (z : polynomialE2 X), e2 (c • z) = c • e2 z
  e2_lambda :
    letI := classicalScalar
    ∀ z : polynomialE2 X,
      e2 ((Polynomial.X : Polynomial (ZMod 2)) • z) = totalLambda X 2 (e2 z)
  e2_monomial :
    letI := classicalScalar
    ∀ (s t : ℤ) (k : ℕ) (x : classicalE2 X (s,t)),
      e2 (DirectSum.of _ (s,t) (PolynomialModule.single (ZMod 2) k x)) =
        DirectSum.of (page X 2) (s,t,t-k)
          (targetNuLabel background X.adamsObject s t k x)
  classical_ext : ∀ (s t : ℤ),
    classicalE2 X (s,t) ≃ₗ[ℤ]
      SteenrodExt.ext (X.adamsObject.obj background.auxiliary) s t
  differential_degree : ∀ r : ℤ,
    (synthetic X).sequence.diffDeg r = syntheticAdamsRawShift r
  differential_formula : ∀ (s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : classicalE2 X (s,t)) (y : classicalE2 X (s+r,t+r-1)),
      (HasDifferential (classical X) r (s,t) (s+r,t+r-1) x y ↔
        SyntheticHasDifferential (synthetic X) r
          (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1) : ℕ))
          (targetNuLabel background X.adamsObject s t k x)
          (targetNuLabel background X.adamsObject (s+r) (t+r-1) (k+(r-1)) y))
  /-- The same actual λ maps carry an E₂ representative and its later-page
  class to a representative and class at weight one lower. -/
  lambda_representatives : ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ)
    (x : page X 2 (s,t,w)) (z : page X r (s,t,w)),
    SyntheticRepresentsOnPage (synthetic X) r (s,t,w) x z →
      SyntheticRepresentsOnPage (synthetic X) r (s,t,w-1)
        (pageLambda X.adamsObject 2 s t w x)
        (pageLambda X.adamsObject r s t w z)
  differential_lambda : ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ),
    syntheticDifferential background X.adamsObject r s t w ≫
        pageLambda X.adamsObject r (s+r) (t+r-1) w =
      pageLambda X.adamsObject r s t w ≫
        syntheticDifferential background X.adamsObject r s t (w-1)
  above_diagonal : ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ), t < w →
    IsZero ((synthetic X).Page r (s,t,w))
  /-- Every actual page element below the diagonal, including zero and
  boundary classes, has a classical differential whose labels represent
  that specified element and its actual synthetic differential. -/
  differential_exhaustion :
    ∀ (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (hw : w ≤ t)
      (z : page X r (s,t,w)),
    ∃ (x : classicalE2 X (s,t)) (y : classicalE2 X (s+r,t+r-1)),
      HasDifferential (classical X) r (s,t) (s+r,t+r-1) x y ∧
      SyntheticRepresentsOnPage (synthetic X) r (s,t,w)
        (nuWeightLabel background X.adamsObject s t w hw x) z ∧
      SyntheticRepresentsOnPage (synthetic X) r (s+r,t+r-1,w)
        (nuWeightLabel background X.adamsObject (s+r) (t+r-1) w (by omega) y)
        (syntheticDifferential background X.adamsObject r s t w z)
  /-- The selected E∞ comparison is calibrated on actual tower lifts. -/
  canonical_convergence :
    SyntheticCanonicalIdentification background.syntheticTower
      (background.nu.functor.obj (X.adamsObject.obj background.auxiliary))
      (background.convergence (.nu X.adamsObject)).identification
  complete : ∀ p : ℤ × ℤ,
    Nonempty (Filtration.CompletionWitness
      (background.syntheticTower.filtration
        (background.nu.functor.obj (X.adamsObject.obj background.auxiliary))) p)
  separated : HomotopySeparated background.syntheticTower
    (background.nu.functor.obj (X.adamsObject.obj background.auxiliary))
  exhaustive :
    (background.syntheticTower.filtration
      (background.nu.functor.obj (X.adamsObject.obj background.auxiliary))).IsExhaustive

end SyntheticAdamsTheorem

/-- Theorem 3.6 for completed connective spectra of finite mod-two type:
the whole trigraded polynomial E₂ page, actual Ext, differential formula
and exhaustiveness, λ-linearity, and strong convergence to actual synthetic
homotopy. -/
public theorem synthetic_adams_theorem (X : PaperSpectrum) :
    Nonempty (SyntheticAdamsTheorem.Data X) := by
  sorry

end KIP126.Literature.Standard
