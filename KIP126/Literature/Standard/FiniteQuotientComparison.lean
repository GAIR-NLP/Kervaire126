module

public import KIP126.AdamsSynthetic.Completed.Background

/-!
The fixed Standard finite λ quotient as an exact smash functor.

The comparison uses the selected quotient objects, maps, and inclusions.
The suspension and exactness fields use one specified shift structure.
-/

@[expose] section
namespace KIP126.Literature.Standard

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Completed (SyntheticSpectrum background)

noncomputable section
set_option autoImplicit false

/-- Natural smash comparison for the finite λ quotient, with an exact
shift structure compatible with the inclusion. Transport along `tensorIso`
equips the smash functor with this shift and exactness data. -/
public structure FiniteQuotientComparison (q : ℕ) where
  commShift : (background.quotients.functoriality.functor q).CommShift ℤ
  isTriangulated : letI := commShift
    (background.quotients.functoriality.functor q).IsTriangulated
  tensorIso : background.quotients.functoriality.functor q ≅
    tensorLeft (XModLambdaN (SphereSpectrum : SyntheticSpectrum) q)
  incl_tensor : ∀ X : SyntheticSpectrum,
    XModLambdaN.incl X q ≫ tensorIso.hom.app X =
      (λ_ X).inv ≫ (XModLambdaN.incl (SphereSpectrum : SyntheticSpectrum) q ▷ X)
  incl_shift : letI := commShift
    ∀ (n : ℤ) (X : SyntheticSpectrum),
      XModLambdaN.incl (X⟦n⟧) q ≫
          ((background.quotients.functoriality.functor q).commShiftIso n).hom.app X =
        (shiftFunctor SyntheticSpectrum n).map (XModLambdaN.incl X q)

/-- The finite λ quotient–smash comparison on the fixed Standard background.
It includes exactness and the inclusion coherences. -/
public def finiteQuotientComparison (q : ℕ) (hq : 0 < q) :
    FiniteQuotientComparison q := by
  sorry

/-- The finite quotient of a distinguished triangle, with last map
induced by the exact functor's inclusion-compatible suspension comparison. -/
public theorem finite_quotient_horizontal_row
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ) (hq : 0 < q) :
    ∃ eA : XModLambdaN (N.obj₁⟦(1 : ℤ)⟧) q ≅
        (XModLambdaN N.obj₁ q)⟦(1 : ℤ)⟧,
      XModLambdaN.incl (N.obj₁⟦(1 : ℤ)⟧) q ≫ eA.hom =
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (XModLambdaN.incl N.obj₁ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
        (XModLambdaN.map N.mor₃ q ≫ eA.hom) ∈ distTriang SyntheticSpectrum := by
  let C := finiteQuotientComparison q hq
  letI := C.commShift
  letI := C.isTriangulated
  refine ⟨((background.quotients.functoriality.functor q).commShiftIso (1 : ℤ)).app N.obj₁,
    C.incl_shift 1 N.obj₁, ?_⟩
  exact (background.quotients.functoriality.functor q).map_distinguished N hN

end
end KIP126.Literature.Standard
