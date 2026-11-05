module

public import KIP126.Literature.Standard
public import KIP126.Literature.Triangles
import KIP126.Literature.Standard.FiniteQuotientComparison

/-! The signed finite-quotient row on arbitrary admissible vertices. -/
@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exactness of the normalized quotient row with its specified maps,
boundary sign and inclusion-compatible suspension comparison. -/
public theorem normalized_finite_quotient_horizontal_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (q : ℕ) (hq : 0 < q) :
    let N := KIP126.Literature.normalizedTriangle background T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q ≫ esusp.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum := by
  let N := KIP126.Literature.normalizedTriangle background T he
  have hN : N ∈ distTriang SyntheticSpectrum := normalized_triangle_distinguished T he
  obtain ⟨esusp, hinc, hrow⟩ := finite_quotient_horizontal_row N.rotate
    (rot_of_distTriang N hN) q hq
  refine ⟨esusp, hinc, ?_⟩
  let C := finiteQuotientComparison q hq
  letI := C.commShift
  letI := C.isTriangulated
  have hneg : XModLambdaN.map (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map N.mor₁)) q =
      -XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1 : ℤ)).map N.mor₁) q :=
    (background.quotients.functoriality.functor q).map_neg
  change Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (XModLambdaN.map (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map N.mor₁)) q ≫
      esusp.hom) ∈ distTriang SyntheticSpectrum at hrow
  simpa only [hneg, Preadditive.neg_comp] using hrow

end
end KIP126.Literature.Standard
