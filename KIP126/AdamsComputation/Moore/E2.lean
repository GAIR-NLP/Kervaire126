module

public import KIP126.AdamsComputation.Moore.Object
public import KIP126.AdamsComputation.Table

/-! E₂ cell maps and bottom-cell image for the completed Moore spectrum. -/

@[expose] section
namespace KIP126.AdamsComputation.Moore
open CategoryTheory KIP126.StableHomotopy
open KIP126.AdamsSynthetic.Completed
noncomputable section

public def bottomPageMap (s t : ℤ) :
    background.classical.sphere.Page 2 (s,t) →ₗ[ℤ] sequence.Page 2 (s,t) :=
  (background.classical.pageMap bottom 2 (s,t)).hom

public def topPageMap (s t : ℤ) :
    sequence.Page 2 (s,t) →ₗ[ℤ]
      (background.classical.obj ((SphereSpectrum (C := Spectrum))⟦(1 : ℤ)⟧)).Page 2 (s,t) :=
  (background.classical.pageMap top 2 (s,t)).hom

/-- Bottom-cell image of sphere basis[0] in bidegree (8,132). -/
public def bottomSource : Page 8 132 :=
  bottomPageMap 8 132 (KIP126.Computation.Table.basis .sphere 8 132 0)

end
end KIP126.AdamsComputation.Moore
