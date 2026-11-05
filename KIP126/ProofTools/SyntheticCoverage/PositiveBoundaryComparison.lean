module

import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative

/-! First labels of the actual boundary of a positive normalized finite
image. The source automorphism in the quotient-shift comparison is retained
on full classes and removed only after projection to the first quotient. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem positive_finite_image_boundary_label
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (_hN : 0<N) (s t : ℤ)
    (u : Ambient background T.X (s+N+1,t+N))
    (z : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hz : adjacentBoundaryLabel T.X N s t z =
      nativeFirstLabel T.X (s+N+1) (t+N) u) :
    let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z
    homotopyRegrade
        (show (t-s)-1=((t+N)+1)-((s+N+1)+1) by omega)
        (show (t+1)+N=(t+N)+1 by omega)
        (biSuspensionHomEquiv (t-s) (t+1) N
          (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel T.Y ((s+N+1)+1) ((t+N)+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+N+1) (t+N) u) := by
  let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t z
  have hη : positiveBoundaryFiniteImage T.X T.Y (lastLayerNormalizedMap T hf) N s t z =
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl η := by
    simp [η,positiveBoundaryFiniteImage,positiveFiniteImage,verticalTranslate,
      regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,
      Iso.homCongr,regrade_comp,Category.assoc]
  have hb := positive_boundary_finite_image_boundary T.X T.Y
    (lastLayerNormalizedMap T hf) N s t z
  rw [hη] at hb
  dsimp only [boundaryRepresentative] at hb
  rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans] at hb
  have hfirst := positive_full_source_first_label T.X (s+N+1) (t+N) u
    (positiveAdjustedBoundary T.X N s t z)
    ((positive_adjusted_boundary_first T.X N s t z).trans hz)
  have hmap := normalizedFirstMap_boundary T hf (s+N+1) (t+N) u
  rw [←hfirst,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc] at hmap
  have hb' := congrArg (homotopyRegrade
    (show ((t+1)+N)-((s+1)+N+1)=((t+N)+1)-((s+N+1)+1) by omega)
    (show (t+1)+N=(t+N)+1 by omega)) hb
  have hproj := congrArg (fun a => a ≫ XModLambdaN.incl _ 1) hb'
  simp only [normalized_homotopy_regrade_trans,regrade_comp] at hproj hmap
  dsimp only
  exact hproj.trans hmap

end
end KIP126.ProofTools.Internal.SyntheticCoverage
