module

import all KIP126.ProofTools.FiniteLifting.LevelSourceLift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift

/-! Lambda multiplication commutes with the selected vertical translate on
the same full homotopy class. Only its forced weight reindexing is inserted. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem lambda_multiply_vertical_translate_comm
    (A : SyntheticSpectrum) (e : ℤ) (k : ℕ) (m w : ℤ) (a : BiHom m w A) :
    homotopyRegrade rfl (show (w+e)-(k:ℤ)=(w-(k:ℤ))+e by omega)
      (lambdaMultiply k (verticalTranslate A e m w a)) =
        verticalTranslate A e m (w-(k:ℤ)) (lambdaMultiply k a) := by
  have translate (w₀ : ℤ) (b : BiHom m w₀ A) :
      verticalTranslate A e m w₀ b =
        homotopyRegrade (m':=m) (by simp) rfl
          (shiftHomotopyClass (0,e) (m,w₀) b) := by
    simp [verticalTranslate,AddEquiv.trans_apply,regradeAddEquiv,
      suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,shiftHomotopyClass]
  rw [translate,translate]
  have h := congrArg (homotopyRegrade (rfl : m=m)
    (show w+e-(k:ℤ)=(w-(k:ℤ))+e by omega))
      (lambda_multiply_shift m w e k a)
  simpa only [normalized_homotopy_regrade_trans] using h.symm

end
end KIP126.ProofTools.Internal.SyntheticCoverage
