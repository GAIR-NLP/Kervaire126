module

import all KIP126.ProofTools.FiniteLifting.LevelSourceLift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedMahowald.Coherence

/-! Positive-weight translation and the positive-target lambda map on
one homotopy representative, using quotient coherence. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

private theorem vertical_translate_explicit (A : SyntheticSpectrum)
    (e m w : ℤ) (a : BiHom m w A) :
    verticalTranslate A e m w a =
      (biShiftAddIso (m,w) (0,e) (m,w+e) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (0,e)).map a := by
  change homotopyRegrade (add_zero m) rfl (susp_invariance m w 0 e A a) = _
  exact susp_regrade_eq m w 0 e m (w+e) (add_zero m) rfl A a

/-- Positive translation followed by the matching lambda power equals
postcomposition with the positive-target lambda map on the same source class. -/
private theorem lambda_multiply_vertical_translate (A : SyntheticSpectrum)
    (k : ℕ) (m w : ℤ) (a : BiHom m w A) :
    homotopyRegrade rfl (show (w+(k:ℤ))-(k:ℤ)=w by omega)
      (lambdaMultiply k (verticalTranslate A (k:ℤ) m w a)) =
        a ≫ lambdaToPositivePow k A := by
  rw [lambda_multiply_raw,normalized_homotopy_regrade_trans,regrade_comp,shift_regrade,
    vertical_translate_explicit]
  have h := shift_hom_associativity background.quotients.coherence
    (m,w) (0,(k:ℤ)) (0,-(k:ℤ)) (m,w+k) (0,0) (m,w)
    (by ext <;> simp) (by ext <;> simp)
    (by ext <;> dsimp <;> omega) (by ext <;> simp) a
  rw [←h]
  have hunit : (biShiftAddIso (m,w) (0,0) (m,w) (by ext <;> simp)).app S_0_0 =
      SyntheticCategory.biShift_zero.app (Smn m w : SyntheticSpectrum) := by
    apply Iso.ext
    exact background.quotients.coherence.right_unit (m,w) S_0_0
  have hz : (biShiftAddIso (m,w) (0,0) (m,w) (by ext <;> simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,0)).map a = a ≫ SyntheticCategory.biShift_zero.inv.app A := by
    rw [←Iso.app_inv,hunit]
    exact (SyntheticCategory.biShift_zero.inv.naturality a).symm
  simp only [←Category.assoc]
  rw [hz]
  simp only [lambdaToPositivePow,biShiftAddIso,Iso.trans_inv,
    NatTrans.comp_app,eqToIso.inv,eqToHom_app,Category.assoc]

end
end KIP126.ProofTools.Internal.SyntheticCoverage
