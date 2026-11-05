module

public import KIP126.ProofTools.Laws
public import KIP126.ProofTools.Representatives
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.WitnessSquare
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom

/-! The level-aware generalized Leibniz theorem. Its law is defined
in Laws; `Standard.generalizedLeibnizAtLevel` is proved
in GeneralizedLeibnizAtLevel.lean. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem lambda_target_class (Y : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) (k j : ℕ)
    (x : Ambient background Y (s,t)) (hx : IsPermanent background Y (s,t) x)
    (e : ((background.family.nu background.nu (Y.obj background.auxiliary)).sequence.ssData (s,t,t-k)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,t-k) (targetNuLabel background Y s t k x) e) :
    KIP126.Literature.Standard.infinityNuWindow Y (s,t) (t-k-j) (by omega)
      (KIP126.Literature.Standard.infinityLambda (.nu Y) j (s,t) (t-k) e) =
      KIP126.Literature.subquotientClass (KIP126.Literature.permanentCycles background Y (s,t))
        (KIP126.Literature.boundaries background Y (1+t-(t-k-j)) (s,t)) ⟨x,hx⟩ := by
  have hlabel : nuWeightLabel background Y s t (t-k) (by omega) x =
      targetNuLabel background Y s t k x := by
    have hk : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a = b)
        (h : (s,t,t-a) = (s,t,t-b)) :
        regradeE2 h (targetNuLabel background Y s t a x) = targetNuLabel background Y s t b x := by
      subst b
      rfl
    exact transport _ k hk _
  have heq := (KIP126.Literature.Standard.eInfinity_nu_labels Y s t (t-k)
    (by omega) x e).mp (by rwa [hlabel])
  have hm := KIP126.Literature.Standard.eInfinity_lambda_nu Y j (s,t) (t-k) (by omega) e
  rw [heq.2] at hm
  exact hm

end
end KIP126.ProofTools.Standard
