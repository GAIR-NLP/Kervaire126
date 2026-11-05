module

import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer

/-! Exact identification of the signed May output with one selected highest-layer inclusion. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem top_target_regrade_self {A : SyntheticSpectrum} {m w : ℤ}
    (a : BiHom m w A) : homotopyRegrade rfl rfl a=a := rfl

/-- One selected Q₁-to-top-layer inclusion, with only quotient-length and
weight equalities transported. -/
private def finiteTopLabelAtWeight (X : AdamsObject (coefficients := background.coefficients)) (d : ℕ) (hd : 0<d)
    (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
    (x : Ambient background X (s,t)) :
    BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) :=
  hN ▸ homotopyRegrade rfl hw (finiteTopLabel X d hd s t x)

private theorem finite_top_label_at_weight_detects
    (X : AdamsObject (coefficients := background.coefficients)) (d : ℕ) (hd : 0<d)
    (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
    (x : Ambient background X (s,t)) :
    Detects (background.convergence (.quotient N (.nu X))) (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) x))
      (finiteTopLabelAtWeight X d hd N hN s t w hw x) := by
  subst N
  subst w
  rw [finite_coefficient_weight_label]
  simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using
    finiteTopLabel_detects X d hd s t x

/-- The highest-layer target of the specified May label v,
using the selected top inclusion. -/
private def finiteMayTopLabel (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q)
    (s t : ℤ) (v : Ambient background X (s+q+1,t+q)) :
    BiHom ((t-s)-1) (t-c)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))) :=
  homotopyRegrade (by omega) rfl
    (finiteTopLabelAtWeight X (c+q) (by omega) (c+(q+1)) (by omega)
      (s+q+1) (t+q) (t-c) (by omega) v)

private theorem finite_may_top_label_detects
    (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q)) :
    Detects (background.convergence (.quotient (c+(q+1)) (.nu X))) (s+q+1,t+q,t-c)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))).pageMap
        2 (s+q+1,t+q,t-c) (nuWeightLabel background X (s+q+1) (t+q) (t-c) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl (finiteMayTopLabel X c q hq s t v)) := by
  simpa only [finiteMayTopLabel,homotopy_regrade_inverse] using
    finite_top_label_at_weight_detects X (c+q) (by omega) (c+(q+1)) (by omega)
      (s+q+1) (t+q) (t-c) (by omega) v

/-- Highest-layer uniqueness identifies the homotopy class
of the specified top target. -/
private theorem finite_may_target_eq_top_of_detects
    (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q))
    (bN : BiHom ((t-s)-1) (t-c)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))))
    (hb : Detects (background.convergence (.quotient (c+(q+1)) (.nu X))) (s+q+1,t+q,t-c)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))).pageMap
        2 (s+q+1,t+q,t-c) (nuWeightLabel background X (s+q+1) (t+q) (t-c) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl bN)) :
    bN = finiteMayTopLabel X c q hq s t v := by
  have h := finite_top_detection_unique X (c+(q+1)) (by omega)
    (s+q+1) (t+q) (t-c) (by omega) _ _ _ hb
    (finite_may_top_label_detects X c q hq s t v)
  have h' := congrArg (homotopyRegrade
    (show (t+q)-(s+q+1)=(t-s)-1 by omega) (rfl : t-c=t-c)) h
  simpa only [homotopy_regrade_inverse] using h'

/-- The raw signed and coefficient-extended May output is precisely the
ordinary suspension of the single selected Q₁-to-Qₚ highest-layer inclusion
of the specified v. -/
private theorem finite_may_signed_target_eq_top_at_level
    (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q))
    (en : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (q+1)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) ⟶
        XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
    finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
      ordinarySuspendedRepresentative _ (t-s) (t-c) (finiteMayTopLabel X c q hq s t v) := by
  dsimp only
  obtain ⟨bN,hb,hraw⟩ := finite_may_signed_target_at_level X c q hq s t v en eN hen heN
  rw [finite_may_target_eq_top_of_detects X c q hq s t v bN hb] at hraw
  exact hraw

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
