module

import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryLastLayer
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget

/-! The last-layer image for a filtration-zero first arrow. A candidate-space
kernel condition is applied to its label after constructing the differential. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem last_layer_ordinary_image_eq_top_at_weight
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d N : ℕ) (hd : 0 < d) (hN : d+1=N)
    (s t w : ℤ) (hw : t-d=w)
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ e : Ambient background X (s,t),
      a ≫ XModLambdaN.map (background.nu.functor.map f) N =
        finiteTopLabelAtWeight Y d hd N hN s t w hw
          ((background.classical.map f).pageMap 2 (s,t) e) := by
  subst N
  subst w
  obtain ⟨e,rfl⟩ := finiteTopLabel_exists X d hd s t a ha
  exact ⟨e,finite_top_label_ordinary_natural X Y f d hd s t e⟩

/-- Decode the actual last-layer error in the coordinates of the finite
May construction. The ordinary map and the E₂ image come from the same f. -/
private theorem last_layer_ordinary_image_eq_finite_may_top
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
    (a : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))))
    (ha : FiltrationAtLeast background.syntheticTower (B+q+1) a) :
    ∃ e : Ambient background X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
        (a ≫ XModLambdaN.map (background.nu.functor.map f) (c+(q+1))) =
        finiteMayTopLabel Y c q hq B W
          ((background.classical.map f).pageMap 2 (B+q+1,W+q) e) := by
  let a' := homotopyRegrade
    (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl a
  have ha' : FiltrationAtLeast background.syntheticTower (B+q+1) a' :=
    homotopy_regrade_filtration (by omega) rfl _ a ha
  obtain ⟨e,he⟩ := last_layer_ordinary_image_eq_top_at_weight X Y f
    (c+q) (c+(q+1)) (by omega) (by omega)
    (B+q+1) (W+q) (W-c) (by push_cast; omega) a' ha'
  refine ⟨e,?_⟩
  have hh := congrArg (homotopyRegrade
    (show (W+q)-(B+q+1)=(W-B)-1 by omega)
    (rfl : W-c=W-c)) he
  simpa only [a',regrade_comp,last_layer_regrade_trans,finiteMayTopLabel] using hh

end
end KIP126.ProofTools.Internal.SyntheticCoverage
