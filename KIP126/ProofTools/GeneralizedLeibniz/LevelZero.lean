module
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
/-! Zero-level compatibility of finite extension witnesses, preserving
the extension equation through the label comparison. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem finite_witness_native_source_zero (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (W : FiniteExtensionWitness background X Y f page m s t x y) :
    ∃ z : ((background.family.obj ((SyntheticObject.quotient (page-1) (.nu X)).obj
        background.nu background.auxiliary)).sequence.ssData (s,t,t-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t-(0:ℕ))
        (finiteTargetLabel background X (page-1) s t 0 x) z := by
  have hpage := W.page_ge_two
  have hx : x∈cycles background X ((page-1:ℕ)-t+(t-(0:ℕ))) (s,t) := by
    have h := ((isCycle_iff_reaches background X page (by omega) (s,t) x).mpr W.source_cycle).2
    convert h using 1
    congr 1
    omega
  let C := KIP126.Literature.Standard.infinityFiniteWindow X (page-1)
    (by omega) (s,t) (t-(0:ℕ)) (by constructor <;> omega)
  let z := C.symm (subquotientClass _ (boundaries background X (1+t-(t-(0:ℕ))) (s,t)) ⟨x,hx⟩)
  refine ⟨z,(finite_target_label_iff X (page-1) (by omega) s t 0 (by omega) ⟨x,hx⟩ z).mpr ?_⟩
  exact C.apply_symm_apply _

private theorem level_zero_projected_weight_heq (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (s t w w' : ℤ) (hw : w=w') (hwt : w≤t) (hw't : w'≤t)
    (x : Ambient background X (s,t)) :
    HEq ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
      2 (s,t,w) (nuWeightLabel background X s t w hwt x))
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s,t,w') (nuWeightLabel background X s t w' hw't x)) := by
  subst w'
  rfl

private theorem level_finite_target_zero_heq (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (m s t : ℤ)
    (hm : (normalizedExponent background.classicalTower f : ℤ)≤m)
    (y : Ambient background Y (s+m,t+m)) :
    HEq (levelFiniteTargetLabel X Y f q 0 m s t hm y)
      (finiteTargetForExtension background X Y f q m s t hm y) := by
  have h := finite_extension_target_weight_label X Y f q m s t hm y
  apply (regradeE2_heq _ _).trans
  exact (level_zero_projected_weight_heq Y q (s+m) (t+m)
    (t+normalizedExponent background.classicalTower f-(0:ℕ))
    (t+normalizedExponent background.classicalTower f) (by omega) (by omega) (by omega) y).trans
      ((heq_of_eq h).symm.trans (regradeE2_heq _ _))

/-- Preserve the actual zero-level finite extension, with the source label
calibrated by the native finite window and the selected quotient shift. -/
private def level_finite_extension_of_zero (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+m,t+m))
    (W : FiniteExtensionWitness background X Y f page m s t x y) :
    LevelFiniteExtensionWitness X Y f page 0 m s t x y := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let q := page-1
  have hq : 0<q := by dsimp [q]; have := W.page_ge_two; omega
  have he : e=0 ∨ e=1 := by
    have h := normalizedExponent_le_one background.classicalTower f
    dsimp [e]
    omega
  have hps : (s,(t-s)+s,t+e)=(s,(t-s)+s,t+e-(0:ℕ)) := by simp
  have hpt : (s+m,(t-s)+(s+m),t+e)=(s+m,(t-s)+(s+m),t+e-(0:ℕ)) := by simp
  let zS := (eqToHom (congrArg (fun i => ((background.family.obj
    ((SyntheticObject.quotient q (extensionSourceObject background X Y f)).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty) hps)) W.source
  let zT := (eqToHom (congrArg (fun i => ((background.family.obj
    ((SyntheticObject.quotient q (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty) hpt)) W.target
  have hsourceOld : HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e-(0:ℕ))
      (regradeE2 (by simp) (finiteNuLabel background X q e s t 0 x)) zS := by
    have H := representative_transport hps _ _ W.source_rep
    simpa only [finiteSourceForExtension,normalized_regrade_trans,q,e,zS,
      extensionSourceObject] using H
  let z := Classical.choose (finite_witness_native_source_zero X Y f page m s t x y W)
  have hz := Classical.choose_spec (finite_witness_native_source_zero X Y f page m s t x y W)
  have hsourceEq := level_finite_source_zero_compatible X q hq e s t he x z hz zS hsourceOld
  have hsource : HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e-(0:ℕ))
      (levelFiniteSourceLabel X q e s t 0 x) zS := by
    rw [←hsourceEq]
    exact level_finite_source_representative X q e s t 0 x z hz
  have htarget : HasInfinityRepresentative _ 2 (s+m,(t-s)+(s+m),t+e-(0:ℕ))
      (levelFiniteTargetLabel X Y f q 0 m s t W.length_lower y) zT := by
    have H := representative_transport hpt _ _ W.target_rep
    have hlabel : regradeE2 hpt (finiteTargetForExtension background X Y f q m s t W.length_lower y) =
        levelFiniteTargetLabel X Y f q 0 m s t W.length_lower y :=
      eq_of_heq ((regradeE2_heq _ _).trans
        (level_finite_target_zero_heq X Y f q m s t W.length_lower y).symm)
    rw [hlabel] at H
    exact H
  refine ⟨W.page_ge_two,W.length_lower,W.length_upper,zS,zT,hsource,htarget,?_⟩
  exact left_extension_heq (.quotient q (extensionSourceObject background X Y f))
    (.quotient q (.nu Y)) (finiteExtensionMap background X Y f q)
    (t-s,t+e) (t-s,t+e-(0:ℕ)) (by simp) s m W.source zS W.target zT
    (eqToHom_apply_heq _ W.source).symm (eqToHom_apply_heq _ W.target).symm W.equation

end
end KIP126.ProofTools.Internal.Leibniz
