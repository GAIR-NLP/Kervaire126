module
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyInput
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative

/-! The actual positive-H last layer in the ordinary-first-arrow branch. -/
@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- The fixed positive first-quotient operation controls an arbitrary
actual positive normalized map; it need not be the triangle's first arrow. -/
private theorem positive_map_top_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (hH : ∀ x : Ambient background X (s,t), positiveFirstQuotientOperation X Y F s t x ∈
      boundaries background Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) 1)) :
    finiteTopOfFirst _ d hd (t-s) (t+1) a≫XModLambdaN.map F (d+1)=0 := by
  let x := (background.firstQuotient X 1 s t) a
  have hfirst := (positive_first_quotient_native_label X Y F s t x).symm
  dsimp only [x] at hfirst
  rw [LinearEquiv.symm_apply_apply] at hfirst
  rw [finiteTopOfFirst_natural]
  have hh := congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1)) hfirst
  rw [←finiteTopOfFirst_regrade] at hh
  have hzero := (finiteTopLabel_zero_iff_boundary Y d hd (s+1) (t+1) _).mpr (hH x)
  change _=finiteTopLabel Y d hd (s+1) (t+1) _ at hh
  rw [hzero] at hh
  have hh' := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (rfl : t+1-d=t+1-d)) hh
  simpa only [homotopy_regrade_inverse,last_layer_regrade_zero] using hh'

private theorem positive_map_last_layer_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (d+1)≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (hεq : XModLambdaN.incl _ (d+1)≫εq.hom=(SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (d+1)))
    (hH : ∀ x : Ambient background X (s,t), positiveFirstQuotientOperation X Y F s t x ∈
      boundaries background Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    (homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,1) (t-s,t-d) a)≫εq.inv)≫XModLambdaN.map F (d+1)=0 := by
  obtain ⟨x,rfl⟩ := finiteTopLabel_exists X d hd s t a ha
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists background.quotients.coherence (0,1) ((d+1)-d) A
  let b := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel X s t x)
  have htop : finiteTopLabel X d hd s t x=
      finiteLambdaClass X (d+1) d hd (Nat.lt_succ_self d) s t b :=
    finiteTopOfFirst_eq_raw A d hd (t-s) t _
  have hshift := shifted_finite_lambda_class_general X (0,1) (d+1) d hd
    (Nat.lt_succ_self d) s t εn εq hεn hεq b
  rw [←htop] at hshift
  have hshift' :
      homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
          (shiftHomotopyClass (0,1) (t-s,t-d) (finiteTopLabel X d hd s t x))≫εq.inv=
        finiteTopOfFirst _ d hd (t-s+0) (t+1)
          (oneQuotientUncast _ ((d+1)-d) (by omega) (t-s+0) (t+1)
            (shiftHomotopyClass (0,1) (t-s,t) b≫εn.inv)) := by
    exact hshift.trans (raw_eq_finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A) d hd
      (t-s+0) (t+1) (shiftHomotopyClass (0,1) (t-s,t) b≫εn.inv))
  rw [hshift']
  have hz := positive_map_top_zero X Y F d hd s t hH
  have transport (m m' : ℤ) (hm : m=m')
      (h : ∀ (b : BiHom m (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1)),
        finiteTopOfFirst _ d hd m (t+1) b≫XModLambdaN.map F (d+1)=0) :
      ∀ (b : BiHom m' (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1)),
        finiteTopOfFirst _ d hd m' (t+1) b≫XModLambdaN.map F (d+1)=0 := by
    subst m'
    exact h
  exact transport (t-s) (t-s+0) (by omega) hz _

/-- Positive shifting reflects vanishing of the actual negative-lift
image. The finite comparison is used only on the specified sphere class. -/
private theorem negative_lift_last_layer_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (hH : ∀ x : Ambient background X (s,t), positiveFirstQuotientOperation X Y F s t x ∈
      boundaries background Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    a≫XModLambdaN.map (negativeLift 1 F) (d+1)=0 := by
  let E := levelQuotientShiftIso X 1 (d+1)
  let D := levelQuotientShiftIso Y (-1) (d+1)
  let P := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let b := homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
    (shiftHomotopyClass (0,1) (t-s,t-d) a)≫E.inv
  have hb : b≫XModLambdaN.map F (d+1)=0 :=
    positive_map_last_layer_zero X Y F d hd s t E (level_quotient_shift_incl X 1 (d+1)) hH a ha
  have hp := positive_shift_negative_lift_quotient X Y F (d+1) (by omega) (t-s+0) (t+1-d) b
  rw [hb] at hp
  dsimp only [b] at hp
  simp only [E,Category.assoc,Iso.inv_hom_id_assoc] at hp
  apply (cancel_mono D.hom).mp
  rw [zero_comp]
  apply shift_class_injective (.shift (0,-1) (.quotient (d+1) (.nu Y))) (0,1) (t-s,t-d)
  apply (cancel_mono (shiftNegativePositiveUnit.hom.app
    (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (d+1)))).mp
  simp only [shiftHomotopyClass,Functor.map_zero,comp_zero,zero_comp]
  have hp' := congrArg (homotopyRegrade (rfl : t-s+0=t-s+0)
    (show t+1-d=(t-d)+1 by omega)) hp.symm
  simpa only [regrade_comp,normalized_homotopy_regrade_trans,shiftHomotopyClass,
    Category.assoc,last_layer_regrade_zero,D,Functor.map_comp,top_target_regrade_self] using hp'


private theorem positive_h_native_last_layer_zero
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (hH : ∀ z : Ambient background T.Z (s,t),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z ∈
        boundaries background (.shift 1 T.X) (d+1) (s+1,t+1))
    (e : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) (d+1)))
    (hefil : FiltrationAtLeast background.syntheticTower s e) :
    e≫XModLambdaN.map (positiveHNativeRaw T hh) (d+1)=0 := by
  have hz := negative_lift_last_layer_zero T.Z (.shift 1 T.X) (positiveHMap T hh) d hd s t hH e hefil
  simp only [positiveHNativeRaw,background.quotients.functoriality.map_comp,←Category.assoc]
  rw [hz,zero_comp,zero_comp]

/-- The original positive-H whole-image boundary condition kills the
actual normalized connecting map on every class in the last finite layer.
The first and second normalized exponents are zero. -/
private theorem ordinary_positive_h_last_layer_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (a : ℕ) (ha : 2≤a) (P V : ℤ)
    (hH : ∀ z : Ambient background T.Z (P,V),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) P V z ∈
        boundaries background (.shift 1 T.X) a (P+1,V+1))
    (e : BiHom (V-P) (V-(a-1:ℕ)) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (hefil : FiltrationAtLeast background.syntheticTower P e) :
    e≫XModLambdaN.map ((normalizedThirdZeroIso T he hg).inv≫(normalizedTriangle background T he).mor₃) a=0 := by
  have hz : e≫XModLambdaN.map (positiveHNativeRaw T hh) a=0 := by
    cases a with
    | zero => omega
    | succ d => exact positive_h_native_last_layer_zero T hh d (by omega) P V hH e hefil
  let E := normalizedThirdZeroIso T he hg
  let D := normalizedSuspensionZeroIso T he hf
  have hmap : (E.inv≫(normalizedTriangle background T he).mor₃)≫D.hom=positiveHNativeRaw T hh := by
    rw [Category.assoc,normalized_third_arrow_positive T he hf hg hh]
    simp only [E,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  apply (cancel_mono ((background.quotients.functoriality.functor a).mapIso D).hom).mp
  change (e≫XModLambdaN.map (E.inv≫(normalizedTriangle background T he).mor₃) a)≫XModLambdaN.map D.hom a=0≫_
  rw [zero_comp,Category.assoc,←background.quotients.functoriality.map_comp,hmap,hz]

/-- The same statement in the unshifted root-comparison coordinates. -/
private theorem ordinary_positive_h_terminal_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (a : ℕ) (ha : 2≤a) (s t : ℤ)
    (hH : ∀ z : Ambient background T.Z (s+a-1,t+a-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (s+a-1) (t+a-1) z ∈
        boundaries background (.shift 1 T.X) a ((s+a-1)+1,(t+a-1)+1))
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (hefil : FiltrationAtLeast background.syntheticTower (s+a-1) e) :
    e≫XModLambdaN.map ((normalizedThirdZeroIso T he hg).inv≫(normalizedTriangle background T he).mor₃) a=0 := by
  let e' := homotopyRegrade (show t-s=(t+a-1)-(s+a-1) by omega)
    (show t=(t+a-1)-(a-1:ℕ) by omega) e
  have hefil' : FiltrationAtLeast background.syntheticTower (s+a-1) e' :=
    (regrade_filtration_iff _ _ _ _).mpr hefil
  have hz := ordinary_positive_h_last_layer_zero T he hf hg hh a ha (s+a-1) (t+a-1) hH e' hefil'
  apply (last_layer_regrade_zero_iff (show t-s=(t+a-1)-(s+a-1) by omega)
    (show t=(t+a-1)-(a-1:ℕ) by omega) _).mp
  simpa only [e',regrade_comp] using hz

end
end KIP126.ProofTools.Internal.SyntheticCoverage
