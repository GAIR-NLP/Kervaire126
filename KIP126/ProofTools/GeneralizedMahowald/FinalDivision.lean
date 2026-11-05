module
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private theorem finite_filtered_target_label (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0<q) (s t w : ℤ) (hw : 0≤t-w ∧ t-w<q)
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : FiltrationAtLeast background.syntheticTower s b) :
    ∃ y : Ambient background X (s,t),
      y ∈ cycles background X (q-t+w) (s,t) ∧
      Detects (background.convergence (.quotient q (.nu X))) (s,t,w)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
          (nuWeightLabel background X s t w (by omega) y)) b := by
  obtain ⟨br,hbr⟩ := filtration_representative_exists background.syntheticTower _ (t-s,w) s b hb
  let e := ((background.convergence (.quotient q (.nu X))).identification (s,t,w)).inv
    ((background.syntheticTower.filtration _).toAssociatedGraded s (t-s,w) br)
  obtain ⟨y,hy⟩ := CrossingLabels.subquotient_rep
    (cycles background X (q-t+w) (s,t)) (boundaries background X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw e)
  refine ⟨y.val,y.property,e,?_,br,hbr,?_⟩
  · exact (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw y.val e).mpr
      ⟨y.property,hy.symm⟩
  · exact ((background.convergence (.quotient q (.nu X))).identification (s,t,w)).toLinearEquiv.apply_symm_apply _

private def finiteWeightedLambdaClass (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
  homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
    (shiftHomotopyClass (0,-(k:ℤ)) (t-s,w) b) ≫
    ((background.quotients.tower _).triangle hk hkq).lambdaMap

private theorem finite_weighted_lambda_detects (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (hb : Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).pageMap 2 (s,t,w)
        (nuWeightLabel background X s t w (by omega) y)) b) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel background X s t (w-k) (by omega) y))
      (finiteWeightedLambdaClass X q k hk hkq s t w b) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.quotient (q-k) (.nu X))).obj background.nu background.auxiliary) ⟶
      ((SyntheticObject.quotient q (.nu X)).obj background.nu background.auxiliary) :=
    ((background.quotients.tower A).triangle hk hkq).lambdaMap
  have hs : (s,t,w)=(s,(t-s)+s,w) := by simp
  have hbStem := detects_transport hs _ _ hb
  have hm := shifted_map_detects (.quotient (q-k) (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ b hbStem
  have hp : (s,((t-s,w)+(0,-(k:ℤ))).1+s,((t-s,w)+(0,-(k:ℤ))).2) =
      (s,t,w-k) := by ext <;> simp [sub_eq_add_neg]
  have hm := detects_transport hp _ _ hm
  obtain ⟨e,he,br,hbr,hge⟩ := hm
  obtain ⟨e0,he0,_⟩ := hb
  have heMap := shifted_representative_map (.quotient (q-k) (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ _ (representative_transport hs _ _ he0)
  have heMap := representative_transport hp _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) w e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    rw [infinity_map_regrade L hp]
    rfl
  have hlabel : HasInfinityRepresentative _ 2 (s,t,w-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel background X s t (w-k) (by omega) y))
      (KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) w e0) := by
    obtain ⟨hy,hye⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X (q-k) (by omega)
      s t w hw y e0).mp he0
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
      s t (w-k) (by omega) y _).mpr
    have hy' : y ∈ cycles background X (q-t+(w-k)) (s,t) := by
      convert hy using 1
      congr 1
      omega
    refine ⟨hy',?_⟩
    rw [KIP126.Literature.Standard.eInfinity_lambda_finite X q k hkq (s,t) w hw,hye]
    rfl
  refine ⟨e,?_,br,?_,hge⟩
  · rw [heq']
    exact hlabel
  · convert hbr using 1
    simp only [finiteWeightedLambdaClass,regrade_precomp,Category.assoc]
    simp only [←Category.assoc,eqToHom_trans]
    rfl

private theorem finite_lambda_target_label_congruent (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (hb : FiltrationAtLeast background.syntheticTower s b)
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel background X s t (w-k) (by omega) y))
      (finiteWeightedLambdaClass X q k hk hkq s t w b)) :
    ∃ y' : Ambient background X (s,t),
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).pageMap 2 (s,t,w)
          (nuWeightLabel background X s t w (by omega) y')) b ∧
      y'-y ∈ boundaries background X (1+t-w+k) (s,t) := by
  obtain ⟨y',_,hy'⟩ := finite_filtered_target_label X (q-k) (by omega) s t w hw b hb
  have hl := finite_weighted_lambda_detects X q k hk hkq s t w hw y' b hy'
  refine ⟨y',hy',?_⟩
  have hc := finite_detected_labels_congruent X q (by omega) s t (w-k) (by omega)
    y' y _ hl ha
  convert hc using 1
  congr 1
  omega

private def finiteWeightedLambdaDivisionClass (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hkq : k<q) (s t w : ℤ)
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) := by
  by_cases hk : k=0
  · subst k
    exact homotopyRegrade rfl (by simp) b
  · exact finiteWeightedLambdaClass X q k (by omega) hkq s t w b

private theorem finite_lambda_target_label_congruent_uniform (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (hb : FiltrationAtLeast background.syntheticTower s b)
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel background X s t (w-k) (by omega) y))
      (finiteWeightedLambdaDivisionClass X q k hkq s t w b)) :
    ∃ y' : Ambient background X (s,t),
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).pageMap 2 (s,t,w)
          (nuWeightLabel background X s t w (by omega) y')) b ∧
      y'-y ∈ boundaries background X (1+t-w+k) (s,t) := by
  by_cases hk : k=0
  · subst k
    obtain ⟨y',_,hy'⟩ := finite_filtered_target_label X q hkq s t w hw b hb
    have hy : Detects (background.convergence (.quotient q (.nu X))) (s,t,w)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
          (nuWeightLabel background X s t w (by omega) y)) b := by
      have hp : (s,t,w-(0:ℕ))=(s,t,w) := by simp
      have ht := detects_transport hp _ _ ha
      convert ht using 1
      · have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
            (h : (s,t,v)=(s,t,v')) :
            regradeE2 h
              ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,v)
                (nuWeightLabel background X s t v hv₁ y)) =
              ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,v')
                (nuWeightLabel background X s t v' hv₂ y)) := by subst v'; rfl
        exact (transport _ w (by simp) _ _ hp).symm
      · simp only [finiteWeightedLambdaDivisionClass,↓reduceDIte]
        have cancel (A : SyntheticSpectrum) (m v v' : ℤ) (hv : v=v') (hv' : v'=v)
            (c : BiHom m v A) :
            homotopyRegrade rfl hv' (homotopyRegrade rfl hv c)=c := by subst v'; rfl
        exact (cancel _ _ _ _ _ _ b).symm
    refine ⟨y',hy',?_⟩
    simpa only [Nat.cast_zero,add_zero] using
      finite_detected_labels_congruent X q hkq s t w hw y' y b hy' hy
  · exact finite_lambda_target_label_congruent X q k (by omega) hkq s t w hw y b hb
      (by simpa only [finiteWeightedLambdaDivisionClass,dif_neg hk] using ha)

/-- The final target and its boundary ambiguity for a divided source
in the required target filtration. The inputs are a strict finite f-image
and detection of its long-quotient lambda image. -/
private theorem final_f_division_target (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q k : ℕ) (hkq : k<q) (n s t : ℤ)
    (hn : (normalizedExponent background.classicalTower f : ℤ)≤n)
    (hw : n-normalizedExponent background.classicalTower f<(q-k:ℕ))
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (af : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((SyntheticObject.quotient (q-k) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary))
    (haf : Detects (background.convergence (.quotient (q-k) (extensionSourceObject background X Y f)))
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
      (finiteSourceForExtension background X Y f (q-k) s t x)
      (homotopyRegrade (by dsimp; omega) rfl af))
    (hfil : FiltrationAtLeast background.syntheticTower (s+n)
      (af≫finiteExtensionMap background X Y f (q-k)))
    (hMay : Detects (background.convergence (.quotient q (.nu Y)))
      (s+n,t+n,t+normalizedExponent background.classicalTower f-k)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap 2
        (s+n,t+n,t+normalizedExponent background.classicalTower f-k)
        (nuWeightLabel background Y (s+n) (t+n)
          (t+normalizedExponent background.classicalTower f-k) (by omega) y))
      (finiteWeightedLambdaDivisionClass Y q k hkq (s+n) (t+n)
        (t+normalizedExponent background.classicalTower f)
        (homotopyRegrade (by omega) rfl (af≫finiteExtensionMap background X Y f (q-k))))) :
    ∃ y' : Ambient background Y (s+n,t+n),
      y'-y∈boundaries background Y (1+n-normalizedExponent background.classicalTower f+k) (s+n,t+n) ∧
      ∃ (a : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
          ((SyntheticObject.quotient (q-k) (extensionSourceObject background X Y f)).obj background.nu background.auxiliary))
        (b : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
          (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (q-k))),
        Detects (background.convergence (.quotient (q-k) (extensionSourceObject background X Y f)))
          (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
          (finiteSourceForExtension background X Y f (q-k) s t x)
          (homotopyRegrade (by dsimp; omega) rfl a) ∧
        Detects (background.convergence (.quotient (q-k) (.nu Y)))
          (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
          (finiteTargetForExtension background X Y f (q-k) n s t hn y')
          (homotopyRegrade (by dsimp; omega) rfl b) ∧
        a≫finiteExtensionMap background X Y f (q-k)=b := by
  let b := af≫finiteExtensionMap background X Y f (q-k)
  let b' := homotopyRegrade (by omega : t-s=(t+n)-(s+n)) rfl b
  have hfil' : FiltrationAtLeast background.syntheticTower (s+n) b' := by
    exact (regrade_filtration_iff _ _ _ _).mpr hfil
  obtain ⟨y',hy',hcong⟩ := finite_lambda_target_label_congruent_uniform Y q k hkq
    (s+n) (t+n) (t+normalizedExponent background.classicalTower f) (by omega)
    y b' hfil' hMay
  refine ⟨y',?_,af,b,haf,?_,rfl⟩
  · convert hcong using 1
    congr 1
    omega
  · have hp : (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)=
        (s+n,t+n,t+normalizedExponent background.classicalTower f) := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · dsimp
          omega
        · rfl
    have ht := detects_transport hp.symm _ _ hy'
    have hl := finite_extension_target_weight_label X Y f (q-k) n s t hn y'
    have hregrade {E : SyntheticAdamsSS} {p p' : Tridegree} (h : p=p') (z : E.E₂ p) :
        regradeE2 h.symm (regradeE2 h z)=z := by subst p'; rfl
    rw [←hl,hregrade] at ht
    convert ht using 1
    dsimp only [b']
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]

private theorem finite_lambda_inclusion (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) :
    finiteLambdaClass X q k hk hkq s t (a≫XModLambdaN.incl _ (q-k)) =
      lambdaMultiply k a≫XModLambdaN.incl _ q := by
  simp only [finiteLambdaClass,regrade_precomp,shiftHomotopyClass,Functor.map_comp,
    lambdaMultiply,Category.assoc]
  rw [((background.quotients.tower _).triangle hk hkq).lambda_quotient,
    ←Category.assoc ((SyntheticCategory.biShift (0,-(k:ℤ))).map a),lambdaPow_naturality]
  simp only [←Category.assoc]

private theorem finite_lambda_add (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k))) :
    finiteLambdaClass X q k hk hkq s t (a+b)=
      finiteLambdaClass X q k hk hkq s t a+finiteLambdaClass X q k hk hkq s t b := by
  simp only [finiteLambdaClass,shiftHomotopyClass,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,regrade_precomp]

/-- Correct the divided source's first label by a boundary torsion lift,
preserving its strict lambda image. -/
private theorem finite_divided_source_exact_label (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x x0 : Ambient background X (s,t))
    (b0 : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (hb0 : b0≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
      firstLabel background X s t x0≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a≫XModLambdaN.incl _ 1=
      firstLabel background X s t (x-x0)≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (haz : lambdaMultiply k a=0) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)),
      b≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (q-k) s t 0 x)) b ∧
      finiteLambdaClass X q k hk hkq s t b=finiteLambdaClass X q k hk hkq s t b0 := by
  let b := b0+a≫XModLambdaN.incl _ (q-k)
  have hfirst : b≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
      firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    dsimp only [b]
    rw [Preadditive.add_comp,hb0,Category.assoc,(background.quotients.tower _).rho_quotient,ha,
      firstLabel_sub,Preadditive.sub_comp]
    abel
  refine ⟨b,hfirst,first_label_detects_unshifted X (q-k) (by omega) s t x b hfirst,?_⟩
  dsimp only [b]
  rw [finite_lambda_add,finite_lambda_inclusion,haz,zero_comp,add_zero]

/-- Positive finite lambda division with the prescribed exact source label.
The boundary ambiguity of an arbitrary preimage is corrected by a torsion
representative, leaving its strict long-quotient lambda image unchanged. -/
private theorem finite_detected_source_division_exact (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background X s t (t-k) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)),
      b≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (q-k) s t 0 x)) b ∧
      finiteLambdaClass X q k hk hkq s t b=a := by
  obtain ⟨b0,hb0⟩ := finite_detected_source_division X q k hk hkq s t x a ha
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X (q-k) (by omega) s t b0
  have hb0' : finiteLambdaClass X q k hk hkq s t b0=a :=
    (finiteLambdaClass_vertical X q k hk hkq s t b0).trans hb0
  have hcong := finite_lambda_first_label_congruent X q k hk hkq s t x x0 b0 hx0 a ha hb0'
  obtain ⟨c,hc,hcz⟩ := cumulative_boundary_torsion_lift_unshifted X k s t (x-x0) hcong
  obtain ⟨b,hb,hbd,hbl⟩ := finite_divided_source_exact_label X q k hk hkq s t x x0 b0 hx0 c hc hcz
  exact ⟨b,hb,hbd,hbl.trans hb0'⟩

private theorem finite_detected_bottom_first (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0<q) (s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,t)
        (nuWeightLabel background X s t t (by omega) x)) a) :
    a≫(background.quotients.tower _).rho 1 q hq=
      firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X q hq s t a
  have hdet := first_label_detects_unshifted X q hq s t x0 a hx0
  rw [←zero_weight_label X q s t x0] at hdet
  have hc := finite_detected_labels_congruent X q hq s t t (by omega) x x0 a ha hdet
  have he : x=x0 := by simpa only [add_sub_cancel_right,boundaries_one,Submodule.mem_bot,sub_eq_zero] using hc
  simpa only [he] using hx0

private theorem finite_detected_source_division_exact_uniform (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel background X s t (t-k) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)),
      b≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (q-k) s t 0 x)) b ∧
      finiteLambdaDivisionClass X q k hkq s t b=a := by
  by_cases hk : k=0
  · subst k
    let b := homotopyRegrade rfl (by simp : t-(0:ℕ)=t) a
    have hp : (s,t,t-(0:ℕ))=(s,t,t) := by simp
    have ht := detects_transport hp _ _ ha
    have hbdet : Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,t)
          (nuWeightLabel background X s t t (by omega) x)) b := by
      convert ht using 1
      · have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
            (h : (s,t,v)=(s,t,v')) :
            regradeE2 h
              ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,v)
                (nuWeightLabel background X s t v hv₁ x)) =
              ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,v')
                (nuWeightLabel background X s t v' hv₂ x)) := by subst v'; rfl
        exact (transport _ t (by simp) _ _ hp).symm
    have hbfirst := finite_detected_bottom_first X q hkq s t x b hbdet
    refine ⟨b,hbfirst,first_label_detects_unshifted X q hkq s t x b hbfirst,?_⟩
    simp only [finiteLambdaDivisionClass,↓reduceDIte,b]
    have cancel (A : SyntheticSpectrum) (m v v' : ℤ) (hv : v=v') (hv' : v'=v)
        (c : BiHom m v A) :
        homotopyRegrade rfl hv' (homotopyRegrade rfl hv c)=c := by subst v'; rfl
    exact cancel _ _ _ _ _ _ a
  · obtain ⟨b,hb,hbd,hbl⟩ := finite_detected_source_division_exact X q k (by omega) hkq s t x a ha
    refine ⟨b,hb,hbd,?_⟩
    simpa only [finiteLambdaDivisionClass,dif_neg hk] using hbl

private theorem finite_target_source_division_exact (X : AdamsObject (coefficients := background.coefficients))
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k x) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)),
      b≫(background.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel background X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X (q-k) s t 0 x)) b ∧
      finiteLambdaDivisionClass X q k hkq s t b=a := by
  have hlabel : nuWeightLabel background X s t (t-k) (by omega) x =
      targetNuLabel background X s t k x := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel background X s t a x) = targetNuLabel background X s t b x := by
      subst b
      rfl
    exact transport _ k hk' _
  apply finite_detected_source_division_exact_uniform X q k hkq s t x a
  rw [hlabel]
  exact ha

end
end KIP126.ProofTools.Internal.Mahowald
