module

import all KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.TerminalComparison
import all KIP126.ProofTools.LastLayerComparison.Boundary
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival

/-! Specified finite heads for restricted source corrections.
The construction retains the given ordinary H₂ label and its genuine finite
cycle qualification, while annihilating its actual following finite map. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem selective_coefficient_insert_zero (A : SyntheticSpectrum)
    (k q : ℕ) (hq : 0<q) (m w : ℤ) : finiteCoefficientInsert A k q hq m w 0=0 := by
  have cast_zero {n n' : ℕ} (h : n=n') :
      (congrArg (fun v => BiHom m w (XModLambdaN A v)) h).mp
        (0 : BiHom m w (XModLambdaN A n))=0 := by subst n'; rfl
  unfold finiteCoefficientInsert
  change finiteCoefficientShiftClass A (k+q) k _ m w
    ((congrArg (fun v => BiHom m w (XModLambdaN A v))
      (show q=k+q-k by omega)).mp 0)=0
  rw [cast_zero (show q=k+q-k by omega)]
  have rz {A : SyntheticSpectrum} {m m' w w' : ℤ}
      (hm : m=m') (hw : w=w') : homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
    subst m'; subst w'; rfl
  by_cases hk : k=0
  · subst k
    simp only [finiteCoefficientShiftClass,dite_true,rz]
  · simp only [finiteCoefficientShiftClass,dif_neg hk,shiftHomotopyClass,
      Functor.map_zero,comp_zero,rz,zero_comp]

/-- A specified ordinary H₂ source in the positive-second-map branch
produces a native finite representative of its literal desuspended label.
The finite νf-image is zero by the actual horizontal quotient triangle. -/
private theorem selective_positive_g_native_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1))
    (hz : z ∈ cycles background T.Z q (s+1,t+1))
    (u : Ambient background T.X (s+1,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u)) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      Detects (background.convergence (.quotient (k+q) (.nu T.X))) (s+1,t,t-k)
        (finiteTargetLabel background T.X (k+q) (s+1) t k u) b ∧
      b≫XModLambdaN.map (background.nu.functor.map T.f) (k+q)=0 := by
  let N := normalizedTriangle background T he
  let EZ := normalizedThirdNegativeIso T he hg
  obtain ⟨z₀,hz₀⟩ := (KIP126.Literature.Standard.finite_lift_criterion T.Z q hq (s+1) (t+1) z).mp
    ((isCycle_iff_reaches background T.Z (q+1) (by omega) (s+1,t+1) z).mp
      ⟨by omega,by simpa only [add_sub_cancel_right] using hz⟩)
  let zN := z₀≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q
  have hzN : zN≫(background.quotients.tower (background.nu.functor.obj (T.Z.obj background.auxiliary))).rho 1 q hq=
      nativeFirstLabel T.Z (s+1) (t+1) z := by
    dsimp only [zN]
    erw [Category.assoc,←(background.quotients.natural (SyntheticCategory.biShift_zero.hom.app
      (background.nu.functor.obj (T.Z.obj background.auxiliary)))).rho_naturality (show 1≤q by omega),
      ←Category.assoc,hz₀]
    rfl
  let za := shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1) zN≫(levelQuotientShiftIso T.Z (-1) q).inv
  have hza : za≫(background.quotients.tower _).rho 1 q hq=
      shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
        (nativeFirstLabel T.Z (s+1) (t+1) z)≫(levelQuotientShiftIso T.Z (-1) 1).inv := by
    apply (cancel_mono (levelQuotientShiftIso T.Z (-1) 1).hom).mp
    rw [Category.assoc,quotient_shift_restriction_on_spheres T.Z (0,-1) 1 q
      (by decide) hq (levelQuotientShiftIso T.Z (-1) 1) (levelQuotientShiftIso T.Z (-1) q)
      (level_quotient_shift_incl T.Z (-1) 1) (level_quotient_shift_incl T.Z (-1) q)]
    dsimp only [za]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
    rw [←shift_hom_comp,hzN]
  let a : BiHom (t-s) t (XModLambdaN N.obj₃ q) :=
    homotopyRegrade (by dsimp;omega) (by dsimp;omega) (za≫XModLambdaN.map EZ.inv q)
  have ha : a≫(background.quotients.tower _).rho 1 q hq=
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z))≫
        (levelQuotientShiftIso T.Z (-1) 1).inv≫XModLambdaN.map EZ.inv 1 := by
    dsimp only [a]
    rw [←regrade_comp,Category.assoc,←(background.quotients.natural EZ.inv).rho_naturality hq,
      ←Category.assoc,hza]
    simp only [regrade_comp,Category.assoc]
  let d := a≫XModLambdaN.map N.mor₃ q
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) q
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (k+q)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  have hdet := (positive_g_may_source_at_level T he hf hg hh k q q hq le_rfl
    s t z u hu εq ε hεq hε a d ha (by
      rw [(background.quotients.tower _).rho_id,Category.comp_id])).2
  let b := finiteCoefficientInsert _ k q hq (t-s) t d
  refine ⟨positiveHSourceDesuspend T he hf (k+q) k s t ε b,hdet,?_⟩
  apply middle_raw_ordinary_image_zero_implies_native_zero T he hf (k+q) k (by omega) s t ε hε b
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ q≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ q≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  dsimp only [b]
  rw [finite_coefficient_insert_natural]
  have hd0 : d≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    dsimp only [d]
    rw [Category.assoc,hzero',comp_zero]
  rw [hd0,selective_coefficient_insert_zero]


/-- The positive finite map preserves the specified E₂ head, including
boundary heads, through the first-quotient shift comparison. -/
private theorem selective_positive_top_image
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (hεq : XModLambdaN.incl _ (d+1) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (d+1)))
    (x : Ambient background T.X (s,t)) :
    homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
      (show (t-d)+1=t+1-d by omega)
      (positiveFiniteImage T hf (d+1) εq (t-s) (t-d)
        (finiteTopLabel T.X d hd s t x)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists background.quotients.coherence (0,1) ((d+1)-d) A
  let b := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel T.X s t x)
  have htop : finiteTopLabel T.X d hd s t x =
      finiteLambdaClass T.X (d+1) d hd (Nat.lt_succ_self d) s t b :=
    finiteTopOfFirst_eq_raw A d hd (t-s) t _
  have hshift := shifted_finite_lambda_class_general T.X (0,1) (d+1) d hd
    (Nat.lt_succ_self d) s t εn εq hεn hεq b
  rw [←htop] at hshift
  let b₁ := oneQuotientUncast _ ((d+1)-d) (by omega) (t-s+0) (t+1)
    (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)
  have hshift' :
      homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
          (shiftHomotopyClass (0,1) (t-s,t-d) (finiteTopLabel T.X d hd s t x)) ≫ εq.inv =
        finiteTopOfFirst _ d hd (t-s+0) (t+1) b₁ := by
    exact hshift.trans (raw_eq_finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A)
      d hd (t-s+0) (t+1) (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv))
  let b₀ := homotopyRegrade (show t-s+0=t-s by omega) rfl b₁
  have hlabel : (background.firstQuotient T.X 1 s t) b₀=x := by
    have hb := KIP126.ProofTools.Internal.LastLayerComparison.shifted_first_label_uncast
      T.X ((d+1)-d) (by omega) s t x εn hεn
    change b₀=(background.firstQuotient T.X 1 s t).symm x at hb
    rw [hb,LinearEquiv.apply_symm_apply]
  have hi := congrArg (fun u => u ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) (d+1)) hshift'
  have hi' := congrArg (homotopyRegrade (show t-s+0=(t+1)-(s+1) by omega)
    (rfl : t+1-d=t+1-d)) hi
  have hb := normalized_first_map_top_eq T hf d hd s t b₀
  rw [hlabel,regrade_comp,←finiteTopOfFirst_regrade] at hb
  simp only [regrade_comp,last_layer_regrade_trans] at hi' hb
  simpa only [positiveFiniteImage,b₀,regrade_comp,last_layer_regrade_trans,Category.assoc] using
    hi'.trans hb

/-- Restriction commutes with the selected positive image for any two
inclusion-compatible quotient comparisons. -/
private theorem selective_positive_image_restriction
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (i N : ℕ) (hi : 0 < i) (hiN : i ≤ N)
    (εi : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) i ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) i))
    (εN : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hεi : XModLambdaN.incl _ i ≫ εi.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ i))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    positiveFiniteImage T hf N εN m w a ≫ (background.quotients.tower _).rho i N hiN =
      positiveFiniteImage T hf i εi m w (a ≫ (background.quotients.tower _).rho i N hiN) := by
  let a' := homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
    (shiftHomotopyClass (0,1) (m,w) a) ≫ εN.inv
  have hshift : a' ≫ (background.quotients.tower _).rho i N hiN =
      homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
        (shiftHomotopyClass (0,1) (m,w) (a ≫ (background.quotients.tower _).rho i N hiN)) ≫ εi.inv := by
    apply (cancel_mono εi.hom).mp
    have h := quotient_shift_restriction_on_spheres T.X (0,1) i N hi hiN
      εi εN hεi hεN m (w+1) a'
    simpa only [a',Category.assoc,Iso.inv_hom_id,Iso.inv_hom_id_assoc,Category.comp_id,
      shift_hom_comp,regrade_comp] using h
  change (a' ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) N) ≫
    (background.quotients.tower _).rho i N hiN = _
  rw [Category.assoc,←(background.quotients.natural (lastLayerNormalizedMap T hf)).rho_naturality hiN,
    ←Category.assoc,hshift]
  rfl

/-- Every actual quotient restriction retains the same finite target label. -/
private theorem selective_finite_target_restriction_detects
    (X : (AdamsObject (coefficients := background.coefficients))) (i N k : ℕ) (hiN : i ≤ N) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X N s t k x) a) :
    Detects (background.convergence (.quotient i (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X i s t k x)
      (a≫(background.quotients.tower _).rho i N hiN) := by
  let ρ := (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho
    i N hiN
  have hlabel : familyPageMap background.family ρ 2 (s,t,t-k)
      (finiteTargetLabel background X N s t k x)=finiteTargetLabel background X i s t k x := by
    unfold finiteTargetLabel
    change familyPageMap background.family ρ 2 (s,t,t-k)
      (familyPageMap background.family (XModLambdaN.incl _ N) 2 (s,t,t-k) _) = _
    rw [←ModuleCat.comp_apply,family_page_comp]
    rw [(background.quotients.tower _).rho_quotient]
    rfl
  have hdet := detects_map (.quotient N (.nu X)) (.quotient i (.nu X)) ρ
    (s,t,t-k) _ a ha
  erw [hlabel] at hdet
  exact hdet

/-- The positive normalized finite image detects the operation
on the specified source head. -/
private theorem selective_positive_image_detects
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (N k : ℕ) (hk : 0 < k) (hkN : k < N) (s t : ℤ)
    (εN : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (x : Ambient background T.X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : Detects (background.convergence (.quotient N (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel background T.X N s t k x) a) :
    Detects (background.convergence (.quotient N (.nu T.Y))) (s+1,t+1,(t+1)-k)
      (finiteTargetLabel background T.Y N (s+1) (t+1) k
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x))
      (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show (t-k)+1=(t+1)-k by omega)
        (positiveFiniteImage T hf N εN (t-s) (t-k) a)) := by
  have hdet := selective_finite_target_restriction_detects T.X (k+1) N k
    (by omega) s t x a ha
  have htop := finite_top_detection_unique T.X (k+1) (by omega) s t (t-k) (by omega)
    _ _ _ hdet (finiteTopLabel_detects T.X k hk s t x)
  let εi := levelQuotientShiftIso T.X 1 (k+1)
  have hεi := level_quotient_shift_incl T.X 1 (k+1)
  apply finite_target_rho_detects T.Y (k+1) N k (by omega) (by omega) (s+1) (t+1)
    _ (finiteTopLabel T.Y k hk (s+1) (t+1) _) (finiteTopLabel_detects T.Y k hk (s+1) (t+1) _)
  rw [←regrade_comp,selective_positive_image_restriction T hf (k+1) N (by omega)
    (by omega) εi εN hεi hεN,htop]
  exact selective_positive_top_image T hf k hk s t εi hεi x


/-- Zero in the suspended raw image reflects to the actual positive image.
The comparison's sphere automorphism is retained until zero is reflected. -/
private theorem selective_raw_positive_image_zero_implies_native_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N k : ℕ) (hN : 0<N) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (hεp : XModLambdaN.incl _ N ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s+1) (t-k+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (hz : a≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N=0) :
    positiveFiniteImage T hf N εp (t-s) (t-k)
      (rawMaySourceDesuspend T he hf N k s t ε a)=0 := by
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  obtain ⟨v,hv⟩ := native_positive_image_up_to_sphere T he hf N k hN s t ε εp hε hεp ey hey a
  rw [←Category.assoc,hz,zero_comp] at hv
  have hs : ordinarySuspendedRepresentative _ (t-s+1) (t-k+1)
      (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
        (positiveFiniteImage T hf N εp (t-s) (t-k)
          (rawMaySourceDesuspend T he hf N k s t ε a)))=0 := by
    apply (cancel_epi v.hom).mp
    simpa only [comp_zero] using hv.symm
  rw [ordinary_suspended_eq_source_iso] at hs
  have hm : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
        (positiveFiniteImage T hf N εp (t-s) (t-k)
          (rawMaySourceDesuspend T he hf N k s t ε a)))=0 := by
    apply (cancel_epi (ordinarySphereIso (t-s+1) (t-k+1)).hom).mp
    simpa only [comp_zero] using hs
  have hr : homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
      (positiveFiniteImage T hf N εp (t-s) (t-k)
        (rawMaySourceDesuspend T he hf N k s t ε a))=0 := by
    apply (shiftFunctor SyntheticSpectrum (1:ℤ)).map_injective
    simpa only [Functor.map_zero] using hm
  exact (ordinary_regrade_zero_iff (show t-s=(t-s+1)-1 by omega) rfl _).mp hr

/-- In the positive-first-map branch a given ordinary H₂ cycle supplies a
native finite representative of its literal desuspension, killed by the
same selected positive finite image. -/
private theorem selective_positive_f_native_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q : ℕ) (hq : 0<q) (s t : ℤ)
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (k+q) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (hεp : XModLambdaN.incl _ (k+q) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (k+q)))
    (z : Ambient background T.Z (s,t+1))
    (hz : z ∈ cycles background T.Z q (s,t+1))
    (u : Ambient background T.X (s,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using u)) :
    ∃ b : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      Detects (background.convergence (.quotient (k+q) (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel background T.X (k+q) s t k u) b ∧
      positiveFiniteImage T hf (k+q) εp (t-s) (t-k) b=0 := by
  let N := normalizedTriangle background T he
  let EZ := normalizedThirdZeroIso T he hg
  obtain ⟨z₀,hz₀⟩ := (KIP126.Literature.Standard.finite_lift_criterion T.Z q hq s (t+1) z).mp
    ((isCycle_iff_reaches background T.Z (q+1) (by omega) (s,t+1) z).mp
      ⟨by omega,by simpa only [add_sub_cancel_right] using hz⟩)
  let zN := z₀≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q
  have hzN : zN≫(background.quotients.tower (background.nu.functor.obj (T.Z.obj background.auxiliary))).rho 1 q hq=
      nativeFirstLabel T.Z s (t+1) z := by
    dsimp only [zN]
    erw [Category.assoc,←(background.quotients.natural (SyntheticCategory.biShift_zero.hom.app
      (background.nu.functor.obj (T.Z.obj background.auxiliary)))).rho_naturality (show 1≤q by omega),
      ←Category.assoc,hz₀]
    rfl
  let b := zN≫XModLambdaN.map EZ.inv q
  have hb : b≫(background.quotients.tower N.obj₃).rho 1 q hq=
      nativeFirstLabel T.Z s (t+1) z≫XModLambdaN.map EZ.inv 1 := by
    dsimp only [b]
    rw [Category.assoc,←(background.quotients.natural EZ.inv).rho_naturality hq,
      ←Category.assoc,hzN]
  let a₀ := b≫XModLambdaN.map N.mor₃ q
  have hdet₀ := (finite_may_source_detects T he hf hg hh q q hq le_rfl s (t+1) z b a₀ hb
    (by rw [(background.quotients.tower _).rho_id,Category.comp_id])).1
  let a := homotopyRegrade (show (t+1)-s=t-s+1 by omega)
    (show (t+1)-k=t-k+1 by omega)
    (finiteCoefficientInsert _ k q hq ((t+1)-s) (t+1) a₀)
  have hdetSigma : Detects (background.convergence (.quotient (k+q) (.nu (.shift 1 T.X))))
      (s,t+1,t+1-k) (finiteTargetLabel background (.shift 1 T.X) (k+q) s (t+1) k
        ((background.classical.map T.h).pageMap 2 (s,t+1) z))
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a≫XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (k+q))) := by
    have h := finite_coefficient_insert_detects (.shift 1 T.X) k q hq s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z)
      (a₀≫XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom q) hdet₀
    rw [←finite_coefficient_insert_natural] at h
    simpa only [a,regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp] using h
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (k+q)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  refine ⟨rawMaySourceDesuspend T he hf (k+q) k s t ε a,
    raw_may_source_desuspend_detects T he hf (k+q) k (by omega) s t ε hε u _ hu a hdetSigma,?_⟩
  apply selective_raw_positive_image_zero_implies_native_zero T he hf (k+q) k (by omega)
    s t ε εp hε hεp a
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ q≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ q≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  have ha₀zero : a₀≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    dsimp only [a₀]
    rw [Category.assoc,hzero',comp_zero]
  dsimp only [a]
  rw [←regrade_comp,finite_coefficient_insert_natural,ha₀zero,selective_coefficient_insert_zero]
  exact last_layer_regrade_zero _ _

end
end KIP126.ProofTools.Internal.SyntheticCoverage
