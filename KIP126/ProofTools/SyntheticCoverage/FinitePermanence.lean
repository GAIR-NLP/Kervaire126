module

public import KIP126.ProofTools.SyntheticCoverage.Permanence

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.Permanence

/-! Finite source ambiguity for the higher-layer permanence arguments,
using the representatives, quotient maps, and filtrations of the fixed background.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- The actual first-quotient kernel lies one filtration above the initial
source degree. This assertion concerns every finite representative. -/
private theorem finite_first_kernel_filtration
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 2 ≤ q) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : a ≫ (background.quotients.tower _).rho 1 q (by omega) = 0) :
    FiltrationAtLeast background.syntheticTower (s+1) a := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle (show 0<1 by decide) (show 1<q by omega)
  have hz : a ≫ T.rho = 0 := by
    simpa only [T,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  change BiHom (t-s) t
    ((SyntheticCategory.biShift (0,-(1:ℤ))).obj (XModLambdaN A (q-1))) at e
  have heF := KIP126.ProofTools.Internal.Leibniz.shifted_quotient_bottom_filtration
    X (q-1) (by omega) (-1) (t-s) t e
  have heP : FiltrationAtLeast background.syntheticTower (s+1) e := by
    convert heF using 1; omega
  have haP := map_preserves_filtration (background.convergentMap
    (.shift (0,-1) (.quotient (q-1) (.nu X))) (.quotient q (.nu X)) T.lambdaMap)
      (t-s,t) (s+1) e heP
  change FiltrationAtLeast background.syntheticTower (s+1) (e ≫ T.lambdaMap) at haP
  change a = e ≫ T.lambdaMap at he
  rw [←he] at haP
  exact haP

/-- Vanishing of the intermediate E₃ groups moves every first-layer error
of the specified representative to the final finite layer. -/
private theorem finite_first_kernel_top_filtration_of_third_page_vanishes
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 2 ≤ q) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ q-2 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : a ≫ (background.quotients.tower _).rho 1 q (by omega) = 0) :
    FiltrationAtLeast background.syntheticTower (s+q-1) a := by
  have hfirst := finite_first_kernel_filtration X q hq s t a ha
  have hcollapse : FiltrationAtLeast background.syntheticTower (s+1) a ↔
      FiltrationAtLeast background.syntheticTower (s+q-1) a := by
    apply filtration_iff_of_infinity_zero (background.convergence (.quotient q (.nu X)))
      (s+1) (s+q-1) (t-s) t (by omega)
    intro k hk hk'
    let j := (k-s).toNat
    have hj : (j:ℤ)=k-s := by dsimp [j]; omega
    have hj1 : 1 ≤ j := by omega
    have hjq : j ≤ q-2 := by omega
    letI := hmid j hj1 hjq
    have hzero := finite_infinity_zero_of_cycles_le_boundaries X q (by omega)
      (s+j) (t+j) t (by omega) (by
        convert middle_boundaries_of_third_page_vanishes X (s+j,t+j) q j hj1 hjq
          using 1 <;> congr 1 <;> omega)
    have hks : s+(j:ℤ)=k := by omega
    have hkt : t+(j:ℤ)=t-s+k := by omega
    simpa only [hks,hkt,SyntheticAdamsFamily.quotient,SyntheticObject.obj] using hzero
  exact hcollapse.mp hfirst

/-- The entire source error is a single actual last-layer E2 label once all
intermediate E3 groups vanish. -/
private theorem finite_first_kernel_is_top_label_of_third_page_vanishes
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0 < d) (p t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3
        (p-d+j,t-d+j)))
    (a : BiHom (t-p) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (ha : a ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) = 0) :
    ∃ e : Ambient background X (p,t), a = finiteTopLabel X d hd p t e := by
  let a' : BiHom ((t-d)-(p-d)) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)) :=
    homotopyRegrade (by omega) rfl a
  have hfirst : a' ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) = 0 := by
    dsimp only [a']
    rw [←regrade_comp,ha]
    exact regrade_zero _ _
  have htop := finite_first_kernel_top_filtration_of_third_page_vanishes X (d+1)
    (by omega) (p-d) (t-d) (by
      intro j hj hjd
      exact hmid j hj (by omega)) a' hfirst
  have htop' : FiltrationAtLeast background.syntheticTower p a := by
    have hp : p-d+(d+1:ℕ)-1=p := by omega
    rw [hp] at htop
    exact (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff _ _ p a).mp htop
  exact finiteTopLabel_exists X d hd p t a htop'

/-- Multiplication of the specified complete class by lambda^d gives the
actual final-layer class of its first label in Q_(d+1). -/
private theorem lambda_power_first_label_projection_eq_top
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0 < d) (p t : ℤ)
    (b : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (w : Ambient background X (p,t))
    (hb : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X p t w) :
    lambdaMultiply d b ≫ XModLambdaN.incl _ (d+1) =
      finiteTopLabel X d hd p t w := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have cast_incl (n : ℕ) (hn : n=1) :
      oneQuotientCast A n hn (t-p) t (b ≫ XModLambdaN.incl A 1) =
        b ≫ XModLambdaN.incl A n := by
    subst n
    rfl
  unfold finiteTopLabel
  rw [finiteTopOfFirst_eq_raw,←hb,cast_incl]
  exact (finite_lambda_inclusion X (d+1) d hd (by omega) p t b).symm

/-- The higher-layer analogue of the two-layer error formula. The source
error ranges over the whole last E2 group; the final discrepancy is a true
boundary through d_(d+1), which is B_<d+2 in the source document. -/
private theorem ordinary_finite_error_is_boundary_of_third_page_vanishes
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0 < d) (p t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3
        (p-d+j,t-d+j)))
    (a : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (b : BiHom (t-p) t (background.nu.functor.obj (Y.obj background.auxiliary)))
    (w v : Ambient background Y (p,t))
    (hsame : a ≫ XModLambdaN.incl _ 1 =
      c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      finiteTopLabel Y d hd p t v)
    (hb : lambdaMultiply d b = a ≫ background.nu.functor.map f)
    (hw : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y p t w) :
    ∃ e : Ambient background X (p,t),
      w-v-(background.classical.map f).pageMap 2 (p,t) e ∈
        boundaries background Y (d+1) (p,t) := by
  have hz : (a ≫ XModLambdaN.incl _ (d+1)-c) ≫
      (background.quotients.tower _).rho 1 (d+1) (by omega) = 0 := by
    rw [Preadditive.sub_comp,Category.assoc,
      (background.quotients.tower _).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := finite_first_kernel_is_top_label_of_third_page_vanishes X d hd p t hmid
    (a ≫ XModLambdaN.incl _ (d+1)-c) hz
  have himage :
      (a ≫ XModLambdaN.incl _ (d+1)-c) ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      finiteTopLabel Y d hd p t ((background.classical.map f).pageMap 2 (p,t) e) := by
    rw [he,finite_top_label_ordinary_natural]
  have ht := lambda_power_first_label_projection_eq_top Y d hd p t b w hw
  rw [hb] at ht
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,
    ←Category.assoc,ht,hc] at himage
  refine ⟨e,(finite_top_difference_zero_iff_boundary Y d hd p t w v
    ((background.classical.map f).pageMap 2 (p,t) e)).mp ?_⟩
  exact sub_eq_zero.mpr himage

/-- Exactness at the specified full image, in arbitrary lambda degree. -/
private theorem full_image_lambda_power_preimage_native
    {A B : SyntheticSpectrum} (g : A ⟶ B) (d : ℕ) (m t : ℤ)
    (a : BiHom m (t-d) A) (hz : (a ≫ g) ≫ XModLambdaN.incl B d = 0) :
    ∃ b : BiHom m t B, lambdaMultiply d b = a ≫ g := by
  obtain ⟨b₀,hb₀⟩ := (XModLambdaN.cofiberTriangle B d).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished B d) (a ≫ g) hz
  change a ≫ g = b₀ ≫ lambdaPow d B at hb₀
  let δ : ℤ × ℤ := (0,-(d:ℤ))
  let p : ℤ × ℤ := (m,t)
  let b₁ : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj B) :=
    homotopyRegrade (by simp [p,δ]) (by dsimp [p,δ]; omega) b₀
  let b : BiHom m t B := (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ b₁)
  have hb : shiftHomotopyClass δ p b = b₁ := by
    simp [b,shiftHomotopyClass]
  refine ⟨b,?_⟩
  rw [KIP126.ProofTools.Internal.FiniteLifting.lambda_multiply_raw m t d b]
  rw [show shiftHomotopyClass (0,-(d:ℤ)) (m,t) b = b₁ from hb]
  dsimp only [b₁]
  rw [regrade_comp,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
  simpa only [homotopyRegrade] using hb₀.symm

/-- The first label of the complete lambda^d preimage detects the realization
of the very same full image; zero output is allowed. -/
private theorem full_image_lambda_power_first_label_detects
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticSpectrum) (Y : (AdamsObject (coefficients := background.coefficients)))
    (g : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) (d : ℕ) (s t : ℤ)
    (a : BiHom (t-s) (t-d) A)
    (hz : (a ≫ g) ≫ XModLambdaN.incl _ d = 0) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary)),
      lambdaMultiply d b = a ≫ g ∧
      ∃ w : Ambient background Y (s,t),
        b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y s t w ∧
        w ∈ permanentCycles background Y (s,t) ∧
        ClassicalDetects (background.classicalConvergence Y) (s,t) w
          ((R.sphere (t-s) (t-d)).hom ≫ background.recovery.realization.map (a ≫ g) ≫
            (hcomp.nu Y).target.hom) := by
  obtain ⟨b,hb⟩ := full_image_lambda_power_preimage_native g d (t-s) t a hz
  obtain ⟨w,hw,hp,hclass⟩ := full_representative_first_label_detects R hcomp Y s t b
  refine ⟨b,hb,w,hw,hp,?_⟩
  have he := KIP126.ProofTools.Internal.FiniteLifting.realization_lambda_multiply R (t-s) t d b
  rw [hb] at he
  have he' : (R.sphere (t-s) (t-d)).hom ≫ background.recovery.realization.map (a ≫ g) ≫
      (hcomp.nu Y).target.hom =
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map b ≫
        (hcomp.nu Y).target.hom := by
    simpa only [Category.assoc] using congrArg (fun u => u ≫ (hcomp.nu Y).target.hom) he
  exact he'.symm ▸ hclass

private theorem finite_top_restriction_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    finiteTopLabel X d hd s t x ≫
      (background.quotients.tower _).rho d (d+1) (by omega) = 0 := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle hd (Nat.lt_succ_self d)
  unfold finiteTopLabel
  rw [finiteTopOfFirst_eq_raw,Category.assoc]
  have hz := comp_distTriang_mor_zero₁₂ _ T.distinguished
  change T.lambdaMap ≫ T.rho = 0 at hz
  rw [(background.quotients.tower A).triangle_rho] at hz
  rw [hz,comp_zero]

/-- The ordinary-arrow finite permanence comparison with complete
E3-vanishing hypotheses. The common finite representative
and the specified complete source are retained throughout. The common class
c and its two image equations are explicit hypotheses. -/
private theorem ordinary_finite_source_permanence_of_third_page_vanishes
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0 < d) (p t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3
        (p-d+j,t-d+j)))
    (a : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (v : Ambient background Y (p,t)) (P : Submodule ℤ (Ambient background Y (p,t)))
    (hP : permanentCycles background Y (p,t) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (p,t)).hom.range ⊓ P ≤
      finalBoundaries Y (p,t))
    (hsame : a ≫ XModLambdaN.incl _ 1 =
      c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      finiteTopLabel Y d hd p t v) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (p,t) v ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) v
        ((R.sphere (t-p) (t-d)).hom ≫
          background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
            (hcomp.nu Y).target.hom) := by
  have herr0 : (a ≫ XModLambdaN.incl _ (d+1)-c) ≫
      (background.quotients.tower _).rho 1 (d+1) (by omega) = 0 := by
    rw [Preadditive.sub_comp,Category.assoc,
      (background.quotients.tower _).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := finite_first_kernel_is_top_label_of_third_page_vanishes X d hd p t hmid
    (a ≫ XModLambdaN.incl _ (d+1)-c) herr0
  have himage :
      (a ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ (d+1) -
          finiteTopLabel Y d hd p t v =
      finiteTopLabel Y d hd p t ((background.classical.map f).pageMap 2 (p,t) e) := by
    have h := congrArg (fun u => u ≫ XModLambdaN.map (background.nu.functor.map f) (d+1)) he
    rw [finite_top_label_ordinary_natural,Preadditive.sub_comp,Category.assoc,
      ←XModLambdaN.incl_naturality,←Category.assoc,hc] at h
    exact h
  have hz : (a ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ d = 0 := by
    have h := congrArg (fun u => u ≫ (background.quotients.tower
      (background.nu.functor.obj (Y.obj background.auxiliary))).rho d (d+1) (by omega)) himage
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero,finite_top_restriction_zero,sub_zero] at h
    exact h
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp
    (background.nu.functor.obj (X.obj background.auxiliary)) Y (background.nu.functor.map f) d p t a hz
  obtain ⟨e,herr⟩ := ordinary_finite_error_is_boundary_of_third_page_vanishes X Y f
    d hd p t hmid a c b w v hsame hc hb hw
  exact classical_detects_of_terminal_image X Y (p,t) (p,t)
    ((background.classical.map f).pageMap 2 (p,t)).hom P hP hterminal w v hwp hv e (d+1)
      herr _ hdet

/-- Every classical source strictly detected by x has the specified target
class under the ordinary arrow, once the same common finite c is supplied.
The complete lift is constructed with its realization equal to that source. -/
private theorem ordinary_finite_permanence_of_common_lift
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (x : Ambient background X (s,t)) (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (v : Ambient background Y (s+d,t+d))
    (P : Submodule ℤ (Ambient background Y (s+d,t+d)))
    (hP : permanentCycles background Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries Y (s+d,t+d))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) =
      nativeFirstLabel X s t x)
    (himage : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      homotopyRegrade (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
        (finiteTopLabel Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ClassicalDetects (background.classicalConvergence Y) (s+d,t+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫ a ≫ f) := by
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp X s t x a hx ha
  let b' : BiHom ((t+d)-(s+d)) ((t+d)-d)
      (background.nu.functor.obj (X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) b
  let c' : BiHom ((t+d)-(s+d)) ((t+d)-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)) :=
    homotopyRegrade (by omega) (by omega) c
  have hsame : b' ≫ XModLambdaN.incl _ 1 =
      c' ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) := by
    dsimp only [b',c']
    rw [←regrade_comp,←regrade_comp,hb,hfirst]
  have hc : c' ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      finiteTopLabel Y d hd (s+d) (t+d) v := by
    dsimp only [c']
    rw [←regrade_comp,himage,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  obtain ⟨hp,hdet⟩ := ordinary_finite_source_permanence_of_third_page_vanishes
    R hcomp X Y f d hd (s+d) (t+d) (by
      intro j hj hjd
      simpa only [add_sub_cancel_right] using hmid j hj hjd)
    b' c' v P hP hv hterminal hsame hc
  refine ⟨hp,?_⟩
  have hreal' : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
      (b ≫ background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom = a ≫ f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target X]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ f) hreal
  have htransport := realization_homotopy_regrade_full R
    (show t-s=(t+d)-(s+d) by omega) (show t=(t+d)-d by omega)
      (b ≫ background.nu.functor.map f)
  have ht := congrArg (fun z => z ≫ (hcomp.nu Y).target.hom) htransport
  simp only [Category.assoc] at ht
  rw [hreal'] at ht
  have hreal'' : (R.sphere ((t+d)-(s+d)) ((t+d)-d)).hom ≫
      background.recovery.realization.map (b' ≫ background.nu.functor.map f) ≫
        (hcomp.nu Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+d)-(s+d)=t-s by omega)) ≫ a ≫ f := by
    simpa only [b',regrade_comp] using ht
  exact hreal'' ▸ hdet

/-- Coordinate-independent target version of the preceding fixed-source comparison. -/
private theorem ordinary_finite_permanence_of_common_lift_at
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (p u : ℤ) (hp : p=s+d) (hu : u=t+d)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (x : Ambient background X (s,t)) (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (v : Ambient background Y (p,u))
    (P : Submodule ℤ (Ambient background Y (p,u)))
    (hP : permanentCycles background Y (p,u) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (p,u)).hom.range ⊓ P ≤
      finalBoundaries Y (p,u))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) =
      nativeFirstLabel X s t x)
    (himage : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      homotopyRegrade (show u-p=t-s by omega) (show u-d=t by omega)
        (finiteTopLabel Y d hd p u v)) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (p,u) v ∧
      ClassicalDetects (background.classicalConvergence Y) (p,u) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show u-p=t-s by omega)) ≫ a ≫ f) := by
  subst p
  subst u
  exact ordinary_finite_permanence_of_common_lift hcomp X Y f d hd s t hmid x a hx ha
    v P hP hv hterminal c hfirst himage

/-- Finite permanence in the positive-h normalization.
Here q+1 is both the finite quotient length and the bottom differential page.
Every intermediate E3 group vanishes, and every specified strict source is retained. -/
public theorem finite_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (_hs : 0 ≤ s)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (a : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s+1,t) x a)
    (_hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ q-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s+1+j,t+j)))
    (P : Submodule ℤ (Ambient background T.Y (s+q+1,t+q)))
    (hP : permanentCycles background T.Y (s+q+1,t+q) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+q+1,t+q)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+q+1,t+q)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+q+1,t+q) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+q+1,t+q) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+q)-(s+q+1)=t-(s+1) by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_lift_positive_h T (by simp [hf,hg,hh])
    hT hf hg hh q hq s t z x v hH hd
  exact ordinary_finite_permanence_of_common_lift_at hcomp T.X T.Y T.f q hq (s+1) t
    (s+q+1) (t+q) (by omega) rfl hmid x a hx ha v P hP hv hterminal c hfirst himage

/-- Finite permanence in the positive-g normalization.
Here q+1 is both the finite quotient length and the bottom differential page.
Every intermediate E3 group vanishes, and every specified strict source is retained. -/
public theorem finite_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (_hs : 0 ≤ s+1)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v))
    (a : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s+1,t) x a)
    (_hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ q-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s+1+j,t+j)))
    (P : Submodule ℤ (Ambient background T.Y (s+q+1,t+q)))
    (hP : permanentCycles background T.Y (s+q+1,t+q) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+q+1,t+q)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+q+1,t+q)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+q+1,t+q) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+q+1,t+q) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+q)-(s+q+1)=t-(s+1) by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_lift_positive_g T (by simp [hf,hg,hh])
    hT hf hg hh q hq s t z x v hH hd
  exact ordinary_finite_permanence_of_common_lift_at hcomp T.X T.Y T.f q hq (s+1) t
    (s+q+1) (t+q) (by omega) rfl hmid x a hx ha v P hP hv hterminal c hfirst himage

end
end KIP126.ProofTools.Internal.SyntheticCoverage
