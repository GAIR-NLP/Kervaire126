module

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.FinitePermanence
import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferential

/-! Coefficient extensions that retain the specified finite source and its
actual absolute boundary. These are the bottom construction for the
finite-source differential criterion, before the upper source division. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- Vanishing of the specified absolute boundary in Q_q extends the same
Q_L class. The full boundary of the new lift is retained in the lambda
identity, including the weight regrading. -/
private theorem finite_extension_of_boundary_projection_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (L q : ℕ) (hL : 0<L) (hq : 0<q)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) L))
    (ha : biSuspensionHomEquiv m w L (background.nu.functor.obj (X.obj background.auxiliary))
      (a ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ q = 0) :
    ∃ b : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (L+q)),
      b ≫ (background.quotients.tower _).rho L (L+q) (by omega) = a ∧
      biSuspensionHomEquiv m w L (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ L) =
        homotopyRegrade rfl (show (w+(L+q:ℕ))-q=w+L by omega)
          (lambdaMultiply q (biSuspensionHomEquiv m w ((L+q:ℕ):ℤ)
            (background.nu.functor.obj (X.obj background.auxiliary)) (b ≫ XModLambdaN.proj _ (L+q)))) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let D := (background.quotients.tower A).triangle hL (show L<L+q by omega)
  have hzero : a ≫ D.delta = 0 := by
    apply (biSuspensionHomEquiv m w L (XModLambdaN A (L+q-L))).injective
    rw [map_zero,cofiber_boundary_projection X L (L+q) hL (by omega) m w a]
    have hz (k : ℕ) (hk : k=q) :
        biSuspensionHomEquiv m w L (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ k = 0 := by
      subst k
      exact ha
    exact hz (L+q-L) (by omega)
  obtain ⟨b,hb⟩ := (Triangle.mk D.lambdaMap D.rho D.delta).coyoneda_exact₃
    D.distinguished a hzero
  change a = b ≫ D.rho at hb
  have hb' : b ≫ (background.quotients.tower A).rho L (L+q) (by omega) = a := by
    simpa only [D,(background.quotients.tower A).triangle_rho] using hb.symm
  refine ⟨b,hb',?_⟩
  have h := absolute_boundary_restriction X L (L+q) (by omega) m w b
  rw [hb'] at h
  have hcast (k : ℕ) (hk : k=q) (hw : (w+(L+q:ℕ))-k=w+L) :
      homotopyRegrade rfl hw
        (lambdaMultiply k (biSuspensionHomEquiv m w ((L+q:ℕ):ℤ) A
          (b ≫ XModLambdaN.proj _ (L+q)))) =
      homotopyRegrade rfl (show (w+(L+q:ℕ))-q=w+L by omega)
        (lambdaMultiply q (biSuspensionHomEquiv m w ((L+q:ℕ):ℤ) A
          (b ≫ XModLambdaN.proj _ (L+q)))) := by
    subst k
    rfl
  exact h.trans (hcast (L+q-L) (by omega) _)

/-- A top-layer formula for the boundary of a fixed finite source produces
an extension of that source and compares the first label of its actual
boundary with the prescribed top label. -/
private theorem finite_extension_of_boundary_top
    (X : (AdamsObject (coefficients := background.coefficients))) (L q : ℕ) (hL : 0<L) (hq : 0<q)
    (m t S W : ℤ) (hm : m-1=W-S) (hW : t+L+q=W)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) L))
    (v : Ambient background X (S,W))
    (htop : homotopyRegrade
        hm (show t+L=W-q by omega)
        (biSuspensionHomEquiv m t L (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabel X q hq S W v) :
    ∃ b : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (L+q)),
    ∃ w : Ambient background X (S,W),
      b ≫ (background.quotients.tower _).rho L (L+q) (by omega) = a ∧
      homotopyRegrade
          hm (show t+(L+q:ℕ)=W by omega)
          (biSuspensionHomEquiv m t ((L+q:ℕ):ℤ) (background.nu.functor.obj (X.obj background.auxiliary))
            (b ≫ XModLambdaN.proj _ (L+q))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel X S W w ∧
      w ∈ permanentCycles background X (S,W) ∧
      w-v ∈ boundaries background X (q+1) (S,W) := by
  let U := biSuspensionHomEquiv m t L (background.nu.functor.obj (X.obj background.auxiliary))
    (a ≫ XModLambdaN.proj _ L)
  have hzero : U ≫ XModLambdaN.incl _ q = 0 := by
    have h := congrArg (fun z => z ≫ (background.quotients.tower
      (background.nu.functor.obj (X.obj background.auxiliary))).rho q (q+1) (by omega)) htop
    rw [←regrade_comp,Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero] at h
    exact (homotopy_regrade_eq_zero _ _ _).mp h
  obtain ⟨b,hb,hlambda⟩ := finite_extension_of_boundary_projection_zero X L q hL hq m t a hzero
  let V := homotopyRegrade
    hm (show t+(L+q:ℕ)=W by omega)
    (biSuspensionHomEquiv m t ((L+q:ℕ):ℤ) (background.nu.functor.obj (X.obj background.auxiliary))
      (b ≫ XModLambdaN.proj _ (L+q)))
  obtain ⟨w,hw⟩ := native_first_label_surjective X S W
    (V ≫ XModLambdaN.incl _ 1)
  have hp := first_label_lift_permanent X S W w V hw.symm
  refine ⟨b,w,hb,hw.symm,hp,?_⟩
  have ht := lambda_power_first_label_projection_eq_top X q hq S W V w hw.symm
  have heq : lambdaMultiply q V =
      homotopyRegrade hm (show t+L=W-q by omega) U := by
    dsimp only [V,U]
    rw [hlambda,lambda_regrade,normalized_homotopy_regrade_trans]
  have htop' : finiteTopLabel X q hq S W w = finiteTopLabel X q hq S W v := by
    rw [←ht,heq,←regrade_comp]
    exact htop
  apply (finiteTopLabel_zero_iff_boundary X q hq S W (w-v)).mp
  rw [finite_top_label_sub,htop',sub_self]

private theorem finite_extension_of_boundary_top_at_weight
    (X : (AdamsObject (coefficients := background.coefficients))) (L q M : ℕ) (hL : 0<L) (hq : 0<q) (hM : q+1=M)
    (m t S W w0 : ℤ) (hm : m-1=W-S) (hW : t+L+q=W) (hw0 : t+L=w0)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) L))
    (v : Ambient background X (S,W))
    (htop : homotopyRegrade hm hw0
        (biSuspensionHomEquiv m t L (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ M) =
      finiteTopLabelAtWeight X q hq M hM S W w0 (by omega) v) :
    ∃ b : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (L+q)),
    ∃ w : Ambient background X (S,W),
      b ≫ (background.quotients.tower _).rho L (L+q) (by omega) = a ∧
      homotopyRegrade hm (show t+(L+q:ℕ)=W by omega)
          (biSuspensionHomEquiv m t ((L+q:ℕ):ℤ) (background.nu.functor.obj (X.obj background.auxiliary))
            (b ≫ XModLambdaN.proj _ (L+q))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel X S W w ∧
      w ∈ permanentCycles background X (S,W) ∧
      w-v ∈ boundaries background X (q+1) (S,W) := by
  subst M
  apply finite_extension_of_boundary_top X L q hL hq m t S W hm hW a v
  have h := congrArg (homotopyRegrade (m':=W-S) rfl (show w0=W-q by omega)) htop
  simpa only [finiteTopLabelAtWeight,normalized_homotopy_regrade_trans,
    top_target_regrade_self] using h

private theorem positive_finite_image_full_projection
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (m w : ℤ)
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary))) :
    positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w
        (a ≫ XModLambdaN.incl _ N) =
      (verticalTranslate _ 1 m w a ≫ lastLayerNormalizedMap T hf) ≫ XModLambdaN.incl _ N := by
  have hshift := level_quotient_shift_incl T.X 1 N
  have hs := congrArg (fun f => f ≫ (levelQuotientShiftIso T.X 1 N).inv) hshift
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at hs
  have hp : positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w
        (a ≫ XModLambdaN.incl _ N) =
      (verticalTranslate _ 1 m w (a ≫ XModLambdaN.incl _ N) ≫
        (levelQuotientShiftIso T.X 1 N).inv) ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) N := by
    simp [positiveFiniteImage,verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,
      susp_invariance,shiftHomotopyClass,Iso.homCongr,regrade_comp,Category.assoc]
  rw [hp]
  rw [←vertical_translate_comp]
  simp only [Category.assoc]
  rw [←Category.assoc ((SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (levelQuotientShiftIso T.X 1 N).inv (XModLambdaN.map (lastLayerNormalizedMap T hf) N),
    ←hs,←XModLambdaN.incl_naturality]

private theorem positive_finite_image_absolute_boundary
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (L : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L)) :
    homotopyRegrade (show (t-s)-1=(t+L)-(s+L+1) by omega)
        (show (t+1)+L=(t+L)+1 by omega)
        (biSuspensionHomEquiv (t-s) (t+1) L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t z ≫
            XModLambdaN.proj _ L)) =
      verticalTranslate _ 1 ((t+L)-(s+L+1)) (t+L) (positiveAdjustedBoundary T.X L s t z) ≫
        lastLayerNormalizedMap T hf := by
  let η := positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t z
  have hη : positiveBoundaryFiniteImage T.X T.Y (lastLayerNormalizedMap T hf) L s t z =
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl η := by
    simp [η,positiveBoundaryFiniteImage,positiveFiniteImage,verticalTranslate,
      regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,
      Iso.homCongr,regrade_comp,Category.assoc]
  have hb := positive_boundary_finite_image_boundary T.X T.Y
    (lastLayerNormalizedMap T hf) L s t z
  rw [hη] at hb
  dsimp only [boundaryRepresentative] at hb
  rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans] at hb
  have h := congrArg (homotopyRegrade
    (show ((t+1)+L)-((s+1)+L+1)=(t+L)-(s+L+1) by omega)
    (show (t+1)+L=(t+L)+1 by omega)) hb
  simpa only [η,normalized_homotopy_regrade_trans,top_target_regrade_self] using h

/-- The bottom finite zigzag and full intermediate image conditions extend
the positive image of the same specified source. Its actual full boundary
supplies the permanent target label; the remaining discrepancy is precisely
one F₂ image and a true boundary through the bottom page. -/
private theorem positive_bottom_finite_lift_of_middle_images
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L q : ℕ) (hL : 0<L) (hq : 0<q) (s t : ℤ)
    (u : Ambient background T.X (s+L+1,t+L))
    (z : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+L+1,(t+L)+1) ((s+L+1)+q+1,((t+L)+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L))
    (hζ : adjacentBoundaryLabel T.X L s t ζ = nativeFirstLabel T.X (s+L+1) (t+L) u) :
    ∃ η : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (L+(0+q))),
    ∃ wv : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
    ∃ e : Ambient background T.X ((s+L+1)+q,(t+L)+q),
    ∃ error : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+L+1)+q) ((t+L)+q) e) ∧
      η ≫ (background.quotients.tower _).rho L (L+(0+q)) (by omega) =
        positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ ∧
      homotopyRegrade
          (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
          (show (t+1)+(L+(0+q):ℕ)=((t+L)+1)+q by omega)
          (biSuspensionHomEquiv (t-s) (t+1) ((L+(0+q):ℕ):ℤ)
            (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ (L+(0+q)))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel T.Y ((s+L+1)+q+1) (((t+L)+1)+q) wv ∧
      wv ∈ permanentCycles background T.Y ((s+L+1)+q+1,((t+L)+1)+q) ∧
      wv-v-error ∈ boundaries background T.Y (q+1) ((s+L+1)+q+1,((t+L)+1)+q) := by
  let U := positiveAdjustedBoundary T.X L s t ζ
  have hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (s+L+1) (t+L) u :=
    (positive_adjusted_boundary_first T.X L s t ζ).trans hζ
  let a := U ≫ XModLambdaN.incl _ (0+(q+1))
  have ha : a ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      nativeFirstLabel T.X (s+L+1) (t+L) u := by
    dsimp only [a]
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  obtain ⟨e,error,herror,htop⟩ := positive_source_finite_top_restriction T he hT hf hg hh
    q (0+(q+1)) hq (by omega) (s+L+1) (t+L) u z v hu hdz hmid a ha
  rw [(background.quotients.tower _).rho_id,Category.comp_id] at htop
  dsimp only [a] at htop
  rw [positive_finite_image_full_projection] at htop
  let aY := positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ
  have hboundary := positive_finite_image_absolute_boundary T hf L s t ζ
  have hboundaryTop := congrArg (fun b => b ≫ XModLambdaN.incl
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (0+(q+1))) hboundary
  have htopY : homotopyRegrade
      (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (show (t+1)+L=(t+L)+1 by omega)
      (biSuspensionHomEquiv (t-s) (t+1) L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (aY ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (0+(q+1))) =
      finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
        ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (v+error) := by
    have h := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (rfl : (t+L)+1=(t+L)+1)) hboundaryTop
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at h
    exact h.trans htop
  obtain ⟨η,wv,hη,hwv,hp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L (0+q) (0+(q+1)) hL (by omega) (by omega) (t-s) (t+1)
    ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (by omega) (by omega)
    aY (v+error) htopY
  refine ⟨η,wv,e,error,herror,hη,hwv,hp,?_⟩
  have hid : wv-v-error=wv-(v+error) := by abel
  simpa only [hid,Nat.cast_add,Nat.cast_zero,zero_add] using herr

/-- The original bottom zigzag supplies a native common source with its
specified first label and exact positive normalized top image. -/
private theorem positive_finite_common_native_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0 < q) (S V : ℤ)
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hεp : XModLambdaN.incl _ (c+(q+1)) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+(q+1)))) :
    ∃ a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel background T.X (c+(q+1)) S V c u) a ∧
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
          (show (V-c)+1=(V+1)-c by omega)
          (positiveFiniteImage T hf (c+(q+1)) εp (V-S) (V-c) a) =
        finiteMayTopLabel T.Y c q hq S (V+1) v := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  obtain ⟨a,ha,hi,_⟩ := (positive_first_finite_core
    T he hT hf hg hh c q hq S V u z v hu hdz ey hey ε hε).1
  refine ⟨rawMaySourceDesuspend T he hf N c S V ε a,ha,?_⟩
  have hc := congrArg (fun a => a ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq S (V+1)
    v ey eY hey heY
  have himage : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega)
        (show (V+1)-c=V-c+1 by omega)
        (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
          (finiteMayTopLabel T.Y c q hq S (V+1) v)) := by
    rw [←homotopyRegrade_comp] at hc
    simpa only [Category.assoc] using hc.trans (congrArg (homotopyRegrade
      (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)) htop)
  exact finite_may_top_of_raw_positive_image T he hf c q hq S V ε εp hε hεp
    eY heY a v (by rw [←ordinary_suspended_representative_regrade]; exact himage)

/-- Restricted middle conditions suffice for the positive image of this
specified full source. Membership in each candidate space follows from
the full image, before the restricted condition is applied. -/
private theorem positive_full_image_of_selective_middle
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q : ℕ) (hq : 0 < q) (S V : ℤ)
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      permanentCycles background T.Y (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)+q)-(S+q+1) by omega) rfl
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf) ≫
          XModLambdaN.incl _ (0+(q+1))) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (S+q+1) ((V+1)+q) (V+1) (by omega) (v+error) := by
  let N := 0+(q+1)
  let ε := levelQuotientShiftIso T.X 1 N
  have hε := level_quotient_shift_incl T.X 1 N
  let a₀ : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    homotopyRegrade rfl (by omega) (U ≫ XModLambdaN.incl _ N)
  have hfirst : (U ≫ XModLambdaN.incl _ N) ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) =
      nativeFirstLabel T.X S V u := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hfirst
  rw [←zero_weight_label] at hdet
  have ha₀ := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hdet
  rw [finite_coefficient_weight_label] at ha₀
  obtain ⟨a,ha,hai⟩ := positive_finite_common_native_source
    T he hT hf hg hh 0 q hq S V u z v hu hdz ε hε
  have hres := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (S,V,V-(0:ℕ)) ha₀ ha
  let f := positiveFiniteImage T hf N ε (V-S) (V-(0:ℕ))
  let β := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega)
    (verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf)
  have hfull : f a₀ = β ≫ XModLambdaN.incl _ N := by
    dsimp only [f,a₀,β,ε]
    rw [←positiveFiniteImage_regrade,positive_finite_image_full_projection,regrade_comp]
  have hvfil : FiltrationAtLeast background.syntheticTower (S+(q+1)) (f a) := by
    apply (regrade_filtration_iff _ _ (S+(q+1)) (f a)).mp
    rw [show homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (f a) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) v from hai]
    have hvd := finite_may_top_label_detects T.Y 0 q hq S (V+1) v
    have hvf := (regrade_filtration_iff _ _ (S+q+1) _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (S+q+1,(V+1)+q,(V+1)-(0:ℕ)) _ _ hvd)
    simpa only [Nat.cast_add,Nat.cast_one,Int.add_assoc] using hvf
  obtain ⟨e,hefil,hei⟩ := selective_positive_f_native_residual_same_image
    T he hf hg hh hT 0 (q+1) (by omega) S V ε hε Pm hPm
    (by simpa only [Nat.cast_zero,zero_add] using hmid) (a₀-a) hres β (f a) hvfil
    (by rw [positiveFiniteImage_sub]; exact congrArg (fun z => z-f a) hfull)
  have hefil' : FiltrationAtLeast background.syntheticTower (S+q) e := by
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hefil
  obtain ⟨e₂,error,herror,heiTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf 0 q hq S V ε hε e hefil'
  have hsum : f a₀=f a+f e := by
    change f e=f (a₀-a) at hei
    dsimp only [f] at hei ⊢
    rw [positiveFiniteImage_sub] at hei
    rw [hei]; abel
  have htop : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (f a₀) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) (v+error) := by
    rw [hsum,regrade_add,hai,heiTop,finite_may_top_label_add]
  rw [hfull] at htop
  have ht := congrArg (homotopyRegrade
    (show ((V+1)-S)-1=((V+1)+q)-(S+q+1) by omega)
    (show (V+1)-(0:ℕ)=V+1 by omega)) htop
  refine ⟨e₂,error,herror,?_⟩
  simp only [β,←regrade_comp,finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [top_target_regrade_self] using ht

/-- The original selective bottom condition extends the image of the same
source lift and retains the actual absolute boundary used by source division. -/
private theorem positive_bottom_finite_lift_of_selective_middle
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L q : ℕ) (hL : 0<L) (hq : 0<q) (s t : ℤ)
    (u : Ambient background T.X (s+L+1,t+L))
    (z : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+L+1,(t+L)+1) ((s+L+1)+q+1,((t+L)+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
          ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L))
    (hζ : adjacentBoundaryLabel T.X L s t ζ = nativeFirstLabel T.X (s+L+1) (t+L) u) :
    ∃ η : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (L+(0+q))),
    ∃ wv : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
    ∃ e : Ambient background T.X ((s+L+1)+q,(t+L)+q),
    ∃ error : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+L+1)+q) ((t+L)+q) e) ∧
      η ≫ (background.quotients.tower _).rho L (L+(0+q)) (by omega) =
        positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ ∧
      homotopyRegrade
          (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
          (show (t+1)+(L+(0+q):ℕ)=((t+L)+1)+q by omega)
          (biSuspensionHomEquiv (t-s) (t+1) ((L+(0+q):ℕ):ℤ)
            (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ (L+(0+q)))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel T.Y ((s+L+1)+q+1) (((t+L)+1)+q) wv ∧
      wv ∈ permanentCycles background T.Y ((s+L+1)+q+1,((t+L)+1)+q) ∧
      wv-v-error ∈ boundaries background T.Y (q+1) ((s+L+1)+q+1,((t+L)+1)+q) := by
  let U := positiveAdjustedBoundary T.X L s t ζ
  have hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (s+L+1) (t+L) u :=
    (positive_adjusted_boundary_first T.X L s t ζ).trans hζ
  obtain ⟨e,error,herror,htop⟩ := positive_full_image_of_selective_middle
    T he hT hf hg hh q hq (s+L+1) (t+L) u z v hu hdz Pm hPm hmid U hU
  let aY := positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ
  have hboundary := positive_finite_image_absolute_boundary T hf L s t ζ
  have hboundaryTop := congrArg (fun b => b ≫ XModLambdaN.incl
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (0+(q+1))) hboundary
  have htopY : homotopyRegrade
      (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (show (t+1)+L=(t+L)+1 by omega)
      (biSuspensionHomEquiv (t-s) (t+1) L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (aY ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (0+(q+1))) =
      finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
        ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (v+error) := by
    have h := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (rfl : (t+L)+1=(t+L)+1)) hboundaryTop
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at h
    exact h.trans htop
  obtain ⟨η,wv,hη,hwv,hp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L (0+q) (0+(q+1)) hL (by omega) (by omega) (t-s) (t+1)
    ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (by omega) (by omega)
    aY (v+error) htopY
  refine ⟨η,wv,e,error,herror,hη,hwv,hp,?_⟩
  have hid : wv-v-error=wv-(v+error) := by abel
  simpa only [hid,Nat.cast_add,Nat.cast_zero,zero_add] using herr

end
end KIP126.ProofTools.Internal.SyntheticCoverage
