module

import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison
import all KIP126.ProofTools.SyntheticCoverage.SelectiveHead

/-! Corrections of a supplied common root for the positive second arrow,
preserving its first quotient and adjacent boundary. -/
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

/-- Classical rotation reuses the specified first-arrow
finite-image construction. -/
private def positiveGArrowTriangle (T : TriangleData background.auxiliary) :
    TriangleData background.auxiliary where
  X := T.Y
  Y := T.Z
  Z := .shift 1 T.X
  f := T.g
  g := T.h
  h := -((shiftFunctor Spectrum (1:ℤ)).map T.f)
  distinguished := rot_of_distTriang _ T.distinguished

private theorem positive_g_normalized_composite_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he) :
    normalizedSecondPositiveMap T hg ≫ background.nu.functor.map T.h=0 := by
  let G := normalizedSecondPositiveMap T hg
  let P := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let N := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hz : negativeLift 1 G ≫ N.map (background.nu.functor.map T.h)=0 := by
    rw [←normalized_second_arrow_positive T he hg,Category.assoc,
      ←middle_positive_g_third_map T he hf hg hh,←Category.assoc,
      comp_distTriang_mor_zero₂₃ _ hT,zero_comp]
  have hc := shift_negativeLift_cancel 1 G
  change P.map (negativeLift 1 G) ≫ shiftNegativePositiveUnit.hom.app _=G at hc
  change G ≫ background.nu.functor.map T.h=0
  have hn := shiftNegativePositiveUnit.hom.naturality (background.nu.functor.map T.h)
  change P.map (N.map (background.nu.functor.map T.h)) ≫ shiftNegativePositiveUnit.hom.app _ =
    shiftNegativePositiveUnit.hom.app _ ≫ background.nu.functor.map T.h at hn
  rw [←hc,Category.assoc,←hn]
  change P.map (negativeLift 1 G) ≫ P.map (N.map (background.nu.functor.map T.h)) ≫
    shiftNegativePositiveUnit.hom.app _=0
  rw [←P.map_comp_assoc,hz,Functor.map_zero,zero_comp]

private theorem positive_g_rotated_first_map
    (T : TriangleData background.auxiliary)
    (hg : normalizedExponent background.classicalTower T.g=1) :
    lastLayerNormalizedMap (positiveGArrowTriangle T) hg = normalizedSecondPositiveMap T hg := by
  change normalizedClassicalPositiveMap T.Y T.Z T.g hg = normalizedSecondPositiveMap T hg
  exact (normalized_second_positive_map_eq T hg).symm

private theorem positive_g_rotated_first_operation
    (T : TriangleData background.auxiliary)
    (hg : normalizedExponent background.classicalTower T.g=1) (s t : ℤ)
    (x : Ambient background T.Y (s,t)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary (positiveGArrowTriangle T) hg s t x =
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t x := by
  apply native_first_label_injective T.Z (s+1) (t+1)
  have hl := cofiberFirstQuotientBoundary_native_label (positiveGArrowTriangle T) hg s t x
  refine hl.trans ?_
  rw [positive_first_quotient_native_label]
  have heq : normalizedFirstMap (positiveGArrowTriangle T) hg=normalizedSecondPositiveMap T hg :=
    positive_g_rotated_first_map T hg
  rw [heq]
  rfl


private theorem positive_g_native_correction
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a j : ℕ) (hj : 0<j) (hja : j<a) (p t : ℤ)
    (y : Ambient background T.Y (p,t)) (hy : y ∈ cycles background T.Y (a-j:ℕ) (p,t)) :
    ∃ b : BiHom ((t+1)-(p+1)) ((t+1)-j)
        (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a),
      Detects (background.convergence (.quotient a (.nu T.Z))) (p+1,t+1,(t+1)-j)
        (finiteTargetLabel background T.Z a (p+1) (t+1) j
          (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p t y)) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.h) a=0 := by
  obtain ⟨b,hb⟩ := higher_finite_cycle_representative T.Y a j hja p t y hy
  let V := positiveGArrowTriangle T
  let ε := levelQuotientShiftIso T.Y 1 a
  let c := positiveFiniteImage V hg a ε (t-p) (t-j) b
  have hd := selective_positive_image_detects V hg a j hj hja p t ε
    (level_quotient_shift_incl T.Y 1 a) y b hb
  rw [positive_g_rotated_first_operation] at hd
  refine ⟨homotopyRegrade (show t-p=(t+1)-(p+1) by omega)
    (show (t-j)+1=(t+1)-j by omega) c,hd,?_⟩
  rw [←regrade_comp]
  have hc : c ≫ XModLambdaN.map (background.nu.functor.map T.h) a=0 := by
    dsimp only [c,positiveFiniteImage]
    rw [positive_g_rotated_first_map,Category.assoc,
      quotient_map_comp_zero _ _ (positive_g_normalized_composite_zero T he hf hg hh hT),comp_zero]
  rw [hc,regrade_zero]

private theorem positive_g_root_correction_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a N j : ℕ) (hja : j<a) (haN : a≤N) (hj : 0<j) (p t : ℤ)
    (hR : ∀ z : Ambient background T.Z (p+1,t+1), z ∈ cycles background T.Z (a-j:ℕ) (p+1,t+1) →
      ∃ u : Ambient background T.Y (p,t), u ∈ cycles background T.Y (a-j:ℕ) (p,t) ∧
      ∃ k : Ambient background T.Z (p+1,t+1), k ∈ cycles background T.Z (N+1-j:ℕ) (p+1,t+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p t u-k ∈ boundaries background T.Z (j+1) (p+1,t+1))
    (R : BiHom ((t+1)-(p+1)) ((t+1)-j) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (root : BiHom ((t+1)-(p+1)) ((t+1)-j) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower (p+1)
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom ((t+1)-(p+1)) ((t+1)-j) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
      (root' : BiHom ((t+1)-(p+1)) ((t+1)-j) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a (by omega)=R ≫ (background.quotients.tower _).rho 1 a (by omega) ∧
      R' ≫ XModLambdaN.map (background.nu.functor.map T.h) a=R ≫ XModLambdaN.map (background.nu.functor.map T.h) a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower ((p+1)+1)
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.Z a j hja (p+1) (t+1)
    (R-root ≫ (background.quotients.tower _).rho a N haN) herror
  obtain ⟨u,hu,k,hk,hcong⟩ := hR z hzc
  obtain ⟨b,hbimage,hbzero⟩ := positive_g_native_correction T he hf hg hh hT a j hj hja p t u hu
  obtain ⟨c,hc,hcf,hcd⟩ := higher_root_correction T.Z N j hj (by omega) (p+1) (t+1) k hk
  have hcshort := higher_finite_restriction_detects T.Z a (N+1) j (by omega) (p+1) (t+1) k c hc
  have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
    (.quotient a (.nu T.Z)) (p+1,t+1,(t+1)-j) hzd hbimage
  rw [←finiteTargetLabel_sub] at hsub
  have hnext := middle_finite_congruent_difference T.Z a j hja (p+1) (t+1)
    (z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p t u) k hcong
    ((R-root ≫ (background.quotients.tower _).rho a N haN)-b)
    (c ≫ (background.quotients.tower _).rho a (N+1) (by omega)) hsub hcshort
  have hbfirst : b ≫ (background.quotients.tower _).rho 1 a (by omega)=0 :=
    finite_filtered_first_quotient_zero T.Z a j (by omega) hj (p+1) (t+1) b
      (KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient a (.nu T.Z))
        (p+1,t+1,(t+1)-j) _ b hbimage)
  refine ⟨R-b,
    root+c ≫ (background.quotients.tower _).rho N (N+1) (by omega),?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hbfirst,sub_zero]
  · rw [Preadditive.sub_comp,hbzero,sub_zero]
  · rw [Preadditive.add_comp,hcf,add_zero]
  · rw [Preadditive.add_comp,hcd,add_zero]
  · rw [Preadditive.add_comp,Category.assoc,(background.quotients.tower _).rho_comp]
    convert hnext using 1
    abel


private theorem positive_g_root_correction_step_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a N j : ℕ) (hja : j<a) (haN : a≤N) (hj : 0<j) (p t m w : ℤ) (hm : m=(t+1)-(p+1)) (hw : w=(t+1)-j)
    (hR : ∀ z : Ambient background T.Z (p+1,t+1), z ∈ cycles background T.Z (a-j:ℕ) (p+1,t+1) →
      ∃ u : Ambient background T.Y (p,t), u ∈ cycles background T.Y (a-j:ℕ) (p,t) ∧
      ∃ k : Ambient background T.Z (p+1,t+1), k ∈ cycles background T.Z (N+1-j:ℕ) (p+1,t+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p t u-k ∈ boundaries background T.Z (j+1) (p+1,t+1))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (root : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower (p+1)
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
      (root' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a (by omega)=R ≫ (background.quotients.tower _).rho 1 a (by omega) ∧
      R' ≫ XModLambdaN.map (background.nu.functor.map T.h) a=R ≫ XModLambdaN.map (background.nu.functor.map T.h) a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower ((p+1)+1)
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  subst m
  subst w
  exact positive_g_root_correction_step T he hf hg hh hT a N j hja haN hj p t hR R root herror

private theorem positive_g_root_correction_to_last
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a N : ℕ) (ha : 0<a) (haN : a≤N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u+1-w) (hv : v≤(a:ℤ)+w-m-1)
    (hR : ∀ p : ℤ, u≤p → p<v →
      ∀ z : Ambient background T.Z (p+1,(m+p)+1), z ∈ cycles background T.Z (a-(m+p+1-w).toNat:ℕ) (p+1,(m+p)+1) →
      ∃ y : Ambient background T.Y (p,m+p), y ∈ cycles background T.Y (a-(m+p+1-w).toNat:ℕ) (p,m+p) ∧
      ∃ k : Ambient background T.Z (p+1,(m+p)+1), k ∈ cycles background T.Z (N+1-(m+p+1-w).toNat:ℕ) (p+1,(m+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (m+p) y-k ∈
          boundaries background T.Z ((m+p+1-w).toNat+1) (p+1,(m+p)+1))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (root : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower (u+1)
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
      (root' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a ha=R ≫ (background.quotients.tower _).rho 1 a ha ∧
      R' ≫ XModLambdaN.map (background.nu.functor.map T.h) a=R ≫ XModLambdaN.map (background.nu.functor.map T.h) a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower (v+1)
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u R root with
  | h n ih =>
    by_cases heq : v≤u
    · have huv' : u=v := le_antisymm huv heq
      exact ⟨R,root,rfl,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u+1-w).toNat
      have hj : (j:ℤ)=m+u+1-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hja : j<a := by omega
      obtain ⟨R₁,root₁,hRfirst,hRimage,hrootfirst,hrootboundary,hnext⟩ :=
        positive_g_root_correction_step_at T he hf hg hh hT a N j hja haN hjpos
          u (m+u) m w (by omega) (by omega) (hR u le_rfl (by omega)) R root herror
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨R₂,root₂,hRfirst₂,hRimage₂,hrootfirst₂,hrootboundary₂,hfinal⟩ :=
        ih (v-(u+1)).toNat hd' (u+1) (by omega) (by omega)
          (fun p hp hpv => hR p (by omega) hpv) R₁ root₁ hnext rfl
      exact ⟨R₂,root₂,hRfirst₂.trans hRfirst,hRimage₂.trans hRimage,
        hrootfirst₂.trans hrootfirst,hrootboundary₂.trans hrootboundary,hfinal⟩



/-- Complete native comparison for the original positive-G root spaces.
The ordinary H image is only killed at the last layer. -/
private theorem positive_g_native_root_compatible
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a N : ℕ) (ha : 2≤a) (haN : a≤N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background T.Z (p+1,(t-s+p)+1),
        z ∈ cycles background T.Z (a-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) →
      ∃ y : Ambient background T.Y (p,t-s+p),
        y ∈ cycles background T.Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p+1,(t-s+p)+1),
        k ∈ cycles background T.Z (N+1-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p+1,(t-s+p)+1))
    (hH : ∀ z : Ambient background T.Z (s+a,(t+a-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+a) (t+a-1) z ∈
        boundaries background T.X a (s+a,t+a-1))
    (R : BiHom (t-s) (t+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a))
    (root : BiHom (t-s) (t+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N))
    (hfirst : R ≫ (background.quotients.tower _).rho 1 a (by omega)=
      root ≫ (background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) (t+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) N),
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫ XModLambdaN.map (background.nu.functor.map T.h) a=
        R ≫ XModLambdaN.map (background.nu.functor.map T.h) a := by
  let e₀ := R-root ≫ (background.quotients.tower _).rho a N haN
  let e₁ := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl e₀
  have hfirst₀ : e₁ ≫ (background.quotients.tower _).rho 1 a (by omega)=0 := by
    dsimp only [e₁,e₀]
    rw [←regrade_comp,Preadditive.sub_comp,Category.assoc,
      (background.quotients.tower _).rho_comp,hfirst,sub_self,regrade_zero]
  have herror : FiltrationAtLeast background.syntheticTower ((s+1)+1) e₀ :=
    (regrade_filtration_iff _ _ _ _).mp
      (finite_first_kernel_filtration T.Z a ha (s+1) (t+1) e₁ hfirst₀)
  obtain ⟨R',root',_,hRimage,hrootfirst,hrootboundary,hfinal⟩ :=
    positive_g_root_correction_to_last T he hf hg hh hT
      a N (by omega) haN (t-s) (t+1) (s+1) (s+a-1) (by omega) (by omega) (by omega)
      (by
        intro p hp hpv
        have hi : (t-s+p+1-(t+1)).toNat=(p-s).toNat := by congr 1; omega
        simpa only [hi] using hR p hp hpv) R root herror
  let e := R'-root' ≫ (background.quotients.tower _).rho a N haN
  let e' := homotopyRegrade (show t-s=((t+a-1)+1)-(s+a) by omega) rfl e
  have hef : FiltrationAtLeast background.syntheticTower (s+a) e' := by
    apply (regrade_filtration_iff _ _ _ _).mpr
    convert hfinal using 1; omega
  have he' := ordinary_map_top_filtration_zero T.Z (.shift 1 T.X) T.h a ha
    (s+a) ((t+a-1)+1) (t+1) (by omega)
    (higher_whole_h_image_suspended_boundary T a (s+a) (t+a-1) hH) e' hef
  have hz : e ≫ XModLambdaN.map (background.nu.functor.map T.h) a=0 := by
    apply (ordinary_regrade_zero_iff (show t-s=((t+a-1)+1)-(s+a) by omega) rfl _).mp
    simpa only [e',regrade_comp] using he'
  have heq : R' ≫ XModLambdaN.map (background.nu.functor.map T.h) a=
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫ XModLambdaN.map (background.nu.functor.map T.h) a := by
    exact sub_eq_zero.mp (by simpa only [e,Preadditive.sub_comp] using hz)
  exact ⟨root',hrootfirst,hrootboundary,heq.symm.trans hRimage⟩


private def negativeRootEquiv (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (m w : ℤ) :
    BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) ≃+
      BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q) :=
  (verticalShiftEquiv _ 1 m w).trans
    (homPostcompAddEquiv (levelQuotientShiftIso X (-1) q).symm)

private theorem negative_root_equiv_apply (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (m w : ℤ)
    (b : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    negativeRootEquiv X q m w b =
      homotopyRegrade (show m+0=m by omega) (show w+1+(-1)=w by omega)
        (shiftHomotopyClass (0,-1) (m,w+1) b) ≫ (levelQuotientShiftIso X (-1) q).inv := by
  have hs : susp_invariance m (w+1) 0 (-1) _ b =
      shiftHomotopyClass (0,-1) (m,w+1) b := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  change homotopyRegrade (add_zero m) (add_neg_cancel_right w (1:ℤ))
    (susp_invariance m (w+1) 0 (-1) _ b) ≫ _ = _
  rw [hs]
  rfl

private theorem negative_root_equiv_restriction (X : (AdamsObject (coefficients := background.coefficients)))
    (i q : ℕ) (hi : 0 < i) (hiq : i≤q) (m w : ℤ)
    (b : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    negativeRootEquiv X q m w b ≫ (background.quotients.tower _).rho i q hiq =
      negativeRootEquiv X i m w (b ≫ (background.quotients.tower _).rho i q hiq) := by
  apply (cancel_mono (levelQuotientShiftIso X (-1) i).hom).mp
  rw [Category.assoc,quotient_shift_restriction_on_spheres X (0,-1) i q hi hiq
    (levelQuotientShiftIso X (-1) i) (levelQuotientShiftIso X (-1) q)
    (level_quotient_shift_incl X (-1) i) (level_quotient_shift_incl X (-1) q)]
  simp only [negative_root_equiv_apply,Category.assoc,Iso.inv_hom_id_assoc,
    Iso.inv_hom_id,Category.comp_id]
  rw [←regrade_comp,←shift_hom_comp]

private theorem negative_root_equiv_boundary_congr (X : (AdamsObject (coefficients := background.coefficients)))
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (b c : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (heq : b ≫ adjacentDelta _ q hq = c ≫ adjacentDelta _ q hq) :
    negativeRootEquiv X q m w b ≫ adjacentDelta _ q hq =
      negativeRootEquiv X q m w c ≫ adjacentDelta _ q hq := by
  simp only [negative_root_equiv_apply,←regrade_comp]
  rw [adjacent_delta_weight_shift,adjacent_delta_weight_shift,heq]

private theorem negative_root_equiv_ordinary_map (X Y : (AdamsObject (coefficients := background.coefficients)))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (b : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    negativeRootEquiv X q m w b ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,-1)).map (background.nu.functor.map f)) q =
      negativeRootEquiv Y q m w (b ≫ XModLambdaN.map (background.nu.functor.map f) q) := by
  apply (cancel_mono (levelQuotientShiftIso Y (-1) q).hom).mp
  rw [Category.assoc,shifted_ordinary_quotient_map_on_spheres X Y f q hq (0,-1)
    (levelQuotientShiftIso X (-1) q) (levelQuotientShiftIso Y (-1) q)
    (level_quotient_shift_incl X (-1) q) (level_quotient_shift_incl Y (-1) q)]
  simp only [negative_root_equiv_apply,Category.assoc,Iso.inv_hom_id_assoc,
    Iso.inv_hom_id,Category.comp_id]
  rw [←regrade_comp,←shift_hom_comp]

private def positiveGRootEquiv
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (q : ℕ) (m w : ℤ) :
    BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) q) ≃+
      BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ q) :=
  (negativeRootEquiv T.Z q m w).trans
    (homPostcompAddEquiv ((background.quotients.functoriality.functor q).mapIso
      (normalizedThirdNegativeIso T he hg)).symm)

private theorem positive_g_root_equiv_apply
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (q : ℕ) (m w : ℤ)
    (b : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) q)) :
    positiveGRootEquiv T he hg q m w b =
      negativeRootEquiv T.Z q m w b ≫ XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv q := rfl

private theorem positive_g_root_equiv_restriction
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (i q : ℕ) (hi : 0 < i) (hiq : i≤q) (m w : ℤ)
    (b : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) q)) :
    positiveGRootEquiv T he hg q m w b ≫ (background.quotients.tower _).rho i q hiq =
      positiveGRootEquiv T he hg i m w (b ≫ (background.quotients.tower _).rho i q hiq) := by
  simp only [positive_g_root_equiv_apply]
  rw [Category.assoc,←(background.quotients.natural (normalizedThirdNegativeIso T he hg).inv).rho_naturality hiq,
    ←Category.assoc,negative_root_equiv_restriction T.Z i q hi hiq m w b]

private theorem positive_g_adjacent_delta_equality_iff
    (A : SyntheticSpectrum) (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN A q)) :
    a ≫ adjacentDelta A q hq=b ≫ adjacentDelta A q hq ↔
      a ≫ ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta=
        b ≫ ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta := by
  constructor
  · intro hab
    have transport (n : ℕ) (hn : n=1)
        (d : XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
        (hd : a ≫ Eq.mp (congrArg (fun l => XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A l))⟦(1:ℤ)⟧) hn) d=
          b ≫ Eq.mp (congrArg (fun l => XModLambdaN A q ⟶
            ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A l))⟦(1:ℤ)⟧) hn) d) :
        a ≫ d=b ≫ d := by
      subst n
      exact hd
    exact transport (q.succ-q) (by omega) _ hab
  · exact higher_adjacent_delta_equality A q hq m w a b

private theorem positive_g_root_equiv_boundary_congr
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (b c : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) q))
    (heq : b ≫ adjacentDelta _ q hq = c ≫ adjacentDelta _ q hq) :
    positiveGRootEquiv T he hg q m w b ≫ adjacentDelta _ q hq =
      positiveGRootEquiv T he hg q m w c ≫ adjacentDelta _ q hq := by
  simp only [positive_g_root_equiv_apply,Category.assoc,adjacent_delta_natural]
  rw [←Category.assoc,←Category.assoc,
    negative_root_equiv_boundary_congr T.Z q hq m w b c heq]


private theorem positive_g_root_equiv_image_congr
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (b c : BiHom m (w+1) (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) q))
    (heq : b ≫ XModLambdaN.map (background.nu.functor.map T.h) q =
      c ≫ XModLambdaN.map (background.nu.functor.map T.h) q) :
    positiveGRootEquiv T he hg q m w b ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q =
      positiveGRootEquiv T he hg q m w c ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q := by
  let E := middlePositiveGTargetIso T he hf
  apply (cancel_mono ((background.quotients.functoriality.functor q).mapIso E).hom).mp
  change (_ ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) ≫ XModLambdaN.map E.hom q =
    (_ ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) ≫ XModLambdaN.map E.hom q
  have hc := congrArg (fun f => XModLambdaN.map f q) (middle_positive_g_third_map T he hf hg hh)
  rw [background.quotients.functoriality.map_comp,background.quotients.functoriality.map_comp] at hc
  simp only [Category.assoc]
  rw [hc]
  have hcancel : XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv q ≫
      XModLambdaN.map (normalizedThirdNegativeIso T he hg).hom q=𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  simp only [positive_g_root_equiv_apply,Category.assoc]
  rw [←Category.assoc (XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv q),
    hcancel,Category.id_comp]
  rw [negative_root_equiv_ordinary_map T.Z (.shift 1 T.X) T.h q hq m w b,
    negative_root_equiv_ordinary_map T.Z (.shift 1 T.X) T.h q hq m w c,heq]

/-- The same comparison on the fixed normalized third object. The chosen
root retains its literal first quotient and literal adjacent differential target. -/
private theorem positive_g_normalized_root_compatible
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (a N : ℕ) (ha : 2≤a) (haN : a≤N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background T.Z (p+1,(t-s+p)+1),
        z ∈ cycles background T.Z (a-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) →
      ∃ y : Ambient background T.Y (p,t-s+p),
        y ∈ cycles background T.Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p+1,(t-s+p)+1),
        k ∈ cycles background T.Z (N+1-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p+1,(t-s+p)+1))
    (hH : ∀ z : Ambient background T.Z (s+a,(t+a-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+a) (t+a-1) z ∈
        boundaries background T.X a (s+a,t+a-1))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ a))
    (root : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N))
    (hfirst : R ≫ (background.quotients.tower _).rho 1 a (by omega)=
      root ≫ (background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N),
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ a=
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ a := by
  let E := fun q => positiveGRootEquiv T he hg q (t-s) t
  let Rn := (E a).symm R
  let rootn := (E N).symm root
  have hRn : E a Rn=R := AddEquiv.apply_symm_apply _ _
  have hrootn : E N rootn=root := AddEquiv.apply_symm_apply _ _
  have hfirstn : Rn ≫ (background.quotients.tower _).rho 1 a (by omega)=
      rootn ≫ (background.quotients.tower _).rho 1 N (by omega) := by
    apply (E 1).injective
    dsimp only [E]
    rw [←positive_g_root_equiv_restriction T he hg 1 a (by decide) (by omega),
      ←positive_g_root_equiv_restriction T he hg 1 N (by decide) (by omega)]
    change (E a Rn) ≫ _ = (E N rootn) ≫ _
    rw [hRn,hrootn,hfirst]
  obtain ⟨b,hbf,hbd,hbh⟩ := positive_g_native_root_compatible T he hf hg hh hT
    a N ha haN s t hR hH Rn rootn hfirstn
  refine ⟨E N b,?_,?_,?_⟩
  · dsimp only [E]
    rw [positive_g_root_equiv_restriction T he hg 1 N (by decide) (by omega),hbf,
      ←positive_g_root_equiv_restriction T he hg 1 N (by decide) (by omega)]
    change (E N rootn) ≫ _ = _
    rw [hrootn]
  · have h := positive_g_root_equiv_boundary_congr T he hg N (by omega) (t-s) t b rootn
      (higher_adjacent_delta_equality _ N (by omega) (t-s) (t+1) b rootn hbd)
    change (E N b) ≫ _ = (E N rootn) ≫ _ at h
    rw [hrootn] at h
    exact (positive_g_adjacent_delta_equality_iff _ N (by omega) (t-s) t _ _).mp h
  · dsimp only [E]
    rw [positive_g_root_equiv_restriction T he hg a N (by omega) haN]
    have h := positive_g_root_equiv_image_congr T he hf hg hh a (by omega) (t-s) t
      (b ≫ (background.quotients.tower _).rho a N haN) Rn hbh
    change (E a (b ≫ _)) ≫ _ = (E a Rn) ≫ _ at h
    rw [hRn] at h
    exact h

end
end KIP126.ProofTools.Internal.SyntheticCoverage
