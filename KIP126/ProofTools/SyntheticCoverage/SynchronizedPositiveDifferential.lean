module

import all KIP126.ProofTools.SyntheticCoverage.SynchronizedPositiveBottom
import all KIP126.ProofTools.SyntheticCoverage.SynchronizedBottomDifferential

/-! The original known-source theorem with synchronized early source
boundaries, for the positive first arrow. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private theorem synchronized_known_source_differential_positive_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+L+1,t+L))
    (z₁ : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+a+1,(t+1)+a))
    (z₂ : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+b+1,((t+L)+1)+b))
    (_hFx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z₁) (by simpa using x))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z₂) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (s,t+1) (s+a+1,(t+1)+a) z₁
      ((background.classical.map T.g).pageMap 2 (s+a+1,(t+1)+a) y))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (s+L+1,(t+L)+1) ((s+L+1)+b+1,((t+L)+1)+b) z₂
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+b+1,((t+L)+1)+b) v))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X (s+j,t+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) (s+j,t+j) →
        ∃ z' : Ambient background T.Z (s+j,t+j+1),
          z' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) (s+j,t+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+j) (t+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (s+j,t+j))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (b+1)-1 →
      boundaries background T.Y ((L-a:ℕ)+j) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1 ≤ j → j < (b+1)-1 →
      ∀ x' : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        x' ∈ cycles background T.X (((b+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
          ((s+L+1)+j) ((t+L)+j) x' ∈ Pm j →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((b+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((L-a:ℕ)+j) ((s+L+1)+j,(t+L)+j))
    (himage : ∀ e : Ambient background T.X (s+a,t+a),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+a) (t+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (s+a+1,(t+a)+1))
    (hy : y ∈ cycles background T.Y (L+b-a:ℕ) (s+a+1,(t+1)+a))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1)+b+1,((t+L)+1)+b)))
    (hP : permanentCycles background T.Y ((s+L+1)+b+1,((t+L)+1)+b) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+L+1)+b+1,((t+L)+1)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((s+L+1)+b+1,((t+L)+1)+b)) :
    IsCycle background T.Y (L+b-a:ℕ) (s+a+1,(t+1)+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((s+L+1)+b+1,((t+L)+1)+b) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (s+a+1,(t+1)+a)
        ((s+L+1)+b+1,((t+L)+1)+b) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega) s t x u).mp hdx
  obtain ⟨et,sourceError,heTop,hTop⟩ := positive_source_finite_top_restriction
    T he hT hf hg hh a L ha haL s t x z₁ y hxz hdz₁ htop ζ hζ
  let S := s+L+1
  let W := t+L
  let A := s+a+1
  let B := (t+1)+a
  let ζ₀ := homotopyRegrade (show t-s=W-S+1 by dsimp [S,W]; omega)
    (show t=W-L by dsimp [W]; omega) ζ
  have hcal : (homotopyRegrade (show W-S+1=B-A by dsimp [S,W,A,B]; omega)
      (show (W-L)+1=B-a by dsimp [W,B]; omega)
      (positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (W-S+1) (W-L) ζ₀))≫
      (background.quotients.tower _).rho (a+1) L haL=finiteTopLabel T.Y a ha A B (y+sourceError) := by
    have normalize (d n : ℕ) (hd : d=a) (hn : n=a+1)
        (hdpos : 0<d) (hdn : d+1=n) (hNL : n≤L) (hw : B-d=t+1)
        (h : homotopyRegrade (show t-s=B-A by dsimp [A,B];omega) rfl
            (positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ≫
              (background.quotients.tower _).rho n L hNL)=
            finiteTopLabelAtWeight T.Y d hdpos n hdn A B (t+1) hw (y+sourceError)) :
        (homotopyRegrade (show W-S+1=B-A by dsimp [S,W,A,B];omega)
          (show (W-L)+1=B-a by dsimp [W,B];omega)
          (positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (W-S+1) (W-L) ζ₀))≫
          (background.quotients.tower _).rho (a+1) L haL=
          finiteTopLabel T.Y a ha A B (y+sourceError) := by
      subst d; subst n
      have h' := congrArg (homotopyRegrade (rfl : B-A=B-A) (show t+1=B-a by dsimp [B];omega)) h
      simpa only [ζ₀,←positiveFiniteImage_regrade,←regrade_comp,
        normalized_homotopy_regrade_trans,finiteTopLabelAtWeight,top_target_regrade_self] using h'
    exact normalize (0+a) (0+(a+1)) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by dsimp [B];omega) hTop
  have hsourceError : sourceError∈cycles background T.Y ((L+b-a:ℕ)+1) (A,B) := by
    have h := classical_cycle_heq T.Y ((L+b-a:ℕ)+1)
      (show (s+a+1,t+a+1)=(A,B) by dsimp [A,B]; congr 1; omega)
      _ sourceError heTop.symm ⟨by omega,himage et⟩
    exact h.2
  have hyTop : y+sourceError∈cycles background T.Y (L+b-a:ℕ) (A,B) :=
    (cycles background T.Y (L+b-a:ℕ) (A,B)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) hsourceError)
  have hfirstU : synchronizedPositiveBoundary T.X L S W ζ₀≫XModLambdaN.incl _ 1=
      nativeFirstLabel T.X S W u := by
    rw [synchronized_positive_boundary_first]
    have hb := synchronized_adjacent_boundary_coordinates T.X L s t S W rfl rfl ζ
    rw [show ζ₀=homotopyRegrade (show t-s=W-S+1 by dsimp [S,W];omega)
      (show t=W-L by dsimp [W];omega) ζ from rfl,hb,←regrade_comp,←adjacentBoundaryLabel,hU]
    exact top_target_regrade_self _
  obtain ⟨c₀,hcDet,hcImg⟩ := synchronized_positive_common_native
    T he hT hf hg hh b hb S W u z₂ v huz hdz₂
  have hdet := first_label_detects_unshifted T.X (b+1) (by omega) S W u
    (synchronizedPositiveBoundary T.X L S W ζ₀≫XModLambdaN.incl _ (b+1))
    (by rw [Category.assoc,(background.quotients.tower _).rho_quotient,hfirstU]; rfl)
  have hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedPositiveBoundary T.X L S W ζ₀≫XModLambdaN.incl _ (b+1)-c₀) := by
    exact detects_sub_filtration (background.convergence (.quotient (b+1) (.nu T.X)))
      (S,W,W) hdet
      (first_label_detects_unshifted T.X (b+1) (by omega) S W u c₀ hcDet)
  have hcfil : FiltrationAtLeast background.syntheticTower (S+(b+1))
      (synchronizedPositiveImage T hf (b+1) S W c₀) := by
    apply (regrade_filtration_iff _ _ (S+(b+1)) _).mp
    rw [hcImg]
    have hvf := finite_top_label_at_weight_detects T.Y b hb (b+1) rfl
      (S+b+1) ((W+1)+b) (W+1) (by omega) v
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using detects_filtration
      (.quotient (b+1) (.nu T.Y)) (S+b+1,(W+1)+b,W+1) _ _ hvf
  obtain ⟨ζ',c,hρ,_,hci,hres⟩ := synchronized_positive_bottom_core T he hf hg hh hT L a (b+1)
    ha (by omega) (by omega) S W A B ((L+b-a:ℕ)+1) (by dsimp [S,A];omega)
    (by dsimp [W,B];omega) (by omega) ζ₀ (y+sourceError)
    (by simpa only [add_sub_cancel_right] using hyTop) hcal c₀ hcfil hstart Pm hPm hbottom
  obtain ⟨eb,targetError,heBottom,hBottom⟩ := synchronized_positive_top_of_residual T hf b hb S W
    (synchronizedPositiveBoundary T.X L S W ζ') c v
    (by rw [hci]; exact hcImg)
    (by simpa only [Nat.cast_add,Nat.cast_one,show S+(b+1)-1=S+b by omega] using hres)
  have hBoundaryTop := synchronized_positive_boundary_top T hf L b hb S W ζ' (v+targetError) hBottom
  let η := homotopyRegrade (show W-S+1=B-A by dsimp [S,W,A,B];omega)
    (show (W-L)+1=t+1 by dsimp [W];omega)
    (positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (W-S+1) (W-L) ζ')
  have hηcal : η≫(background.quotients.tower _).rho (a+1) L haL=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A B (t+1) (by dsimp [B];omega) (y+sourceError) := by
    dsimp only [η]
    rw [←regrade_comp,positive_finite_image_restriction T hf (a+1) L (by omega),hρ,
      ←positive_finite_image_restriction T hf (a+1) L (by omega)]
    have h := congrArg (homotopyRegrade (rfl : B-A=B-A) (show B-a=t+1 by dsimp [B];omega)) hcal
    simpa only [←regrade_comp,normalized_homotopy_regrade_trans,finiteTopLabelAtWeight] using h
  have hηtop : homotopyRegrade
      (show (B-A)-1=((W+1)+b)-(S+b+1) by dsimp [S,W,A,B];omega)
      (show (t+1)+L=((W+1)+b)-b by dsimp [W];omega)
      (biSuspensionHomEquiv (B-A) (t+1) L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ L)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel T.Y b hb (S+b+1) ((W+1)+b) (v+targetError) := by
    simpa only [η,←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans] using hBoundaryTop
  have hzero : (background.classical.map T.g).pageMap 2 (S+b+1,(W+1)+b) targetError=0 := by
    have h := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY T hf hg hh (S+b) (W+b)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+b) (W+b) eb)).mpr ⟨eb,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p') (u : Ambient background T.Y p) (v : Ambient background T.Y p')
        (huv : HEq u v) (hv : (background.classical.map T.g).pageMap 2 p' v=0) :
        (background.classical.map T.g).pageMap 2 p u=0 := by
      subst p'; cases eq_of_heq huv; exact hv
    exact transport _ _ (by congr 1;omega) _ _ heBottom h
  exact synchronized_finite_differential_at_weight_and_degree T.Y L a (a+1) b hb ha (by omega) rfl
    A B (t+1) 1 (S+b+1) ((W+1)+b) (by dsimp [B];omega)
    (by dsimp [A,S];omega) (by dsimp [B,W];omega) (y+sourceError) y sourceError
    (by rw [add_sub_cancel_left,sub_self]; exact (boundaries background T.Y 1 _).zero_mem)
    hsourceError η hηcal v targetError P hP hv (fun he => hker targetError he hzero) hηtop

end
end KIP126.ProofTools.Internal.SyntheticCoverage
