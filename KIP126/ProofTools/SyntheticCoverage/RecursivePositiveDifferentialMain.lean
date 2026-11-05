module

public import KIP126.ProofTools.SyntheticCoverage.RecursivePermanence

public import KIP126.ProofTools.SyntheticCoverage.RecursiveDifferentialMain

public import KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential

public import KIP126.ProofTools.SyntheticCoverage.PositivePermanence

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.RecursiveDifferentialMain
import all KIP126.ProofTools.SyntheticCoverage.RecursivePositiveCoordinates
import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferentialMain

/-! The original bottom three-layer criterion for the positive first arrow.
The finite source and bottom common representative are constructed from the
original differentials. All relation members and true finite boundary
cutoffs are retained. -/

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
set_option maxHeartbeats 3000000

private theorem recursive_positive_boundary_top_from_coordinates
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (p t : ℤ)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (v : Ambient background T.Y (p+1+1,(t+1)+1))
    (hi : recursivePositiveImage T hf p t
      (((recursivePositiveBoundaryIso N p t).hom≫recursiveBoundaryRepresentative T.X N p t ζ)≫
        XModLambdaN.incl _ 3)=recursivePositiveTopLabel T.Y p t v) :
    homotopyRegrade (show (t-p+1)-1=((t+1)+1)-(p+1+1) by omega)
      (show ((t-1-N)+1)+N=((t+1)+1)-2 by omega)
      (biSuspensionHomEquiv (t-p+1) ((t-1-N)+1) N
        (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-p+1) (t-1-N) ζ≫
          XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel T.Y 2 (by decide) (p+1+1) ((t+1)+1) v := by
  have h := congrArg (homotopyRegrade (show t-p=((t+1)+1)-(p+1+1) by omega)
    (show t=((t+1)+1)-2 by omega))
    ((recursive_positive_boundary_square T hf N p t ζ).symm.trans hi)
  simpa only [recursivePositiveTopLabel,last_layer_regrade_trans,top_target_regrade_self] using h

/-- The recursive differential criterion with positive first arrow and upper
length one. -/
public theorem recursive_differential_positive_first_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s+1,t+1))
    (hyF : y=KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x)
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1))
    (z₂ : Ambient background T.Z (s+N+1,(t+N)+1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+N+1) ((t+N)+1)
      ((background.classical.map T.h).pageMap 2 (s+N+1,(t+N)+1) z₂) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      (s+N+1,(t+N)+1) (((s+N+1)+1)+1+1,((t+N+1)+1)+1) z₂
      ((background.classical.map T.g).pageMap 2 (((s+N+1)+1)+1+1,((t+N+1)+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X ((s+N+1)+1,t+N+1)))
    (_hK₀ : K₀≤cycles background T.X 2 ((s+N+1)+1,t+N+1) ⊓
      LinearMap.ker (positiveFirstOperationLinear T hf ((s+N+1)+1) (t+N+1)))
    (Pm B : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1)))
    (hPm : permanentCycles background T.Y (((s+N+1)+1)+1,(t+N+1)+1)≤Pm)
    (hB : boundaries background T.Y ((N:ℤ)+1) (((s+N+1)+1)+1,(t+N+1)+1)≤B)
    (hmid : RecursiveDifferentialFMiddle T hf N 1 ((s+N+1)+1) (t+N+1) Pm B K₀)
    (hsurj : RecursivePositiveFSurjective T ((s+N+1)+1) (t+N+1) K₀)
    (hy : y∈cycles background T.Y (N+2:ℕ) (s+1,t+1))
    (P : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1)))
    (hP : permanentCycles background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialFTerminal T hf ((N+2:ℕ)+1)
      ((s+N+1)+1) (t+N+1) K₀ P) :
    IsCycle background T.Y (N+2:ℕ) (s+1,t+1) y ∧
      IsCycle background T.Y (N+2:ℕ) (((s+N+1)+1)+1+1,((t+N+1)+1)+1) v ∧
      DifferentialAt background T.Y ((N+2:ℕ)+1) (s+1,t+1)
        (((s+N+1)+1)+1+1,((t+N+1)+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN s t x u).mp hdx
  obtain ⟨c,hcfirst,hci⟩ := finite_common_native_lift_positive_f_at T he hT hf hg hh
    2 (by decide) (s+N+1) (t+N) (((s+N+1)+1)+1+1) (((t+N+1)+1)+1)
    (by omega) (by omega) z₂ u v hu hdz
  let p := (s+N+1)+1
  let w := t+N+1
  let ζm := homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
    (show t=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (t+N)-(s+N+1)=w-p by dsimp [p,w];omega)
    (show t+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N s t p w
    (by dsimp [p];omega) rfl ζ
  have hsame : ((recursivePositiveBoundaryIso N p w).hom≫recursiveBoundaryRepresentative T.X N p w ζm)≫
      XModLambdaN.incl _ 1=cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [recursive_positive_boundary_first,hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N s t ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : recursivePositiveImage T hf p w cm=recursivePositiveTopLabel T.Y p w v := by
    dsimp only [cm,recursivePositiveImage,recursivePositiveTopLabel]
    rw [←positiveFiniteImage_regrade,hci,last_layer_regrade_trans,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=(t+1)-(s+1) by dsimp [p,w];omega)
      (show (w-1-N)+1=t+1 by dsimp [w];omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (w-p+1) (w-1-N) ζm))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y (s+1) (t+1) y := by
    dsimp only [ζm]
    rw [←positiveFiniteImage_regrade,last_layer_regrade_trans,←regrade_comp,
      positive_finite_image_restriction T hf 1 N (by decide) hN,hζ]
    rw [hyF]
    exact positive_finite_image_native_first T hf s t x
  have hgate (a : Ambient background T.X (p,w))
      (ha : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a)
        (((recursivePositiveBoundaryIso N p w).hom≫recursiveBoundaryRepresentative T.X N p w ζm)≫
          XModLambdaN.incl _ 3-cm)) :
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p w a∈B :=
    hB (recursive_positive_first_head_gate T hf N hN p w (s+1) (t+1)
      (by dsimp [p];omega) (by dsimp [w];omega) ζm y
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hy) hsource cm v hcm a ha)
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_f_relation_image_of_head_gate
    T he hT hf hg hh N 1 (by decide) hN p w K₀ Pm B hPm hmid hsurj
    (recursivePositiveBoundaryIso N p w) ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=(t+1)-(s+1) by dsimp [p,w];omega)
    (show (w-1-N)+1=t+1 by dsimp [w];omega)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (w-p+1) (w-1-N) ζ')
  have hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y (s+1) (t+1) y := by
    dsimp only [η]
    rw [←regrade_comp,recursive_positive_protected_image T hf 1 N (by decide) hN _ _ ζ' ζm hρ]
    simpa only [regrade_comp] using hsource
  have htop₀ := recursive_positive_boundary_top_from_coordinates T hf N p w ζ' _ hi
  have htop : homotopyRegrade
      (show ((t+1)-(s+1))-1=((w+1)+1)-(p+1+1) by dsimp [p,w];omega)
      (show (t+1)+N=((w+1)+1)-2 by dsimp [w];omega)
      (biSuspensionHomEquiv ((t+1)-(s+1)) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel T.Y 2 (by decide) (p+1+1) ((w+1)+1)
        (v+z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (p+1) (w+1) e) := by
    simpa only [η,←regrade_comp,bi_susp_regrade,last_layer_regrade_trans] using htop₀
  exact recursive_first_differential_at_degree T.Y N hN (s+1) (t+1) (p+1+1) ((w+1)+1)
    (by dsimp [p];omega) (by dsimp [w];omega) y η hfirst v z
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (p+1) (w+1) e) P hP hv
    (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htop

/-- The recursive differential criterion with positive first arrow and a
genuine finite upper fold. The complete upper middle conditions and correction-image survival
are retained, and the independent survival input refers to the original y. -/
public theorem recursive_differential_positive_first_finite_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 0<q) (hqN : q+1≤N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (z₁ : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+q+1,(t+1)+q))
    (_hFx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x=0)
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z₁) (by simpa using x))
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t+1) (s+q+1,(t+1)+q) z₁
      ((background.classical.map T.g).pageMap 2 (s+q+1,(t+1)+q) y))
    (htop : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (s+j,t+j),
        a∈cycles background T.X (((q+1:ℕ):ℤ)-j) (s+j,t+j) →
        ∃ z' : Ambient background T.Z (s+j,t+j+1),
          z'∈cycles background T.Z (((q+1:ℕ):ℤ)-j) (s+j,t+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+j) (t+j) z'∈
            boundaries background T.X ((j:ℤ)+1) (s+j,t+j))
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1))
    (z₂ : Ambient background T.Z (s+N+1,(t+N)+1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+N+1) ((t+N)+1)
      ((background.classical.map T.h).pageMap 2 (s+N+1,(t+N)+1) z₂) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      (s+N+1,(t+N)+1) (((s+N+1)+1)+1+1,((t+N+1)+1)+1) z₂
      ((background.classical.map T.g).pageMap 2 (((s+N+1)+1)+1+1,((t+N+1)+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X ((s+N+1)+1,t+N+1)))
    (_hK₀ : K₀≤cycles background T.X 2 ((s+N+1)+1,t+N+1) ⊓
      LinearMap.ker (positiveFirstOperationLinear T hf ((s+N+1)+1) (t+N+1)))
    (Pm B : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1)))
    (hPm : permanentCycles background T.Y (((s+N+1)+1)+1,(t+N+1)+1)≤Pm)
    (hB : boundaries background T.Y ((N-q:ℕ)+1) (((s+N+1)+1)+1,(t+N+1)+1)≤B)
    (hmid : RecursiveDifferentialFMiddle T hf N (q+1) ((s+N+1)+1) (t+N+1) Pm B K₀)
    (hsurj : RecursivePositiveFSurjective T ((s+N+1)+1) (t+N+1) K₀)
    (himage : ∀ e : Ambient background T.X (s+q,t+q),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e∈
        cycles background T.Y ((N+2-q:ℕ)+1) (s+q+1,(t+q)+1))
    (hy : y∈cycles background T.Y (N+2-q:ℕ) (s+q+1,(t+1)+q))
    (P : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1)))
    (hP : permanentCycles background T.Y (((s+N+1)+1)+1+1,((t+N+1)+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialFTerminal T hf ((N+2-q:ℕ)+1)
      ((s+N+1)+1) (t+N+1) K₀ P) :
    IsCycle background T.Y (N+2-q:ℕ) (s+q+1,(t+1)+q) y ∧
      IsCycle background T.Y (N+2-q:ℕ) (((s+N+1)+1)+1+1,((t+N+1)+1)+1) v ∧
      DifferentialAt background T.Y ((N+2-q:ℕ)+1) (s+q+1,(t+1)+q)
        (((s+N+1)+1)+1+1,((t+N+1)+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hN : 0<N := by omega
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN s t x u).mp hdx
  obtain ⟨etop,error,herror,ht⟩ := positive_source_finite_top_restriction
    T he hT hf hg hh q N hq hqN s t x z₁ y hxz hdz₁ htop ζ hζ
  let A := s+q+1
  let V := (t+1)+q
  let ytop := y+error
  have hecycle : error∈cycles background T.Y ((N+2-q:ℕ)+1) (A,V) := by
    have h := classical_cycle_heq T.Y ((N+2-q:ℕ)+1)
      (show (s+q+1,(t+q)+1)=(A,V) by dsimp only [A,V]; congr 1; omega)
      _ error herror.symm ⟨by omega,himage etop⟩
    exact h.2
  have ht' : homotopyRegrade (show t-s=V-A by dsimp [A,V];omega) rfl
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ≫
        (background.quotients.tower _).rho (q+1) N hqN)=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl A V (t+1) (by dsimp [V];omega) ytop := by
    have transport (M : ℕ) (hM : 0+(q+1)=M) :
        homotopyRegrade (show t-s=V-A by dsimp [A,V];omega) rfl
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ≫
            (background.quotients.tower _).rho M N (by omega))=
        finiteTopLabelAtWeight T.Y (0+q) (by omega) M (by omega) A V (t+1)
          (by dsimp [V];omega) ytop := by
      subst M
      exact ht
    simpa only [Nat.zero_add] using transport (q+1) (by omega)
  have hytop : ytop∈cycles background T.Y ((N-q:ℕ)+2) (A,V) := by
    have hindex : ((N-q:ℕ):ℤ)+2=(N+2-q:ℕ) := by omega
    rw [hindex]
    exact (cycles background T.Y (N+2-q:ℕ) (A,V)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) hecycle)
  obtain ⟨c,hcfirst,hci⟩ := finite_common_native_lift_positive_f_at T he hT hf hg hh
    2 (by decide) (s+N+1) (t+N) (((s+N+1)+1)+1+1) (((t+N+1)+1)+1)
    (by omega) (by omega) z₂ u v hu hdz
  let p := (s+N+1)+1
  let w := t+N+1
  let ζm := homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
    (show t=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (t+N)-(s+N+1)=w-p by dsimp [p,w];omega)
    (show t+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N s t p w
    (by dsimp [p];omega) rfl ζ
  have hsame : ((recursivePositiveBoundaryIso N p w).hom≫recursiveBoundaryRepresentative T.X N p w ζm)≫
      XModLambdaN.incl _ 1=cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [recursive_positive_boundary_first,hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N s t ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : recursivePositiveImage T hf p w cm=recursivePositiveTopLabel T.Y p w v := by
    dsimp only [cm,recursivePositiveImage,recursivePositiveTopLabel]
    rw [←positiveFiniteImage_regrade,hci,last_layer_regrade_trans,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
      (show (w-1-N)+1=V-q by dsimp [w,V];omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (w-p+1) (w-1-N) ζm))≫
      (background.quotients.tower _).rho (q+1) N hqN=finiteTopLabel T.Y q hq A V ytop := by
    have h := congrArg (homotopyRegrade (rfl : V-A=V-A) (show t+1=V-q by dsimp [V];omega)) ht'
    dsimp only [ζm]
    simpa only [←positiveFiniteImage_regrade,←regrade_comp,last_layer_regrade_trans,
      finiteTopLabelAtWeight,top_target_regrade_self] using h
  have hgate (a : Ambient background T.X (p,w))
      (ha : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a)
        (((recursivePositiveBoundaryIso N p w).hom≫recursiveBoundaryRepresentative T.X N p w ζm)≫
          XModLambdaN.incl _ 3-cm)) :
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p w a∈B :=
    hB (recursive_positive_divided_head_gate T hf q N hq (by omega) p w A V
      (by dsimp [p,A];omega) (by dsimp [w,V];omega) ζm ytop hytop hsource cm v hcm a ha)
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_f_relation_image_of_head_gate
    T he hT hf hg hh N (q+1) (by omega) hqN p w K₀ Pm B hPm hmid hsurj
    (recursivePositiveBoundaryIso N p w) ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
    (show (w-1-N)+1=V-q by dsimp [w,V];omega)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (w-p+1) (w-1-N) ζ')
  have hcalibration : η≫(background.quotients.tower _).rho (q+1) N hqN=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl A V (V-q) rfl ytop := by
    dsimp only [η]
    rw [←regrade_comp,recursive_positive_protected_image T hf (q+1) N (by omega) hqN _ _ ζ' ζm hρ]
    simpa only [regrade_comp,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have htop₀ := recursive_positive_boundary_top_from_coordinates T hf N p w ζ' _ hi
  have htopfin : homotopyRegrade
      (show (V-A)-1=((w+1)+1)-(p+1+1) by dsimp [p,w,A,V];omega)
      (show (V-q)+N=((w+1)+1)-2 by dsimp [w,V];omega)
      (biSuspensionHomEquiv (V-A) (V-q) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel T.Y 2 (by decide) (p+1+1) ((w+1)+1)
        (v+z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (p+1) (w+1) e) := by
    simpa only [η,←regrade_comp,bi_susp_regrade,last_layer_regrade_trans] using htop₀
  exact recursive_finite_differential_at_weight_and_degree T.Y N q (q+1) hq (by omega) rfl
    A V (V-q) (q+1) (p+1+1) ((w+1)+1) rfl
    (by dsimp [p,A];omega) (by dsimp [w,V];omega)
    ytop y error
    (by dsimp only [ytop]; have hz : y+error-y-error=0 := by abel
        rw [hz]; exact (boundaries background T.Y _ _).zero_mem)
    hecycle η hcalibration v z
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (p+1) (w+1) e)
    P hP hv (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htopfin

end
end KIP126.ProofTools.Internal.SyntheticCoverage
