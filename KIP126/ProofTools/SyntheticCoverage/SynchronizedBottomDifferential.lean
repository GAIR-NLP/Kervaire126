module

import all KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential
import all KIP126.ProofTools.SyntheticCoverage.KnownSourceOrdinary
import all KIP126.ProofTools.SyntheticCoverage.SynchronizedBottomElimination

/-! Final differential comparisons after synchronous source-boundary
corrections, with the complete protected upper calibration retained. -/

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

private theorem synchronized_terminal_target_early_boundary
    (Y : (AdamsObject (coefficients := background.coefficients))) (b : ℕ) (D : ℤ) (hD : (b:ℤ)+2≤D) (p : Bidegree)
    (P : Submodule ℤ (Ambient background Y p)) (hP : permanentCycles background Y p≤P)
    (w v error : Ambient background Y p)
    (hw : w∈permanentCycles background Y p) (hv : v∈P)
    (herr : w-(v+error)∈boundaries background Y (b+1) p)
    (hterminal : error∈P → error∈boundaries background Y (D-1) p) :
    w-v∈boundaries background Y (D-1) p := by
  have hbP := hP (finalBoundaries_le_permanentCycles Y p
    (boundaries_le_finalBoundaries Y p (b+1) herr))
  have hsumP : error∈P := by
    have h := P.sub_mem (P.sub_mem (hP hw) hv) hbP
    convert h using 1
    abel
  have hb := boundaries_monotone background Y p (by omega : (b+1:ℕ)≤D-1) herr
  have h := (boundaries background Y (D-1) p).add_mem hb (hterminal hsumP)
  convert h using 1
  abel

/-- After the synchronized finite comparison, the original protected top
calibration produces d_D. The original source error is removed using its
independent next-page survival and a genuine source boundary. -/
private theorem synchronized_finite_differential_of_top
    (Y : (AdamsObject (coefficients := background.coefficients))) (N d b : ℕ) (hb : 0<b) (hd : 0<d) (hdN : d<N) (s t B : ℤ)
    (x y sourceError : Ambient background Y (s,t))
    (hsourceError : x-y-sourceError∈boundaries background Y B (s,t))
    (hsourceSurvives : sourceError∈cycles background Y ((N+b-d:ℕ)+1) (s,t))
    (η : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hcalibration : η≫(background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabel Y d hd s t x)
    (v targetError : Ambient background Y (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ)))
    (P : Submodule ℤ (Ambient background Y (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ))))
    (hP : permanentCycles background Y (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ))≤P)
    (hv : v∈P)
    (hterminal : targetError∈P → targetError∈boundaries background Y
      (N+b-d:ℕ) (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ)))
    (htop : homotopyRegrade
      (show (t-s)-1=(t+(N+b-d:ℕ))-(s+(N+b-d:ℕ)+1) by omega)
      (show (t-d)+N=(t+(N+b-d:ℕ))-b by omega)
      (biSuspensionHomEquiv (t-s) (t-d) N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel Y b hb (s+(N+b-d:ℕ)+1) (t+(N+b-d:ℕ))
        (v+targetError)) :
    IsCycle background Y (N+b-d:ℕ) (s,t) y ∧
      IsCycle background Y (N+b-d:ℕ) (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ)) v ∧
      DifferentialAt background Y ((N+b-d:ℕ)+1) (s,t)
        (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ)) y v := by
  obtain ⟨η',w,hρ,hfirst,hwp,hbound⟩ := finite_extension_of_boundary_top Y N b
    (by omega) hb (t-s) (t-d) (s+(N+b-d:ℕ)+1) (t+(N+b-d:ℕ))
    (by omega) (by omega) η (v+targetError) htop
  have hcalibration' : η'≫(background.quotients.tower _).rho (d+1) (N+b) (by omega)=
      finiteTopLabel Y d hd s t x := by
    rw [←(background.quotients.tower _).rho_comp (show d+1≤N by omega) (show N≤N+b by omega),
      ←Category.assoc,hρ,hcalibration]
  have hdifferential := finite_source_differential_of_top_restriction Y d (N+b) hd (by omega)
    s t x w η' hcalibration' hfirst
  have hwv := synchronized_terminal_target_early_boundary Y b ((N+b-d:ℕ)+1) (by omega)
    _ P hP w v targetError hwp hv hbound (by simpa only [add_sub_cancel_right] using hterminal)
  have h := differential_of_source_correction Y ((N+b-d:ℕ)+1) B (s,t)
    (s+(N+b-d:ℕ)+1,t+(N+b-d:ℕ)) x y sourceError w v hdifferential
      hsourceError hsourceSurvives hwv
  simpa only [add_sub_cancel_right] using h

/-- The K1=1 endpoint uses the original ordinary first source label, with
no artificial positive coefficient division. -/
private theorem synchronized_first_differential_of_top
    (Y : (AdamsObject (coefficients := background.coefficients))) (N b : ℕ) (hN : 0<N) (hb : 0<b) (s t : ℤ)
    (y : Ambient background Y (s,t))
    (η : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y s t y)
    (v targetError : Ambient background Y (s+(N+b:ℕ)+1,t+(N+b:ℕ)))
    (P : Submodule ℤ (Ambient background Y (s+(N+b:ℕ)+1,t+(N+b:ℕ))))
    (hP : permanentCycles background Y (s+(N+b:ℕ)+1,t+(N+b:ℕ))≤P) (hv : v∈P)
    (hterminal : targetError∈P → targetError∈boundaries background Y
      (N+b:ℕ) (s+(N+b:ℕ)+1,t+(N+b:ℕ)))
    (htop : homotopyRegrade
      (show (t-s)-1=(t+(N+b:ℕ))-(s+(N+b:ℕ)+1) by omega)
      (show t+N=(t+(N+b:ℕ))-b by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel Y b hb (s+(N+b:ℕ)+1) (t+(N+b:ℕ)) (v+targetError)) :
    IsCycle background Y (N+b:ℕ) (s,t) y ∧
      IsCycle background Y (N+b:ℕ) (s+(N+b:ℕ)+1,t+(N+b:ℕ)) v ∧
      DifferentialAt background Y ((N+b:ℕ)+1) (s,t)
        (s+(N+b:ℕ)+1,t+(N+b:ℕ)) y v := by
  obtain ⟨η',w,hρ,hw,hwp,hbound⟩ := finite_extension_of_boundary_top Y N b hN hb
    (t-s) t (s+(N+b:ℕ)+1) (t+(N+b:ℕ)) (by omega) (by omega) η _ htop
  have hη' : η'≫(background.quotients.tower _).rho 1 (N+b) (by omega)=nativeFirstLabel Y s t y := by
    rw [←(background.quotients.tower _).rho_comp hN (show N≤N+b by omega),←Category.assoc,hρ,hfirst]
  have hdifferential : DifferentialAt background Y ((N+b:ℕ)+1) (s,t)
      (s+(N+b:ℕ)+1,t+(N+b:ℕ)) y w := by
    refine ⟨by omega,adjacent_boundary_differential Y (N+b) (by omega) s t y w η' hη' ?_⟩
    exact hw
  have hwv := synchronized_terminal_target_early_boundary Y b ((N+b:ℕ)+1) (by omega)
    _ P hP w v targetError hwp hv hbound (by simpa only [add_sub_cancel_right] using hterminal)
  have h := differential_of_source_correction Y ((N+b:ℕ)+1) 1 (s,t)
    (s+(N+b:ℕ)+1,t+(N+b:ℕ)) y y 0 w v hdifferential
    (by simp) (by exact (cycles background Y ((N+b:ℕ)+1) (s,t)).zero_mem) hwv
  simpa only [add_sub_cancel_right] using h


private theorem synchronized_finite_differential_at_weight_and_degree
    (Y : (AdamsObject (coefficients := background.coefficients))) (N d M b : ℕ) (hb : 0<b) (hd : 0<d) (hdN : d<N) (hM : d+1=M)
    (s t w B A V : ℤ) (hw : t-d=w)
    (hA : A=s+(N+b-d:ℕ)+1) (hV : V=t+(N+b-d:ℕ))
    (x y sourceError : Ambient background Y (s,t))
    (hsourceError : x-y-sourceError∈boundaries background Y B (s,t))
    (hsourceSurvives : sourceError∈cycles background Y ((N+b-d:ℕ)+1) (s,t))
    (η : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hcalibration : η≫(background.quotients.tower _).rho M N (by omega)=
      finiteTopLabelAtWeight Y d hd M hM s t w hw x)
    (v targetError : Ambient background Y (A,V))
    (P : Submodule ℤ (Ambient background Y (A,V)))
    (hP : permanentCycles background Y (A,V)≤P) (hv : v∈P)
    (hterminal : targetError∈P → targetError∈boundaries background Y (N+b-d:ℕ) (A,V))
    (htop : homotopyRegrade
      (show (t-s)-1=V-A by omega) (show w+N=V-b by omega)
      (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel Y b hb A V (v+targetError)) :
    IsCycle background Y (N+b-d:ℕ) (s,t) y ∧ IsCycle background Y (N+b-d:ℕ) (A,V) v ∧
      DifferentialAt background Y ((N+b-d:ℕ)+1) (s,t) (A,V) y v := by
  subst M; subst w; subst A; subst V
  apply synchronized_finite_differential_of_top Y N d b hb hd hdN s t B
    x y sourceError hsourceError hsourceSurvives η _ v targetError P hP hv hterminal htop
  simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using hcalibration

private theorem synchronized_first_differential_at_degree
    (Y : (AdamsObject (coefficients := background.coefficients))) (N b : ℕ) (hN : 0<N) (hb : 0<b) (s t A V : ℤ)
    (hA : A=s+(N+b:ℕ)+1) (hV : V=t+(N+b:ℕ))
    (y : Ambient background Y (s,t))
    (η : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y s t y)
    (v targetError : Ambient background Y (A,V))
    (P : Submodule ℤ (Ambient background Y (A,V)))
    (hP : permanentCycles background Y (A,V)≤P) (hv : v∈P)
    (hterminal : targetError∈P → targetError∈boundaries background Y (N+b:ℕ) (A,V))
    (htop : homotopyRegrade
      (show (t-s)-1=V-A by omega) (show t+N=V-b by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel Y b hb A V (v+targetError)) :
    IsCycle background Y (N+b:ℕ) (s,t) y ∧ IsCycle background Y (N+b:ℕ) (A,V) v ∧
      DifferentialAt background Y ((N+b:ℕ)+1) (s,t) (A,V) y v := by
  subst A; subst V
  exact synchronized_first_differential_of_top Y N b hN hb s t y η hfirst
    v targetError P hP hv hterminal htop


private theorem synchronized_adjacent_boundary_coordinates
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t S W : ℤ)
    (hS : S=s+N+1) (hW : W=t+N)
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedBoundary X N S W
      (homotopyRegrade (show t-s=W-S+1 by omega) (show t=W-N by omega) ζ)=
      homotopyRegrade (show (t+N)-(s+N+1)=W-S by omega) hW.symm
        (boundaryRepresentative X N s t ζ) := by
  simp only [synchronizedBoundary,boundaryRepresentative,
    source_boundary_regrade,last_layer_regrade_trans]

private theorem synchronized_boundary_top_from_coordinates
    (Y : (AdamsObject (coefficients := background.coefficients))) (N b : ℕ) (hb : 0<b) (m w S W A B : ℤ)
    (hm : m-1=W-S) (hw : w+N=W) (hA : A=S+b) (hB : B=W+b)
    (η : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (v : Ambient background Y (A,B))
    (htop : homotopyRegrade (show W-S=B-A by omega) rfl
        (synchronizedBoundary Y N S W
          (homotopyRegrade (show m=W-S+1 by omega) (show w=W-N by omega) η)≫
          XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight Y b hb (b+1) rfl A B W (by omega) v) :
    homotopyRegrade (show m-1=B-A by omega) (show w+N=B-b by omega)
      (biSuspensionHomEquiv m w N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabel Y b hb A B v := by
  have h := congrArg (homotopyRegrade (rfl : B-A=B-A) (show W=B-b by omega)) htop
  simpa only [synchronizedBoundary,source_boundary_regrade,
    ←regrade_comp,bi_susp_regrade,last_layer_regrade_trans,
    finiteTopLabelAtWeight,top_target_regrade_self] using h

private def synchronizedAdjacentSource
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    BiHom ((t+N)-(s+N+1)+1) ((t+N)-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) :=
  homotopyRegrade (by omega) (by omega) ζ

private theorem synchronized_adjacent_source_boundary
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t : ℤ)
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedBoundary X N (s+N+1) (t+N) (synchronizedAdjacentSource X N s t ζ)=
      boundaryRepresentative X N s t ζ := by
  simpa only [synchronizedAdjacentSource,top_target_regrade_self] using
    synchronized_adjacent_boundary_coordinates X N s t (s+N+1) (t+N) rfl rfl ζ

private theorem synchronized_initial_residual_filtration
    (X : (AdamsObject (coefficients := background.coefficients))) (N b : ℕ) (_hN : 0<N) (hb : 0<b) (s t : ℤ)
    (u : Ambient background X (s+N+1,t+N))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hU : adjacentBoundaryLabel X N s t ζ=nativeFirstLabel X (s+N+1) (t+N) u)
    (c : BiHom ((t+N)-(s+N+1)) (t+N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (b+1)))
    (hc : c≫(background.quotients.tower _).rho 1 (b+1) (by omega)=
      nativeFirstLabel X (s+N+1) (t+N) u) :
    FiltrationAtLeast background.syntheticTower ((s+N+1)+1)
      (synchronizedBoundary X N (s+N+1) (t+N) (synchronizedAdjacentSource X N s t ζ)≫
        XModLambdaN.incl _ (b+1)-c) := by
  rw [synchronized_adjacent_source_boundary]
  have ha : (boundaryRepresentative X N s t ζ≫XModLambdaN.incl _ (b+1))≫
      (background.quotients.tower _).rho 1 (b+1) (by omega)=
      nativeFirstLabel X (s+N+1) (t+N) u := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient]
    exact hU
  exact detects_sub_filtration (background.convergence (.quotient (b+1) (.nu X)))
    (s+N+1,t+N,t+N)
    (first_label_detects_unshifted X (b+1) (by omega) (s+N+1) (t+N) u _ ha)
    (first_label_detects_unshifted X (b+1) (by omega) (s+N+1) (t+N) u c hc)

private theorem synchronized_common_top_filtration
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (b : ℕ) (hb : 0<b) (S W A B : ℤ) (hA : A=S+b) (hB : B=W+b)
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (b+1)))
    (v : Ambient background Y (A,B))
    (hc : c≫XModLambdaN.map (background.nu.functor.map f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega)
        (finiteTopLabel Y b hb A B v)) :
    FiltrationAtLeast background.syntheticTower (S+b)
      (c≫XModLambdaN.map (background.nu.functor.map f) (b+1)) := by
  rw [hc]
  apply (regrade_filtration_iff _ _ _ _).mpr
  have h := KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (b+1) (.nu Y))
    (A,B,B-b) _ _ (finiteTopLabel_detects Y b hb A B v)
  simpa only [hA] using h

/-- Original known-source criterion with synchronous early source-boundary corrections. -/
private theorem synchronized_known_source_differential_ordinary_second_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (b L : ℕ) (hb : 0 < b) (hL : 0 < L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (y : Ambient background T.Y (B+1,W))
    (hyF : y=(background.classical.map T.f).pageMap 2 (B+1,W) x)
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L)+1,(W+L)+1))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      ((background.classical.map T.h).pageMap 2 (((B+1)+L)+1,(W+L)+1) z₂) (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L)+1,(W+L)+1) ((((B+1)+L)+b+1)+1,((W+L)+b)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j,(W+L)+j+1),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j+1) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j) ((W+L)+j+1)
            ((background.classical.map T.h).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j+1) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((L:ℤ)+j) ((((B+1)+L)+1)+j,(W+L)+j))
    (hy : y ∈ cycles background T.Y (L+b:ℕ) (B+1,W))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b:ℕ) (B+1,W) y ∧
      IsCycle background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b:ℕ)+1) (B+1,W) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  obtain ⟨c,hcfirst,hci⟩ := finite_common_lift_positive_g T he hT hf hg hh
    b hb ((B+1)+L) (W+L) z₂ u v huz hdz₂
  let S := ((B+1)+L)+1
  let Wm := W+L
  let ζm := synchronizedAdjacentSource T.X L (B+1) W ζ
  have hstart := synchronized_initial_residual_filtration T.X L b (by omega) hb
    (B+1) W u ζ hU c hcfirst
  have hcfil := synchronized_common_top_filtration T.X T.Y T.f b hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl c v hci
  have hsource : (homotopyRegrade (show Wm-S+1=W-(B+1) by dsimp [S,Wm];omega)
      (show Wm-L=W by dsimp [Wm];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) L))≫
      (background.quotients.tower _).rho 1 L (by omega)=nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [ζm,synchronizedAdjacentSource]
    simp only [←regrade_comp,last_layer_regrade_trans,top_target_regrade_self]
    rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  have hgate := synchronized_ordinary_first_protected_gate T.X T.Y T.f L b hL hb
    S Wm (B+1) W ((L+b:ℕ)+1) rfl rfl (by omega) ζm y
    (by simpa only [add_sub_cancel_right] using hy) hsource c hcfil Pm
    (by simpa only [Nat.cast_add] using hPm)
  obtain ⟨ζ',e,hρ,_,htop⟩ := synchronized_ordinary_full_image_g
    T he hf hg hh hT L 1 b (by omega) hL hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl ζm c hstart v hci Pm hgate (by
      intro j hj hjb x' hx' hfx'
      have hlevel : ((b+1-j:ℕ):ℤ)=((b+1:ℕ):ℤ)-j := by omega
      obtain ⟨z',hz',u',hu',hbound⟩ := hbottom j hj hjb x' (by simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hx') hfx'
      refine ⟨z',?_,u',?_,?_⟩
      · simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hz'
      · simpa only [sub_add_cancel] using hu'
      · exact boundaries_monotone background T.X _ (by omega) hbound)
  let η := homotopyRegrade (show Wm-S+1=W-(B+1) by dsimp [S,Wm];omega)
    (show Wm-L=W by dsimp [Wm];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) L)
  have hcalibration : η≫(background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f 1 L hL _ _ ζ' ζm hρ]
    simpa only [regrade_comp] using hsource
  have htopm : homotopyRegrade (show Wm-S=((W+L)+b)-(((B+1)+L)+b+1) by dsimp [S,Wm];omega) rfl
      (synchronizedBoundary T.Y L S Wm
        (homotopyRegrade (show W-(B+1)=Wm-S+1 by dsimp [S,Wm];omega)
          (show W=Wm-L by dsimp [Wm];omega) η)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl (((B+1)+L)+b+1) ((W+L)+b) Wm
        (by dsimp [Wm];omega)
        (v+(background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,synchronized_boundary_natural]
    exact htop
  have htop' := synchronized_boundary_top_from_coordinates T.Y L b hb (W-(B+1)) W
    S Wm (((B+1)+L)+b+1) ((W+L)+b)
    (by dsimp [S,Wm];omega) rfl
    (by dsimp [S];omega) rfl η _ htopm
  exact synchronized_first_differential_at_degree T.Y L b hL hb (B+1) W
    (((B+1)+L)+b+1) ((W+L)+b) (by omega) (by omega) y η hcalibration
    v ((background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e)
    P hP hv (fun heP => hker _ heP (positive_second_triangle_composite_zero T hf hg hh hT (((B+1)+L)+b+1) ((W+L)+b) e)) htop'

/-- Original known-source criterion with synchronous early source-boundary corrections. -/
private theorem synchronized_known_source_differential_ordinary_third_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (b L : ℕ) (hb : 0 < b) (hL : 0 < L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (y : Ambient background T.Y (B+1,W))
    (hyF : y=(background.classical.map T.f).pageMap 2 (B+1,W) x)
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L),(W+L)))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) ((B+1)+L) (W+L) z₂)
      (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L),(W+L)) (((B+1)+L)+b+1,(W+L)+b) z₂
      ((background.classical.map T.g).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1,(W+L)+j),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1,(W+L)+j) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((((B+1)+L)+1)+j-1) ((W+L)+j) z₂) (by simpa only [sub_add_cancel,add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((L:ℤ)+j) ((((B+1)+L)+1)+j,(W+L)+j))
    (hy : y ∈ cycles background T.Y (L+b:ℕ) (B+1,W))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, (background.classical.map T.g).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) z = 0 →
      z ∈ boundaries background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b:ℕ) (B+1,W) y ∧
      IsCycle background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b:ℕ)+1) (B+1,W) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  obtain ⟨c,hcfirst,hci⟩ := finite_common_lift_positive_h T he hT hf hg hh
    b hb ((B+1)+L) (W+L) z₂ u v huz hdz₂
  let S := ((B+1)+L)+1
  let Wm := W+L
  let ζm := synchronizedAdjacentSource T.X L (B+1) W ζ
  have hstart := synchronized_initial_residual_filtration T.X L b (by omega) hb
    (B+1) W u ζ hU c hcfirst
  have hcfil := synchronized_common_top_filtration T.X T.Y T.f b hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl c v hci
  have hsource : (homotopyRegrade (show Wm-S+1=W-(B+1) by dsimp [S,Wm];omega)
      (show Wm-L=W by dsimp [Wm];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) L))≫
      (background.quotients.tower _).rho 1 L (by omega)=nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [ζm,synchronizedAdjacentSource]
    simp only [←regrade_comp,last_layer_regrade_trans,top_target_regrade_self]
    rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  have hgate := synchronized_ordinary_first_protected_gate T.X T.Y T.f L b hL hb
    S Wm (B+1) W ((L+b:ℕ)+1) rfl rfl (by omega) ζm y
    (by simpa only [add_sub_cancel_right] using hy) hsource c hcfil Pm
    (by simpa only [Nat.cast_add] using hPm)
  obtain ⟨ζ',e,hρ,_,htop⟩ := synchronized_ordinary_full_image_h
    T he hf hg hh hT L 1 b (by omega) hL hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl ζm c hstart v hci Pm hgate (by
      intro j hj hjb x' hx' hfx'
      have hlevel : ((b+1-j:ℕ):ℤ)=((b+1:ℕ):ℤ)-j := by omega
      obtain ⟨z',hz',u',hu',hbound⟩ := hbottom j hj hjb x' (by simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hx') hfx'
      refine ⟨z',?_,u',?_,?_⟩
      · simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hz'
      · simpa only [sub_add_cancel] using hu'
      · exact boundaries_monotone background T.X _ (by omega) hbound)
  let η := homotopyRegrade (show Wm-S+1=W-(B+1) by dsimp [S,Wm];omega)
    (show Wm-L=W by dsimp [Wm];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) L)
  have hcalibration : η≫(background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f 1 L hL _ _ ζ' ζm hρ]
    simpa only [regrade_comp] using hsource
  have htopm : homotopyRegrade (show Wm-S=((W+L)+b)-(((B+1)+L)+b+1) by dsimp [S,Wm];omega) rfl
      (synchronizedBoundary T.Y L S Wm
        (homotopyRegrade (show W-(B+1)=Wm-S+1 by dsimp [S,Wm];omega)
          (show W=Wm-L by dsimp [Wm];omega) η)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl (((B+1)+L)+b+1) ((W+L)+b) Wm
        (by dsimp [Wm];omega)
        (v+(background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,synchronized_boundary_natural]
    exact htop
  have htop' := synchronized_boundary_top_from_coordinates T.Y L b hb (W-(B+1)) W
    S Wm (((B+1)+L)+b+1) ((W+L)+b)
    (by dsimp [S,Wm];omega) rfl
    (by dsimp [S];omega) rfl η _ htopm
  exact synchronized_first_differential_at_degree T.Y L b hL hb (B+1) W
    (((B+1)+L)+b+1) ((W+L)+b) (by omega) (by omega) y η hcalibration
    v ((background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e)
    P hP hv (fun heP => hker _ heP (ordinary_triangle_composite_zero T (((B+1)+L)+b+1) ((W+L)+b) e)) htop'

/-- Original known-source criterion with synchronous early source-boundary corrections. -/
private theorem synchronized_known_source_differential_ordinary_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z₁ : Ambient background T.Z (B+1,W+1))
    (y : Ambient background T.Y (B+a+1,W+a))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z₁) (by simpa using x))
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (B+1,W+1) ((B+a+1)+1,(W+a)+1) z₁
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+a+1) (W+a) y))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X (B+1+j,W+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z₁' : Ambient background T.Z (B+1+j,W+j+1),
          z₁' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z₁' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L)+1,(W+L)+1))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      ((background.classical.map T.h).pageMap 2 (((B+1)+L)+1,(W+L)+1) z₂) (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L)+1,(W+L)+1) ((((B+1)+L)+b+1)+1,((W+L)+b)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L-a:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j,(W+L)+j+1),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j+1) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j) ((W+L)+j+1)
            ((background.classical.map T.h).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j+1) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((L-a:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j))
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a))
    (hy : y ∈ cycles background T.Y (L+b-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a L haL B W x ζ hζ
  obtain ⟨etop,hitop⟩ := ordinary_finite_image_of_same_source_second T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have ht := ordinary_source_image_restriction_top T.X T.Y T.f a L ha haL B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop) hitop
  let A₀ := B+a+1
  let V₀ := W+a
  let ytop := y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop
  have ht' : homotopyRegrade (show W-(B+1)=V₀-A₀ by dsimp [A₀,V₀];omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) L)≫
        (background.quotients.tower _).rho (a+1) L haL)=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A₀ V₀ W (by dsimp [V₀];omega) ytop := by
    have transport (M : ℕ) (hM : 0+(a+1)=M) :
        homotopyRegrade (show W-(B+1)=V₀-A₀ by dsimp [A₀,V₀];omega) rfl
          ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) L)≫
            (background.quotients.tower _).rho M L (by omega))=
        finiteTopLabelAtWeight T.Y (0+a) (by omega) M (by omega) A₀ V₀ W
          (by dsimp [V₀];omega) ytop := by
      subst M
      exact ht
    simpa only [Nat.zero_add] using transport (a+1) (by omega)
  have hytop : ytop∈cycles background T.Y (L+b-a:ℕ) (A₀,V₀) :=
    (cycles background T.Y (L+b-a:ℕ) (A₀,V₀)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) (himage etop))
  obtain ⟨c,hcfirst,hci⟩ := finite_common_lift_positive_g T he hT hf hg hh
    b hb ((B+1)+L) (W+L) z₂ u v huz hdz₂
  let S := ((B+1)+L)+1
  let Wm := W+L
  let ζm := synchronizedAdjacentSource T.X L (B+1) W ζ
  have hstart := synchronized_initial_residual_filtration T.X L b (by omega) hb
    (B+1) W u ζ hU c hcfirst
  have hcfil := synchronized_common_top_filtration T.X T.Y T.f b hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl c v hci
  have hsource : (homotopyRegrade (show Wm-S+1=V₀-A₀ by dsimp [S,Wm,A₀,V₀];omega)
      (show Wm-L=V₀-a by dsimp [Wm,V₀];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) L))≫
      (background.quotients.tower _).rho (a+1) L haL=finiteTopLabel T.Y a ha A₀ V₀ ytop := by
    have h := congrArg (homotopyRegrade (rfl : V₀-A₀=V₀-A₀) (show W=V₀-a by dsimp [V₀];omega)) ht'
    dsimp only [ζm,synchronizedAdjacentSource]
    simpa only [←regrade_comp,last_layer_regrade_trans,finiteTopLabelAtWeight,
      top_target_regrade_self] using h
  have hgate := synchronized_ordinary_divided_protected_gate T.X T.Y T.f a L b ha (by omega) hb
    S Wm A₀ V₀ ((L+b-a:ℕ)+1) (by dsimp [S,A₀];omega) (by dsimp [Wm,V₀];omega)
    (by omega) ζm ytop (by simpa only [add_sub_cancel_right] using hytop) hsource c hcfil Pm hPm
  obtain ⟨ζ',e,hρ,_,htop⟩ := synchronized_ordinary_full_image_g
    T he hf hg hh hT L (a+1) b (by omega) haL hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl ζm c hstart v hci Pm hgate (by
      intro j hj hjb x' hx' hfx'
      have hlevel : ((b+1-j:ℕ):ℤ)=((b+1:ℕ):ℤ)-j := by omega
      obtain ⟨z',hz',u',hu',hbound⟩ := hbottom j hj hjb x' (by simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hx') hfx'
      refine ⟨z',?_,u',?_,?_⟩
      · simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hz'
      · simpa only [sub_add_cancel] using hu'
      · exact boundaries_monotone background T.X _ (by omega) hbound)
  let η := homotopyRegrade (show Wm-S+1=V₀-A₀ by dsimp [S,Wm,A₀,V₀];omega)
    (show Wm-L=(V₀-a) by dsimp [Wm,V₀];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) L)
  have hcalibration : η≫(background.quotients.tower _).rho (a+1) L haL=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A₀ V₀ (V₀-a) rfl ytop := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f (a+1) L haL _ _ ζ' ζm hρ]
    simpa only [regrade_comp,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have htopm : homotopyRegrade (show Wm-S=((W+L)+b)-(((B+1)+L)+b+1) by dsimp [S,Wm];omega) rfl
      (synchronizedBoundary T.Y L S Wm
        (homotopyRegrade (show V₀-A₀=Wm-S+1 by dsimp [S,Wm,A₀,V₀];omega)
          (show (V₀-a)=Wm-L by dsimp [Wm,V₀];omega) η)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl (((B+1)+L)+b+1) ((W+L)+b) Wm
        (by dsimp [Wm];omega)
        (v+(background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,synchronized_boundary_natural]
    exact htop
  have htop' := synchronized_boundary_top_from_coordinates T.Y L b hb (V₀-A₀) (V₀-a)
    S Wm (((B+1)+L)+b+1) ((W+L)+b)
    (by dsimp [S,Wm,A₀,V₀];omega) (by dsimp [Wm,V₀];omega)
    (by dsimp [S];omega) rfl η _ htopm
  exact synchronized_finite_differential_at_weight_and_degree T.Y L a (a+1) b hb ha
    (by omega) rfl A₀ V₀ (V₀-a) (a+1) (((B+1)+L)+b+1) ((W+L)+b) rfl
    (by dsimp [A₀];omega) (by dsimp [V₀];omega)
    ytop y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop)
    (by dsimp only [ytop]; have hz : y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop-y-
        (background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop=0 := by abel
        rw [hz]; exact (boundaries background T.Y _ _).zero_mem)
    (himage etop) η hcalibration v ((background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e)
    P hP hv (fun heP => hker _ heP (positive_second_triangle_composite_zero T hf hg hh hT (((B+1)+L)+b+1) ((W+L)+b) e)) htop'

/-- Original known-source criterion with synchronous early source-boundary corrections. -/
private theorem synchronized_known_source_differential_ordinary_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z₁ : Ambient background T.Z (B,W))
    (y : Ambient background T.Y (B+a+1,W+a))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z₁)
      (by simpa using x))
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (B,W) (B+a+1,W+a) z₁
      ((background.classical.map T.g).pageMap 2 (B+a+1,W+a) y))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X ((B+1)+j-1+1,W+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z₁' : Ambient background T.Z ((B+1)+j-1,W+j),
          z₁' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z₁') (by simpa only [add_sub_cancel_right] using u') ∧
          x'-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L),(W+L)))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) ((B+1)+L) (W+L) z₂)
      (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L),(W+L)) (((B+1)+L)+b+1,(W+L)+b) z₂
      ((background.classical.map T.g).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L-a:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1,(W+L)+j),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1,(W+L)+j) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((((B+1)+L)+1)+j-1) ((W+L)+j) z₂) (by simpa only [sub_add_cancel,add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((L-a:ℕ)+j) ((((B+1)+L)+1)+j,(W+L)+j))
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a))
    (hy : y ∈ cycles background T.Y (L+b-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, (background.classical.map T.g).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a L haL B W x ζ hζ
  obtain ⟨etop,hitop⟩ := ordinary_finite_image_of_same_source_third T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have ht := ordinary_source_image_restriction_top T.X T.Y T.f a L ha haL B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop) hitop
  let A₀ := B+a+1
  let V₀ := W+a
  let ytop := y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop
  have ht' : homotopyRegrade (show W-(B+1)=V₀-A₀ by dsimp [A₀,V₀];omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) L)≫
        (background.quotients.tower _).rho (a+1) L haL)=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A₀ V₀ W (by dsimp [V₀];omega) ytop := by
    have transport (M : ℕ) (hM : 0+(a+1)=M) :
        homotopyRegrade (show W-(B+1)=V₀-A₀ by dsimp [A₀,V₀];omega) rfl
          ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) L)≫
            (background.quotients.tower _).rho M L (by omega))=
        finiteTopLabelAtWeight T.Y (0+a) (by omega) M (by omega) A₀ V₀ W
          (by dsimp [V₀];omega) ytop := by
      subst M
      exact ht
    simpa only [Nat.zero_add] using transport (a+1) (by omega)
  have hytop : ytop∈cycles background T.Y (L+b-a:ℕ) (A₀,V₀) :=
    (cycles background T.Y (L+b-a:ℕ) (A₀,V₀)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) (himage etop))
  obtain ⟨c,hcfirst,hci⟩ := finite_common_lift_positive_h T he hT hf hg hh
    b hb ((B+1)+L) (W+L) z₂ u v huz hdz₂
  let S := ((B+1)+L)+1
  let Wm := W+L
  let ζm := synchronizedAdjacentSource T.X L (B+1) W ζ
  have hstart := synchronized_initial_residual_filtration T.X L b (by omega) hb
    (B+1) W u ζ hU c hcfirst
  have hcfil := synchronized_common_top_filtration T.X T.Y T.f b hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl c v hci
  have hsource : (homotopyRegrade (show Wm-S+1=V₀-A₀ by dsimp [S,Wm,A₀,V₀];omega)
      (show Wm-L=V₀-a by dsimp [Wm,V₀];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) L))≫
      (background.quotients.tower _).rho (a+1) L haL=finiteTopLabel T.Y a ha A₀ V₀ ytop := by
    have h := congrArg (homotopyRegrade (rfl : V₀-A₀=V₀-A₀) (show W=V₀-a by dsimp [V₀];omega)) ht'
    dsimp only [ζm,synchronizedAdjacentSource]
    simpa only [←regrade_comp,last_layer_regrade_trans,finiteTopLabelAtWeight,
      top_target_regrade_self] using h
  have hgate := synchronized_ordinary_divided_protected_gate T.X T.Y T.f a L b ha (by omega) hb
    S Wm A₀ V₀ ((L+b-a:ℕ)+1) (by dsimp [S,A₀];omega) (by dsimp [Wm,V₀];omega)
    (by omega) ζm ytop (by simpa only [add_sub_cancel_right] using hytop) hsource c hcfil Pm hPm
  obtain ⟨ζ',e,hρ,_,htop⟩ := synchronized_ordinary_full_image_h
    T he hf hg hh hT L (a+1) b (by omega) haL hb S Wm
    (((B+1)+L)+b+1) ((W+L)+b) (by dsimp [S];omega) rfl ζm c hstart v hci Pm hgate (by
      intro j hj hjb x' hx' hfx'
      have hlevel : ((b+1-j:ℕ):ℤ)=((b+1:ℕ):ℤ)-j := by omega
      obtain ⟨z',hz',u',hu',hbound⟩ := hbottom j hj hjb x' (by simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hx') hfx'
      refine ⟨z',?_,u',?_,?_⟩
      · simpa only [hlevel,Nat.cast_add,Nat.cast_one] using hz'
      · simpa only [sub_add_cancel] using hu'
      · exact boundaries_monotone background T.X _ (by omega) hbound)
  let η := homotopyRegrade (show Wm-S+1=V₀-A₀ by dsimp [S,Wm,A₀,V₀];omega)
    (show Wm-L=(V₀-a) by dsimp [Wm,V₀];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) L)
  have hcalibration : η≫(background.quotients.tower _).rho (a+1) L haL=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A₀ V₀ (V₀-a) rfl ytop := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f (a+1) L haL _ _ ζ' ζm hρ]
    simpa only [regrade_comp,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have htopm : homotopyRegrade (show Wm-S=((W+L)+b)-(((B+1)+L)+b+1) by dsimp [S,Wm];omega) rfl
      (synchronizedBoundary T.Y L S Wm
        (homotopyRegrade (show V₀-A₀=Wm-S+1 by dsimp [S,Wm,A₀,V₀];omega)
          (show (V₀-a)=Wm-L by dsimp [Wm,V₀];omega) η)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl (((B+1)+L)+b+1) ((W+L)+b) Wm
        (by dsimp [Wm];omega)
        (v+(background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,synchronized_boundary_natural]
    exact htop
  have htop' := synchronized_boundary_top_from_coordinates T.Y L b hb (V₀-A₀) (V₀-a)
    S Wm (((B+1)+L)+b+1) ((W+L)+b)
    (by dsimp [S,Wm,A₀,V₀];omega) (by dsimp [Wm,V₀];omega)
    (by dsimp [S];omega) rfl η _ htopm
  exact synchronized_finite_differential_at_weight_and_degree T.Y L a (a+1) b hb ha
    (by omega) rfl A₀ V₀ (V₀-a) (a+1) (((B+1)+L)+b+1) ((W+L)+b) rfl
    (by dsimp [A₀];omega) (by dsimp [V₀];omega)
    ytop y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop)
    (by dsimp only [ytop]; have hz : y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop-y-
        (background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop=0 := by abel
        rw [hz]; exact (boundaries background T.Y _ _).zero_mem)
    (himage etop) η hcalibration v ((background.classical.map T.f).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) e)
    P hP hv (fun heP => hker _ heP (ordinary_triangle_composite_zero T (((B+1)+L)+b+1) ((W+L)+b) e)) htop'

end
end KIP126.ProofTools.Internal.SyntheticCoverage
