module

public import KIP126.ProofTools.MahowaldLeibniz

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.Language

import all KIP126.ProofTools.SyntheticCoverage.RecursivePermanence
import all KIP126.ProofTools.SyntheticCoverage.KnownSourceSurvival
import all KIP126.ProofTools.SyntheticCoverage.EarlySourceCorrection

/-! The finite-boundary corrections for the bottom three-layer relation.
Every source correction is made on the original coefficient representative;
its absolute boundary and its top restriction are updated together.
-/

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

/-- A specified finite-torsion full class is the actual boundary of one
finite source. This is exactness of the selected coefficient triangle. -/
private theorem recursive_torsion_boundary_source
    (A : SyntheticSpectrum) (N : ℕ) (m w : ℤ)
    (U : BiHom (m-1) (w+N) A) (hU : lambdaMultiply N U=0) :
    ∃ ζ : BiHom m w (XModLambdaN A N),
      biSuspensionHomEquiv m w N A (ζ≫XModLambdaN.proj A N)=U := by
  have hraw : lambdaPow N (Smn (m-1) (w+N))≫U=0 := by
    simpa only [lambdaMultiply,comp_eq_zero_iff_of_epi] using hU
  have hmap : (SyntheticCategory.biShift (0,-(N:ℤ))).map U≫lambdaPow N A=0 :=
    (lambdaPow_naturality N U).trans hraw
  have hδ := (shifted_representative_zero_iff m w N A A (lambdaPow N A) U).mpr hmap
  let C := XModLambdaN.cofiberTriangle A N
  have hz : ((biSuspensionHomEquiv m w N A).symm U)≫C.rotate.mor₃=0 := by
    change _≫(-(shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow N A))=0
    rw [Preadditive.comp_neg,hδ,neg_zero]
  obtain ⟨ζ,hζ⟩ := C.rotate.coyoneda_exact₃
    (rot_of_distTriang C (XModLambdaN.cofiberTriangle_distinguished A N)) _ hz
  change (biSuspensionHomEquiv m w N A).symm U=ζ≫XModLambdaN.proj A N at hζ
  refine ⟨ζ,?_⟩
  rw [←hζ,AddEquiv.apply_symm_apply]

/-- The normalized insertion vanishes on the entire protected quotient. -/
private theorem recursive_normalized_insertion_restriction_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (K N : ℕ) (hK : 0<K) (hKN : K<N) (m t : ℤ)
    (a : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-K))) :
    boundaryNormalizedInsertion X K N hK hKN m t a≫
      (background.quotients.tower _).rho K N hKN.le=0 := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let C := (background.quotients.tower A).triangle hK hKN
  have hz : C.lambdaMap≫(background.quotients.tower A).rho K N hKN.le=0 := by
    rw [←(background.quotients.tower A).triangle_rho hK hKN]
    exact comp_distTriang_mor_zero₁₂ _ C.distinguished
  dsimp only [boundaryNormalizedInsertion]
  rw [Category.assoc,hz,comp_zero]

/-- A finite early-boundary torsion bound produces a correction of the
original source length with zero protected top restriction. Its absolute
boundary is literally one lambda times the chosen full correction. -/
private theorem recursive_synchronized_torsion_correction_strict
    (X : (AdamsObject (coefficients := background.coefficients))) (N K : ℕ) (hK : 0<K) (hKN : K<N) (m w : ℤ)
    (T : BiHom (m-1) (w+N+1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hT : lambdaMultiply (N-K+1) T=0) :
    ∃ ζb : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζb≫(background.quotients.tower _).rho K N hKN.le=0 ∧
      biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
        (ζb≫XModLambdaN.proj _ N)=
      homotopyRegrade rfl (show (w+N+1)-(1:ℕ)=w+N by omega) (lambdaMultiply 1 T) := by
  let q := N-K+1
  let T' := homotopyRegrade (rfl : m-1=m-1)
    (show w+N+1=(w+K)+q by dsimp only [q]; omega) T
  have hT' : lambdaMultiply q T'=0 := by
    dsimp only [T']
    rw [lambda_regrade,hT,regrade_zero]
  obtain ⟨a,ha⟩ := recursive_torsion_boundary_source _ q m (w+K) T' hT'
  let b := a≫(background.quotients.tower _).rho (N-K) q (by dsimp only [q]; omega)
  have hb := absolute_boundary_restriction X (N-K) q (by dsimp only [q]; omega) m (w+K) a
  rw [ha] at hb
  have hcast (i : ℕ) (hi : i=1) (hw : (w+K+q)-i=w+K+(N-K:ℕ)) :
      homotopyRegrade rfl hw (lambdaMultiply i T')=
        homotopyRegrade rfl (show (w+K+q)-(1:ℕ)=w+K+(N-K:ℕ) by dsimp only [q]; omega)
          (lambdaMultiply 1 T') := by
    subst i
    rfl
  have hb' := hb.trans (hcast (q-(N-K)) (by dsimp only [q]; omega) _)
  let ζ := boundaryNormalizedInsertion X K N hK hKN m (w+K) b
  let ζb := homotopyRegrade rfl (show (w+K)-K=w by omega) ζ
  refine ⟨ζb,?_,?_⟩
  · dsimp only [ζb,ζ]
    rw [←regrade_comp,recursive_normalized_insertion_restriction_zero,regrade_zero]
  · have hζ := boundary_normalized_insertion_boundary X K N hK hKN m (w+K) b
    rw [hb'] at hζ
    have hζ' := congrArg (homotopyRegrade (rfl : m-1=m-1)
      (show (w+K)+(N-K:ℕ)=w+N by omega)) hζ
    dsimp only [ζb,ζ]
    rw [←regrade_comp,bi_susp_regrade]
    simp only [T',lambda_regrade,normalized_homotopy_regrade_trans] at hζ'
    convert hζ' using 1

private theorem recursive_synchronized_torsion_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K : ℕ) (hK : 0<K) (hKN : K≤N) (m w : ℤ)
    (T : BiHom (m-1) (w+N+1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hT : lambdaMultiply (N-K+1) T=0) :
    ∃ ζb : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζb≫(background.quotients.tower _).rho K N hKN=0 ∧
      biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
        (ζb≫XModLambdaN.proj _ N)=
      homotopyRegrade rfl (show (w+N+1)-(1:ℕ)=w+N by omega) (lambdaMultiply 1 T) := by
  by_cases hlt : K<N
  · exact recursive_synchronized_torsion_correction_strict X N K hK hlt m w T hT
  · have hEq : N-K+1=1 := by omega
    rw [hEq] at hT
    refine ⟨0,by simp,?_⟩
    rw [zero_comp,map_zero,hT,regrade_zero]

private def recursiveBoundaryRepresentative (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (p t : ℤ)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    BiHom (t-p) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)) :=
  homotopyRegrade (show (t-p+1)-1=t-p by omega) (show (t-1-N)+N=t-1 by omega)
    (biSuspensionHomEquiv (t-p+1) (t-1-N) N (background.nu.functor.obj (X.obj background.auxiliary))
      (ζ≫XModLambdaN.proj _ N))

private theorem recursive_boundary_representative_sub (X : (AdamsObject (coefficients := background.coefficients)))
    (N : ℕ) (p t : ℤ)
    (a b : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    recursiveBoundaryRepresentative X N p t (a-b)=
      recursiveBoundaryRepresentative X N p t a-recursiveBoundaryRepresentative X N p t b := by
  simp only [recursiveBoundaryRepresentative,Preadditive.sub_comp,map_sub,homotopy_regrade_sub]

/-- The early-boundary cutoff supplies the torsion bound protecting Q_K. -/
private theorem recursive_early_boundary_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K : ℕ) (hK : 0<K) (hKN : K≤N) (p t : ℤ)
    (b : Ambient background X (p,t))
    (hb : b∈boundaries background X ((N-K:ℕ)+2) (p,t)) :
    ∃ (T : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary)))
      (ζb : BiHom (t-p+1) (t-1-N)
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)),
      T≫XModLambdaN.incl _ 1=nativeFirstLabel X p t b ∧
      lambdaMultiply (N-K+1) T=0 ∧
      ζb≫(background.quotients.tower _).rho K N hKN=0 ∧
      recursiveBoundaryRepresentative X N p t ζb=lambdaMultiply 1 T := by
  obtain ⟨T,hT,hTzero⟩ := cumulative_boundary_torsion_lift_unshifted X (N-K+1) p t b
    (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,Int.reduceAdd] using hb)
  let T' := homotopyRegrade (show t-p=(t-p+1)-1 by omega)
    (show t=(t-1-N)+N+1 by omega) T
  have hT' : lambdaMultiply (N-K+1) T'=0 := by
    dsimp only [T']
    rw [lambda_regrade,hTzero,regrade_zero]
  obtain ⟨ζb,hzero,hboundary⟩ := recursive_synchronized_torsion_correction X N K hK hKN
    (t-p+1) (t-1-N) T' hT'
  refine ⟨T,ζb,hT,hTzero,hzero,?_⟩
  dsimp only [recursiveBoundaryRepresentative]
  rw [hboundary]
  simp only [T',lambda_regrade,normalized_homotopy_regrade_trans]
  rfl

/-- Simultaneous source/boundary correction of the actual residual. The
protected top, both original first labels, and the literal K0 head survive. -/
private theorem recursive_synchronized_residual_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K : ℕ) (hK : 0<K) (hKN : K≤N) (p t : ℤ)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c h : BiHom (t-p) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (y u k : Ambient background X (p,t))
    (hy : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 y)
      (recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-c))
    (hu : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 u) h)
    (hb : y-u-k∈boundaries background X ((N-K:ℕ)+2) (p,t)) :
    ∃ ζ' : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ'≫(background.quotients.tower _).rho K N hKN=
        ζ≫(background.quotients.tower _).rho K N hKN ∧
      ζ'≫(background.quotients.tower _).rho 1 N (by omega)=
        ζ≫(background.quotients.tower _).rho 1 N (by omega) ∧
      recursiveBoundaryRepresentative X N p t ζ'≫XModLambdaN.incl _ 1=
        recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 1 ∧
      (c+h)≫(background.quotients.tower _).rho 1 3 (by decide)=
        c≫(background.quotients.tower _).rho 1 3 (by decide) ∧
      Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
        (finiteTargetLabel background X 3 p t 1 k)
        (recursiveBoundaryRepresentative X N p t ζ'≫XModLambdaN.incl _ 3-(c+h)) := by
  obtain ⟨T,ζb,hT,_,hζb,hboundary⟩ := recursive_early_boundary_correction X N K hK hKN
    p t (y-u-k) hb
  have hTdet := full_first_label_lambda_projection_detects X 3 1 (by decide) (by decide)
    p t (y-u-k) T hT
  have hTfirst := lambda_power_first_quotient_zero X 1 (by decide) (t-p) t T
  have hhfil := KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu X))
    (p,t,t-1) _ h hu
  have hhfirst := finite_filtered_first_quotient_zero X 3 1 (by decide) (by decide) p t h hhfil
  refine ⟨ζ-ζb,?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hζb,sub_zero]
  · have hz : ζb≫(background.quotients.tower _).rho 1 N (by omega)=0 := by
      rw [←(background.quotients.tower _).rho_comp (show 1≤K by omega) hKN,←Category.assoc,hζb,zero_comp]
    rw [Preadditive.sub_comp,hz,sub_zero]
  · rw [recursive_boundary_representative_sub,hboundary,Preadditive.sub_comp,hTfirst,sub_zero]
  · rw [Preadditive.add_comp,hhfirst,add_zero]
  · have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient 3 (.nu X))
      (p,t,t-1) hy hTdet
    have hh := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient 3 (.nu X))
      (p,t,t-1) hsub hu
    rw [←finiteTargetLabel_sub,←finiteTargetLabel_sub,show y-(y-u-k)-u=k by abel] at hh
    rw [recursive_boundary_representative_sub,hboundary,Preadditive.sub_comp]
    have heq : recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-
        lambdaMultiply 1 T≫XModLambdaN.incl _ 3-(c+h)=
      recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-c-
        lambdaMultiply 1 T≫XModLambdaN.incl _ 3-h := by abel
    rw [heq]
    exact hh

/-- The complete terminal relation is used on the sum of its actual z and
F₂ error. The conclusion uses the finite B_<D cutoff. -/
private theorem recursive_terminal_target_early_boundary
    (Y : (AdamsObject (coefficients := background.coefficients))) (D : ℤ) (hD : 4≤D) (p : Bidegree)
    (P : Submodule ℤ (Ambient background Y p)) (hP : permanentCycles background Y p≤P)
    (w v z error : Ambient background Y p)
    (hw : w∈permanentCycles background Y p) (hv : v∈P)
    (herr : w-(v+z+error)∈boundaries background Y 3 p)
    (hterminal : z+error∈P → z+error∈boundaries background Y (D-1) p) :
    w-v∈boundaries background Y (D-1) p := by
  have hbP := hP (finalBoundaries_le_permanentCycles Y p
    (boundaries_le_finalBoundaries Y p 3 herr))
  have hsumP : z+error∈P := by
    have h := P.sub_mem (P.sub_mem (hP hw) hv) hbP
    convert h using 1
    abel
  have hb := boundaries_monotone background Y p (by omega : (3:ℤ)≤D-1) herr
  have h := (boundaries background Y (D-1) p).add_mem hb (hterminal hsumP)
  convert h using 1
  abel

/-- After the synchronized Q3 comparison, the original protected top
calibration produces d_D. The original source error is removed using its
independent next-page survival and a genuine source boundary. -/
private theorem recursive_finite_differential_of_relation_image
    (Y : (AdamsObject (coefficients := background.coefficients))) (N d : ℕ) (hd : 0<d) (hdN : d<N) (s t B : ℤ)
    (x y sourceError : Ambient background Y (s,t))
    (hsourceError : x-y-sourceError∈boundaries background Y B (s,t))
    (hsourceSurvives : sourceError∈cycles background Y ((N+2-d:ℕ)+1) (s,t))
    (η : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hcalibration : η≫(background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabel Y d hd s t x)
    (v z targetError : Ambient background Y (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ)))
    (P : Submodule ℤ (Ambient background Y (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ))))
    (hP : permanentCycles background Y (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ))≤P)
    (hv : v∈P)
    (hterminal : z+targetError∈P → z+targetError∈boundaries background Y
      (N+2-d:ℕ) (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ)))
    (htop : homotopyRegrade
      (show (t-s)-1=(t+(N+2-d:ℕ))-(s+(N+2-d:ℕ)+1) by omega)
      (show (t-d)+N=(t+(N+2-d:ℕ))-2 by omega)
      (biSuspensionHomEquiv (t-s) (t-d) N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel Y 2 (by decide) (s+(N+2-d:ℕ)+1) (t+(N+2-d:ℕ))
        (v+z+targetError)) :
    IsCycle background Y (N+2-d:ℕ) (s,t) y ∧
      IsCycle background Y (N+2-d:ℕ) (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ)) v ∧
      DifferentialAt background Y ((N+2-d:ℕ)+1) (s,t)
        (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ)) y v := by
  obtain ⟨η',w,hρ,hfirst,hwp,hbound⟩ := finite_extension_of_boundary_top Y N 2
    (by omega) (by decide) (t-s) (t-d) (s+(N+2-d:ℕ)+1) (t+(N+2-d:ℕ))
    (by omega) (by omega) η (v+z+targetError) htop
  have hcalibration' : η'≫(background.quotients.tower _).rho (d+1) (N+2) (by omega)=
      finiteTopLabel Y d hd s t x := by
    rw [←(background.quotients.tower _).rho_comp (show d+1≤N by omega) (show N≤N+2 by omega),
      ←Category.assoc,hρ,hcalibration]
  have hdifferential := finite_source_differential_of_top_restriction Y d (N+2) hd (by omega)
    s t x w η' hcalibration' hfirst
  have hwv := recursive_terminal_target_early_boundary Y ((N+2-d:ℕ)+1) (by omega)
    _ P hP w v z targetError hwp hv hbound (by simpa only [add_sub_cancel_right] using hterminal)
  have h := differential_of_source_correction Y ((N+2-d:ℕ)+1) B (s,t)
    (s+(N+2-d:ℕ)+1,t+(N+2-d:ℕ)) x y sourceError w v hdifferential
      hsourceError hsourceSurvives hwv
  simpa only [add_sub_cancel_right] using h

/-- The K1=1 endpoint uses the original ordinary first source label, with
no artificial positive coefficient division. -/
private theorem recursive_first_differential_of_relation_image
    (Y : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (hN : 0<N) (s t : ℤ)
    (y : Ambient background Y (s,t))
    (η : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y s t y)
    (v z targetError : Ambient background Y (s+(N+2:ℕ)+1,t+(N+2:ℕ)))
    (P : Submodule ℤ (Ambient background Y (s+(N+2:ℕ)+1,t+(N+2:ℕ))))
    (hP : permanentCycles background Y (s+(N+2:ℕ)+1,t+(N+2:ℕ))≤P) (hv : v∈P)
    (hterminal : z+targetError∈P → z+targetError∈boundaries background Y
      (N+2:ℕ) (s+(N+2:ℕ)+1,t+(N+2:ℕ)))
    (htop : homotopyRegrade
      (show (t-s)-1=(t+(N+2:ℕ))-(s+(N+2:ℕ)+1) by omega)
      (show t+N=(t+(N+2:ℕ))-2 by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel Y 2 (by decide) (s+(N+2:ℕ)+1) (t+(N+2:ℕ)) (v+z+targetError)) :
    IsCycle background Y (N+2:ℕ) (s,t) y ∧
      IsCycle background Y (N+2:ℕ) (s+(N+2:ℕ)+1,t+(N+2:ℕ)) v ∧
      DifferentialAt background Y ((N+2:ℕ)+1) (s,t)
        (s+(N+2:ℕ)+1,t+(N+2:ℕ)) y v := by
  obtain ⟨η',w,hρ,hw,hwp,hbound⟩ := finite_extension_of_boundary_top Y N 2 hN (by decide)
    (t-s) t (s+(N+2:ℕ)+1) (t+(N+2:ℕ)) (by omega) (by omega) η _ htop
  have hη' : η'≫(background.quotients.tower _).rho 1 (N+2) (by omega)=nativeFirstLabel Y s t y := by
    rw [←(background.quotients.tower _).rho_comp hN (show N≤N+2 by omega),←Category.assoc,hρ,hfirst]
  have hdifferential : DifferentialAt background Y ((N+2:ℕ)+1) (s,t)
      (s+(N+2:ℕ)+1,t+(N+2:ℕ)) y w := by
    refine ⟨by omega,adjacent_boundary_differential Y (N+2) (by omega) s t y w η' hη' ?_⟩
    exact hw
  have hwv := recursive_terminal_target_early_boundary Y ((N+2:ℕ)+1) (by omega)
    _ P hP w v z targetError hwp hv hbound (by simpa only [add_sub_cancel_right] using hterminal)
  have h := differential_of_source_correction Y ((N+2:ℕ)+1) 1 (s,t)
    (s+(N+2:ℕ)+1,t+(N+2:ℕ)) y y 0 w v hdifferential
    (by simp) (by exact (cycles background Y ((N+2:ℕ)+1) (s,t)).zero_mem) hwv
  simpa only [add_sub_cancel_right] using h

/-- Synchronization retaining the fixed boundary-coordinate automorphism
and using its invariance of finite detection. -/
private theorem recursive_synchronized_residual_correction_with_automorphism
    (X : (AdamsObject (coefficients := background.coefficients))) (N K : ℕ) (hK : 0<K) (hKN : K≤N) (p t : ℤ)
    (v : Smn (Syn:=SyntheticSpectrum) (t-p) (t-1) ≅ Smn (t-p) (t-1))
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c h : BiHom (t-p) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (y u k : Ambient background X (p,t))
    (hy : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 y)
      ((v.hom≫recursiveBoundaryRepresentative X N p t ζ)≫XModLambdaN.incl _ 3-c))
    (hu : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 u) h)
    (hb : y-u-k∈boundaries background X ((N-K:ℕ)+2) (p,t)) :
    ∃ ζ' : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ'≫(background.quotients.tower _).rho K N hKN=
        ζ≫(background.quotients.tower _).rho K N hKN ∧
      ζ'≫(background.quotients.tower _).rho 1 N (by omega)=
        ζ≫(background.quotients.tower _).rho 1 N (by omega) ∧
      (v.hom≫recursiveBoundaryRepresentative X N p t ζ')≫XModLambdaN.incl _ 1=
        (v.hom≫recursiveBoundaryRepresentative X N p t ζ)≫XModLambdaN.incl _ 1 ∧
      (c+h)≫(background.quotients.tower _).rho 1 3 (by decide)=
        c≫(background.quotients.tower _).rho 1 3 (by decide) ∧
      Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
        (finiteTargetLabel background X 3 p t 1 k)
        ((v.hom≫recursiveBoundaryRepresentative X N p t ζ')≫XModLambdaN.incl _ 3-(c+h)) := by
  obtain ⟨T,ζb,hT,_,hζb,hboundary⟩ := recursive_early_boundary_correction X N K hK hKN
    p t (y-u-k) hb
  have hTdet₀ := full_first_label_lambda_projection_detects X 3 1 (by decide) (by decide)
    p t (y-u-k) T hT
  have hTdet := sphere_automorphism_finite_detects X 3 1 (by decide) p t (y-u-k) v
    (lambdaMultiply 1 T≫XModLambdaN.incl _ 3) hTdet₀
  have hTfirst := lambda_power_first_quotient_zero X 1 (by decide) (t-p) t T
  have hhfil := KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu X))
    (p,t,t-1) _ h hu
  have hhfirst := finite_filtered_first_quotient_zero X 3 1 (by decide) (by decide) p t h hhfil
  refine ⟨ζ-ζb,?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hζb,sub_zero]
  · have hz : ζb≫(background.quotients.tower _).rho 1 N (by omega)=0 := by
      rw [←(background.quotients.tower _).rho_comp (show 1≤K by omega) hKN,←Category.assoc,hζb,zero_comp]
    rw [Preadditive.sub_comp,hz,sub_zero]
  · rw [recursive_boundary_representative_sub,hboundary,Preadditive.comp_sub,Preadditive.sub_comp]
    simp only [Category.assoc,hTfirst,comp_zero,sub_zero]
  · rw [Preadditive.add_comp,hhfirst,add_zero]
  · have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient 3 (.nu X))
      (p,t,t-1) hy hTdet
    have hh := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient 3 (.nu X))
      (p,t,t-1) hsub hu
    rw [←finiteTargetLabel_sub,←finiteTargetLabel_sub,show y-(y-u-k)-u=k by abel] at hh
    rw [recursive_boundary_representative_sub,hboundary,Preadditive.comp_sub,Preadditive.sub_comp]
    simp only [Category.assoc] at hh ⊢
    have heq : v.hom≫recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-
        v.hom≫lambdaMultiply 1 T≫XModLambdaN.incl _ 3-(c+h)=
      v.hom≫recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-c-
        v.hom≫lambdaMultiply 1 T≫XModLambdaN.incl _ 3-h := by abel
    rw [heq]
    exact hh

private theorem recursive_ordinary_protected_image
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (K N : ℕ) (hKN : K≤N) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (h : a≫(background.quotients.tower _).rho K N hKN=b≫(background.quotients.tower _).rho K N hKN) :
    (a≫XModLambdaN.map (background.nu.functor.map f) N)≫(background.quotients.tower _).rho K N hKN=
      (b≫XModLambdaN.map (background.nu.functor.map f) N)≫(background.quotients.tower _).rho K N hKN := by
  simp only [Category.assoc]
  rw [←(background.quotients.natural (background.nu.functor.map f)).rho_naturality hKN]
  simpa only [Category.assoc] using congrArg (fun z => z≫XModLambdaN.map (background.nu.functor.map f) K) h

private theorem recursive_positive_protected_image
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (K N : ℕ) (hK : 0<K) (hKN : K≤N) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (h : a≫(background.quotients.tower _).rho K N hKN=b≫(background.quotients.tower _).rho K N hKN) :
    positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w a≫
        (background.quotients.tower _).rho K N hKN=
      positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w b≫
        (background.quotients.tower _).rho K N hKN := by
  rw [positive_finite_image_restriction T hf K N hK hKN,
    positive_finite_image_restriction T hf K N hK hKN,h]

public def RecursiveDifferentialHMiddle
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (N K : ℕ) (s t : ℤ)
    (P B : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ y : Ambient background T.X (s+1,t), y∈cycles background T.X 2 (s+1,t) →
    (background.classical.map T.f).pageMap 2 (s+1,t) y∈P ⊓ B →
    ∃ (z : Ambient background T.Z (s,t)) (u k : Ambient background T.X (s+1,t)),
      z∈cycles background T.Z 2 (s,t) ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
        (by simpa only [add_sub_cancel_right] using u) ∧ k∈K₀ ∧
      y-u-k∈boundaries background T.X ((N-K:ℕ)+2) (s+1,t)

/-- The whole relation is applied to the unique actual intermediate head
remaining after the finite-boundary synchronization. The head gate is
supplied by the independent known-source survival comparison. -/
private theorem recursive_positive_h_relation_image_of_head_gate
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (N K : ℕ) (hK : 0<K) (hKN : K≤N) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P B : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : permanentCycles background T.Y (s+1,t)≤P)
    (hmid : RecursiveDifferentialHMiddle T hh N K s t P B K₀)
    (hsurj : RecursivePositiveHSurjective T hh s t K₀)
    (ζ : BiHom (t-(s+1)+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hsame : recursiveBoundaryRepresentative T.X N (s+1) t ζ≫XModLambdaN.incl _ 1=
      c≫(background.quotients.tower _).rho 1 3 (by decide))
    (hc : c≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v)
    (hgate : ∀ y : Ambient background T.X (s+1,t),
      Detects (background.convergence (.quotient 3 (.nu T.X))) (s+1,t,t-1)
        (finiteTargetLabel background T.X 3 (s+1) t 1 y)
        (recursiveBoundaryRepresentative T.X N (s+1) t ζ≫XModLambdaN.incl _ 3-c) →
      (background.classical.map T.f).pageMap 2 (s+1,t) y∈B) :
    ∃ (k : Ambient background T.X (s+1,t)) (U : Ambient background T.Z (s,t))
      (z : Ambient background T.Y (s+1+1,t+1)) (e : Ambient background T.X (s+1+1,t+1))
      (ζ' : BiHom (t-(s+1)+1) (t-1-N)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      k∈K₀ ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z) ∧
      ζ'≫(background.quotients.tower _).rho K N hKN=ζ≫(background.quotients.tower _).rho K N hKN ∧
      (recursiveBoundaryRepresentative T.X N (s+1) t ζ'≫XModLambdaN.incl _ 3)≫
        XModLambdaN.map (background.nu.functor.map T.f) 3=
        recursiveTopLabel T.Y (s+1) t
          (v+z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e) := by
  let a := recursiveBoundaryRepresentative T.X N (s+1) t ζ
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X (s+1) t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (c≫XModLambdaN.map (background.nu.functor.map T.f) 3-
        (0 : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero,hc]
    exact recursive_top_label_filtration T.Y (s+1) t v
  have hFy := ordinary_affine_error_label_image_permanent T.X T.Y T.f 3 1 (by decide)
    (s+1) t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hb⟩ := hmid y hy ⟨hP hFy,hgate y hyd⟩
  obtain ⟨h,hhdet,hhzero⟩ := middle_positive_h_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t z₀ hz₀ u hu
  obtain ⟨ζ',hρ,_,_,_,hres⟩ := recursive_synchronized_residual_correction
    T.X N K hK hKN (s+1) t ζ c h y u k hyd hhdet hb
  obtain ⟨U,z,hU,hd,ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_h
    T he hT hf hg hh s t K₀ hsurj k hk
  have hc' : (c+h)≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v := by
    rw [Preadditive.add_comp,hhzero,add_zero,hc]
  obtain ⟨e,hi⟩ := recursive_ordinary_image_from_residual T.X T.Y T.f (s+1) t
    (recursiveBoundaryRepresentative T.X N (s+1) t ζ'≫XModLambdaN.incl _ 3)
    (c+h) k v z hres hc' ck hckfirst hckimage
  exact ⟨k,U,z,e,ζ',hk,hU,hd,hρ,hi⟩

public def RecursiveDifferentialGMiddle
    (T : TriangleData background.auxiliary) (_hg : normalizedExponent background.classicalTower T.g=1)
    (N K : ℕ) (s t : ℤ)
    (P B : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ y : Ambient background T.X (s+1,t), y∈cycles background T.X 2 (s+1,t) →
    (background.classical.map T.f).pageMap 2 (s+1,t) y∈P ⊓ B →
    ∃ (z : Ambient background T.Z (s+1,t+1)) (u k : Ambient background T.X (s+1,t)),
      z∈cycles background T.Z 2 (s+1,t+1) ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
        (by simpa only [add_sub_cancel_right] using u) ∧ k∈K₀ ∧
      y-u-k∈boundaries background T.X ((N-K:ℕ)+2) (s+1,t)

/-- The whole relation is applied to the unique actual intermediate head
remaining after the finite-boundary synchronization. The head gate is
supplied by the independent known-source survival comparison. -/
private theorem recursive_positive_g_relation_image_of_head_gate
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N K : ℕ) (hK : 0<K) (hKN : K≤N) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P B : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : permanentCycles background T.Y (s+1,t)≤P)
    (hmid : RecursiveDifferentialGMiddle T hg N K s t P B K₀)
    (hsurj : RecursivePositiveGSurjective T hg s t K₀)
    (ζ : BiHom (t-(s+1)+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hsame : recursiveBoundaryRepresentative T.X N (s+1) t ζ≫XModLambdaN.incl _ 1=
      c≫(background.quotients.tower _).rho 1 3 (by decide))
    (hc : c≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v)
    (hgate : ∀ y : Ambient background T.X (s+1,t),
      Detects (background.convergence (.quotient 3 (.nu T.X))) (s+1,t,t-1)
        (finiteTargetLabel background T.X 3 (s+1) t 1 y)
        (recursiveBoundaryRepresentative T.X N (s+1) t ζ≫XModLambdaN.incl _ 3-c) →
      (background.classical.map T.f).pageMap 2 (s+1,t) y∈B) :
    ∃ (k : Ambient background T.X (s+1,t)) (U : Ambient background T.Z (s+1,t+1))
      (z : Ambient background T.Y (s+1+1,t+1)) (e : Ambient background T.X (s+1+1,t+1))
      (ζ' : BiHom (t-(s+1)+1) (t-1-N)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      k∈K₀ ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z) ∧
      ζ'≫(background.quotients.tower _).rho K N hKN=ζ≫(background.quotients.tower _).rho K N hKN ∧
      (recursiveBoundaryRepresentative T.X N (s+1) t ζ'≫XModLambdaN.incl _ 3)≫
        XModLambdaN.map (background.nu.functor.map T.f) 3=
        recursiveTopLabel T.Y (s+1) t
          (v+z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e) := by
  let a := recursiveBoundaryRepresentative T.X N (s+1) t ζ
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X (s+1) t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (c≫XModLambdaN.map (background.nu.functor.map T.f) 3-
        (0 : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero,hc]
    exact recursive_top_label_filtration T.Y (s+1) t v
  have hFy := ordinary_affine_error_label_image_permanent T.X T.Y T.f 3 1 (by decide)
    (s+1) t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hb⟩ := hmid y hy ⟨hP hFy,hgate y hyd⟩
  obtain ⟨h,hhdet,hhzero⟩ := selective_positive_g_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t z₀ hz₀ u hu
  obtain ⟨ζ',hρ,_,_,_,hres⟩ := recursive_synchronized_residual_correction
    T.X N K hK hKN (s+1) t ζ c h y u k hyd hhdet hb
  obtain ⟨U,z,hU,hd,ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_g
    T he hT hf hg hh s t K₀ hsurj k hk
  have hc' : (c+h)≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v := by
    rw [Preadditive.add_comp,hhzero,add_zero,hc]
  obtain ⟨e,hi⟩ := recursive_ordinary_image_from_residual T.X T.Y T.f (s+1) t
    (recursiveBoundaryRepresentative T.X N (s+1) t ζ'≫XModLambdaN.incl _ 3)
    (c+h) k v z hres hc' ck hckfirst hckimage
  exact ⟨k,U,z,e,ζ',hk,hU,hd,hρ,hi⟩

public def RecursiveDifferentialFMiddle
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N K : ℕ) (s t : ℤ) (P B : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ y : Ambient background T.X (s,t), y∈cycles background T.X 2 (s,t) →
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t y∈P ⊓ B →
    ∃ (z : Ambient background T.Z (s,t+1)) (u k : Ambient background T.X (s,t)),
      z∈cycles background T.Z 2 (s,t+1) ∧
      (background.classicalSuspension T.X).DesuspendsClass s (t+1)
        ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using u) ∧ k∈K₀ ∧
      y-u-k∈boundaries background T.X ((N-K:ℕ)+2) (s,t)

private theorem recursive_positive_f_relation_image_of_head_gate
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N K : ℕ) (hK : 0<K) (hKN : K≤N) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (P B : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : permanentCycles background T.Y (s+1,t+1)≤P)
    (hmid : RecursiveDifferentialFMiddle T hf N K s t P B K₀)
    (hsurj : RecursivePositiveFSurjective T s t K₀)
    (v₀ : Smn (Syn:=SyntheticSpectrum) (t-s) (t-1) ≅ Smn (t-s) (t-1))
    (ζ : BiHom (t-s+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hsame : (v₀.hom≫recursiveBoundaryRepresentative T.X N s t ζ)≫XModLambdaN.incl _ 1=
      c≫(background.quotients.tower _).rho 1 3 (by decide))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (hgate : ∀ y : Ambient background T.X (s,t),
      Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
        (finiteTargetLabel background T.X 3 s t 1 y)
        ((v₀.hom≫recursiveBoundaryRepresentative T.X N s t ζ)≫XModLambdaN.incl _ 3-c) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t y∈B) :
    ∃ (k : Ambient background T.X (s,t)) (U : Ambient background T.Z (s,t+1))
      (z : Ambient background T.Y (s+1+1,(t+1)+1)) (e : Ambient background T.X (s+1,t+1))
      (ζ' : BiHom (t-s+1) (t-1-N)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      k∈K₀ ∧
      (background.classicalSuspension T.X).DesuspendsClass s (t+1)
        ((background.classical.map T.h).pageMap 2 (s,t+1) U) (by simpa using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s,t+1) (s+1+1,(t+1)+1) U
        ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) z) ∧
      ζ'≫(background.quotients.tower _).rho K N hKN=ζ≫(background.quotients.tower _).rho K N hKN ∧
      recursivePositiveImage T hf s t
        ((v₀.hom≫recursiveBoundaryRepresentative T.X N s t ζ')≫XModLambdaN.incl _ 3)=
        recursivePositiveTopLabel T.Y s t
          (v+z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) e) := by
  let a := v₀.hom≫recursiveBoundaryRepresentative T.X N s t ζ
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X s t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower (s+2)
      (positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) c-
        (0 : BiHom (t-s) ((t-1)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero]
    apply (regrade_filtration_iff (rfl : t-s=t-s) (show (t-1)+1=t by omega) _ _).mp
    change FiltrationAtLeast background.syntheticTower (s+2) (recursivePositiveImage T hf s t c)
    rw [hc]
    apply (regrade_filtration_iff _ _ _ _).mpr
    have h : FiltrationAtLeast background.syntheticTower (s+1+1)
        (finiteTopLabel T.Y 2 (by decide) (s+1+1) ((t+1)+1) v) :=
      KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu T.Y))
        (s+1+1,(t+1)+1,((t+1)+1)-2) _ _
        (finiteTopLabel_detects T.Y 2 (by decide) (s+1+1) ((t+1)+1) v)
    convert h using 1; omega
  have hFy := positive_affine_error_label_image_permanent T hf 3 1 (by decide) (by decide)
    s t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hb⟩ := hmid y hy ⟨hP hFy,hgate y hyd⟩
  obtain ⟨h,hhdet,hhzero⟩ := selective_positive_f_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t (levelQuotientShiftIso T.X 1 3) (level_quotient_shift_incl T.X 1 3)
      z₀ hz₀ u hu
  obtain ⟨ζ',hρ,_,_,_,hres⟩ := recursive_synchronized_residual_correction_with_automorphism
    T.X N K hK hKN s t v₀ ζ c h y u k hyd hhdet hb
  obtain ⟨U,z,hU,hd⟩ := hsurj k hk
  obtain ⟨ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_f T he hT hf hg hh s t U k z hU hd
  have hc' : recursivePositiveImage T hf s t (c+h)=recursivePositiveTopLabel T.Y s t v := by
    have hz : positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) h=0 := by
      convert hhzero using 1 <;> rfl
    unfold recursivePositiveImage
    rw [positive_finite_image_add,hz,add_zero]
    exact hc
  obtain ⟨e,hi⟩ := recursive_positive_image_from_residual T hf s t
    ((v₀.hom≫recursiveBoundaryRepresentative T.X N s t ζ')≫XModLambdaN.incl _ 3)
    (c+h) k v z hres hc' ck hckfirst hckimage
  exact ⟨k,U,z,e,ζ',hk,hU,hd,hρ,hi⟩

/-- Naturality uses the literal boundary of the retained finite source. -/
private theorem recursive_boundary_representative_natural
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N : ℕ) (p t : ℤ)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    recursiveBoundaryRepresentative Y N p t (ζ≫XModLambdaN.map (background.nu.functor.map f) N)=
      recursiveBoundaryRepresentative X N p t ζ≫background.nu.functor.map f := by
  unfold recursiveBoundaryRepresentative
  rw [Category.assoc,XModLambdaN.proj_naturality,←Category.assoc,
    bi_susp_natural background.quotients.coherence,homotopyRegrade_comp]

/-- A prescribed top candidate lies above the middle head; adding it back
preserves detection of that head’s image. -/
private theorem recursive_ordinary_error_image_detects
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (p t : ℤ)
    (a : BiHom (t-p) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (v : Ambient background Y (p+1,t+1))
    (hc : c≫XModLambdaN.map (background.nu.functor.map f) 3=recursiveTopLabel Y p t v)
    (x : Ambient background X (p,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 x) (a≫XModLambdaN.incl _ 3-c)) :
    Detects (background.convergence (.quotient 3 (.nu Y))) (p,t,t-1)
      (finiteTargetLabel background Y 3 p t 1 ((background.classical.map f).pageMap 2 (p,t) x))
      ((a≫background.nu.functor.map f)≫XModLambdaN.incl _ 3) := by
  have hmap := KIP126.ProofTools.Internal.detects_map (.quotient 3 (.nu X)) (.quotient 3 (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) 3) (p,t,t-1) _ _ hx
  rw [←middle_finite_label_as_weight X 3 1 p t x] at hmap
  erw [finite_weight_label_natural X Y f 3 p t (t-1) (by omega) x] at hmap
  erw [middle_finite_label_as_weight Y 3 1 p t] at hmap
  apply detects_of_next_filtration_difference (.quotient 3 (.nu Y)) (p,t,t-1) _ _ _ hmap
  have heq : (a≫background.nu.functor.map f)≫XModLambdaN.incl _ 3-
      (a≫XModLambdaN.incl _ 3-c)≫XModLambdaN.map (background.nu.functor.map f) 3 =
      c≫XModLambdaN.map (background.nu.functor.map f) 3 := by
    simp only [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality]
    abel
  rw [heq,hc]
  exact recursive_top_label_filtration Y p t v

/-- The K1=1 head gate in the same coordinates as the recursive relation. -/
private theorem recursive_ordinary_first_head_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N : ℕ) (hN : 0<N) (p t A B : ℤ)
    (hA : p=A+(N:ℤ)+2) (hB : t=B+(N:ℤ)+1)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B))
    (hy : y ∈ cycles background Y ((N:ℤ)+2) (A,B))
    (hsource : (homotopyRegrade (show t-p+1=B-A by omega) (show t-1-N=B by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
        (background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y A B y)
    (c : BiHom (t-p) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (v : Ambient background Y (p+1,t+1))
    (hc : c≫XModLambdaN.map (background.nu.functor.map f) 3=recursiveTopLabel Y p t v)
    (x : Ambient background X (p,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 x)
      (recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-c)) :
    (background.classical.map f).pageMap 2 (p,t) x ∈ boundaries background Y ((N:ℤ)+1) (p,t) := by
  have hd := recursive_ordinary_error_image_detects X Y f p t
    (recursiveBoundaryRepresentative X N p t ζ) c v hc x hx
  rw [←recursive_boundary_representative_natural] at hd
  have hboundary : recursiveBoundaryRepresentative Y N p t
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N)=
      homotopyRegrade (show (B-A)-1=t-p by omega) (show B+N=t-1 by omega)
        (biSuspensionHomEquiv (B-A) B N (background.nu.functor.obj (Y.obj background.auxiliary))
          ((homotopyRegrade (show t-p+1=B-A by omega) (show t-1-N=B by omega)
            (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫XModLambdaN.proj _ N)) := by
    rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans]
    rfl
  have hh := known_source_finite_label_boundary_at_degree Y N 1 3 hN (by decide) (by decide)
    A B p t ((N:ℤ)+3) (by omega) (by omega) (by omega) y _ hsource
    (by simpa only [show (N:ℤ)+3-1=(N:ℤ)+2 by omega] using hy)
    _ hboundary _ _ hd
    (by rw [sub_self]; exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem)
  simpa only [Nat.cast_add,Nat.cast_one] using hh

/-- The top-divisible head gate preserves the original source calibration
and uses the divided source with literally the same absolute boundary. -/
private theorem recursive_ordinary_divided_head_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d N : ℕ) (hd : 0<d) (hdN : d<N) (p t A B : ℤ)
    (hA : p=A+(N-d:ℕ)+2) (hB : t=B+(N-d:ℕ)+1)
    (ζ : BiHom (t-p+1) (t-1-N)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B))
    (hy : y ∈ cycles background Y ((N-d:ℕ)+2) (A,B))
    (hsource : (homotopyRegrade (show t-p+1=B-A by omega) (show t-1-N=B-d by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
        (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel Y d hd A B y)
    (c : BiHom (t-p) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (v : Ambient background Y (p+1,t+1))
    (hc : c≫XModLambdaN.map (background.nu.functor.map f) 3=recursiveTopLabel Y p t v)
    (x : Ambient background X (p,t))
    (hx : Detects (background.convergence (.quotient 3 (.nu X))) (p,t,t-1)
      (finiteTargetLabel background X 3 p t 1 x)
      (recursiveBoundaryRepresentative X N p t ζ≫XModLambdaN.incl _ 3-c)) :
    (background.classical.map f).pageMap 2 (p,t) x ∈ boundaries background Y ((N-d:ℕ)+1) (p,t) := by
  have hdet := recursive_ordinary_error_image_detects X Y f p t
    (recursiveBoundaryRepresentative X N p t ζ) c v hc x hx
  rw [←recursive_boundary_representative_natural] at hdet
  have htop : (homotopyRegrade (show t-p+1=B-A by omega) (show t-1-N=B-d by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
        (background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabelAtWeight Y d hd (d+1) rfl A B (B-d) rfl y := by
    convert hsource using 1; rfl
  have hb : Detects (background.convergence (.quotient 3 (.nu Y))) (p,t,t-1)
      (finiteTargetLabel background Y 3 p t 1 ((background.classical.map f).pageMap 2 (p,t) x))
      (homotopyRegrade (show (B-A)-1=t-p by omega) (show (B-d)+N=t-1 by omega)
        (biSuspensionHomEquiv (B-A) (B-d) N (background.nu.functor.obj (Y.obj background.auxiliary))
          ((homotopyRegrade (show t-p+1=B-A by omega) (show t-1-N=B-d by omega)
            (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫XModLambdaN.proj _ N)≫
              XModLambdaN.incl _ 3)) := by
    rw [←regrade_comp,bi_susp_regrade,regrade_comp,normalized_homotopy_regrade_trans]
    exact hdet
  have hh := known_source_divided_boundary_detected_head Y d N (d+1) 1 3 hd hdN rfl
    (by decide) (by decide) A B (B-d) p t ((N-d:ℕ)+3) rfl (by omega) (by omega) (by omega)
    y (by simpa only [show ((N-d:ℕ):ℤ)+3-1=((N-d:ℕ):ℤ)+2 by omega] using hy) _ htop _ hb
  simpa only [Nat.cast_add,Nat.cast_one] using hh

end
end KIP126.ProofTools.Internal.SyntheticCoverage
