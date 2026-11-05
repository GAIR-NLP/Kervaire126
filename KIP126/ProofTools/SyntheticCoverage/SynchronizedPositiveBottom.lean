module

import all KIP126.ProofTools.SyntheticCoverage.SynchronizedBottomElimination
import all KIP126.ProofTools.SyntheticCoverage.RecursivePositiveCoordinates

/-! Positive synchronized bottom elimination. The selected positive-boundary
sphere automorphism is retained throughout the actual source corrections. -/

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

private def synchronizedPositiveBoundaryIso (N : ℕ) (S W : ℤ) :
    Smn (Syn:=SyntheticSpectrum) (W-S) W ≅ Smn (W-S) W :=
  recursiveSphereRegradeIso (show (W-S+1)-1=W-S by omega)
    (show (W-N)+N=W by omega) (positiveBoundarySourceIso 1 N (W-S+1) (W-N))

private def synchronizedPositiveBoundary (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    BiHom (W-S) W (background.nu.functor.obj (X.obj background.auxiliary)) :=
  (synchronizedPositiveBoundaryIso N S W).hom≫synchronizedBoundary X N S W ζ

private theorem synchronized_positive_boundary_sub (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (S W : ℤ)
    (a b : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedPositiveBoundary X N S W (a-b)=
      synchronizedPositiveBoundary X N S W a-synchronizedPositiveBoundary X N S W b := by
  simp only [synchronizedPositiveBoundary,synchronized_boundary_sub,Preadditive.comp_sub]

private theorem synchronized_positive_boundary_first (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedPositiveBoundary X N S W ζ≫XModLambdaN.incl _ 1=
      synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ 1 := by
  rw [synchronizedPositiveBoundary,Category.assoc,sphere_automorphism_quotient_projection]

private theorem synchronized_positive_residual_step
    (X : (AdamsObject (coefficients := background.coefficients))) (N K Q j : ℕ) (hK : 0<K) (hKN : K≤N) (hj : 0<j) (hjQ : j<Q) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c h : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (x u : Ambient background X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedPositiveBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)))
    (hu : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j u) (synchronizedLayer S W j h))
    (hb : x-u∈boundaries background X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ ζ' : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ'≫(background.quotients.tower _).rho K N hKN=ζ≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedPositiveBoundary X N S W ζ'≫XModLambdaN.incl _ 1=
        synchronizedPositiveBoundary X N S W ζ≫XModLambdaN.incl _ 1 ∧
      FiltrationAtLeast background.syntheticTower (S+j+1)
        (synchronizedPositiveBoundary X N S W ζ'≫XModLambdaN.incl _ Q-(c+h)) := by
  obtain ⟨T,ζb,hT,hρ,hbd⟩ := synchronized_boundary_layer_correction X N K j hK hKN S W (x-u) hb
  let T₀ := homotopyRegrade (show W-S=(W+j)-(S+j) by omega) rfl T
  have hT₀ : T₀≫XModLambdaN.incl _ 1=nativeFirstLabel X (S+j) (W+j) (x-u) := by
    simp only [T₀,←regrade_comp,hT,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have hTdet₀ := full_first_label_lambda_projection_detects X Q j hj hjQ (S+j) (W+j) (x-u) T₀ hT₀
  let v := recursiveSphereRegradeIso (show W-S=(W+j)-(S+j) by omega)
    (show W=(W+j)-j by omega) (synchronizedPositiveBoundaryIso N S W)
  have hTdet := sphere_automorphism_finite_detects X Q j hjQ (S+j) (W+j) (x-u) v
    (lambdaMultiply j T₀≫XModLambdaN.incl _ Q) hTdet₀
  have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient Q (.nu X))
    (S+j,W+j,(W+j)-j) hx hTdet
  rw [←finiteTargetLabel_sub,show x-(x-u)=u by abel] at hsub
  have hnext := detects_sub_filtration (background.convergence (.quotient Q (.nu X)))
    (S+j,W+j,(W+j)-j) hsub hu
  refine ⟨ζ-ζb,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hρ,sub_zero]
  · rw [synchronized_positive_boundary_first,synchronized_positive_boundary_first,
      synchronized_boundary_sub,hbd,Preadditive.sub_comp,←regrade_comp,
      lambda_power_first_quotient_zero X j hj (W-S) (W+j) T,regrade_zero,sub_zero]
  · apply (regrade_filtration_iff (show W-S=(W+j)-(S+j) by omega)
      (show W=(W+j)-j by omega) _ _).mp
    rw [synchronized_positive_boundary_sub,Preadditive.sub_comp]
    have heq : synchronizedPositiveBoundary X N S W ζ≫XModLambdaN.incl _ Q-
        synchronizedPositiveBoundary X N S W ζb≫XModLambdaN.incl _ Q-(c+h)=
        (synchronizedPositiveBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)-
          synchronizedPositiveBoundary X N S W ζb≫XModLambdaN.incl _ Q-h := by abel
    rw [heq]
    have hproj : lambdaMultiply j T₀≫XModLambdaN.incl _ Q=
        synchronizedLayer S W j
          (homotopyRegrade rfl (show (W+j)-j=W by omega) (lambdaMultiply j T)≫XModLambdaN.incl _ Q) := by
      simp only [T₀,synchronizedLayer,lambda_regrade,←regrade_comp,normalized_homotopy_regrade_trans]
    have hbd' : synchronizedLayer S W j (synchronizedPositiveBoundary X N S W ζb≫XModLambdaN.incl _ Q)=
        v.hom≫(lambdaMultiply j T₀≫XModLambdaN.incl _ Q) := by
      rw [hproj]
      dsimp only [v,synchronizedLayer,synchronizedPositiveBoundary]
      rw [recursive_sphere_regrade_precomp,hbd]
      simp only [Category.assoc]
    rw [←hbd'] at hnext
    simpa only [synchronizedLayer,homotopy_regrade_sub] using hnext

private def synchronizedPositiveImage
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (Q : ℕ) (S W : ℤ)
    (a : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)) :
    BiHom (W-S) (W+1) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) Q) :=
  positiveFiniteImage T hf Q (levelQuotientShiftIso T.X 1 Q) (W-S) W a

private theorem synchronized_positive_image_add
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (Q : ℕ) (S W : ℤ)
    (a b : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)) :
    synchronizedPositiveImage T hf Q S W (a+b)=
      synchronizedPositiveImage T hf Q S W a+synchronizedPositiveImage T hf Q S W b := by
  simp only [synchronizedPositiveImage,positiveFiniteImage,shiftHomotopyClass,
    Preadditive.comp_add,Functor.map_add,regrade_add,Preadditive.add_comp]

private theorem synchronized_positive_bottom_iteration
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N K Q : ℕ) (hK : 0<K) (hKN : K≤N) (hQ : 2≤Q) (S W : ℤ)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q))
    (hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ Q-c₀))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,W+j+1)))
    (hgate : ∀ j : ℕ, 1≤j → j<Q-1 →
      ∀ ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN →
      ∀ c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q),
      synchronizedPositiveImage T hf Q S W c=synchronizedPositiveImage T hf Q S W c₀ →
      ∀ x : Ambient background T.X (S+j,W+j),
      Detects (background.convergence (.quotient Q (.nu T.X))) (S+j,W+j,(W+j)-j)
        (finiteTargetLabel background T.X Q (S+j) (W+j) j x)
        (synchronizedLayer S W j (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c)) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x∈P j)
    (hcorrection : ∀ j : ℕ, 1≤j → j<Q-1 →
      ∀ x : Ambient background T.X (S+j,W+j), x∈cycles background T.X (Q-j:ℕ) (S+j,W+j) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x∈P j →
      ∃ (u : Ambient background T.X (S+j,W+j))
        (h : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)),
        Detects (background.convergence (.quotient Q (.nu T.X))) (S+j,W+j,(W+j)-j)
          (finiteTargetLabel background T.X Q (S+j) (W+j) j u) (synchronizedLayer S W j h) ∧
        synchronizedPositiveImage T hf Q S W h=0 ∧
        x-u∈boundaries background T.X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ 1=synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
      synchronizedPositiveImage T hf Q S W c=synchronizedPositiveImage T hf Q S W c₀ ∧
      FiltrationAtLeast background.syntheticTower (S+Q-1)
        (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c) := by
  have recur (j : ℕ) (hj : 1≤j) (hjQ : j≤Q-1)
      (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q))
      (hρ : ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN)
      (hb : synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ 1=synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1)
      (hc : synchronizedPositiveImage T hf Q S W c=synchronizedPositiveImage T hf Q S W c₀)
      (hr : FiltrationAtLeast background.syntheticTower (S+j)
        (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c)) :
      ∃ (ζ' : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
        (c' : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)),
        ζ'≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
        synchronizedPositiveBoundary T.X N S W ζ'≫XModLambdaN.incl _ 1=synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
        synchronizedPositiveImage T hf Q S W c'=synchronizedPositiveImage T hf Q S W c₀ ∧
        FiltrationAtLeast background.syntheticTower (S+Q-1)
          (synchronizedPositiveBoundary T.X N S W ζ'≫XModLambdaN.incl _ Q-c') := by
    induction hn : Q-1-j using Nat.strong_induction_on generalizing j ζ c with
    | h n ih =>
      by_cases hend : Q-1≤j
      · refine ⟨ζ,c,hρ,hb,hc,?_⟩
        convert hr using 1
        omega
      · have hrlayer : FiltrationAtLeast background.syntheticTower (S+j)
            (synchronizedLayer S W j (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c)) :=
          (regrade_filtration_iff _ _ _ _).mpr hr
        obtain ⟨x,hx,hxd⟩ := middle_finite_filtration_label T.X Q j (by omega)
          (S+j) (W+j) _ hrlayer
        obtain ⟨u,h,hdet,hzero,hbound⟩ := hcorrection j hj (by omega) x hx
          (hgate j hj (by omega) ζ hρ c hc x hxd)
        obtain ⟨ζ',hρ',hb',hres⟩ := synchronized_positive_residual_step T.X N K Q j
          hK hKN (by omega) (by omega) S W ζ c h x u hxd hdet hbound
        have hc' : synchronizedPositiveImage T hf Q S W (c+h)=synchronizedPositiveImage T hf Q S W c := by
          rw [synchronized_positive_image_add,hzero,add_zero]
        apply ih (Q-1-(j+1)) (by omega) (j+1) (by omega) (by omega) ζ' (c+h)
          (hρ'.trans hρ) (hb'.trans hb) (hc'.trans hc)
        · convert hres using 1
          push_cast
          omega
        · rfl
  exact recur 1 (by omega) (by omega) ζ₀ c₀ rfl rfl rfl
    (by simpa only [Nat.cast_one] using hstart)

private theorem synchronized_positive_full_boundary_square
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    verticalTranslate _ 1 (W-S) W (synchronizedPositiveBoundary T.X N S W ζ)≫lastLayerNormalizedMap T hf=
      homotopyRegrade (show (W-S+1)-1=W-S by omega) (show ((W-N)+1)+N=W+1 by omega)
        (biSuspensionHomEquiv (W-S+1) ((W-N)+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (W-S+1) (W-N) ζ≫XModLambdaN.proj _ N)) := by
  dsimp only [synchronizedPositiveBoundary,synchronizedPositiveBoundaryIso,synchronizedBoundary]
  rw [recursive_sphere_regrade_precomp,vertical_translate_regrade,←regrade_comp,
    recursive_positive_absolute_boundary_coordinates,normalized_homotopy_regrade_trans]

private theorem synchronized_positive_error_image_detects
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N Q j : ℕ) (hj : 0<j) (hjQ : j<Q) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q))
    (hc : FiltrationAtLeast background.syntheticTower (S+j+2) (synchronizedPositiveImage T hf Q S W c))
    (x : Ambient background T.X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu T.X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background T.X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c))) :
    Detects (background.convergence (.quotient Q (.nu T.Y))) (S+j+1,W+j+1,(W+j+1)-j)
      (finiteTargetLabel background T.Y Q (S+j+1) (W+j+1) j
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x))
      (homotopyRegrade (show W-S=(W+j+1)-(S+j+1) by omega) (show W+1=(W+j+1)-j by omega)
        (synchronizedPositiveImage T hf Q S W
          (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q))) := by
  have hmap := selective_positive_image_detects T hf Q j hj hjQ (S+j) (W+j)
    (levelQuotientShiftIso T.X 1 Q) (level_quotient_shift_incl T.X 1 Q) x _ hx
  have hmap' : Detects (background.convergence (.quotient Q (.nu T.Y))) (S+j+1,W+j+1,(W+j+1)-j)
      (finiteTargetLabel background T.Y Q (S+j+1) (W+j+1) j
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x))
      (homotopyRegrade (show W-S=(W+j+1)-(S+j+1) by omega) (show W+1=(W+j+1)-j by omega)
        (synchronizedPositiveImage T hf Q S W
          (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c))) := by
    simpa only [synchronizedLayer,synchronizedPositiveImage,←positiveFiniteImage_regrade,
      normalized_homotopy_regrade_trans] using hmap
  apply detects_of_next_filtration_difference (.quotient Q (.nu T.Y))
    (S+j+1,W+j+1,(W+j+1)-j) _ _ _ hmap'
  rw [←homotopy_regrade_sub]
  simp only [synchronizedPositiveImage,positiveFiniteImage_sub,sub_sub_cancel]
  exact (regrade_filtration_iff _ _ _ _).mpr (by simpa only [synchronizedPositiveImage,show S+j+1+1=S+j+2 by omega] using hc)

private theorem synchronized_positive_divided_head_gate
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (d N Q j : ℕ) (hd : 0<d) (hdN : d<N) (hj : 0<j) (hjQ : j<Q)
    (S W A B D : ℤ) (hS : S=A+(N-d:ℕ)) (hW : W+1=B+(N-d:ℕ))
    (hD : ((N-d:ℕ):ℤ)+j+1<D)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (y : Ambient background T.Y (A,B)) (hy : y∈cycles background T.Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show (W-N)+1=B-d by omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (W-S+1) (W-N) ζ))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel T.Y d hd A B y)
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q))
    (hc : FiltrationAtLeast background.syntheticTower (S+j+2) (synchronizedPositiveImage T hf Q S W c))
    (x : Ambient background T.X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu T.X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background T.X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c))) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x∈
      boundaries background T.Y ((N-d:ℕ)+j) (S+j+1,W+j+1) := by
  have hdet := synchronized_positive_error_image_detects T hf N Q j hj hjQ S W ζ c hc x hx
  simp only [synchronizedPositiveImage,positive_finite_image_full_projection] at hdet
  rw [synchronized_positive_full_boundary_square,←regrade_comp,normalized_homotopy_regrade_trans] at hdet
  have htop : (homotopyRegrade (show W-S+1=B-A by omega) (show (W-N)+1=B-d by omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (W-S+1) (W-N) ζ))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabelAtWeight T.Y d hd (d+1) rfl A B (B-d) rfl y := by
    simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  apply known_source_divided_boundary_detected_head T.Y d N (d+1) j Q hd hdN rfl hj hjQ
    A B (B-d) (S+j+1) (W+j+1) D rfl (by omega) (by omega) hD y hy _ htop
  simpa only [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans] using hdet
private theorem synchronized_positive_h_cycle_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (Q j q : ℕ) (hq : 0<q) (hQ : Q=j+q) (s t m w : ℤ)
    (hm : m=t-s) (hw : w=t-j)
    (z : Ambient background T.Z (s,t+1)) (hz : z∈cycles background T.Z q (s,t+1)) :
    ∃ h : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q),
      Detects (background.convergence (.quotient Q (.nu T.X))) (s,t,t-j)
        (finiteTargetLabel background T.X Q s t j (KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z))
        (homotopyRegrade hm hw h) ∧
      positiveFiniteImage T hf Q (levelQuotientShiftIso T.X 1 Q) m w h=0 := by
  subst Q; subst m; subst w
  exact selective_positive_f_native_cycle_image T he hf hg hh hT j q hq s t
    (levelQuotientShiftIso T.X 1 (j+q)) (level_quotient_shift_incl T.X 1 (j+q)) z hz _
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T s t z)

private theorem synchronized_positive_bottom_core
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N d Q : ℕ) (hd : 0<d) (hdN : d<N) (hQ : 2≤Q) (S W A B D : ℤ)
    (hS : S=A+(N-d:ℕ)) (hW : W+1=B+(N-d:ℕ)) (hD : (N-d:ℕ)+Q≤D)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (y : Ambient background T.Y (A,B)) (hy : y∈cycles background T.Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show (W-N)+1=B-d by omega)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (W-S+1) (W-N) ζ₀))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel T.Y d hd A B y)
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q))
    (hc₀ : FiltrationAtLeast background.syntheticTower (S+Q) (synchronizedPositiveImage T hf Q S W c₀))
    (hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ Q-c₀))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,W+j+1)))
    (hP : ∀ j : ℕ, 1≤j → j<Q-1 → boundaries background T.Y ((N-d:ℕ)+j) (S+j+1,W+j+1)≤P j)
    (hmid : ∀ j : ℕ, 1≤j → j<Q-1 →
      ∀ x : Ambient background T.X (S+j,W+j), x∈cycles background T.X ((Q:ℤ)-j) (S+j,W+j) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (W+j) x∈P j →
      ∃ z : Ambient background T.Z (S+j,W+j+1), z∈cycles background T.Z ((Q:ℤ)-j) (S+j,W+j+1) ∧
        x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (W+j) z ∈
          boundaries background T.X ((N-d:ℕ)+j) (S+j,W+j)) :
    ∃ (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q)),
      ζ≫(background.quotients.tower _).rho (d+1) N (by omega)=ζ₀≫(background.quotients.tower _).rho (d+1) N (by omega) ∧
      synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ 1=synchronizedPositiveBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
      synchronizedPositiveImage T hf Q S W c=synchronizedPositiveImage T hf Q S W c₀ ∧
      FiltrationAtLeast background.syntheticTower (S+Q-1)
        (synchronizedPositiveBoundary T.X N S W ζ≫XModLambdaN.incl _ Q-c) := by
  apply synchronized_positive_bottom_iteration T hf N (d+1) Q (by omega) (by omega) hQ S W ζ₀ c₀ hstart P
  · intro j hj hjQ ζ hρ c hc x hx
    apply hP j hj hjQ
    apply synchronized_positive_divided_head_gate T hf d N Q j hd hdN (by omega) (by omega)
      S W A B D hS hW (by omega) ζ y hy _ c _ x hx
    · rw [←regrade_comp,positive_finite_image_restriction T hf (d+1) N (by omega),hρ,
        ←positive_finite_image_restriction T hf (d+1) N (by omega),regrade_comp]
      exact hsource
    · rw [hc]
      exact background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hc₀
  · intro j hj hjQ x hx hxp
    obtain ⟨z,hz,hxz⟩ := hmid j hj hjQ x
      (by simpa only [Nat.cast_sub (show j≤Q by omega)] using hx) hxp
    obtain ⟨h,hdet,hzero⟩ := synchronized_positive_h_cycle_at T he hf hg hh hT Q j (Q-j)
      (by omega) (by omega) (S+j) (W+j) (W-S) W (by omega) (by omega) z
      (by simpa only [Nat.cast_sub (show j≤Q by omega)] using hz)
    refine ⟨_,h,hdet,hzero,?_⟩
    convert hxz using 1
    congr 1
    omega
private theorem synchronized_positive_top_of_residual
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (q : ℕ) (hq : 0<q) (S W : ℤ)
    (U : BiHom (W-S) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (v : Ambient background T.Y (S+q+1,(W+1)+q))
    (hc : homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) rfl
      (synchronizedPositiveImage T hf (q+1) S W c)=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) ((W+1)+q) (W+1) (by omega) v)
    (hres : FiltrationAtLeast background.syntheticTower (S+q)
      (U≫XModLambdaN.incl _ (q+1)-c)) :
    ∃ e : Ambient background T.X (S+q,W+q), ∃ error : Ambient background T.Y (S+q+1,(W+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (W+q) e) ∧
      homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) rfl
        ((verticalTranslate _ 1 (W-S) W U≫lastLayerNormalizedMap T hf)≫XModLambdaN.incl _ (q+1))=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) ((W+1)+q) (W+1) (by omega) (v+error) := by
  let e₀ := homotopyRegrade (show W-S=(W+q)-(S+q) by omega) rfl
    (U≫XModLambdaN.incl _ (q+1)-c)
  obtain ⟨e,ht⟩ := last_layer_positive_image_eq_top_at_weight T hf q (q+1) hq rfl
    (S+q) (W+q) W (by omega) (levelQuotientShiftIso T.X 1 (q+1))
    (level_quotient_shift_incl T.X 1 (q+1)) e₀ ((regrade_filtration_iff _ _ _ _).mpr hres)
  let error := topClassicalRegrade (X:=T.Y)
    (show (S+q+1,W+q+1)=(S+q+1,(W+1)+q) by congr 1;omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (W+q) e)
  have ht' := congrArg (homotopyRegrade
    (show (W+q+1)-(S+q+1)=((W+1)+q)-(S+q+1) by omega) (rfl : W+1=W+1)) ht
  rw [top_label_at_weight_regrade T.Y q (q+1) hq rfl
    (S+q+1) (W+q+1) (S+q+1) ((W+1)+q) (W+1) rfl (by omega)] at ht'
  have ht'' : homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) rfl
      (synchronizedPositiveImage T hf (q+1) S W (U≫XModLambdaN.incl _ (q+1)-c))=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) ((W+1)+q) (W+1) (by omega) error := by
    simpa only [e₀,error,synchronizedPositiveImage,←positiveFiniteImage_regrade,
      normalized_homotopy_regrade_trans] using ht'
  have hsum : synchronizedPositiveImage T hf (q+1) S W (U≫XModLambdaN.incl _ (q+1))=
      synchronizedPositiveImage T hf (q+1) S W c+
        synchronizedPositiveImage T hf (q+1) S W (U≫XModLambdaN.incl _ (q+1)-c) := by
    simp only [synchronizedPositiveImage,positiveFiniteImage_sub]
    abel
  refine ⟨e,error,top_classical_regrade_heq _ _,?_⟩
  have htop := congrArg (homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) (rfl : W+1=W+1)) hsum
  rw [regrade_add,hc,ht'',←finite_top_label_at_weight_add] at htop
  simpa only [synchronizedPositiveImage,positive_finite_image_full_projection] using htop

private theorem synchronized_positive_boundary_top
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N q : ℕ) (hq : 0<q) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (v : Ambient background T.Y (S+q+1,(W+1)+q))
    (htop : homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) rfl
        ((verticalTranslate _ 1 (W-S) W (synchronizedPositiveBoundary T.X N S W ζ)≫lastLayerNormalizedMap T hf)≫
          XModLambdaN.incl _ (q+1))=
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) ((W+1)+q) (W+1) (by omega) v) :
    homotopyRegrade (show (W-S+1)-1=((W+1)+q)-(S+q+1) by omega)
      (show ((W-N)+1)+N=((W+1)+q)-q by omega)
      (biSuspensionHomEquiv (W-S+1) ((W-N)+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (W-S+1) (W-N) ζ≫XModLambdaN.proj _ N)≫
          XModLambdaN.incl _ (q+1))=
      finiteTopLabel T.Y q hq (S+q+1) ((W+1)+q) v := by
  rw [synchronized_positive_full_boundary_square,←regrade_comp,normalized_homotopy_regrade_trans] at htop
  have h := congrArg (homotopyRegrade (rfl : ((W+1)+q)-(S+q+1)=((W+1)+q)-(S+q+1))
    (show W+1=((W+1)+q)-q by omega)) htop
  simpa only [normalized_homotopy_regrade_trans,finiteTopLabelAtWeight,top_target_regrade_self] using h
set_option maxHeartbeats 200000 in
private theorem synchronized_positive_common_native
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (S W : ℤ)
    (u : Ambient background T.X (S,W)) (z : Ambient background T.Z (S,W+1))
    (v : Ambient background T.Y (S+q+1,(W+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (W+1)
      ((background.classical.map T.h).pageMap 2 (S,W+1) z) (by simpa using u))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,W+1) (S+q+1,(W+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(W+1)+q) v)) :
    ∃ c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c≫(background.quotients.tower _).rho 1 (q+1) (by omega)=nativeFirstLabel T.X S W u ∧
      homotopyRegrade (show W-S=((W+1)+q)-(S+q+1) by omega) rfl
        (synchronizedPositiveImage T hf (q+1) S W c)=
        finiteTopLabelAtWeight T.Y q hq (q+1) rfl (S+q+1) ((W+1)+q) (W+1) (by omega) v := by
  obtain ⟨c,hc,hi⟩ := finite_common_native_lift_positive_f_at
    T he hT hf hg hh q hq S W (S+q+1) ((W+1)+q) rfl rfl z u v hu hd
  refine ⟨c,hc,?_⟩
  dsimp only [synchronizedPositiveImage]
  rw [hi,normalized_homotopy_regrade_trans]
  rfl

end
end KIP126.ProofTools.Internal.SyntheticCoverage
