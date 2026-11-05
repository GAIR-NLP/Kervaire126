module

import all KIP126.ProofTools.SyntheticCoverage.SynchronizedSourceCorrection
import all KIP126.ProofTools.SyntheticCoverage.KnownSourceOrdinary

/-! Bottom elimination with genuine early source boundaries. The state is
an actual finite source together with a finite bottom candidate. Every
boundary correction updates the source and its literal boundary together. -/

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

private def synchronizedBoundary (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    BiHom (W-S) W (background.nu.functor.obj (X.obj background.auxiliary)) :=
  homotopyRegrade (show (W-S+1)-1=W-S by omega) (show (W-N)+N=W by omega)
    (biSuspensionHomEquiv (W-S+1) (W-N) N (background.nu.functor.obj (X.obj background.auxiliary))
      (ζ≫XModLambdaN.proj _ N))

private def synchronizedLayer {A : SyntheticSpectrum} (S W : ℤ) (j : ℕ)
    (a : BiHom (W-S) W A) : BiHom ((W+j)-(S+j)) ((W+j)-j) A :=
  homotopyRegrade (by omega) (by omega) a

private theorem synchronized_boundary_sub (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (S W : ℤ)
    (a b : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedBoundary X N S W (a-b)=synchronizedBoundary X N S W a-synchronizedBoundary X N S W b := by
  simp only [synchronizedBoundary,Preadditive.sub_comp,map_sub,homotopy_regrade_sub]

private theorem synchronized_boundary_layer_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K j : ℕ) (hK : 0<K) (hKN : K≤N) (S W : ℤ)
    (b : Ambient background X (S+j,W+j))
    (hb : b∈boundaries background X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ (T : BiHom (W-S) (W+j) (background.nu.functor.obj (X.obj background.auxiliary)))
      (ζb : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)),
      T≫XModLambdaN.incl _ 1=
        homotopyRegrade (show (W+j)-(S+j)=W-S by omega) rfl (nativeFirstLabel X (S+j) (W+j) b) ∧
      ζb≫(background.quotients.tower _).rho K N hKN=0 ∧
      synchronizedBoundary X N S W ζb=
        homotopyRegrade rfl (show (W+j)-j=W by omega) (lambdaMultiply j T) := by
  obtain ⟨T₀,hT₀,hzero⟩ := cumulative_boundary_torsion_lift_unshifted X (N-K+j) (S+j) (W+j) b hb
  let T := homotopyRegrade (show (W+j)-(S+j)=W-S by omega) rfl T₀
  let T' := homotopyRegrade (show W-S=(W-S+1)-1 by omega) (show W+j=(W-N)+N+j by omega) T
  have hT' : lambdaMultiply (N-K+j) T'=0 := by
    simp only [T',T,lambda_regrade,hzero,regrade_zero]
  obtain ⟨ζb,hρ,hboundary⟩ := synchronized_torsion_source_correction X N K j hK hKN
    (W-S+1) (W-N) T' hT'
  refine ⟨T,ζb,?_,hρ,?_⟩
  · simp only [T,←regrade_comp,hT₀]
    rfl
  · dsimp only [synchronizedBoundary]
    rw [hboundary]
    simp only [T',lambda_regrade,normalized_homotopy_regrade_trans]

/-- A single source-boundary and finite-H correction. No image of the
old complete boundary is retained after changing the finite source. -/
private theorem synchronized_residual_step
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N K Q j : ℕ) (hK : 0<K) (hKN : K≤N) (hj : 0<j) (hjQ : j<Q) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c h : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (x u : Ambient background X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)))
    (hu : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j u) (synchronizedLayer S W j h))
    (hzero : h≫XModLambdaN.map (background.nu.functor.map f) Q=0)
    (hb : x-u∈boundaries background X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ ζ' : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ'≫(background.quotients.tower _).rho K N hKN=ζ≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedBoundary X N S W ζ'≫XModLambdaN.incl _ 1=
        synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ 1 ∧
      (c+h)≫XModLambdaN.map (background.nu.functor.map f) Q=c≫XModLambdaN.map (background.nu.functor.map f) Q ∧
      FiltrationAtLeast background.syntheticTower (S+j+1)
        (synchronizedBoundary X N S W ζ'≫XModLambdaN.incl _ Q-(c+h)) := by
  obtain ⟨T,ζb,hT,hρ,hbd⟩ := synchronized_boundary_layer_correction X N K j hK hKN S W (x-u) hb
  let T₀ := homotopyRegrade (show W-S=(W+j)-(S+j) by omega) rfl T
  have hT₀ : T₀≫XModLambdaN.incl _ 1=nativeFirstLabel X (S+j) (W+j) (x-u) := by
    simp only [T₀,←regrade_comp,hT,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have hTdet := full_first_label_lambda_projection_detects X Q j hj hjQ (S+j) (W+j) (x-u) T₀ hT₀
  have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub (.quotient Q (.nu X))
    (S+j,W+j,(W+j)-j) hx hTdet
  rw [←finiteTargetLabel_sub,show x-(x-u)=u by abel] at hsub
  have hnext := detects_sub_filtration (background.convergence (.quotient Q (.nu X)))
    (S+j,W+j,(W+j)-j) hsub hu
  refine ⟨ζ-ζb,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hρ,sub_zero]
  · rw [synchronized_boundary_sub,hbd,Preadditive.sub_comp,←regrade_comp,
      lambda_power_first_quotient_zero X j hj (W-S) (W+j) T,regrade_zero,sub_zero]
  · rw [Preadditive.add_comp,hzero,add_zero]
  · apply (regrade_filtration_iff (show W-S=(W+j)-(S+j) by omega)
      (show W=(W+j)-j by omega) _ _).mp
    rw [synchronized_boundary_sub,hbd,Preadditive.sub_comp]
    have heq : synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-
        homotopyRegrade rfl (show (W+j)-j=W by omega) (lambdaMultiply j T)≫XModLambdaN.incl _ Q-(c+h)=
        (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)-
          homotopyRegrade rfl (show (W+j)-j=W by omega) (lambdaMultiply j T)≫XModLambdaN.incl _ Q-h := by abel
    rw [heq]
    simpa only [synchronizedLayer,T₀,homotopy_regrade_sub,←regrade_comp,
      lambda_regrade,normalized_homotopy_regrade_trans] using hnext

private theorem synchronized_boundary_natural
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    synchronizedBoundary Y N S W (ζ≫XModLambdaN.map (background.nu.functor.map f) N)=
      synchronizedBoundary X N S W ζ≫background.nu.functor.map f := by
  unfold synchronizedBoundary
  rw [Category.assoc,XModLambdaN.proj_naturality,←Category.assoc,
    bi_susp_natural background.quotients.coherence,homotopyRegrade_comp]

private theorem synchronized_ordinary_error_image_detects
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N Q j : ℕ) (S W : ℤ)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (hc : FiltrationAtLeast background.syntheticTower (S+j+1) (c≫XModLambdaN.map (background.nu.functor.map f) Q))
    (x : Ambient background X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c))) :
    Detects (background.convergence (.quotient Q (.nu Y))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background Y Q (S+j) (W+j) j
        ((background.classical.map f).pageMap 2 (S+j,W+j) x))
      (synchronizedLayer S W j
        (synchronizedBoundary Y N S W (ζ≫XModLambdaN.map (background.nu.functor.map f) N)≫XModLambdaN.incl _ Q)) := by
  have hmap := detects_map (.quotient Q (.nu X)) (.quotient Q (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) Q) (S+j,W+j,(W+j)-j) _ _ hx
  erw [←middle_finite_label_as_weight,finite_weight_label_natural X Y f Q (S+j) (W+j)
    ((W+j)-j) (by omega) x,middle_finite_label_as_weight] at hmap
  apply detects_of_next_filtration_difference (.quotient Q (.nu Y))
    (S+j,W+j,(W+j)-j) _ _ _ hmap
  rw [synchronized_boundary_natural]
  simp only [synchronizedLayer,←regrade_comp,←homotopy_regrade_sub]
  have heq : (synchronizedBoundary X N S W ζ≫background.nu.functor.map f)≫XModLambdaN.incl _ Q-
      (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)≫XModLambdaN.map (background.nu.functor.map f) Q=
      c≫XModLambdaN.map (background.nu.functor.map f) Q := by
    simp only [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality]
    abel
  rw [heq]
  exact (regrade_filtration_iff _ _ _ _).mpr hc

/-- The source may have changed, but this gate uses its current protected
top restriction and its current literal absolute boundary. -/
private theorem synchronized_ordinary_divided_head_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d N Q j : ℕ) (hd : 0<d) (hdN : d<N) (hj : 0<j) (hjQ : j<Q)
    (S W A B D : ℤ) (hS : S=A+(N-d:ℕ)+1) (hW : W=B+(N-d:ℕ))
    (hD : ((N-d:ℕ):ℤ)+j+1<D)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B)) (hy : y∈cycles background Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B-d by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel Y d hd A B y)
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (hc : FiltrationAtLeast background.syntheticTower (S+j+1) (c≫XModLambdaN.map (background.nu.functor.map f) Q))
    (x : Ambient background X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c))) :
    (background.classical.map f).pageMap 2 (S+j,W+j) x∈boundaries background Y ((N-d:ℕ)+j) (S+j,W+j) := by
  have hdet := synchronized_ordinary_error_image_detects X Y f N Q j S W ζ c hc x hx
  have htop : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B-d by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=
      finiteTopLabelAtWeight Y d hd (d+1) rfl A B (B-d) rfl y := by
    simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  apply known_source_divided_boundary_detected_head Y d N (d+1) j Q hd hdN rfl hj hjQ
    A B (B-d) (S+j) (W+j) D rfl (by omega) (by omega) hD y hy _ htop
  simpa only [synchronizedLayer,synchronizedBoundary,←regrade_comp,bi_susp_regrade,
    normalized_homotopy_regrade_trans] using hdet

private theorem synchronized_ordinary_first_head_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N Q j : ℕ) (hN : 0<N) (hj : 0<j) (hjQ : j<Q)
    (S W A B D : ℤ) (hS : S=A+N+1) (hW : W=B+N) (hD : (N:ℤ)+j+1<D)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B)) (hy : y∈cycles background Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y A B y)
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (hc : FiltrationAtLeast background.syntheticTower (S+j+1) (c≫XModLambdaN.map (background.nu.functor.map f) Q))
    (x : Ambient background X (S+j,W+j))
    (hx : Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c))) :
    (background.classical.map f).pageMap 2 (S+j,W+j) x∈boundaries background Y ((N+j:ℕ):ℤ) (S+j,W+j) := by
  have hdet := synchronized_ordinary_error_image_detects X Y f N Q j S W ζ c hc x hx
  let η := homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B by omega)
    (ζ≫XModLambdaN.map (background.nu.functor.map f) N)
  let β := synchronizedLayer S W j (synchronizedBoundary Y N S W (ζ≫XModLambdaN.map (background.nu.functor.map f) N))
  have hβ : β=homotopyRegrade (show (B-A)-1=(W+j)-(S+j) by omega) (show B+N=(W+j)-j by omega)
      (biSuspensionHomEquiv (B-A) B N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)) := by
    simp only [β,η,synchronizedLayer,synchronizedBoundary,←regrade_comp,bi_susp_regrade,
      normalized_homotopy_regrade_trans]
  apply known_source_finite_label_boundary_at_degree Y N j Q hN hj hjQ
    A B (S+j) (W+j) D (by omega) (by omega) hD y η hsource hy β hβ _
    (synchronizedLayer S W j
      (synchronizedBoundary Y N S W (ζ≫XModLambdaN.map (background.nu.functor.map f) N)≫XModLambdaN.incl _ Q)) hdet
  simp only [β,synchronizedLayer,←regrade_comp,sub_self]
  exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem

/-- Finite induction on the actual pair (source,candidate). The step
construction is consumed on the unique actual head, and the protected source
restriction is carried through every recursive call. -/
private theorem synchronized_bottom_iteration
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N K Q : ℕ) (hK : 0<K) (hKN : K≤N) (hQ : 2≤Q) (S W : ℤ)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedBoundary X N S W ζ₀≫XModLambdaN.incl _ Q-c₀))
    (P : (j : ℕ) → Submodule ℤ (Ambient background Y (S+j,W+j)))
    (hgate : ∀ j : ℕ, 1≤j → j<Q-1 →
      ∀ ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN →
      ∀ c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q),
      c≫XModLambdaN.map (background.nu.functor.map f) Q=c₀≫XModLambdaN.map (background.nu.functor.map f) Q →
      ∀ x : Ambient background X (S+j,W+j),
      Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
        (finiteTargetLabel background X Q (S+j) (W+j) j x)
        (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)) →
      (background.classical.map f).pageMap 2 (S+j,W+j) x∈P j)
    (hcorrection : ∀ j : ℕ, 1≤j → j<Q-1 →
      ∀ x : Ambient background X (S+j,W+j), x∈cycles background X (Q-j:ℕ) (S+j,W+j) →
      (background.classical.map f).pageMap 2 (S+j,W+j) x∈P j →
      ∃ (u : Ambient background X (S+j,W+j))
        (h : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q)),
        Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
          (finiteTargetLabel background X Q (S+j) (W+j) j u) (synchronizedLayer S W j h) ∧
        h≫XModLambdaN.map (background.nu.functor.map f) Q=0 ∧
        x-u∈boundaries background X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
      (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q)),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ 1=synchronizedBoundary X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
      c≫XModLambdaN.map (background.nu.functor.map f) Q=c₀≫XModLambdaN.map (background.nu.functor.map f) Q ∧
      FiltrationAtLeast background.syntheticTower (S+Q-1)
        (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c) := by
  have recur (j : ℕ) (hj : 1≤j) (hjQ : j≤Q-1)
      (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
      (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
      (hρ : ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN)
      (hb : synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ 1=synchronizedBoundary X N S W ζ₀≫XModLambdaN.incl _ 1)
      (hc : c≫XModLambdaN.map (background.nu.functor.map f) Q=c₀≫XModLambdaN.map (background.nu.functor.map f) Q)
      (hr : FiltrationAtLeast background.syntheticTower (S+j)
        (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)) :
      ∃ (ζ' : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
        (c' : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q)),
        ζ'≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
        synchronizedBoundary X N S W ζ'≫XModLambdaN.incl _ 1=synchronizedBoundary X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
        c'≫XModLambdaN.map (background.nu.functor.map f) Q=c₀≫XModLambdaN.map (background.nu.functor.map f) Q ∧
        FiltrationAtLeast background.syntheticTower (S+Q-1)
          (synchronizedBoundary X N S W ζ'≫XModLambdaN.incl _ Q-c') := by
    induction hn : Q-1-j using Nat.strong_induction_on generalizing j ζ c with
    | h n ih =>
      by_cases hend : Q-1≤j
      · refine ⟨ζ,c,hρ,hb,hc,?_⟩
        convert hr using 1
        omega
      · have hrlayer : FiltrationAtLeast background.syntheticTower (S+j)
            (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)) :=
          (regrade_filtration_iff _ _ _ _).mpr hr
        obtain ⟨x,hx,hxd⟩ := middle_finite_filtration_label X Q j (by omega)
          (S+j) (W+j) _ hrlayer
        obtain ⟨u,h,hdet,hzero,hbound⟩ := hcorrection j hj (by omega) x hx
          (hgate j hj (by omega) ζ hρ c hc x hxd)
        obtain ⟨ζ',hρ',hb',hc',hres⟩ := synchronized_residual_step X Y f N K Q j
          hK hKN (by omega) (by omega) S W ζ c h x u hxd hdet hzero hbound
        apply ih (Q-1-(j+1)) (by omega) (j+1) (by omega) (by omega) ζ' (c+h)
          (hρ'.trans hρ) (hb'.trans hb) (hc'.trans hc)
        · convert hres using 1
          push_cast
          omega
        · rfl
  exact recur 1 (by omega) (by omega) ζ₀ c₀ rfl rfl rfl
    (by simpa only [Nat.cast_one] using hstart)

private theorem synchronized_positive_h_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (Q j q : ℕ) (hq : 0<q) (hQ : Q=j+q) (s p t m w : ℤ)
    (hp : p=s+1) (hm : m=t-p) (hw : w=t-j)
    (z : Ambient background T.Z (s,t)) (hz : z∈cycles background T.Z q (s,t))
    (u : Ambient background T.X (p,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa only [hp,add_sub_cancel_right] using u)) :
    ∃ h : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q),
      Detects (background.convergence (.quotient Q (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X Q p t j u) (homotopyRegrade hm hw h) ∧
      h≫XModLambdaN.map (background.nu.functor.map T.f) Q=0 := by
  subst Q; subst p; subst m; subst w
  obtain ⟨h,hdet,hzero⟩ := middle_positive_h_native_cycle_image T he hf hg hh hT j q hq s t z hz u hu
  exact ⟨h,hdet,hzero⟩

private theorem synchronized_positive_g_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (Q j q : ℕ) (hq : 0<q) (hQ : Q=j+q) (s p t m w : ℤ)
    (hp : p=s+1) (hm : m=t-p) (hw : w=t-j)
    (z : Ambient background T.Z (p,t+1)) (hz : z∈cycles background T.Z q (p,t+1))
    (u : Ambient background T.X (p,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass p (t+1)
      ((background.classical.map T.h).pageMap 2 (p,t+1) z)
      (by simpa only [add_sub_cancel_right] using u)) :
    ∃ h : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) Q),
      Detects (background.convergence (.quotient Q (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X Q p t j u) (homotopyRegrade hm hw h) ∧
      h≫XModLambdaN.map (background.nu.functor.map T.f) Q=0 := by
  subst Q; subst p; subst m; subst w
  obtain ⟨h,hdet,hzero⟩ := selective_positive_g_native_cycle_image T he hf hg hh hT j q hq s t z hz u hu
  exact ⟨h,hdet,hzero⟩

/-- At the last layer the updated source, not the old one, has the exact
prescribed top image plus one actual F₂ error. -/
private theorem synchronized_ordinary_top_of_residual
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N b : ℕ) (hb : 0<b) (S W A B : ℤ) (hA : A=S+b) (hB : B=W+b)
    (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (b+1)))
    (v : Ambient background Y (A,B))
    (hc : c≫XModLambdaN.map (background.nu.functor.map f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel Y b hb A B v))
    (hr : FiltrationAtLeast background.syntheticTower A
      (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ (b+1)-c)) :
    ∃ e : Ambient background X (A,B),
      homotopyRegrade (show W-S=B-A by omega) rfl
        ((synchronizedBoundary X N S W ζ≫background.nu.functor.map f)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight Y b hb (b+1) rfl A B W (by omega)
        (v+(background.classical.map f).pageMap 2 (A,B) e) := by
  let r := synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ (b+1)-c
  let r' := homotopyRegrade (show W-S=B-A by omega) rfl r
  have hr' : FiltrationAtLeast background.syntheticTower A r' :=
    (regrade_filtration_iff _ _ _ _).mpr hr
  obtain ⟨e,he⟩ := last_layer_ordinary_image_eq_top_at_weight X Y f b (b+1) hb rfl
    A B W (by omega) r' hr'
  have hsum : (synchronizedBoundary X N S W ζ≫background.nu.functor.map f)≫XModLambdaN.incl _ (b+1)=
      c≫XModLambdaN.map (background.nu.functor.map f) (b+1)+r≫XModLambdaN.map (background.nu.functor.map f) (b+1) := by
    dsimp only [r]
    rw [Preadditive.sub_comp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    abel
  refine ⟨e,?_⟩
  rw [hsum,regrade_add,hc]
  have hc' : homotopyRegrade (show W-S=B-A by omega) rfl
      (homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel Y b hb A B v))=
      finiteTopLabelAtWeight Y b hb (b+1) rfl A B W (by omega) v := by
    simp only [finiteTopLabelAtWeight,last_layer_regrade_trans]
  rw [hc']
  have he' : homotopyRegrade (show W-S=B-A by omega) rfl
      (r≫XModLambdaN.map (background.nu.functor.map f) (b+1))=
      finiteTopLabelAtWeight Y b hb (b+1) rfl A B W (by omega)
        ((background.classical.map f).pageMap 2 (A,B) e) := by
    simpa only [r',←regrade_comp] using he
  rw [he',finite_top_label_at_weight_add]


private def SynchronizedHeadGate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N K Q : ℕ) (hKN : K≤N) (S W : ℤ)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q))
    (P : (j : ℕ) → Submodule ℤ (Ambient background Y (S+j,W+j))) : Prop :=
  ∀ j : ℕ, 1≤j → j<Q-1 →
    ∀ ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
    ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN →
    ∀ c : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) Q),
    c≫XModLambdaN.map (background.nu.functor.map f) Q=c₀≫XModLambdaN.map (background.nu.functor.map f) Q →
    ∀ x : Ambient background X (S+j,W+j),
    Detects (background.convergence (.quotient Q (.nu X))) (S+j,W+j,(W+j)-j)
      (finiteTargetLabel background X Q (S+j) (W+j) j x)
      (synchronizedLayer S W j (synchronizedBoundary X N S W ζ≫XModLambdaN.incl _ Q-c)) →
    (background.classical.map f).pageMap 2 (S+j,W+j) x∈P j

private theorem synchronized_ordinary_first_protected_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N b : ℕ) (hN : 0<N) (hb : 0<b)
    (S W A B D : ℤ) (hS : S=A+N+1) (hW : W=B+N) (hD : (N:ℤ)+(b+1:ℕ)≤D)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B)) (hy : y∈cycles background Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B by omega)
      (ζ₀≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y A B y)
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (b+1)))
    (hc₀ : FiltrationAtLeast background.syntheticTower (S+b) (c₀≫XModLambdaN.map (background.nu.functor.map f) (b+1)))
    (P : (j : ℕ) → Submodule ℤ (Ambient background Y (S+j,W+j)))
    (hP : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background Y ((N+j:ℕ):ℤ) (S+j,W+j)≤P j) :
    SynchronizedHeadGate X Y f N 1 (b+1) hN S W ζ₀ c₀ P := by
  intro j hj hjb ζ hρ c hc x hx
  have hsource' : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y A B y := by
    rw [←regrade_comp,recursive_ordinary_protected_image X Y f 1 N hN _ _ ζ ζ₀ hρ]
    simpa only [regrade_comp] using hsource
  apply hP j hj hjb
  apply synchronized_ordinary_first_head_gate X Y f N (b+1) j hN (by omega) (by omega)
    S W A B D hS hW (by omega) ζ y hy hsource' c _ x hx
  rw [hc]
  exact background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hc₀

private theorem synchronized_ordinary_divided_protected_gate
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d N b : ℕ) (hd : 0<d) (hdN : d<N) (hb : 0<b)
    (S W A B D : ℤ) (hS : S=A+(N-d:ℕ)+1) (hW : W=B+(N-d:ℕ))
    (hD : ((N-d:ℕ):ℤ)+(b+1:ℕ)≤D)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (y : Ambient background Y (A,B)) (hy : y∈cycles background Y (D-1) (A,B))
    (hsource : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B-d by omega)
      (ζ₀≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel Y d hd A B y)
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (b+1)))
    (hc₀ : FiltrationAtLeast background.syntheticTower (S+b) (c₀≫XModLambdaN.map (background.nu.functor.map f) (b+1)))
    (P : (j : ℕ) → Submodule ℤ (Ambient background Y (S+j,W+j)))
    (hP : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background Y ((N-d:ℕ)+j) (S+j,W+j)≤P j) :
    SynchronizedHeadGate X Y f N (d+1) (b+1) (by omega) S W ζ₀ c₀ P := by
  intro j hj hjb ζ hρ c hc x hx
  have hsource' : (homotopyRegrade (show W-S+1=B-A by omega) (show W-N=B-d by omega)
      (ζ≫XModLambdaN.map (background.nu.functor.map f) N))≫
      (background.quotients.tower _).rho (d+1) N (by omega)=finiteTopLabel Y d hd A B y := by
    rw [←regrade_comp,recursive_ordinary_protected_image X Y f (d+1) N (by omega) _ _ ζ ζ₀ hρ]
    simpa only [regrade_comp] using hsource
  apply hP j hj hjb
  apply synchronized_ordinary_divided_head_gate X Y f d N (b+1) j hd hdN (by omega) (by omega)
    S W A B D hS hW (by omega) ζ y hy hsource' c _ x hx
  rw [hc]
  exact background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hc₀

/-- Complete ordinary bottom elimination in the positive third arrow branch. The H
representative is constructed from the actual source-cycle condition;
every early-boundary correction changes the retained source as well. -/
private theorem synchronized_ordinary_full_image_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (N K b : ℕ) (hK : 0<K) (hKN : K≤N) (hb : 0<b)
    (S W A B : ℤ) (hA : A=S+b) (hB : B=W+b)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (b+1)))
    (hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedBoundary T.X N S W ζ₀≫XModLambdaN.incl _ (b+1)-c₀))
    (v : Ambient background T.Y (A,B))
    (hc₀ : c₀≫XModLambdaN.map (background.nu.functor.map T.f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel T.Y b hb A B v))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j,W+j)))
    (hgate : SynchronizedHeadGate T.X T.Y T.f N K (b+1) hKN S W ζ₀ c₀ P)
    (hmid : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X (S+j,W+j), x∈cycles background T.X (b+1-j:ℕ) (S+j,W+j) →
      (background.classical.map T.f).pageMap 2 (S+j,W+j) x∈P j →
      ∃ z : Ambient background T.Z (S+j-1,W+j),
        z∈cycles background T.Z (b+1-j:ℕ) (S+j-1,W+j) ∧
      ∃ u : Ambient background T.X (S+j,W+j),
        (background.classicalSuspension T.X).DesuspendsClass (S+j-1+1) (W+j+1)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (S+j-1) (W+j) z)
          (by simpa only [sub_add_cancel,add_sub_cancel_right] using u) ∧
        x-u∈boundaries background T.X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (e : Ambient background T.X (A,B)),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedBoundary T.X N S W ζ≫XModLambdaN.incl _ 1=synchronizedBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
      homotopyRegrade (show W-S=B-A by omega) rfl
        ((synchronizedBoundary T.X N S W ζ≫background.nu.functor.map T.f)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl A B W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (A,B) e) := by
  obtain ⟨ζ,c,hρ,hboundary,hci,hres⟩ := synchronized_bottom_iteration T.X T.Y T.f
    N K (b+1) hK hKN (by omega) S W ζ₀ c₀ hstart P hgate (by
      intro j hj hjb x hx hxp
      obtain ⟨z,hz,u,hu,hbound⟩ := hmid j hj hjb x hx hxp
      obtain ⟨h,hdet,hzero⟩ := synchronized_positive_h_cycle_image T he hf hg hh hT
        (b+1) j (b+1-j) (by omega) (by omega) (S+j-1) (S+j) (W+j) (W-S) W
        (by omega) (by omega) (by omega) z hz u (by
          convert hu using 1
          simp only [eq_mpr_eq_cast,eq_mp_eq_cast,cast_cast])
      exact ⟨u,h,hdet,hzero,hbound⟩)
  have hc : c≫XModLambdaN.map (background.nu.functor.map T.f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel T.Y b hb A B v) :=
    hci.trans hc₀
  have hr : FiltrationAtLeast background.syntheticTower A
      (synchronizedBoundary T.X N S W ζ≫XModLambdaN.incl _ (b+1)-c) := by
    convert hres using 1
    push_cast
    omega
  obtain ⟨e,hi⟩ := synchronized_ordinary_top_of_residual T.X T.Y T.f N b hb S W A B hA hB ζ c v hc hr
  exact ⟨ζ,e,hρ,hboundary,hi⟩

/-- Complete ordinary bottom elimination in the positive second arrow branch. The H
representative is constructed from the actual source-cycle condition;
every early-boundary correction changes the retained source as well. -/
private theorem synchronized_ordinary_full_image_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N K b : ℕ) (hK : 0<K) (hKN : K≤N) (hb : 0<b)
    (S W A B : ℤ) (hA : A=S+b) (hB : B=W+b)
    (ζ₀ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (c₀ : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (b+1)))
    (hstart : FiltrationAtLeast background.syntheticTower (S+1)
      (synchronizedBoundary T.X N S W ζ₀≫XModLambdaN.incl _ (b+1)-c₀))
    (v : Ambient background T.Y (A,B))
    (hc₀ : c₀≫XModLambdaN.map (background.nu.functor.map T.f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel T.Y b hb A B v))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j,W+j)))
    (hgate : SynchronizedHeadGate T.X T.Y T.f N K (b+1) hKN S W ζ₀ c₀ P)
    (hmid : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X (S+j,W+j), x∈cycles background T.X (b+1-j:ℕ) (S+j,W+j) →
      (background.classical.map T.f).pageMap 2 (S+j,W+j) x∈P j →
      ∃ z : Ambient background T.Z (S+j,W+j+1),
        z∈cycles background T.Z (b+1-j:ℕ) (S+j,W+j+1) ∧
      ∃ u : Ambient background T.X (S+j,W+j),
        (background.classicalSuspension T.X).DesuspendsClass (S+j) (W+j+1)
          ((background.classical.map T.h).pageMap 2 (S+j,W+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
        x-u∈boundaries background T.X ((N-K+j:ℕ)+1) (S+j,W+j)) :
    ∃ (ζ : BiHom (W-S+1) (W-N) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (e : Ambient background T.X (A,B)),
      ζ≫(background.quotients.tower _).rho K N hKN=ζ₀≫(background.quotients.tower _).rho K N hKN ∧
      synchronizedBoundary T.X N S W ζ≫XModLambdaN.incl _ 1=synchronizedBoundary T.X N S W ζ₀≫XModLambdaN.incl _ 1 ∧
      homotopyRegrade (show W-S=B-A by omega) rfl
        ((synchronizedBoundary T.X N S W ζ≫background.nu.functor.map T.f)≫XModLambdaN.incl _ (b+1))=
      finiteTopLabelAtWeight T.Y b hb (b+1) rfl A B W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (A,B) e) := by
  obtain ⟨ζ,c,hρ,hboundary,hci,hres⟩ := synchronized_bottom_iteration T.X T.Y T.f
    N K (b+1) hK hKN (by omega) S W ζ₀ c₀ hstart P hgate (by
      intro j hj hjb x hx hxp
      obtain ⟨z,hz,u,hu,hbound⟩ := hmid j hj hjb x hx hxp
      obtain ⟨h,hdet,hzero⟩ := synchronized_positive_g_cycle_image T he hf hg hh hT
        (b+1) j (b+1-j) (by omega) (by omega) (S+j-1) (S+j) (W+j) (W-S) W
        (by omega) (by omega) (by omega) z hz u hu
      exact ⟨u,h,hdet,hzero,hbound⟩)
  have hc : c≫XModLambdaN.map (background.nu.functor.map T.f) (b+1)=
      homotopyRegrade (show B-A=W-S by omega) (show B-b=W by omega) (finiteTopLabel T.Y b hb A B v) :=
    hci.trans hc₀
  have hr : FiltrationAtLeast background.syntheticTower A
      (synchronizedBoundary T.X N S W ζ≫XModLambdaN.incl _ (b+1)-c) := by
    convert hres using 1
    push_cast
    omega
  obtain ⟨e,hi⟩ := synchronized_ordinary_top_of_residual T.X T.Y T.f N b hb S W A B hA hB ζ c v hc hr
  exact ⟨ζ,e,hρ,hboundary,hi⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
