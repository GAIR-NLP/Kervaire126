module

import all KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential

/-! The arbitrary-layer source correction in the known-source-survival argument.
A genuine early boundary is lifted with its precise finite torsion bound.
The original source and its boundary are corrected together, preserving
its entire protected quotient and its specified adjacent differential label.
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


/-- General layer-j version of the actual coefficient correction. The
strict early-boundary bound is exactly what protects the entire Q_K. -/
private theorem synchronized_torsion_source_correction_strict
    (X : (AdamsObject (coefficients := background.coefficients))) (N K j : ℕ) (hK : 0<K) (hKN : K<N)
    (m w : ℤ)
    (T : BiHom (m-1) (w+N+j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hT : lambdaMultiply (N-K+j) T=0) :
    ∃ ζb : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζb≫(background.quotients.tower _).rho K N hKN.le=0 ∧
      biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
        (ζb≫XModLambdaN.proj _ N)=
      homotopyRegrade rfl (show (w+N+j)-(j:ℕ)=w+N by omega) (lambdaMultiply j T) := by
  let q := N-K+j
  let T' := homotopyRegrade (rfl : m-1=m-1)
    (show w+N+j=(w+K)+q by dsimp only [q]; omega) T
  have hT' : lambdaMultiply q T'=0 := by
    dsimp only [T']
    rw [lambda_regrade,hT,regrade_zero]
  obtain ⟨a,ha⟩ := recursive_torsion_boundary_source _ q m (w+K) T' hT'
  let b := a≫(background.quotients.tower _).rho (N-K) q (by dsimp only [q]; omega)
  have hb := absolute_boundary_restriction X (N-K) q (by dsimp only [q]; omega) m (w+K) a
  rw [ha] at hb
  have hcast (i : ℕ) (hi : i=j) (hw : (w+K+q)-i=w+K+(N-K:ℕ)) :
      homotopyRegrade rfl hw (lambdaMultiply i T')=
        homotopyRegrade rfl (show (w+K+q)-(j:ℕ)=w+K+(N-K:ℕ) by dsimp only [q]; omega)
          (lambdaMultiply j T') := by
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

private theorem synchronized_torsion_source_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K j : ℕ) (hK : 0<K) (hKN : K≤N)
    (m w : ℤ)
    (T : BiHom (m-1) (w+N+j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hT : lambdaMultiply (N-K+j) T=0) :
    ∃ ζb : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      ζb≫(background.quotients.tower _).rho K N hKN=0 ∧
      biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
        (ζb≫XModLambdaN.proj _ N)=
      homotopyRegrade rfl (show (w+N+j)-(j:ℕ)=w+N by omega) (lambdaMultiply j T) := by
  by_cases hlt : K<N
  · exact synchronized_torsion_source_correction_strict X N K j hK hlt m w T hT
  · have hEq : N-K+j=j := by omega
    rw [hEq] at hT
    refine ⟨0,by simp,?_⟩
    rw [zero_comp,map_zero,hT,regrade_zero]

/-- The original paragraph's arbitrary-layer correction. Here N=r-1,
K=K₁, and the input is the genuine B_<r-K+1+j. The corrected source
has exactly the same protected quotient and the same adjacent label. -/
private theorem synchronized_early_boundary_source_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N K j : ℕ) (hK : 0<K) (hKN : K≤N) (hj : 0<j)
    (s t : ℤ)
    (b : Ambient background X (s+N+1+j,t+N+j))
    (hb : b∈boundaries background X ((N-K+j:ℕ)+1) (s+N+1+j,t+N+j))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    ∃ (T : BiHom ((t-s)-1) (t+N+j) (background.nu.functor.obj (X.obj background.auxiliary)))
      (ζ' : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)),
      T≫XModLambdaN.incl _ 1=
        homotopyRegrade (show (t+N+j)-(s+N+1+j)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+N+1+j) (t+N+j) b) ∧
      lambdaMultiply (N-K+j) T=0 ∧
      ζ'≫(background.quotients.tower _).rho K N hKN=
        ζ≫(background.quotients.tower _).rho K N hKN ∧
      ζ'≫(background.quotients.tower _).rho 1 N (by omega)=
        ζ≫(background.quotients.tower _).rho 1 N (by omega) ∧
      boundaryRepresentative X N s t ζ'=
        boundaryRepresentative X N s t ζ-
          homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
            (show (t+N+j)-(j:ℕ)=t+N by omega) (lambdaMultiply j T) ∧
      adjacentBoundaryLabel X N s t ζ'=adjacentBoundaryLabel X N s t ζ := by
  obtain ⟨T₀,hT₀,hTzero⟩ := cumulative_boundary_torsion_lift_unshifted X (N-K+j)
    (s+N+1+j) (t+N+j) b hb
  let T := homotopyRegrade (show (t+N+j)-(s+N+1+j)=(t-s)-1 by omega) rfl T₀
  have hT : lambdaMultiply (N-K+j) T=0 := by
    dsimp only [T]
    rw [lambda_regrade,hTzero,regrade_zero]
  obtain ⟨ζb,hρ,hbd⟩ := synchronized_torsion_source_correction X N K j hK hKN
    (t-s) t T hT
  have hρ1 : ζb≫(background.quotients.tower _).rho 1 N (by omega)=0 := by
    rw [←(background.quotients.tower _).rho_comp (show 1≤K by omega) hKN,
      ←Category.assoc,hρ,zero_comp]
  have hbdy : boundaryRepresentative X N s t ζb=
      homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega)
        (show (t+N+j)-(j:ℕ)=t+N by omega) (lambdaMultiply j T) := by
    dsimp only [boundaryRepresentative]
    rw [hbd,last_layer_regrade_trans]
  have hfirst : boundaryRepresentative X N s t ζb≫XModLambdaN.incl _ 1=0 := by
    rw [hbdy,←regrade_comp,lambda_power_first_quotient_zero X j hj _ _ T,regrade_zero]
  refine ⟨T,ζ-ζb,?_,hT,?_,?_,?_,?_⟩
  · dsimp only [T]
    rw [←regrade_comp,hT₀]
    rfl
  · rw [Preadditive.sub_comp,hρ,sub_zero]
  · rw [Preadditive.sub_comp,hρ1,sub_zero]
  · simp only [boundaryRepresentative,Preadditive.sub_comp,map_sub,homotopy_regrade_sub]
    exact congrArg (fun a => boundaryRepresentative X N s t ζ-a) hbdy
  · change boundaryRepresentative X N s t (ζ-ζb)≫XModLambdaN.incl _ 1=
      boundaryRepresentative X N s t ζ≫XModLambdaN.incl _ 1
    simp only [boundaryRepresentative,Preadditive.sub_comp,map_sub,homotopy_regrade_sub] at hfirst ⊢
    rw [hfirst,sub_zero]

end
end KIP126.ProofTools.Internal.SyntheticCoverage
