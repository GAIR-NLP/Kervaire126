module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift
import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferential
import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDivision

/-! Exact early-boundary consequences of independently known source survival.
The finite source is fixed throughout the coefficient extension. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- A top label of the actual boundary of a fixed finite source is an
exact early boundary when the same source label independently survives
past the induced differential. The extension still restricts to η₀. -/
private theorem known_source_boundary_top_is_early_boundary
    (Y : (AdamsObject (coefficients := background.coefficients))) (L j : ℕ) (hL : 0<L) (hj : 0<j)
    (s t D : ℤ) (hD : (L:ℤ)+j+1<D)
    (y : Ambient background Y (s,t))
    (η₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL = nativeFirstLabel Y s t y)
    (hy : y ∈ cycles background Y (D-1) (s,t))
    (v : Ambient background Y (s+(L+j:ℕ)+1,t+(L+j:ℕ)))
    (htop : homotopyRegrade
        (show (t-s)-1=(t+(L+j:ℕ))-(s+(L+j:ℕ)+1) by omega)
        (show t+L=(t+(L+j:ℕ))-j by omega)
        (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (j+1)) =
      finiteTopLabel Y j hj (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) v) :
    v ∈ boundaries background Y ((L+j:ℕ):ℤ) (s+(L+j:ℕ)+1,t+(L+j:ℕ)) := by
  obtain ⟨η,w,hρ,hw,hwp,hwv⟩ := finite_extension_of_boundary_top Y L j hL hj
    (t-s) t (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) (by omega) (by omega) η₀ v htop
  have hfirst : η ≫ (background.quotients.tower _).rho 1 (L+j) (by omega) =
      nativeFirstLabel Y s t y := by
    rw [←(background.quotients.tower _).rho_comp hL (show L≤L+j by omega),←Category.assoc,hρ,hη]
  have hd : DifferentialAt background Y ((L+j:ℕ)+1) (s,t)
      (s+(L+j:ℕ)+1,t+(L+j:ℕ)) y w := by
    refine ⟨by omega,adjacent_boundary_differential Y (L+j) (by omega) s t y w η hfirst ?_⟩
    exact hw
  have hwb := selective_earlier_target_boundary Y ((L+j:ℕ)+1) D (by omega)
    (s,t) (s+(L+j:ℕ)+1,t+(L+j:ℕ)) y w hd hy
  have hdiff : w-v ∈ boundaries background Y ((L+j:ℕ):ℤ) (s+(L+j:ℕ)+1,t+(L+j:ℕ)) :=
    boundaries_monotone background Y _ (by omega) hwv
  have hv := (boundaries background Y ((L+j:ℕ):ℤ) _).sub_mem
    (by simpa only [add_sub_cancel_right] using hwb) hdiff
  simpa only [sub_sub_cancel] using hv


/-- A visible finite head of the boundary of the same specified source
has the precise early-boundary cutoff supplied by independent survival. -/
private theorem known_source_finite_label_is_early_boundary
    (Y : (AdamsObject (coefficients := background.coefficients))) (L j N : ℕ) (hL : 0<L) (hj : 0<j) (hjN : j<N)
    (s t D : ℤ) (hD : (L:ℤ)+j+1<D)
    (y : Ambient background Y (s,t))
    (η₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL = nativeFirstLabel Y s t y)
    (hy : y ∈ cycles background Y (D-1) (s,t))
    (v : Ambient background Y (s+(L+j:ℕ)+1,t+(L+j:ℕ)))
    (hfinite : Detects (background.convergence (.quotient N (.nu Y)))
      (s+(L+j:ℕ)+1,t+(L+j:ℕ),(t+(L+j:ℕ))-j)
      (finiteTargetLabel background Y N (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) j v)
      (homotopyRegrade
        (show (t-s)-1=(t+(L+j:ℕ))-(s+(L+j:ℕ)+1) by omega)
        (show t+L=(t+(L+j:ℕ))-j by omega)
        (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ N))) :
    v ∈ boundaries background Y ((L+j:ℕ):ℤ) (s+(L+j:ℕ)+1,t+(L+j:ℕ)) := by
  have hdet := selective_finite_target_restriction_detects Y (j+1) N j (by omega)
    (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) v _ hfinite
  have ht := finite_top_detection_unique Y (j+1) (by omega)
    (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) ((t+(L+j:ℕ))-j) (by omega)
    _ _ _ hdet (finiteTopLabel_detects Y j hj (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) v)
  rw [←regrade_comp,Category.assoc,(background.quotients.tower _).rho_quotient] at ht
  exact known_source_boundary_top_is_early_boundary Y L j hL hj s t D hD y η₀ hη hy v ht

/-- The early-boundary cutoff of the specified head is invariant under
next-filtration ambiguity of the residual. -/
private theorem known_source_finite_label_boundary_of_next_filtration
    (Y : (AdamsObject (coefficients := background.coefficients))) (L j N : ℕ) (hL : 0<L) (hj : 0<j) (hjN : j<N)
    (s t D : ℤ) (hD : (L:ℤ)+j+1<D)
    (y : Ambient background Y (s,t))
    (η₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL = nativeFirstLabel Y s t y)
    (hy : y ∈ cycles background Y (D-1) (s,t))
    (v : Ambient background Y (s+(L+j:ℕ)+1,t+(L+j:ℕ)))
    (b : BiHom ((t+(L+j:ℕ))-(s+(L+j:ℕ)+1)) ((t+(L+j:ℕ))-j)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hb : Detects (background.convergence (.quotient N (.nu Y)))
      (s+(L+j:ℕ)+1,t+(L+j:ℕ),(t+(L+j:ℕ))-j)
      (finiteTargetLabel background Y N (s+(L+j:ℕ)+1) (t+(L+j:ℕ)) j v) b)
    (hnext : FiltrationAtLeast background.syntheticTower (s+(L+j:ℕ)+1+1)
      (homotopyRegrade
        (show (t-s)-1=(t+(L+j:ℕ))-(s+(L+j:ℕ)+1) by omega)
        (show t+L=(t+(L+j:ℕ))-j by omega)
        (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ N)-b)) :
    v ∈ boundaries background Y ((L+j:ℕ):ℤ) (s+(L+j:ℕ)+1,t+(L+j:ℕ)) := by
  exact known_source_finite_label_is_early_boundary Y L j N hL hj hjN s t D hD y η₀ hη hy v
    (detects_of_next_filtration_difference (.quotient N (.nu Y))
      (s+(L+j:ℕ)+1,t+(L+j:ℕ),(t+(L+j:ℕ))-j) _ _ _ hb hnext)

/-- Coordinate-only form of the exact early-boundary gate. The full
class is required to be the boundary of the same retained finite source. -/
private theorem known_source_finite_label_boundary_at_degree
    (Y : (AdamsObject (coefficients := background.coefficients))) (L k N : ℕ) (hL : 0<L) (hk : 0<k) (hkN : k<N)
    (s t S T D : ℤ) (hS : S=s+(L+k:ℕ)+1) (hT : T=t+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background Y (s,t))
    (η₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL = nativeFirstLabel Y s t y)
    (hy : y ∈ cycles background Y (D-1) (s,t))
    (β : BiHom (T-S) (T-k) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (t-s)-1=T-S by omega) (show t+L=T-k by omega)
      (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : Ambient background Y (S,T))
    (b : BiHom (T-S) (T-k) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hb : Detects (background.convergence (.quotient N (.nu Y))) (S,T,T-k)
      (finiteTargetLabel background Y N S T k v) b)
    (hnext : FiltrationAtLeast background.syntheticTower (S+1) (β ≫ XModLambdaN.incl _ N-b)) :
    v ∈ boundaries background Y ((L+k:ℕ):ℤ) (S,T) := by
  subst S; subst T
  apply known_source_finite_label_boundary_of_next_filtration Y L k N hL hk hkN
    s t D hD y η₀ hη hy v b hb
  rw [hβ,←regrade_comp] at hnext
  exact hnext

/-- The literal head of a positive image lies in the exact early boundary
space supplied by the independent survival of the retained source. -/
private theorem known_source_positive_f_finite_head
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N k L : ℕ) (hk : 0<k) (hkN : k<N) (hL : 0<L)
    (s t A B D : ℤ) (hA : s+1=A+(L+k:ℕ)+1) (hB : t+1=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) ((t-k)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=t-s by omega) (show B+L=(t-k)+1 by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (t-s) ((t-k)+1) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf N ε (t-s) (t-k) a=β ≫ XModLambdaN.incl _ N-v) :
    ∃ x : Ambient background T.X (s,t),
      x ∈ cycles background T.X (N-k:ℕ) (s,t) ∧
      Detects (background.convergence (.quotient N (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel background T.X N s t k x) a ∧
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
        boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t+1) := by
  obtain ⟨x,hx,hxa⟩ := middle_finite_filtration_label T.X N k hkN s t a ha
  refine ⟨x,hx,hxa,?_⟩
  have hmap := selective_positive_image_detects T hf N k hk hkN s t ε hε x a hxa
  let β' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show (t-k)+1=(t+1)-k by omega) β
  have hβ' : β'=homotopyRegrade (show (B-A)-1=(t+1)-(s+1) by omega)
      (show B+L=(t+1)-k by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)) := by
    dsimp only [β']
    rw [hβ,normalized_homotopy_regrade_trans]
  apply known_source_finite_label_boundary_at_degree T.Y L k N hL hk hkN
    A B (s+1) (t+1) D hA hB hD y η₀ hη hy β' hβ' _ _ hmap
  have h := congrArg (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show (t-k)+1=(t+1)-k by omega)) himage
  erw [h]
  simp only [β',regrade_precomp,Preadditive.comp_sub,Category.assoc,sub_sub_cancel]
  have hv' := (regrade_filtration_iff (show t-s=(t+1)-(s+1) by omega)
    (show (t-k)+1=(t+1)-k by omega) (s+2) v).mpr hv
  simpa only [regrade_precomp,show s+1+1=s+2 by omega] using hv'
private theorem known_source_positive_f_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (s t A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t+1=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (k+q) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (hε : XModLambdaN.incl _ (k+q) ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (k+q)))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t+1) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s,t), x ∈ cycles background T.X q (s,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈ P →
      ∃ z : Ambient background T.Z (s,t+1), z ∈ cycles background T.Z q (s,t+1) ∧
      ∃ u : Ambient background T.X (s,t),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s,t))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) ((t-k)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=t-s by omega) (show B+L=(t-k)+1 by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (t-s) ((t-k)+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf (k+q) ε (t-s) (t-k) a=β ≫ XModLambdaN.incl _ (k+q)-v) :
    ∃ b : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+1) b ∧
      positiveFiniteImage T hf (k+q) ε (t-s) (t-k) b=
      positiveFiniteImage T hf (k+q) ε (t-s) (t-k) a := by
  obtain ⟨x,hxc,hxd,hxp⟩ := known_source_positive_f_finite_head T hf
    (k+q) k L hk (by omega) hL s t A B D hA hB hD y η₀ hη hy ε hε a ha β hβ v hv himage
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := selective_positive_f_native_cycle_image T he hf hg hh hT
    k q hq s t ε hε z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    s t x u hxu a b hxd hb
  refine ⟨a-b,hnext,?_⟩
  rw [positiveFiniteImage_sub,hbz,sub_zero]


private theorem known_source_positive_f_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (hN : N=k+q) (s t m w A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t+1=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (hm : m=t-s) (hw : w=t-k)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t+1) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s,t), x ∈ cycles background T.X q (s,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈ P →
      ∃ z : Ambient background T.Z (s,t+1), z ∈ cycles background T.Z q (s,t+1) ∧
      ∃ u : Ambient background T.X (s,t),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s,t))
    (a : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom m (w+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=m by omega) (show B+L=w+1 by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom m (w+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf N ε m w a=β ≫ XModLambdaN.incl _ N-v) :
    ∃ b : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+1) b ∧
      positiveFiniteImage T hf N ε m w b=
      positiveFiniteImage T hf N ε m w a := by
  subst N; subst m; subst w
  exact known_source_positive_f_native_step T he hf hg hh hT k q L hk hq hL s t A B D hA hB hD y η₀ hη hy ε hε P hP hmid a ha β hβ v hv himage


/-- Known-source survival restricts every actual positive intermediate head
to the exact early-boundary cutoff. The source η₀ and full image remain fixed. -/
private theorem known_source_positive_f_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K L : ℕ) (hK : 2≤K) (hL : 0<L) (S V A₀ B₀ D : ℤ)
    (hA : S+1=A₀+(L+c:ℕ)+1) (hB : V+1=B₀+(L+c:ℕ))
    (hD : (L:ℤ)+c+K≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((L:ℤ)+c+j) (S+j+1,V+j+1) ≤ P j)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ P j →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a)
    (β : BiHom (V-S) ((V-c)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B₀-A₀)-1=V-S by omega) (show B₀+L=(V-c)+1 by omega)
      (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (V-S) ((V-c)+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K) v)
    (himage : positiveFiniteImage T hf (c+K) ε (V-S) (V-c) a=
      β ≫ XModLambdaN.incl _ (c+K)-v) :
    ∃ e : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1) e ∧
      positiveFiniteImage T hf (c+K) ε (V-S) (V-c) e=
      positiveFiniteImage T hf (c+K) ε (V-S) (V-c) a := by
  let A := XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)
  let f := positiveFiniteImage T hf (c+K) ε (V-S) (V-c)
  have hstep (j : ℕ) (hj : 1≤j) (hjK : j<K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : f b=f a) :
      ∃ b' : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+(j+1:ℕ)) b' ∧ f b'=f b := by
    have H := known_source_positive_f_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) L (by omega) (by omega) hL (by omega)
      (S+j) (V+j) (V-S) (V-c) A₀ B₀ D (by omega) (by omega) (by omega)
      (by omega) (by omega) y η₀ hη hy ε hε
      (P j) (by simpa only [Nat.cast_add,add_assoc] using hP j hj hjK)
      (fun x hx hxp => by
        obtain ⟨z,hz,hxz⟩ := hmid j hj hjK x
          (by simpa only [Nat.cast_sub (show j≤K by omega)] using hx) hxp
        refine ⟨z,?_,_,KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T (S+j) (V+j) z,?_⟩
        · simpa only [Nat.cast_sub (show j≤K by omega)] using hz
        · simpa only [Nat.cast_add,Nat.cast_one] using hxz)
      b hb β hβ v (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage)
    obtain ⟨b',hb',hi'⟩ := H
    refine ⟨b',?_,hi'⟩
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hb'
  have hrec (j : ℕ) (hj : 1≤j) (hjK : j≤K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : f b=f a) :
      ∃ e : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+K-1) e ∧ f e=f a := by
    induction hlen : K-1-j using Nat.strong_induction_on generalizing j b with
    | h n ih =>
      by_cases hend : K-1≤j
      · refine ⟨b,?_,hi⟩
        convert hb using 1
        omega
      · obtain ⟨b',hb',hi'⟩ := hstep j hj (by omega) b hb hi
        exact ih (K-1-(j+1)) (by omega) (j+1) (by omega) (by omega) b' hb' (hi'.trans hi) rfl
  exact hrec 1 (by omega) (by omega) a (by simpa only [Nat.cast_one] using ha) rfl


/-- The specified positive full image has its last top form using only
the early-boundary gates of the same independently surviving source. -/
private theorem known_source_positive_full_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q L : ℕ) (hq : 0<q) (hL : 0<L) (S V A B D : ℤ)
    (hA : S=A+L) (hB : V+1=B+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((L:ℤ)+j) (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
    (hboundary : verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf =
      homotopyRegrade (show (B-A)-1=V-S by omega) (show B+L=V+1 by omega)
        (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L))) :
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
  obtain ⟨e,hefil,hei⟩ := known_source_positive_f_native_residual_same_image
    T he hf hg hh hT 0 (q+1) L (by omega) hL S V A B D
    (by omega) (by omega) (by omega) y η₀ hη hy ε hε Pm
    (by simpa only [Nat.cast_zero,add_zero] using hPm)
    (by simpa only [Nat.cast_zero,zero_add] using hmid) (a₀-a) hres β
    (by dsimp only [β]; rw [hboundary,normalized_homotopy_regrade_trans]) (f a) hvfil
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

private theorem known_source_positive_bottom_differential
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q L : ℕ) (hq : 0<q) (hL : 0<L) (S V A B D : ℤ)
    (hA : S=A+L) (hB : V+1=B+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((L:ℤ)+j) (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
    (hboundary : verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf =
      homotopyRegrade (show (B-A)-1=V-S by omega) (show B+L=V+1 by omega)
        (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)))
    (P : Submodule ℤ (Ambient background T.Y (S+q+1,(V+1)+q)))
    (hP : permanentCycles background T.Y (S+q+1,(V+1)+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P, (background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) a=0 →
      a ∈ boundaries background T.Y (L+q) (S+q+1,(V+1)+q)) :
    IsCycle background T.Y (L+q) (A,B) y ∧
      IsCycle background T.Y (L+q) (S+q+1,(V+1)+q) v ∧
      DifferentialAt background T.Y (L+q+1) (A,B) (S+q+1,(V+1)+q) y v := by
  obtain ⟨e,error,herror,htop⟩ := known_source_positive_full_image
    T he hT hf hg hh q L hq hL S V A B D hA hB hD y η₀ hη hy
    u z v hu hdz Pm hPm hmid U hU hboundary
  rw [hboundary,←regrade_comp,normalized_homotopy_regrade_trans] at htop
  obtain ⟨η,wv,hρ,hwv,hwp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L (0+q) (0+(q+1)) hL (by omega) (by omega) (B-A) B
    (S+q+1) ((V+1)+q) (V+1) (by omega) (by omega) (by omega) η₀ (v+error) htop
  let N := L+(0+q)
  have hN : 0<N := by dsimp [N]; omega
  have ha : η ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.Y A B y := by
    rw [←(background.quotients.tower _).rho_comp hL (show L≤N by dsimp [N];omega),
      ←Category.assoc,hρ,hη]
  let w' : Ambient background T.Y (A+N+1,B+N) :=
    topClassicalRegrade (show (S+q+1,(V+1)+q)=(A+N+1,B+N) by ext <;> dsimp [N] <;> omega) wv
  have hw' : HEq w' wv := top_classical_regrade_heq _ _
  have hb := congrArg (homotopyRegrade
    (show ((V+1)+q)-(S+q+1)=(B+N)-(A+N+1) by dsimp [N];omega)
    (show (V+1)+q=B+N by dsimp [N];omega)) hwv
  rw [source_native_label_transport T.Y (S+q+1) ((V+1)+q)
    (A+N+1) (B+N) (by dsimp [N];omega) (by dsimp [N];omega) wv w' hw'] at hb
  have hba : boundaryRepresentative T.Y N A B η ≫ XModLambdaN.incl _ 1=
      nativeFirstLabel T.Y (A+N+1) (B+N) w' := by
    simpa only [boundaryRepresentative,regrade_comp,last_layer_regrade_trans] using hb
  have hd0 : DifferentialAt background T.Y (N+1) (A,B) (A+N+1,B+N) y w' :=
    ⟨by omega,adjacent_boundary_differential T.Y N hN A B y w' η ha hba⟩
  have hd := classical_differential_heq T.Y (N+1) rfl
    (show (A+N+1,B+N)=(S+q+1,(V+1)+q) by ext <;> dsimp [N] <;> omega)
    y y w' wv HEq.rfl hw' hd0
  have heG : (background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) error=0 := by
    have hb := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY T hf hg hh
      (S+q) (V+q)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'; simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by congr 1;omega) _ _ herror hb
  have herr' : wv-v-error ∈ boundaries background T.Y (q+1) (S+q+1,(V+1)+q) := by
    have heq : wv-v-error=wv-(v+error) := by abel
    simpa only [heq,Nat.cast_add,Nat.cast_zero,zero_add] using herr
  have hd' := differential_target_of_permanent_candidate_kernel T.Y T.Z T.g (N+1)
    (A,B) (S+q+1,(V+1)+q) y wv v error P hP hd hv
    (boundaries_monotone background T.Y _ (by dsimp [N];omega) herr') heG
    (by simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hker)
  have hc := cycles_of_differential T.Y (N+1) _ _ y v hd'
  refine ⟨?_,?_,?_⟩
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hc.1
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hc.2
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hd'

/-- The original known-source criterion, positive-first branch with both
finite ends. Independent input survival is used only to narrow the actual
middle heads; the output differential retains the original specified y and v. -/
public theorem known_source_differential_positive_first
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
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
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
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    s t x u).mp hdx
  obtain ⟨e,error,herror,η₀,wy,hinsert,hfirst,hboundary,hcong,hwy⟩ :=
    positive_source_finite_division_producer T he hT hf hg hh a L ha haL s t (L+b-a:ℕ)
      x z₁ y hxz hdz₁ htop ζ hζ hy
      (fun e => cycles_antitone background T.Y _ (by omega) (himage e))
  let U := positiveAdjustedBoundary T.X L s t ζ
  have hUfirst : U ≫ XModLambdaN.incl _ 1=nativeFirstLabel T.X (s+L+1) (t+L) u :=
    (positive_adjusted_boundary_first T.X L s t ζ).trans hU
  have hlen : ((L-(0+a):ℕ):ℤ)+b=((L+b-a:ℕ):ℤ) := by omega
  have hbot := known_source_positive_bottom_differential T he hT hf hg hh
    b (L-(0+a)) hb (by omega) (s+L+1) (t+L) (s+a+1) ((t+1)+a)
    ((L+b-a:ℕ)+1) (by omega) (by omega) (by omega) wy η₀ hfirst
    (by simpa only [add_sub_cancel_right] using hwy)
    u z₂ v huz hdz₂ Pm
    (by simpa only [Nat.zero_add] using hPm) hbottom U hUfirst hboundary P hP hv
    (by simpa only [hlen] using hker)
  rw [hlen] at hbot
  have hecycle : error ∈ cycles background T.Y ((L+b-a:ℕ)+1) (s+a+1,(t+1)+a) := by
    have h := classical_cycle_heq T.Y ((L+b-a:ℕ)+1)
      (show (s+a+1,t+a+1)=(s+a+1,(t+1)+a) by congr 1; omega)
      _ error herror.symm ⟨by omega,himage e⟩
    exact h.2
  simpa only [add_sub_cancel_right] using differential_of_source_correction T.Y ((L+b-a:ℕ)+1) ((0+a:ℕ)+1)
    (s+a+1,(t+1)+a) ((s+L+1)+b+1,((t+L)+1)+b) wy y error v v hbot.2.2
    hcong hecycle (by rw [sub_self]; exact (boundaries background T.Y _ _).zero_mem)

/-- A head of the actual absolute boundary of a top-divisible source
has the exact early-boundary cutoff forced by independent source survival.
The divided source is constructed with literally the same full boundary. -/
private theorem known_source_divided_boundary_head
    (Y : (AdamsObject (coefficients := background.coefficients))) (d N M j R : ℕ) (hd : 0<d) (hdN : d<N)
    (hM : d+1=M) (hj : 0<j) (hjR : j<R)
    (s t w S T D : ℤ) (hw : t-d=w)
    (hS : S=s+((N-d)+j:ℕ)+1) (hT : T=t+((N-d)+j:ℕ))
    (hD : ((N-d:ℕ):ℤ)+j+1<D)
    (x : Ambient background Y (s,t)) (hx : x ∈ cycles background Y (D-1) (s,t))
    (η : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (htop : η ≫ (background.quotients.tower _).rho M N (by omega)=
      finiteTopLabelAtWeight Y d hd M hM s t w hw x)
    (v : Ambient background Y (S,T))
    (b : BiHom (T-S) (T-j) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) R))
    (hb : Detects (background.convergence (.quotient R (.nu Y))) (S,T,T-j)
      (finiteTargetLabel background Y R S T j v) b)
    (hnext : FiltrationAtLeast background.syntheticTower (S+1)
      (homotopyRegrade (show (t-s)-1=T-S by omega) (show w+N=T-j by omega)
        (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (Y.obj background.auxiliary))
          (η ≫ XModLambdaN.proj _ N) ≫ XModLambdaN.incl _ R)-b)) :
    v ∈ boundaries background Y (((N-d)+j:ℕ):ℤ) (S,T) := by
  obtain ⟨η₀,wy,hinsert,hfirst,hboundary,hcong⟩ := source_finite_division_same_boundary_at_weight
    Y d N M hd hdN hM s t w hw x η htop
  have hwy : wy ∈ cycles background Y (D-1) (s,t) := by
    have h := (cycles background Y (D-1) (s,t)).add_mem
      (boundaries_le_cycles background Y (s,t) (d+1) (D-1) hcong) hx
    simpa only [sub_add_cancel] using h
  let β := homotopyRegrade (show (t-s)-1=T-S by omega) (show w+N=T-j by omega)
    (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (Y.obj background.auxiliary))
      (η ≫ XModLambdaN.proj _ N))
  have hβ : β=homotopyRegrade (show (t-s)-1=T-S by omega) (show t+(N-d:ℕ)=T-j by omega)
      (biSuspensionHomEquiv (t-s) t (N-d:ℕ) (background.nu.functor.obj (Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ (N-d))) := by
    rw [←hboundary,normalized_homotopy_regrade_trans]
  apply known_source_finite_label_boundary_at_degree Y (N-d) j R (by omega) hj hjR
    s t S T D hS hT hD wy η₀ hfirst hwy β hβ v b hb
  simpa only [β,←regrade_comp] using hnext

private theorem known_source_divided_boundary_detected_head
    (Y : (AdamsObject (coefficients := background.coefficients))) (d N M j R : ℕ) (hd : 0<d) (hdN : d<N)
    (hM : d+1=M) (hj : 0<j) (hjR : j<R)
    (s t w S T D : ℤ) (hw : t-d=w)
    (hS : S=s+((N-d)+j:ℕ)+1) (hT : T=t+((N-d)+j:ℕ))
    (hD : ((N-d:ℕ):ℤ)+j+1<D)
    (x : Ambient background Y (s,t)) (hx : x ∈ cycles background Y (D-1) (s,t))
    (η : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (htop : η ≫ (background.quotients.tower _).rho M N (by omega)=
      finiteTopLabelAtWeight Y d hd M hM s t w hw x)
    (v : Ambient background Y (S,T))
    (hb : Detects (background.convergence (.quotient R (.nu Y))) (S,T,T-j)
      (finiteTargetLabel background Y R S T j v)
      (homotopyRegrade (show (t-s)-1=T-S by omega) (show w+N=T-j by omega)
        (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (Y.obj background.auxiliary))
          (η ≫ XModLambdaN.proj _ N) ≫ XModLambdaN.incl _ R))) :
    v ∈ boundaries background Y (((N-d)+j:ℕ):ℤ) (S,T) := by
  apply known_source_divided_boundary_head Y d N M j R hd hdN hM hj hjR
    s t w S T D hw hS hT hD x hx η htop v _ hb
  rw [sub_self]
  exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem

end
end KIP126.ProofTools.Internal.SyntheticCoverage
