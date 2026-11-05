module

public import KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.EarlySourceDifferential
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison

/-! The source higher early-boundary criterion, retaining the specified
main differential target and the original source label after full correction.
The true source-boundary cutoff is independent of the main differential page.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- Corrected finite-image division with arbitrary short quotient length and
explicit classical degrees. The full correction has zero absolute boundary. -/
private theorem higher_source_differential_of_corrected_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (d K N : ℕ) (hd : 0<d) (hK : K=d+1) (hKN : K≤N)
    (S V A B : ℤ) (hA : A=S+d+1) (hB : B=(V+1)+d)
    (u : Ambient background T.X (S+N+1,V+N))
    (y error : Ambient background T.Y (A,B))
    (ζ : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hU : adjacentBoundaryLabel T.X N S V ζ = nativeFirstLabel T.X (S+N+1) (V+N) u)
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (htop : homotopyRegrade (show V-S=B-A by omega) rfl
        ((positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ-
          W ≫ XModLambdaN.incl _ N) ≫ (background.quotients.tower _).rho K N hKN) =
      finiteTopLabelAtWeight T.Y d hd K (by omega) A B (V+1) (by omega) (y+error))
    (himage : error ∈ cycles background T.Y ((N-d:ℕ)+1) (A,B)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+N+1) (V+N) u
    IsCycle background T.Y (N-d:ℕ) (A,B) y ∧
      IsCycle background T.Y (N-d:ℕ) ((S+N+1)+1,(V+N)+1) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (A,B) ((S+N+1)+1,(V+N)+1) y v := by
  dsimp only
  let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+N+1) (V+N) u
  let v' : Ambient background T.Y (A+(N-d:ℕ)+1,B+(N-d:ℕ)) :=
    topClassicalRegrade (show ((S+N+1)+1,(V+N)+1)=(A+(N-d:ℕ)+1,B+(N-d:ℕ)) by
      ext <;> omega) v
  have hv' : HEq v' v := top_classical_regrade_heq _ _
  let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ-
    W ≫ XModLambdaN.incl _ N
  let a : BiHom (B-A) (V+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show V-S=B-A by omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho K N hKN =
      finiteTopLabelAtWeight T.Y d hd K (by omega) A B (V+1) (by omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hb := positive_finite_image_boundary_label T hf N (by omega) S V u ζ hU
  dsimp only at hb
  rw [←finite_full_correction_boundary_unchanged _ N (V-S) (V+1)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V ζ) W] at hb
  have hb' := congrArg (homotopyRegrade
    (show ((V+N)+1)-((S+N+1)+1)=(B+(N-d:ℕ))-(A+(N-d:ℕ)+1) by omega)
    (show (V+N)+1=B+(N-d:ℕ) by omega)) hb
  rw [source_native_label_transport T.Y ((S+N+1)+1) ((V+N)+1)
    (A+(N-d:ℕ)+1) (B+(N-d:ℕ)) (by omega) (by omega) v v' hv'] at hb'
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (B-A) (V+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel T.Y (A+(N-d:ℕ)+1) (B+(N-d:ℕ)) v' := by
    simpa only [a,η,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb'
  have hdiff := finite_source_differential_of_top_at_weight T.Y d N K hd (by omega) (by omega)
    A B (V+1) (by omega) (y+error) v' a ha hba
  have hdy := differential_of_source_later_cycle T.Y ((N-d:ℕ)+1)
    (A,B) (A+(N-d:ℕ)+1,B+(N-d:ℕ)) y (y+error) v' hdiff (by
      simpa only [sub_add_cancel_left,zero_sub] using
        (cycles background T.Y ((N-d:ℕ)+1) (A,B)).neg_mem himage)
  have hfinal := classical_differential_heq T.Y ((N-d:ℕ)+1) rfl
    (show (A+(N-d:ℕ)+1,B+(N-d:ℕ))=((S+N+1)+1,(V+N)+1) by ext <;> omega)
    y y v' v HEq.rfl hv' hdy
  have hcycles := cycles_of_differential T.Y ((N-d:ℕ)+1) _ _ y v hfinal
  exact ⟨by simpa only [add_sub_cancel_right] using hcycles.1,
    by simpa only [add_sub_cancel_right] using hcycles.2,hfinal⟩

/-- The higher early-boundary source criterion in the positive-first-arrow
branch. Write a=i+1, L=q+1, r=N+1, K=L-a+1 and D=r-K+1. Only K≤r-1
is required: the source-boundary correction need not vanish on the r-page. -/
public theorem higher_early_source_differential_positive_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q N : ℕ) (hi : 0 < i) (hiq : i < q) (hKN : (q+1)-i ≤ N) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (x : Ambient background T.X (s+i,t+i-1))
    (u : Ambient background T.X ((s+i)+N+1,(t+i-1)+N))
    (y : Ambient background T.Y (s+q+1,t+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s+i,t+i-1) ((s+i)+N+1,(t+i-1)+N) x u)
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) y))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) x)))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y' : Ambient background T.Y (p,t-s+p), y' ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y'-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+i,(t+i-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+i) (t+i-1) z ∈
        boundaries background T.X (i+1) (s+i,t+i-1))
    (hmid : ∀ j : ℕ, 1≤j → j<((q+1)-i)-1 →
      ∀ a : Ambient background T.X ((s+i)+j,(t+i-1)+j),
        a ∈ cycles background T.X (((q+1-i:ℕ):ℤ)-j) ((s+i)+j,(t+i-1)+j) →
        ∃ z : Ambient background T.Z ((s+i)+j,(t+i-1)+j+1),
          z ∈ cycles background T.Z (((q+1-i:ℕ):ℤ)-j) ((s+i)+j,(t+i-1)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+i)+j) ((t+i-1)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+i)+j,(t+i-1)+j))
    (himage : ∀ e : Ambient background T.X ((s+i)+(q-i:ℕ),(t+i-1)+(q-i:ℕ)),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+i)+(q-i:ℕ)) ((t+i-1)+(q-i:ℕ)) e ∈
        cycles background T.Y ((N-(q-i):ℕ)+1)
          (((s+i)+(q-i:ℕ))+1,((t+i-1)+(q-i:ℕ))+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
      T hf ((s+i)+N+1) ((t+i-1)+N) u
    IsCycle background T.Y (N-(q-i):ℕ) (s+q+1,t+q) y ∧
      IsCycle background T.Y (N-(q-i):ℕ) (((s+i)+N+1)+1,((t+i-1)+N)+1) v ∧
      DifferentialAt background T.Y ((N-(q-i):ℕ)+1) (s+q+1,t+q)
        (((s+i)+N+1)+1,((t+i-1)+N)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,x',aHat,W,hcA,hxx,hW,hW0,hcAi⟩ :=
    higher_positive_compatible_finite_lift T he hT hf hg hh i q hi hiq s t c x y hdroot hearly hR hH
  have hdx' := differential_of_source_boundary_congruent T.X (N+1) (i+1)
    (s+i,t+i-1) ((s+i)+N+1,(t+i-1)+N) x' x u hdx hxx
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    (s+i) (t+i-1) x' u).mp hdx'
  have hK : q-i+1=q+1-i := by omega
  obtain ⟨e,error,herror,htop⟩ := early_positive_finite_source_top_at_degree
    T he hT hf hg hh (q-i) ((q+1)-i) N (by omega) (by omega) hKN
    (s+i) (t+i-1) (s+q+1) (t+q) (by omega) (by omega)
    x' y (by simpa only [hK] using hmid) ζ hζ cA hcA W hcAi
  have hecycle : error ∈ cycles background T.Y ((N-(q-i):ℕ)+1) (s+q+1,t+q) := by
    have transport (p p' : Bidegree) (hp : p=p')
        (a : Ambient background T.Y p) (a' : Ambient background T.Y p')
        (ha : HEq a a') (hc : a' ∈ cycles background T.Y ((N-(q-i):ℕ)+1) p') :
        a ∈ cycles background T.Y ((N-(q-i):ℕ)+1) p := by
      subst p'; cases eq_of_heq ha; exact hc
    exact transport _ _ (by ext <;> omega) error _ herror (himage e)
  exact higher_source_differential_of_corrected_top T hf (q-i) ((q+1)-i) N
    (by omega) (by omega) hKN (s+i) (t+i-1) (s+q+1) (t+q) (by omega) (by omega)
    u y error ζ hU W htop hecycle

end
end KIP126.ProofTools.Internal.SyntheticCoverage
