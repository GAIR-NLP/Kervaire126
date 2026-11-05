module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDivision
import all KIP126.ProofTools.SyntheticCoverage.EarlyBoundaryDifferential
import all KIP126.ProofTools.SyntheticCoverage.EarlySourceTop

/-! Source early-boundary correction for differential criteria.
Subtracting the projection of the actual full correction changes the finite
source image and leaves its absolute boundary unchanged. The subsequent
coefficient division therefore retains the original differential target.
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

/-- Removing a specified full projection leaves the actual absolute
boundary unchanged, before any first-quotient comparison. -/
private theorem finite_full_correction_boundary_unchanged
    (A : SyntheticSpectrum) (N : ℕ) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A N)) (W : BiHom m w A) :
    (a-W ≫ XModLambdaN.incl A N) ≫ XModLambdaN.proj A N = a ≫ XModLambdaN.proj A N := by
  have hz : XModLambdaN.incl A N ≫ XModLambdaN.proj A N = 0 :=
    comp_distTriang_mor_zero₂₃ (XModLambdaN.cofiberTriangle A N)
      (XModLambdaN.cofiberTriangle_distinguished A N)
  rw [Preadditive.sub_comp,Category.assoc,hz,comp_zero,sub_zero]

/-- The actual corrected top restriction yields the prescribed differential
target. The full correction contributes no absolute boundary. -/
private theorem early_source_differential_of_corrected_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q N : ℕ) (hq : 2 ≤ q) (hqN : q ≤ N) (s t : ℤ)
    (u : Ambient background T.X ((s+1)+N+1,t+N))
    (y error : Ambient background T.Y (s+q+1,t+q))
    (ζ : BiHom (t-(s+1)) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hU : adjacentBoundaryLabel T.X N (s+1) t ζ =
      nativeFirstLabel T.X ((s+1)+N+1) (t+N) u)
    (W : BiHom (t-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (htop : homotopyRegrade (show t-(s+1)=(t+q)-(s+q+1) by omega) rfl
        ((positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-(s+1)) t ζ-
          W ≫ XModLambdaN.incl _ N) ≫
          (background.quotients.tower _).rho ((q+1)-1) N (by omega)) =
      finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
        (s+q+1) (t+q) (t+1) (by omega) (y+error))
    (himage : error ∈ cycles background T.Y ((N-(q-1):ℕ)+1) (s+q+1,t+q)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+1)+N+1) (t+N) u
    IsCycle background T.Y (N-(q-1):ℕ) (s+q+1,t+q) y ∧
      IsCycle background T.Y (N-(q-1):ℕ) (((s+1)+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-(q-1):ℕ)+1) (s+q+1,t+q)
        (((s+1)+N+1)+1,(t+N)+1) y v := by
  dsimp only
  let S := s+q+1
  let V := t+q
  let d : ℕ := q-1
  let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+1)+N+1) (t+N) u
  let v' : Ambient background T.Y (S+(N-d:ℕ)+1,V+(N-d:ℕ)) :=
    topClassicalRegrade (show (((s+1)+N+1)+1,(t+N)+1)=(S+(N-d:ℕ)+1,V+(N-d:ℕ)) by
      ext <;> dsimp [S,V,d] <;> omega) v
  have hv' : HEq v' v := top_classical_regrade_heq _ _
  let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-(s+1)) t ζ-
    W ≫ XModLambdaN.incl _ N
  let a : BiHom (V-S) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show t-(s+1)=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho ((q+1)-1) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) ((q+1)-1) (by dsimp [d]; omega)
        S V (t+1) (by dsimp [V,d]; omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hb := positive_finite_image_boundary_label T hf N (by omega) (s+1) t u ζ hU
  dsimp only at hb
  rw [←finite_full_correction_boundary_unchanged _ N (t-(s+1)) (t+1)
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-(s+1)) t ζ) W] at hb
  have hb' := congrArg (homotopyRegrade
    (show ((t+N)+1)-(((s+1)+N+1)+1)=(V+(N-d:ℕ))-(S+(N-d:ℕ)+1) by dsimp [S,V,d]; omega)
    (show (t+N)+1=V+(N-d:ℕ) by dsimp [V,d]; omega)) hb
  rw [source_native_label_transport T.Y (((s+1)+N+1)+1) ((t+N)+1)
    (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) (by dsimp [S,d]; omega) (by dsimp [V,d]; omega) v v' hv'] at hb'
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (V-S) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel T.Y (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) v' := by
    simpa only [a,η,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb'
  have hd := finite_source_differential_of_top_at_weight T.Y d N ((q+1)-1)
    (by dsimp [d]; omega) (by dsimp [d]; omega) (by dsimp [d]; omega)
    S V (t+1) (by dsimp [V,d]; omega) (y+error) v' a ha hba
  have hdy := differential_of_source_later_cycle T.Y ((N-d:ℕ)+1)
    (S,V) (S+(N-d:ℕ)+1,V+(N-d:ℕ)) y (y+error) v' hd (by
      simpa only [sub_add_cancel_left,zero_sub] using
        (cycles background T.Y ((N-d:ℕ)+1) (S,V)).neg_mem himage)
  have hfinal := classical_differential_heq T.Y ((N-d:ℕ)+1) rfl
    (show (S+(N-d:ℕ)+1,V+(N-d:ℕ))=(((s+1)+N+1)+1,(t+N)+1) by
      ext <;> dsimp [S,V,d] <;> omega) y y v' v HEq.rfl hv' hdy
  have hcycles := cycles_of_differential T.Y ((N-d:ℕ)+1) _ _ y v hfinal
  exact ⟨by simpa only [add_sub_cancel_right] using hcycles.1,
    by simpa only [add_sub_cancel_right] using hcycles.2,hfinal⟩

/-- The positive-first-map early-boundary differential criterion with
the specified source and target. Here `L=q+1`, `r=N+1`, and `D=r-L+2`.
The displayed early differentials produce the finite source and full correction. -/
public theorem early_source_differential_positive_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 2≤q) (hqN : q≤N) (s t : ℤ)
    (x : Ambient background T.X (s+1,t))
    (u : Ambient background T.X ((s+1)+N+1,t+N))
    (c : Ambient background T.Y (s,t))
    (y : Ambient background T.Y (s+q+1,t+q))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s+1,t) ((s+1)+N+1,t+N) x u)
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) y))
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t x))
    (hH : ∀ z : Ambient background T.Z (s+1,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+1) t z ∈
        boundaries background T.X 2 (s+1,t))
    (hmid : ∀ j : ℕ, 1≤j → j<q-1 →
      ∀ a : Ambient background T.X ((s+1)+j,t+j),
        a ∈ cycles background T.X ((q:ℤ)-j) ((s+1)+j,t+j) →
        ∃ z : Ambient background T.Z ((s+1)+j,t+j+1),
          z ∈ cycles background T.Z ((q:ℤ)-j) ((s+1)+j,t+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+1)+j) (t+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+1)+j,t+j))
    (himage : ∀ e : Ambient background T.X ((s+1)+(q-1),t+(q-1)),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+1)+(q-1)) (t+(q-1)) e ∈
        cycles background T.Y ((N-(q-1):ℕ)+1) (((s+1)+(q-1))+1,(t+(q-1))+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+1)+N+1) (t+N) u
    IsCycle background T.Y (N-(q-1):ℕ) (s+q+1,t+q) y ∧
      IsCycle background T.Y (N-(q-1):ℕ) (((s+1)+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-(q-1):ℕ)+1) (s+q+1,t+q)
        (((s+1)+N+1)+1,(t+N)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,x',aHat,W,hcA,hxx,hW,hW0,hcAi⟩ :=
    early_positive_compatible_finite_lift T he hT hf hg hh q hq s t c x y hdroot hH hd₂
  have hdx' := differential_of_source_boundary_congruent T.X (N+1) 2
    (s+1,t) ((s+1)+N+1,t+N) x' x u hdx hxx
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    (s+1) t x' u).mp hdx'
  obtain ⟨e,error,herror,htop⟩ := early_positive_finite_source_top_at_early_level
    T he hT hf hg hh q N hq hqN s t x' y hmid ζ hζ cA hcA W hcAi
  have hecycle : error ∈ cycles background T.Y ((N-(q-1):ℕ)+1) (s+q+1,t+q) := by
    have transport (p p' : Bidegree) (hp : p=p')
        (a : Ambient background T.Y p) (a' : Ambient background T.Y p')
        (ha : HEq a a') (hc : a' ∈ cycles background T.Y ((N-(q-1):ℕ)+1) p') :
        a ∈ cycles background T.Y ((N-(q-1):ℕ)+1) p := by
      subst p'; cases eq_of_heq ha; exact hc
    exact transport _ _ (by ext <;> omega) error _ herror (himage e)
  exact early_source_differential_of_corrected_top T hf q N hq hqN s t u y error
    ζ hU W htop hecycle

end
end KIP126.ProofTools.Internal.SyntheticCoverage
