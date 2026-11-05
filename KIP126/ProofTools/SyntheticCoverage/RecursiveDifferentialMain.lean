module

public import KIP126.ProofTools.SyntheticCoverage.RecursivePermanence

public import KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.RecursiveDifferential

/-! Original bottom three-layer relation criteria. The selected adjacent
source and its absolute boundary are constructed from the original main
differential, then corrected together while preserving the entire upper
calibration. All terminal conditions act on the complete relation. -/

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

private theorem recursive_finite_differential_at_weight_and_degree
    (Y : (AdamsObject (coefficients := background.coefficients))) (N d M : ℕ) (hd : 0<d) (hdN : d<N) (hM : d+1=M)
    (s t w B A V : ℤ) (hw : t-d=w)
    (hA : A=s+(N+2-d:ℕ)+1) (hV : V=t+(N+2-d:ℕ))
    (x y sourceError : Ambient background Y (s,t))
    (hsourceError : x-y-sourceError∈boundaries background Y B (s,t))
    (hsourceSurvives : sourceError∈cycles background Y ((N+2-d:ℕ)+1) (s,t))
    (η : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hcalibration : η≫(background.quotients.tower _).rho M N (by omega)=
      finiteTopLabelAtWeight Y d hd M hM s t w hw x)
    (v z targetError : Ambient background Y (A,V))
    (P : Submodule ℤ (Ambient background Y (A,V)))
    (hP : permanentCycles background Y (A,V)≤P) (hv : v∈P)
    (hterminal : z+targetError∈P → z+targetError∈boundaries background Y (N+2-d:ℕ) (A,V))
    (htop : homotopyRegrade
      (show (t-s)-1=V-A by omega) (show w+N=V-2 by omega)
      (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel Y 2 (by decide) A V (v+z+targetError)) :
    IsCycle background Y (N+2-d:ℕ) (s,t) y ∧ IsCycle background Y (N+2-d:ℕ) (A,V) v ∧
      DifferentialAt background Y ((N+2-d:ℕ)+1) (s,t) (A,V) y v := by
  subst M; subst w; subst A; subst V
  apply recursive_finite_differential_of_relation_image Y N d hd hdN s t B
    x y sourceError hsourceError hsourceSurvives η _ v z targetError P hP hv hterminal htop
  simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using hcalibration

private theorem recursive_first_differential_at_degree
    (Y : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (hN : 0<N) (s t A V : ℤ)
    (hA : A=s+(N+2:ℕ)+1) (hV : V=t+(N+2:ℕ))
    (y : Ambient background Y (s,t))
    (η : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel Y s t y)
    (v z targetError : Ambient background Y (A,V))
    (P : Submodule ℤ (Ambient background Y (A,V)))
    (hP : permanentCycles background Y (A,V)≤P) (hv : v∈P)
    (hterminal : z+targetError∈P → z+targetError∈boundaries background Y (N+2:ℕ) (A,V))
    (htop : homotopyRegrade
      (show (t-s)-1=V-A by omega) (show t+N=V-2 by omega)
      (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel Y 2 (by decide) A V (v+z+targetError)) :
    IsCycle background Y (N+2:ℕ) (s,t) y ∧ IsCycle background Y (N+2:ℕ) (A,V) v ∧
      DifferentialAt background Y ((N+2:ℕ)+1) (s,t) (A,V) y v := by
  subst A; subst V
  exact recursive_first_differential_of_relation_image Y N hN s t y η hfirst
    v z targetError P hP hv hterminal htop

private theorem recursive_common_three_layer_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t A B : ℤ) (hA : A=s+2+1) (hB : B=t+2)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (A,B))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      3 (s,t) (A,B) z ((background.classical.map T.g).pageMap 2 (A,B) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3),
      c ≫ (background.quotients.tower _).rho 1 3 (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3 =
        homotopyRegrade (show (B)-(A)=t-(s+1) by omega)
          (show B-2=t by omega)
          (finiteTopLabel T.Y 2 (by decide) (A) (B) v) := by
  subst A; subst B
  exact finite_common_lift_positive_h T he hT hf hg hh 2 (by decide) s t z x v hx hd

private theorem recursive_common_three_layer_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t A B : ℤ) (hA : A=s+2+1) (hB : B=t+2)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (A,B))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      3 (s+1,t+1) ((A)+1,(B)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (A) (B) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3),
      c ≫ (background.quotients.tower _).rho 1 3 (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3 =
        homotopyRegrade (show (B)-(A)=t-(s+1) by omega)
          (show B-2=t by omega)
          (finiteTopLabel T.Y 2 (by decide) (A) (B) v) := by
  subst A; subst B
  exact finite_common_lift_positive_g T he hT hf hg hh 2 (by decide) s t z x v hx hd

public def RecursiveDifferentialHTerminal
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (D s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1))) : Prop :=
  ∀ k∈K₀, ∀ (U : Ambient background T.Z (s,t)) (z : Ambient background T.Y (s+1+1,t+1)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
      (by simpa only [add_sub_cancel_right] using k) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z) →
    ∀ e : Ambient background T.X (s+1+1,t+1),
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈P →
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈boundaries background T.Y (D-1) (s+1+1,t+1)

public def RecursiveDifferentialGTerminal
    (T : TriangleData background.auxiliary) (hg : normalizedExponent background.classicalTower T.g=1)
    (D s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1))) : Prop :=
  ∀ k∈K₀, ∀ (U : Ambient background T.Z (s+1,t+1)) (z : Ambient background T.Y (s+1+1,t+1)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
      (by simpa only [add_sub_cancel_right] using k) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z) →
    ∀ e : Ambient background T.X (s+1+1,t+1),
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈P →
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈boundaries background T.Y (D-1) (s+1+1,t+1)

public def RecursiveDifferentialFTerminal
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (D s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,(t+1)+1))) : Prop :=
  ∀ k∈K₀, ∀ (U : Ambient background T.Z (s,t+1)) (z : Ambient background T.Y (s+1+1,(t+1)+1)),
    (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) U) (by simpa using k) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t+1) (s+1+1,(t+1)+1) U
      ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) z) →
    ∀ e : Ambient background T.X (s+1,t+1),
      z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) e∈P →
      z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) e∈
        boundaries background T.Y (D-1) (s+1+1,(t+1)+1)

/-- The adjacent representative and its actual absolute boundary are
transported together to the middle coordinates used by the Q3 relation. -/
private theorem recursive_adjacent_boundary_coordinates
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (s t p v : ℤ)
    (hp : p=s+N+2) (hv : v=t+N+1)
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    recursiveBoundaryRepresentative X N p v
      (homotopyRegrade (show t-s=v-p+1 by omega) (show t=v-1-N by omega) ζ)=
      homotopyRegrade (show (t+N)-(s+N+1)=v-p by omega) (show t+N=v-1 by omega)
        (boundaryRepresentative X N s t ζ) := by
  simp only [recursiveBoundaryRepresentative,boundaryRepresentative,
    source_boundary_regrade,last_layer_regrade_trans]

private theorem recursive_top_label_unregrade
    (X : (AdamsObject (coefficients := background.coefficients))) (p t : ℤ) (v : Ambient background X (p+1,t+1)) :
    homotopyRegrade (show t-p=(t+1)-(p+1) by omega)
      (show t-1=(t+1)-2 by omega) (recursiveTopLabel X p t v)=
      finiteTopLabel X 2 (by decide) (p+1) (t+1) v := by
  simp only [recursiveTopLabel,last_layer_regrade_trans,top_target_regrade_self]

private theorem recursive_finite_boundary_top_from_coordinates
    (Y : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (m w p t : ℤ)
    (hm : m-1=t-p) (hw : w+N=t-1)
    (η : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (v : Ambient background Y (p+1,t+1))
    (htop : recursiveBoundaryRepresentative Y N p t
        (homotopyRegrade (show m=t-p+1 by omega) (show w=t-1-N by omega) η) ≫
      XModLambdaN.incl _ 3=recursiveTopLabel Y p t v) :
    homotopyRegrade (show m-1=(t+1)-(p+1) by omega) (show w+N=(t+1)-2 by omega)
      (biSuspensionHomEquiv m w N (background.nu.functor.obj (Y.obj background.auxiliary))
        (η≫XModLambdaN.proj _ N)≫XModLambdaN.incl _ 3)=
      finiteTopLabel Y 2 (by decide) (p+1) (t+1) v := by
  have h := congrArg (homotopyRegrade (show t-p=(t+1)-(p+1) by omega)
    (show t-1=(t+1)-2 by omega)) htop
  rw [recursive_top_label_unregrade] at h
  simpa only [recursiveBoundaryRepresentative,source_boundary_regrade,
    ←regrade_comp,bi_susp_regrade,last_layer_regrade_trans] using h

/-- The original whole-relation differential criterion with ordinary
upper length one, positive third arrow. -/
public theorem recursive_differential_ordinary_third_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hyF : y=(background.classical.map T.f).pageMap 2 (s,t) x)
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1))
    (z₂ : Ambient background T.Z (s+N,t+N))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+N+1) ((t+N)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (s+N) (t+N) z₂)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      (s+N,t+N) (((s+N+1)+1)+1,(t+N+1)+1) z₂
      ((background.classical.map T.g).pageMap 2 (((s+N+1)+1)+1,(t+N+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X ((s+N+1)+1,t+N+1)))
    (_hK₀ : ∀ k∈K₀, k∈cycles background T.X 2 ((s+N+1)+1,t+N+1) ∧
      (background.classical.map T.f).pageMap 2 ((s+N+1)+1,t+N+1) k=0)
    (Pm B : Submodule ℤ (Ambient background T.Y ((s+N+1)+1,t+N+1)))
    (hPm : permanentCycles background T.Y ((s+N+1)+1,t+N+1)≤Pm)
    (hB : boundaries background T.Y ((N:ℤ)+1) ((s+N+1)+1,t+N+1)≤B)
    (hmid : RecursiveDifferentialHMiddle T hh N 1 (s+N+1) (t+N+1) Pm B K₀)
    (hsurj : RecursivePositiveHSurjective T hh (s+N+1) (t+N+1) K₀)
    (hy : y∈cycles background T.Y (N+2:ℕ) (s,t))
    (P : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1)))
    (hP : permanentCycles background T.Y (((s+N+1)+1)+1,(t+N+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialHTerminal T hh ((N+2:ℕ)+1)
      (s+N+1) (t+N+1) K₀ P) :
    IsCycle background T.Y (N+2:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+2:ℕ) (((s+N+1)+1)+1,(t+N+1)+1) v ∧
      DifferentialAt background T.Y ((N+2:ℕ)+1) (s,t)
        (((s+N+1)+1)+1,(t+N+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN s t x u).mp hdx
  obtain ⟨c,hcfirst,hci⟩ := recursive_common_three_layer_h T he hT hf hg hh
    (s+N) (t+N) (((s+N+1)+1)+1) ((t+N+1)+1) (by omega) (by omega) z₂ u v hu hdz
  let p := (s+N+1)+1
  let w := t+N+1
  let ζm := homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
    (show t=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (t+N)-(s+N+1)=w-p by dsimp [p,w];omega)
    (show t+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N s t p w
    (by dsimp [p];omega) rfl ζ
  have hsame : recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 1=
      cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N s t ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : cm≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y p w v := by
    dsimp only [cm,recursiveTopLabel]
    rw [←regrade_comp,hci,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=t-s by dsimp [p,w];omega)
      (show w-1-N=t by dsimp [w];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) N))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y s t y := by
    dsimp only [ζm]
    simp only [←regrade_comp,last_layer_regrade_trans,top_target_regrade_self]
    rw [Category.assoc,
      ←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  have hgate (a : Ambient background T.X (p,w))
      (ha : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a)
        (recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 3-cm)) :
      (background.classical.map T.f).pageMap 2 (p,w) a∈B :=
    hB (recursive_ordinary_first_head_gate T.X T.Y T.f N hN p w s t
      (by dsimp [p];omega) rfl ζm y
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hy) hsource cm v hcm a ha)
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_h_relation_image_of_head_gate
    T he hT hf hg hh N 1 (by decide) hN (s+N+1) (t+N+1) K₀ Pm B hPm hmid hsurj
    ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=t-s by dsimp [p,w];omega)
    (show w-1-N=t by dsimp [w];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) N)
  have hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y s t y := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f 1 N hN _ _ ζ' ζm hρ]
    simpa only [regrade_comp] using hsource
  have htopm : recursiveBoundaryRepresentative T.Y N p w
      (homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
        (show t=w-1-N by dsimp [w];omega) η)≫XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y p w (v+z+(background.classical.map T.f).pageMap 2 (p+1,w+1) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,recursive_boundary_representative_natural,
      Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  have htop := recursive_finite_boundary_top_from_coordinates T.Y N (t-s) t p w
    (by dsimp [p,w];omega) (by dsimp [w];omega) η _ htopm
  exact recursive_first_differential_at_degree T.Y N hN s t (p+1) (w+1)
    (by dsimp [p];omega) (by dsimp [w];omega) y η hfirst v z
    ((background.classical.map T.f).pageMap 2 (p+1,w+1) e) P hP hv
    (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htop

/-- The original whole-relation differential criterion with ordinary
upper length one, positive second arrow. -/
public theorem recursive_differential_ordinary_second_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hyF : y=(background.classical.map T.f).pageMap 2 (s,t) x)
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1))
    (z₂ : Ambient background T.Z (s+N+1,(t+N)+1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+N+1) ((t+N)+1)
      ((background.classical.map T.h).pageMap 2 (s+N+1,(t+N)+1) z₂) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      (s+N+1,(t+N)+1) ((((s+N+1)+1)+1)+1,((t+N+1)+1)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((s+N+1)+1)+1) ((t+N+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X ((s+N+1)+1,t+N+1)))
    (_hK₀ : ∀ k∈K₀, k∈cycles background T.X 2 ((s+N+1)+1,t+N+1) ∧
      (background.classical.map T.f).pageMap 2 ((s+N+1)+1,t+N+1) k=0)
    (Pm B : Submodule ℤ (Ambient background T.Y ((s+N+1)+1,t+N+1)))
    (hPm : permanentCycles background T.Y ((s+N+1)+1,t+N+1)≤Pm)
    (hB : boundaries background T.Y ((N:ℤ)+1) ((s+N+1)+1,t+N+1)≤B)
    (hmid : RecursiveDifferentialGMiddle T hg N 1 (s+N+1) (t+N+1) Pm B K₀)
    (hsurj : RecursivePositiveGSurjective T hg (s+N+1) (t+N+1) K₀)
    (hy : y∈cycles background T.Y (N+2:ℕ) (s,t))
    (P : Submodule ℤ (Ambient background T.Y (((s+N+1)+1)+1,(t+N+1)+1)))
    (hP : permanentCycles background T.Y (((s+N+1)+1)+1,(t+N+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialGTerminal T hg ((N+2:ℕ)+1)
      (s+N+1) (t+N+1) K₀ P) :
    IsCycle background T.Y (N+2:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+2:ℕ) (((s+N+1)+1)+1,(t+N+1)+1) v ∧
      DifferentialAt background T.Y ((N+2:ℕ)+1) (s,t)
        (((s+N+1)+1)+1,(t+N+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN s t x u).mp hdx
  obtain ⟨c,hcfirst,hci⟩ := recursive_common_three_layer_g T he hT hf hg hh
    (s+N) (t+N) (((s+N+1)+1)+1) ((t+N+1)+1) (by omega) (by omega) z₂ u v hu hdz
  let p := (s+N+1)+1
  let w := t+N+1
  let ζm := homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
    (show t=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (t+N)-(s+N+1)=w-p by dsimp [p,w];omega)
    (show t+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N s t p w
    (by dsimp [p];omega) rfl ζ
  have hsame : recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 1=
      cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N s t ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : cm≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y p w v := by
    dsimp only [cm,recursiveTopLabel]
    rw [←regrade_comp,hci,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=t-s by dsimp [p,w];omega)
      (show w-1-N=t by dsimp [w];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) N))≫
      (background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y s t y := by
    dsimp only [ζm]
    simp only [←regrade_comp,last_layer_regrade_trans,top_target_regrade_self]
    rw [Category.assoc,
      ←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  have hgate (a : Ambient background T.X (p,w))
      (ha : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a)
        (recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 3-cm)) :
      (background.classical.map T.f).pageMap 2 (p,w) a∈B :=
    hB (recursive_ordinary_first_head_gate T.X T.Y T.f N hN p w s t
      (by dsimp [p];omega) rfl ζm y
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hy) hsource cm v hcm a ha)
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_g_relation_image_of_head_gate
    T he hT hf hg hh N 1 (by decide) hN (s+N+1) (t+N+1) K₀ Pm B hPm hmid hsurj
    ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=t-s by dsimp [p,w];omega)
    (show w-1-N=t by dsimp [w];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) N)
  have hfirst : η≫(background.quotients.tower _).rho 1 N hN=nativeFirstLabel T.Y s t y := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f 1 N hN _ _ ζ' ζm hρ]
    simpa only [regrade_comp] using hsource
  have htopm : recursiveBoundaryRepresentative T.Y N p w
      (homotopyRegrade (show t-s=w-p+1 by dsimp [p,w];omega)
        (show t=w-1-N by dsimp [w];omega) η)≫XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y p w (v+z+(background.classical.map T.f).pageMap 2 (p+1,w+1) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,recursive_boundary_representative_natural,
      Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  have htop := recursive_finite_boundary_top_from_coordinates T.Y N (t-s) t p w
    (by dsimp [p,w];omega) (by dsimp [w];omega) η _ htopm
  exact recursive_first_differential_at_degree T.Y N hN s t (p+1) (w+1)
    (by dsimp [p];omega) (by dsimp [w];omega) y η hfirst v z
    ((background.classical.map T.f).pageMap 2 (p+1,w+1) e) P hP hv
    (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htop

public theorem recursive_differential_ordinary_third_finite_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (a N : ℕ) (ha : 0<a) (haN : a+1≤N) (B W : ℤ)
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
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x=0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) ((B+1),W) ((B+1)+N+1,W+N) x u)
    (v : Ambient background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1))
    (z₂ : Ambient background T.Z ((B+1)+N,W+N))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((B+1)+N+1) ((W+N)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) ((B+1)+N) (W+N) z₂)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      ((B+1)+N,W+N) ((((B+1)+N+1)+1)+1,(W+N+1)+1) z₂
      ((background.classical.map T.g).pageMap 2 ((((B+1)+N+1)+1)+1,(W+N+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X (((B+1)+N+1)+1,W+N+1)))
    (_hK₀ : ∀ k∈K₀, k∈cycles background T.X 2 (((B+1)+N+1)+1,W+N+1) ∧
      (background.classical.map T.f).pageMap 2 (((B+1)+N+1)+1,W+N+1) k=0)
    (Pm Bbar : Submodule ℤ (Ambient background T.Y (((B+1)+N+1)+1,W+N+1)))
    (hPm : permanentCycles background T.Y (((B+1)+N+1)+1,W+N+1)≤Pm)
    (hB : boundaries background T.Y ((N-a:ℕ)+1) (((B+1)+N+1)+1,W+N+1)≤Bbar)
    (hmid : RecursiveDifferentialHMiddle T hh N (a+1) ((B+1)+N+1) (W+N+1) Pm Bbar K₀)
    (hsurj : RecursivePositiveHSurjective T hh ((B+1)+N+1) (W+N+1) K₀)
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e∈
        cycles background T.Y ((N+2-a:ℕ)+1) (B+a+1,W+a))
    (hy : y∈cycles background T.Y (N+2-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1)))
    (hP : permanentCycles background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialHTerminal T hh ((N+2-a:ℕ)+1)
      ((B+1)+N+1) (W+N+1) K₀ P) :
    IsCycle background T.Y (N+2-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (N+2-a:ℕ) ((((B+1)+N+1)+1)+1,(W+N+1)+1) v ∧
      DifferentialAt background T.Y ((N+2-a:ℕ)+1) (B+a+1,W+a)
        ((((B+1)+N+1)+1)+1,(W+N+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hN : 0<N := by omega
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a N haN B W x ζ hζ
  obtain ⟨etop,hitop⟩ := ordinary_finite_image_of_same_source_third T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have ht := ordinary_source_image_restriction_top T.X T.Y T.f a N ha haN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop) hitop
  let A := B+a+1
  let V := W+a
  let ytop := y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop
  have ht' : homotopyRegrade (show W-(B+1)=V-A by dsimp [A,V];omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N)≫
        (background.quotients.tower _).rho (a+1) N haN)=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A V W (by dsimp [V];omega) ytop := by
    have transport (M : ℕ) (hM : 0+(a+1)=M) :
        homotopyRegrade (show W-(B+1)=V-A by dsimp [A,V];omega) rfl
          ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N)≫
            (background.quotients.tower _).rho M N (by omega))=
        finiteTopLabelAtWeight T.Y (0+a) (by omega) M (by omega) A V W
          (by dsimp [V];omega) ytop := by
      subst M
      exact ht
    simpa only [Nat.zero_add] using transport (a+1) (by omega)
  have hytop : ytop∈cycles background T.Y ((N-a:ℕ)+2) (A,V) := by
    have hindex : ((N-a:ℕ):ℤ)+2=(N+2-a:ℕ) := by omega
    rw [hindex]
    exact (cycles background T.Y (N+2-a:ℕ) (A,V)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) (himage etop))
  obtain ⟨c,hcfirst,hci⟩ := recursive_common_three_layer_h T he hT hf hg hh
    ((B+1)+N) (W+N) ((((B+1)+N+1)+1)+1) ((W+N+1)+1) (by omega) (by omega) z₂ u v hu hdz
  let p := ((B+1)+N+1)+1
  let w := W+N+1
  let ζm := homotopyRegrade (show W-(B+1)=w-p+1 by dsimp [p,w];omega)
    (show W=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (W+N)-((B+1)+N+1)=w-p by dsimp [p,w];omega)
    (show W+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N (B+1) W p w
    (by dsimp [p];omega) rfl ζ
  have hsame : recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 1=
      cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N (B+1) W ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : cm≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y p w v := by
    dsimp only [cm,recursiveTopLabel]
    rw [←regrade_comp,hci,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
      (show w-1-N=V-a by dsimp [w,V];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) N))≫
      (background.quotients.tower _).rho (a+1) N haN=finiteTopLabel T.Y a ha A V ytop := by
    have h := congrArg (homotopyRegrade (rfl : V-A=V-A) (show W=V-a by dsimp [V];omega)) ht'
    dsimp only [ζm]
    simpa only [←regrade_comp,last_layer_regrade_trans,finiteTopLabelAtWeight,
      top_target_regrade_self] using h
  have hgate (a' : Ambient background T.X (p,w))
      (ha' : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a')
        (recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 3-cm)) :
      (background.classical.map T.f).pageMap 2 (p,w) a'∈Bbar :=
    hB (recursive_ordinary_divided_head_gate T.X T.Y T.f a N ha (by omega) p w A V
      (by dsimp [p,A];omega) (by dsimp [w,V];omega) ζm ytop hytop hsource cm v hcm a' ha')
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_h_relation_image_of_head_gate
    T he hT hf hg hh N (a+1) (by omega) haN ((B+1)+N+1) (W+N+1) K₀ Pm Bbar hPm hmid hsurj
    ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
    (show w-1-N=V-a by dsimp [w,V];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) N)
  have hcalibration : η≫(background.quotients.tower _).rho (a+1) N haN=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A V (V-a) rfl ytop := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f (a+1) N haN _ _ ζ' ζm hρ]
    simpa only [regrade_comp,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have htopm : recursiveBoundaryRepresentative T.Y N p w
      (homotopyRegrade (show V-A=w-p+1 by dsimp [p,w,A,V];omega)
        (show V-a=w-1-N by dsimp [w,V];omega) η)≫XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y p w (v+z+(background.classical.map T.f).pageMap 2 (p+1,w+1) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,recursive_boundary_representative_natural,
      Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  have htop := recursive_finite_boundary_top_from_coordinates T.Y N (V-A) (V-a) p w
    (by dsimp [p,w,A,V];omega) (by dsimp [w,V];omega) η _ htopm
  exact recursive_finite_differential_at_weight_and_degree T.Y N a (a+1) ha (by omega) rfl
    A V (V-a) (a+1) (p+1) (w+1) rfl (by dsimp [p,A];omega) (by dsimp [w,V];omega)
    ytop y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop)
    (by dsimp only [ytop]; have hz : y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop-y-
        (background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop=0 := by abel
        rw [hz]; exact (boundaries background T.Y _ _).zero_mem)
    (himage etop) η hcalibration v z ((background.classical.map T.f).pageMap 2 (p+1,w+1) e)
    P hP hv (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htop

public theorem recursive_differential_ordinary_second_finite_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (a N : ℕ) (ha : 0<a) (haN : a+1≤N) (B W : ℤ)
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
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x=0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) ((B+1),W) ((B+1)+N+1,W+N) x u)
    (v : Ambient background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1))
    (z₂ : Ambient background T.Z ((B+1)+N+1,(W+N)+1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((B+1)+N+1) ((W+N)+1)
      ((background.classical.map T.h).pageMap 2 ((B+1)+N+1,(W+N)+1) z₂) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 3
      ((B+1)+N+1,(W+N)+1) (((((B+1)+N+1)+1)+1)+1,((W+N+1)+1)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((((B+1)+N+1)+1)+1) ((W+N+1)+1) v))
    (K₀ : Submodule ℤ (Ambient background T.X (((B+1)+N+1)+1,W+N+1)))
    (_hK₀ : ∀ k∈K₀, k∈cycles background T.X 2 (((B+1)+N+1)+1,W+N+1) ∧
      (background.classical.map T.f).pageMap 2 (((B+1)+N+1)+1,W+N+1) k=0)
    (Pm Bbar : Submodule ℤ (Ambient background T.Y (((B+1)+N+1)+1,W+N+1)))
    (hPm : permanentCycles background T.Y (((B+1)+N+1)+1,W+N+1)≤Pm)
    (hB : boundaries background T.Y ((N-a:ℕ)+1) (((B+1)+N+1)+1,W+N+1)≤Bbar)
    (hmid : RecursiveDifferentialGMiddle T hg N (a+1) ((B+1)+N+1) (W+N+1) Pm Bbar K₀)
    (hsurj : RecursivePositiveGSurjective T hg ((B+1)+N+1) (W+N+1) K₀)
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e∈
        cycles background T.Y ((N+2-a:ℕ)+1) (B+a+1,W+a))
    (hy : y∈cycles background T.Y (N+2-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1)))
    (hP : permanentCycles background T.Y ((((B+1)+N+1)+1)+1,(W+N+1)+1)≤P)
    (hv : v∈P)
    (hterminal : RecursiveDifferentialGTerminal T hg ((N+2-a:ℕ)+1)
      ((B+1)+N+1) (W+N+1) K₀ P) :
    IsCycle background T.Y (N+2-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (N+2-a:ℕ) ((((B+1)+N+1)+1)+1,(W+N+1)+1) v ∧
      DifferentialAt background T.Y ((N+2-a:ℕ)+1) (B+a+1,W+a)
        ((((B+1)+N+1)+1)+1,(W+N+1)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hN : 0<N := by omega
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N hN (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a N haN B W x ζ hζ
  obtain ⟨etop,hitop⟩ := ordinary_finite_image_of_same_source_second T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have ht := ordinary_source_image_restriction_top T.X T.Y T.f a N ha haN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop) hitop
  let A := B+a+1
  let V := W+a
  let ytop := y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop
  have ht' : homotopyRegrade (show W-(B+1)=V-A by dsimp [A,V];omega) rfl
      ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N)≫
        (background.quotients.tower _).rho (a+1) N haN)=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A V W (by dsimp [V];omega) ytop := by
    have transport (M : ℕ) (hM : 0+(a+1)=M) :
        homotopyRegrade (show W-(B+1)=V-A by dsimp [A,V];omega) rfl
          ((ζ≫XModLambdaN.map (background.nu.functor.map T.f) N)≫
            (background.quotients.tower _).rho M N (by omega))=
        finiteTopLabelAtWeight T.Y (0+a) (by omega) M (by omega) A V W
          (by dsimp [V];omega) ytop := by
      subst M
      exact ht
    simpa only [Nat.zero_add] using transport (a+1) (by omega)
  have hytop : ytop∈cycles background T.Y ((N-a:ℕ)+2) (A,V) := by
    have hindex : ((N-a:ℕ):ℤ)+2=(N+2-a:ℕ) := by omega
    rw [hindex]
    exact (cycles background T.Y (N+2-a:ℕ) (A,V)).add_mem hy
      (cycles_antitone background T.Y _ (by omega) (himage etop))
  obtain ⟨c,hcfirst,hci⟩ := recursive_common_three_layer_g T he hT hf hg hh
    ((B+1)+N) (W+N) ((((B+1)+N+1)+1)+1) ((W+N+1)+1) (by omega) (by omega) z₂ u v hu hdz
  let p := ((B+1)+N+1)+1
  let w := W+N+1
  let ζm := homotopyRegrade (show W-(B+1)=w-p+1 by dsimp [p,w];omega)
    (show W=w-1-N by dsimp [w];omega) ζ
  let cm := homotopyRegrade (show (W+N)-((B+1)+N+1)=w-p by dsimp [p,w];omega)
    (show W+N=w-1 by dsimp [w];omega) c
  have hbc := recursive_adjacent_boundary_coordinates T.X N (B+1) W p w
    (by dsimp [p];omega) rfl ζ
  have hsame : recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 1=
      cm≫(background.quotients.tower _).rho 1 3 (by decide) := by
    rw [hbc,←regrade_comp]
    change homotopyRegrade _ _ (adjacentBoundaryLabel T.X N (B+1) W ζ)=_
    rw [hU]
    dsimp only [cm]
    rw [←regrade_comp,hcfirst]
  have hcm : cm≫XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y p w v := by
    dsimp only [cm,recursiveTopLabel]
    rw [←regrade_comp,hci,last_layer_regrade_trans]
  have hsource : (homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
      (show w-1-N=V-a by dsimp [w,V];omega)
      (ζm≫XModLambdaN.map (background.nu.functor.map T.f) N))≫
      (background.quotients.tower _).rho (a+1) N haN=finiteTopLabel T.Y a ha A V ytop := by
    have h := congrArg (homotopyRegrade (rfl : V-A=V-A) (show W=V-a by dsimp [V];omega)) ht'
    dsimp only [ζm]
    simpa only [←regrade_comp,last_layer_regrade_trans,finiteTopLabelAtWeight,
      top_target_regrade_self] using h
  have hgate (a' : Ambient background T.X (p,w))
      (ha' : Detects (background.convergence (.quotient 3 (.nu T.X))) (p,w,w-1)
        (finiteTargetLabel background T.X 3 p w 1 a')
        (recursiveBoundaryRepresentative T.X N p w ζm≫XModLambdaN.incl _ 3-cm)) :
      (background.classical.map T.f).pageMap 2 (p,w) a'∈Bbar :=
    hB (recursive_ordinary_divided_head_gate T.X T.Y T.f a N ha (by omega) p w A V
      (by dsimp [p,A];omega) (by dsimp [w,V];omega) ζm ytop hytop hsource cm v hcm a' ha')
  obtain ⟨k,U,z,e,ζ',hk,hUk,hd,hρ,hi⟩ := recursive_positive_g_relation_image_of_head_gate
    T he hT hf hg hh N (a+1) (by omega) haN ((B+1)+N+1) (W+N+1) K₀ Pm Bbar hPm hmid hsurj
    ζm cm v hsame hcm hgate
  let η := homotopyRegrade (show w-p+1=V-A by dsimp [p,w,A,V];omega)
    (show w-1-N=V-a by dsimp [w,V];omega) (ζ'≫XModLambdaN.map (background.nu.functor.map T.f) N)
  have hcalibration : η≫(background.quotients.tower _).rho (a+1) N haN=
      finiteTopLabelAtWeight T.Y a ha (a+1) rfl A V (V-a) rfl ytop := by
    dsimp only [η]
    rw [←regrade_comp,recursive_ordinary_protected_image T.X T.Y T.f (a+1) N haN _ _ ζ' ζm hρ]
    simpa only [regrade_comp,finiteTopLabelAtWeight,top_target_regrade_self] using hsource
  have htopm : recursiveBoundaryRepresentative T.Y N p w
      (homotopyRegrade (show V-A=w-p+1 by dsimp [p,w,A,V];omega)
        (show V-a=w-1-N by dsimp [w,V];omega) η)≫XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y p w (v+z+(background.classical.map T.f).pageMap 2 (p+1,w+1) e) := by
    dsimp only [η]
    rw [last_layer_regrade_trans,top_target_regrade_self,recursive_boundary_representative_natural,
      Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  have htop := recursive_finite_boundary_top_from_coordinates T.Y N (V-A) (V-a) p w
    (by dsimp [p,w,A,V];omega) (by dsimp [w,V];omega) η _ htopm
  exact recursive_finite_differential_at_weight_and_degree T.Y N a (a+1) ha (by omega) rfl
    A V (V-a) (a+1) (p+1) (w+1) rfl (by dsimp [p,A];omega) (by dsimp [w,V];omega)
    ytop y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop)
    (by dsimp only [ytop]; have hz : y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop-y-
        (background.classical.map T.f).pageMap 2 (B+a+1,W+a) etop=0 := by abel
        rw [hz]; exact (boundaries background T.Y _ _).zero_mem)
    (himage etop) η hcalibration v z ((background.classical.map T.f).pageMap 2 (p+1,w+1) e)
    P hP hv (by simpa only [add_sub_cancel_right] using hterminal k hk U z hUk hd e) htop

end
end KIP126.ProofTools.Internal.SyntheticCoverage
