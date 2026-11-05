module

public import KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.FinitePermanence
import all KIP126.ProofTools.SyntheticCoverage.Permanence
import all KIP126.ProofTools.SyntheticCoverage.FullImage

/-! Higher-filtration changes of complete sources for finite comparison.
The source first label is fixed; its classical realization may change by the
next filtration. All corrections are constructed on the actual lambda quotients. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

private theorem ordinary_source_adjusted_correction_step
    (R : RealizationCoordinates background)
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c h : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (z u r : Ambient background X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hu : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j u) h)
    (hzero : h ≫ XModLambdaN.map (background.nu.functor.map f) q=0)
    (hr : r ∈ permanentCycles background X (p,t))
    (hzu : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (p,t) (z-u-r)) :
    ∃ a' : BiHom (t-p) (t-j) (background.nu.functor.obj (X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      (c+h) ≫ (background.quotients.tower _).rho 1 q (by omega)=
        c ≫ (background.quotients.tower _).rho 1 q (by omega) ∧
      (c+h) ≫ XModLambdaN.map (background.nu.functor.map f) q=
        c ≫ XModLambdaN.map (background.nu.functor.map f) q ∧
      FiltrationAtLeast background.syntheticTower (p+1)
        (a' ≫ XModLambdaN.incl _ q-(c+h)) := by
  obtain ⟨k,D,_,_,hfirst,hcfirst,himage,_,hres⟩ :=
    ordinary_affine_correction_with_residual R X Y f q j hj hjq p t a c h z u r hz hu hzero hzu
  obtain ⟨E,hE⟩ := permanent_native_source X p t r hr
  have hEdet := full_first_label_lambda_projection_detects X q j hj hjq p t r E hE
  have hnext := detects_sub_filtration (background.convergence (.quotient q (.nu X)))
    (p,t,t-j) hres hEdet
  refine ⟨a-lambdaMultiply j D-lambdaMultiply j E,?_,hcfirst,himage,?_⟩
  · rw [Preadditive.sub_comp,lambda_power_first_quotient_zero X j hj (t-p) t E,sub_zero,hfirst]
  · have heq : (a-lambdaMultiply j D-lambdaMultiply j E) ≫ XModLambdaN.incl _ q-(c+h) =
        (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h)-lambdaMultiply j E ≫ XModLambdaN.incl _ q := by
      rw [Preadditive.sub_comp]
      abel
    rw [heq]
    exact hnext

private theorem positive_h_source_adjusted_correction_step
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (p,t)))
    (hP : permanentCycles background T.Y (p,t) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      (background.classical.map T.f).pageMap 2 (p,t) z ∈ P →
      ∃ w : Ambient background T.Z (p-1,t), w ∈ cycles background T.Z (N-j:ℕ) (p-1,t) ∧
      ∃ u : Ambient background T.X (p,t),
        (background.classicalSuspension T.X).DesuspendsClass p (t+1)
          (middleLabelRegrade (X := .shift 1 T.X)
            (show (p-1+1,t+1)=(p,t+1) by congr 1; omega)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (p-1) t w))
          (by simpa using u) ∧
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u-r))
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom (t-p) (t-j) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := ordinary_affine_error_label_image_permanent T.X T.Y T.f N j hjN p t
    a c W z hzd hhigh
  obtain ⟨w,hw,u,hu,r,hr,hzu⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_h_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) (p-1) p t (by omega) w hw u hu
  obtain ⟨a',hfirst,hcfirst,himage,hnext⟩ := ordinary_source_adjusted_correction_step R
    T.X T.Y T.f N j hj hjN p t a c b z u r hzd hb hbz hr hzu
  exact ⟨a',c+b,hfirst,hcfirst,himage,hnext⟩

private theorem positive_h_source_adjusted_correction_step_at
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (m w : ℤ) (hm : m=t-p) (hw : w=t-j)
    (P : Submodule ℤ (Ambient background T.Y (p,t)))
    (hP : permanentCycles background T.Y (p,t) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      (background.classical.map T.f).pageMap 2 (p,t) z ∈ P →
      ∃ w : Ambient background T.Z (p-1,t), w ∈ cycles background T.Z (N-j:ℕ) (p-1,t) ∧
      ∃ u : Ambient background T.X (p,t),
        (background.classicalSuspension T.X).DesuspendsClass p (t+1)
          (middleLabelRegrade (X := .shift 1 T.X)
            (show (p-1+1,t+1)=(p,t+1) by congr 1; omega)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (p-1) t w))
          (by simpa using u) ∧
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u-r))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_h_source_adjusted_correction_step R T hf hg hh hT N j hj hjN p t P hP hmid a c W herror hhigh

/-- Finite iteration of the actual positive-h correction. The complete
source may change by full torsion, the finite candidate may change by H
images, and their first quotients, the entire candidate image, are retained. The complete source may also change by higher-filtration
permanent classes. The middle condition is imposed on
all actual cycle vectors whose ordinary F2 image lies in the selected P. -/
private theorem positive_h_source_adjusted_correction_to_last
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N : ℕ) (hN : 0<N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u-w) (hv : v≤(N:ℤ)+w-m)
    (P : ∀ p : ℤ, Submodule ℤ (Ambient background T.Y (p,m+p)))
    (hP : ∀ p : ℤ, u≤p → p<v → permanentCycles background T.Y (p,m+p) ≤ P p)
    (hmid : ∀ p : ℤ, u≤p → p<v →
      ∀ z : Ambient background T.X (p,m+p),
        z ∈ cycles background T.X (N-(m+p-w).toNat:ℕ) (p,m+p) →
        (background.classical.map T.f).pageMap 2 (p,m+p) z ∈ P p →
        ∃ zH : Ambient background T.Z (p-1,m+p),
          zH ∈ cycles background T.Z (N-(m+p-w).toNat:ℕ) (p-1,m+p) ∧
          ∃ z' : Ambient background T.X (p,m+p),
            (background.classicalSuspension T.X).DesuspendsClass p (m+p+1)
              (middleLabelRegrade (X := .shift 1 T.X)
                (show (p-1+1,m+p+1)=(p,m+p+1) by congr 1; omega)
                (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
                  (p-1) (m+p) zH)) (by simpa using z') ∧
            ∃ r : Ambient background T.X (p,m+p), r ∈ permanentCycles background T.X (p,m+p) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p) (z-z'-r))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower u (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower v
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N hN=c ≫ (background.quotients.tower _).rho 1 N hN ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower v (a' ≫ XModLambdaN.incl _ N-c') := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u a c with
  | h n ih =>
    by_cases heq : v≤u
    · have huv' : u=v := le_antisymm huv heq
      exact ⟨a,c,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u-w).toNat
      have hj : (j:ℤ)=m+u-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hjN : j<N := by omega
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+1)
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hnext⟩ := positive_h_source_adjusted_correction_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower v
          (c₁ ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hfinal⟩


private theorem positive_g_source_adjusted_correction_step
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (p,t)))
    (hP : permanentCycles background T.Y (p,t) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      (background.classical.map T.f).pageMap 2 (p,t) z ∈ P →
      ∃ w : Ambient background T.Z (p,t+1), w ∈ cycles background T.Z (N-j:ℕ) (p,t+1) ∧
      ∃ u : Ambient background T.X (p,t),
        (background.classicalSuspension T.X).DesuspendsClass p (t+1)
          ((background.classical.map T.h).pageMap 2 (p,t+1) w)
          (by simpa using u) ∧
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u-r))
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom (t-p) (t-j) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := ordinary_affine_error_label_image_permanent T.X T.Y T.f N j hjN p t
    a c W z hzd hhigh
  obtain ⟨w,hw,u,hu,r,hr,hzu⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_g_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) (p-1) p t (by omega) w hw u hu
  obtain ⟨a',hfirst,hcfirst,himage,hnext⟩ := ordinary_source_adjusted_correction_step R
    T.X T.Y T.f N j hj hjN p t a c b z u r hzd hb hbz hr hzu
  exact ⟨a',c+b,hfirst,hcfirst,himage,hnext⟩

private theorem positive_g_source_adjusted_correction_step_at
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (m w : ℤ) (hm : m=t-p) (hw : w=t-j)
    (P : Submodule ℤ (Ambient background T.Y (p,t)))
    (hP : permanentCycles background T.Y (p,t) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      (background.classical.map T.f).pageMap 2 (p,t) z ∈ P →
      ∃ w : Ambient background T.Z (p,t+1), w ∈ cycles background T.Z (N-j:ℕ) (p,t+1) ∧
      ∃ u : Ambient background T.X (p,t),
        (background.classicalSuspension T.X).DesuspendsClass p (t+1)
          ((background.classical.map T.h).pageMap 2 (p,t+1) w)
          (by simpa using u) ∧
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u-r))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_g_source_adjusted_correction_step R T hf hg hh hT N j hj hjN p t P hP hmid a c W herror hhigh

/-- Finite iteration of the actual positive-g correction. The complete
source may change by full torsion, the finite candidate may change by H
images, and their first quotients, the entire candidate image, are retained. The complete source may also change by higher-filtration
permanent classes. The middle condition is imposed on
all actual cycle vectors whose ordinary F2 image lies in the selected P. -/
private theorem positive_g_source_adjusted_correction_to_last
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N : ℕ) (hN : 0<N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u-w) (hv : v≤(N:ℤ)+w-m)
    (P : ∀ p : ℤ, Submodule ℤ (Ambient background T.Y (p,m+p)))
    (hP : ∀ p : ℤ, u≤p → p<v → permanentCycles background T.Y (p,m+p) ≤ P p)
    (hmid : ∀ p : ℤ, u≤p → p<v →
      ∀ z : Ambient background T.X (p,m+p),
        z ∈ cycles background T.X (N-(m+p-w).toNat:ℕ) (p,m+p) →
        (background.classical.map T.f).pageMap 2 (p,m+p) z ∈ P p →
        ∃ zH : Ambient background T.Z (p,m+p+1),
          zH ∈ cycles background T.Z (N-(m+p-w).toNat:ℕ) (p,m+p+1) ∧
          ∃ z' : Ambient background T.X (p,m+p),
            (background.classicalSuspension T.X).DesuspendsClass p (m+p+1)
              ((background.classical.map T.h).pageMap 2 (p,m+p+1) zH) (by simpa using z') ∧
            ∃ r : Ambient background T.X (p,m+p), r ∈ permanentCycles background T.X (p,m+p) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p) (z-z'-r))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower u (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower v
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N hN=c ≫ (background.quotients.tower _).rho 1 N hN ∧
      c' ≫ XModLambdaN.map (background.nu.functor.map T.f) N=c ≫ XModLambdaN.map (background.nu.functor.map T.f) N ∧
      FiltrationAtLeast background.syntheticTower v (a' ≫ XModLambdaN.incl _ N-c') := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u a c with
  | h n ih =>
    by_cases heq : v≤u
    · have huv' : u=v := le_antisymm huv heq
      exact ⟨a,c,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u-w).toNat
      have hj : (j:ℤ)=m+u-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hjN : j<N := by omega
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+1)
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hnext⟩ := positive_g_source_adjusted_correction_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower v
          (c₁ ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hfinal⟩


private theorem ordinary_source_adjusted_terminal_label
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0<d) (p t : ℤ)
    (a : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-p) (t-d) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background Y (p,t)) (e : Ambient background X (p,t))
    (he : a ≫ XModLambdaN.incl _ (d+1)-c=finiteTopLabel X d hd p t e)
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      W ≫ XModLambdaN.incl _ (d+1)+finiteTopLabel Y d hd p t v) :
    ∃ w : Ambient background Y (p,t),
      w ∈ permanentCycles background Y (p,t) ∧
      w-v-(background.classical.map f).pageMap 2 (p,t) e ∈ boundaries background Y (d+1) (p,t) ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) w
        ((R.sphere (t-p) (t-d)).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
          (hcomp.nu Y).target.hom) := by
  letI := R.additive
  have himage : (a ≫ background.nu.functor.map f-W) ≫ XModLambdaN.incl _ (d+1)-
      finiteTopLabel Y d hd p t v =
      finiteTopLabel Y d hd p t ((background.classical.map f).pageMap 2 (p,t) e) := by
    have h := congrArg (fun z => z ≫ XModLambdaN.map (background.nu.functor.map f) (d+1)) he
    rw [finite_top_label_ordinary_natural] at h
    simp only [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality] at h ⊢
    rw [hc] at h
    simpa only [sub_add_eq_sub_sub] using h
  have hz : (a ≫ background.nu.functor.map f-W) ≫ XModLambdaN.incl _ d=0 := by
    have h := congrArg (fun z => z ≫ (background.quotients.tower
      (background.nu.functor.obj (Y.obj background.auxiliary))).rho d (d+1) (by omega)) himage
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero,finite_top_restriction_zero,sub_zero] at h
    exact h
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp
    (background.nu.functor.obj (Y.obj background.auxiliary)) Y (𝟙 _) d p t
      (a ≫ background.nu.functor.map f-W) (by simpa only [Category.comp_id] using hz)
  simp only [Category.comp_id] at hb hdet
  have ht := lambda_power_first_label_projection_eq_top Y d hd p t b w hw
  rw [hb] at ht
  rw [ht] at himage
  have herr : w-v-(background.classical.map f).pageMap 2 (p,t) e ∈
      boundaries background Y (d+1) (p,t) :=
    (finite_top_difference_zero_iff_boundary Y d hd p t w v _).mp (sub_eq_zero.mpr himage)
  have hWreal := lambda_torsion_realization_zero R (t-p) (t-d) k W hW
  have hreal : (R.sphere (t-p) (t-d)).hom ≫
      background.recovery.realization.map (a ≫ background.nu.functor.map f-W) ≫ (hcomp.nu Y).target.hom =
      (R.sphere (t-p) (t-d)).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
        (hcomp.nu Y).target.hom := by
    have hbase : (R.sphere (t-p) (t-d)).hom ≫
        background.recovery.realization.map (a ≫ background.nu.functor.map f-W) =
        (R.sphere (t-p) (t-d)).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map f) := by
      rw [Functor.map_sub,Preadditive.comp_sub,hWreal,sub_zero]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ (hcomp.nu Y).target.hom) hbase
  rw [hreal] at hdet
  exact ⟨w,hwp,herr,hdet⟩

private theorem ordinary_source_adjusted_terminal
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0<d) (p t : ℤ)
    (a : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-p) (t-d) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background Y (p,t)) (P : Submodule ℤ (Ambient background Y (p,t)))
    (hP : permanentCycles background Y (p,t) ≤ P) (hv : v ∈ P)
    (hterminal : ∀ e : Ambient background X (p,t), (background.classical.map f).pageMap 2 (p,t) e ∈ P →
      ∃ r : Ambient background X (p,t), r ∈ permanentCycles background X (p,t) ∧
        IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) (p,t)
          ((background.classical.map f).pageMap 2 (p,t) e-(background.classical.map f).pageMap 2 (p,t) r))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ (d+1)-c))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+finiteTopLabel Y d hd p t v) :
    ∃ a' : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (p,t) v ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) v
        ((R.sphere (t-p) (t-d)).hom ≫ background.recovery.realization.map (a' ≫ background.nu.functor.map f) ≫
          (hcomp.nu Y).target.hom) := by
  obtain ⟨e,he⟩ := finiteTopLabel_exists X d hd p t (a ≫ XModLambdaN.incl _ (d+1)-c) herror
  obtain ⟨w,hwp,herr,hdet⟩ := ordinary_source_adjusted_terminal_label R hcomp X Y f d hd p t a c W k hW v e he hc
  have herrFinal := boundaries_le_finalBoundaries Y (p,t) (d+1) herr
  have herrP := hP (finalBoundaries_le_permanentCycles Y (p,t) herrFinal)
  have hFeP : (background.classical.map f).pageMap 2 (p,t) e ∈ P := by
    have h := P.sub_mem (P.sub_mem (hP hwp) hv) herrP
    simpa only [sub_sub_cancel] using h
  obtain ⟨r,hr,hrboundary⟩ := hterminal e hFeP
  obtain ⟨E,hE⟩ := permanent_native_source X p t r hr
  let a' := a-lambdaMultiply d E
  have hEtop := lambda_power_first_label_projection_eq_top X d hd p t E r hE
  have he' : a' ≫ XModLambdaN.incl _ (d+1)-c=finiteTopLabel X d hd p t (e-r) := by
    dsimp only [a']
    rw [Preadditive.sub_comp,hEtop,finite_top_label_sub]
    rw [←he]
    abel
  obtain ⟨w',_,herr',hdet'⟩ := ordinary_source_adjusted_terminal_label R hcomp X Y f d hd p t a' c W k hW v (e-r) he' hc
  have hdiff : w'-v ∈ finalBoundaries Y (p,t) := by
    have herrFinal' := boundaries_le_finalBoundaries Y (p,t) (d+1) herr'
    have hr' : (background.classical.map f).pageMap 2 (p,t) (e-r) ∈ finalBoundaries Y (p,t) := by
      apply (mem_finalBoundaries_iff Y (p,t) _).mpr
      simpa only [map_sub] using hrboundary
    simpa only [sub_add_cancel] using (finalBoundaries Y (p,t)).add_mem herrFinal' hr'
  obtain ⟨hp,hvdet⟩ := classical_detects_of_final_boundary_difference Y (p,t) w' v _ hdet' hdiff
  refine ⟨a',?_,hp,hvdet⟩
  dsimp only [a']
  rw [Preadditive.sub_comp,lambda_power_first_quotient_zero X d hd (t-p) t E,sub_zero]

private theorem positive_h_source_adjusted_full_permanence
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-s+r)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r,t-s+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r-1,t-s+r),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r-1,t-s+r) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              (middleLabelRegrade (X := .shift 1 T.X)
                (show (r-1+1,t-s+r+1)=(r,t-s+r+1) by congr 1; omega)
                (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
                  (r-1) (t-s+r) zH)) (by simpa using u) ∧
            ∃ c : Ambient background T.X (r,t-s+r), c ∈ permanentCycles background T.X (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u-c))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ∀ e : Ambient background T.X (s+d,t+d),
      (background.classical.map T.f).pageMap 2 (s+d,t+d) e ∈ P →
      ∃ r : Ambient background T.X (s+d,t+d), r ∈ permanentCycles background T.X (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d)
          ((background.classical.map T.f).pageMap 2 (s+d,t+d) e-(background.classical.map T.f).pageMap 2 (s+d,t+d) r))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    ∃ a' : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a' ≫ background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) := by
  have herror : FiltrationAtLeast background.syntheticTower (s+1)
      (a ≫ XModLambdaN.incl _ (d+1)-c) := by
    apply finite_first_kernel_filtration T.X (d+1) (by omega) s t
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,hfirst,sub_self]
  have hhigh : FiltrationAtLeast background.syntheticTower (s+d)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)-W ≫ XModLambdaN.incl _ (d+1)) := by
    rw [hc,add_sub_cancel_left]
    have htop : FiltrationAtLeast background.syntheticTower (s+d)
        (finiteTopLabel T.Y d hd (s+d) (t+d) v) :=
      KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (d+1) (.nu T.Y))
        (s+d,t+d,(t+d)-d) (finiteTargetLabel background T.Y (d+1) (s+d) (t+d) d v)
        (finiteTopLabel T.Y d hd (s+d) (t+d) v) (finiteTopLabel_detects T.Y d hd (s+d) (t+d) v)
    exact (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff
      (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega) (s+d)
      (finiteTopLabel T.Y d hd (s+d) (t+d) v)).mpr htop
  obtain ⟨a₁,c₁,ha₁,_,himage,hfinal⟩ := positive_h_source_adjusted_correction_to_last R T hf hg hh hT
    (d+1) (by omega) (t-s) t (s+1) (s+d) (by omega) (by omega) (by omega)
    Pmid hPmid (by
      intro r hr hrs
      have hi : (t-s+r-t).toNat=(r-s).toNat := by congr 1; omega
      simpa only [hi] using hmid r hr hrs) a c W herror hhigh
  let a₂ : BiHom ((t+d)-(s+d)) ((t+d)-d) (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) a₁
  let c₂ : BiHom ((t+d)-(s+d)) ((t+d)-d)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)) :=
    homotopyRegrade (by omega) (by omega) c₁
  let W₂ : BiHom ((t+d)-(s+d)) ((t+d)-d) (background.nu.functor.obj (T.Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) W
  have hW₂ : lambdaMultiply k W₂=0 := by
    dsimp only [W₂]
    rw [KIP126.ProofTools.Internal.Leibniz.lambda_regrade,hW]
    exact regrade_zero _ _
  have herror₂ : FiltrationAtLeast background.syntheticTower (s+d)
      (a₂ ≫ XModLambdaN.incl _ (d+1)-c₂) := by
    dsimp only [a₂,c₂]
    rw [←regrade_comp,←homotopy_regrade_sub]
    exact (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff _ _ _ _).mpr hfinal
  have hc₂ : c₂ ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W₂ ≫ XModLambdaN.incl _ (d+1)+finiteTopLabel T.Y d hd (s+d) (t+d) v := by
    dsimp only [c₂,W₂]
    rw [←regrade_comp,himage,hc,regrade_add,regrade_comp,
      KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  obtain ⟨a₃,ha₃,hp,hdet⟩ := ordinary_source_adjusted_terminal R hcomp T.X T.Y T.f d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  let a' : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) a₃
  have hfirst' : a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 := by
    dsimp only [a']
    rw [←regrade_comp,ha₃]
    dsimp only [a₂]
    rw [←regrade_comp,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    exact ha₁
  refine ⟨a',hfirst',hp,?_⟩
  have ht := realization_homotopy_regrade_full R (show t-s=(t+d)-(s+d) by omega)
    (show t=(t+d)-d by omega) (a' ≫ background.nu.functor.map T.f)
  have htransport := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) ht
  have hback : homotopyRegrade (show t-s=(t+d)-(s+d) by omega)
      (show t=(t+d)-d by omega) (a' ≫ background.nu.functor.map T.f) =
      a₃ ≫ background.nu.functor.map T.f := by
    dsimp only [a']
    rw [←regrade_comp,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  rw [hback] at htransport
  have hresult : (R.sphere ((t+d)-(s+d)) ((t+d)-d)).hom ≫
      background.recovery.realization.map (a₃ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a' ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom := by
    simpa only [Category.assoc] using htransport
  exact hresult ▸ hdet

private theorem positive_g_source_adjusted_full_permanence
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-s+r)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r,t-s+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              ((background.classical.map T.h).pageMap 2 (r,t-s+r+1) zH) (by simpa using u) ∧
            ∃ c : Ambient background T.X (r,t-s+r), c ∈ permanentCycles background T.X (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u-c))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ∀ e : Ambient background T.X (s+d,t+d),
      (background.classical.map T.f).pageMap 2 (s+d,t+d) e ∈ P →
      ∃ r : Ambient background T.X (s+d,t+d), r ∈ permanentCycles background T.X (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d)
          ((background.classical.map T.f).pageMap 2 (s+d,t+d) e-(background.classical.map T.f).pageMap 2 (s+d,t+d) r))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    ∃ a' : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a' ≫ background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) := by
  have herror : FiltrationAtLeast background.syntheticTower (s+1)
      (a ≫ XModLambdaN.incl _ (d+1)-c) := by
    apply finite_first_kernel_filtration T.X (d+1) (by omega) s t
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,hfirst,sub_self]
  have hhigh : FiltrationAtLeast background.syntheticTower (s+d)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)-W ≫ XModLambdaN.incl _ (d+1)) := by
    rw [hc,add_sub_cancel_left]
    have htop : FiltrationAtLeast background.syntheticTower (s+d)
        (finiteTopLabel T.Y d hd (s+d) (t+d) v) :=
      KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (d+1) (.nu T.Y))
        (s+d,t+d,(t+d)-d) (finiteTargetLabel background T.Y (d+1) (s+d) (t+d) d v)
        (finiteTopLabel T.Y d hd (s+d) (t+d) v) (finiteTopLabel_detects T.Y d hd (s+d) (t+d) v)
    exact (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff
      (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega) (s+d)
      (finiteTopLabel T.Y d hd (s+d) (t+d) v)).mpr htop
  obtain ⟨a₁,c₁,ha₁,_,himage,hfinal⟩ := positive_g_source_adjusted_correction_to_last R T hf hg hh hT
    (d+1) (by omega) (t-s) t (s+1) (s+d) (by omega) (by omega) (by omega)
    Pmid hPmid (by
      intro r hr hrs
      have hi : (t-s+r-t).toNat=(r-s).toNat := by congr 1; omega
      simpa only [hi] using hmid r hr hrs) a c W herror hhigh
  let a₂ : BiHom ((t+d)-(s+d)) ((t+d)-d) (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) a₁
  let c₂ : BiHom ((t+d)-(s+d)) ((t+d)-d)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)) :=
    homotopyRegrade (by omega) (by omega) c₁
  let W₂ : BiHom ((t+d)-(s+d)) ((t+d)-d) (background.nu.functor.obj (T.Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) W
  have hW₂ : lambdaMultiply k W₂=0 := by
    dsimp only [W₂]
    rw [KIP126.ProofTools.Internal.Leibniz.lambda_regrade,hW]
    exact regrade_zero _ _
  have herror₂ : FiltrationAtLeast background.syntheticTower (s+d)
      (a₂ ≫ XModLambdaN.incl _ (d+1)-c₂) := by
    dsimp only [a₂,c₂]
    rw [←regrade_comp,←homotopy_regrade_sub]
    exact (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff _ _ _ _).mpr hfinal
  have hc₂ : c₂ ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W₂ ≫ XModLambdaN.incl _ (d+1)+finiteTopLabel T.Y d hd (s+d) (t+d) v := by
    dsimp only [c₂,W₂]
    rw [←regrade_comp,himage,hc,regrade_add,regrade_comp,
      KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  obtain ⟨a₃,ha₃,hp,hdet⟩ := ordinary_source_adjusted_terminal R hcomp T.X T.Y T.f d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  let a' : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) a₃
  have hfirst' : a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 := by
    dsimp only [a']
    rw [←regrade_comp,ha₃]
    dsimp only [a₂]
    rw [←regrade_comp,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    exact ha₁
  refine ⟨a',hfirst',hp,?_⟩
  have ht := realization_homotopy_regrade_full R (show t-s=(t+d)-(s+d) by omega)
    (show t=(t+d)-d by omega) (a' ≫ background.nu.functor.map T.f)
  have htransport := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) ht
  have hback : homotopyRegrade (show t-s=(t+d)-(s+d) by omega)
      (show t=(t+d)-d by omega) (a' ≫ background.nu.functor.map T.f) =
      a₃ ≫ background.nu.functor.map T.f := by
    dsimp only [a']
    rw [←regrade_comp,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  rw [hback] at htransport
  have hresult : (R.sphere ((t+d)-(s+d)) ((t+d)-d)).hom ≫
      background.recovery.realization.map (a₃ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a' ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom := by
    simpa only [Category.assoc] using htransport
  exact hresult ▸ hdet

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
