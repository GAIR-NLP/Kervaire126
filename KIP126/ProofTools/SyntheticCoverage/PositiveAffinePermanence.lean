module

public import KIP126.ProofTools.SyntheticCoverage.PositivePermanence

public import KIP126.ProofTools.SyntheticCoverage.Permanence

public import KIP126.ProofTools.MahowaldLeibniz.LastLayerNative

public import KIP126.ProofTools.MahowaldLeibniz.LastLayer

public import KIP126.ProofTools.MahowaldLeibniz.Bockstein

public import KIP126.ProofTools.GeneralizedLeibniz.LevelSource

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.PositiveFinitePermanence
import all KIP126.ProofTools.SyntheticCoverage.SelectiveHead
import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift

/-! Actual affine corrections for the positive normalized first arrow.
The source remains in native coordinates. Its complete realization is kept
fixed, and its finite image is always the selected normalized finite map. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

private theorem positive_finite_image_add
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q : ℕ) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q)) :
    positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) m w (a+b) =
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) m w a +
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) m w b := by
  simp only [positiveFiniteImage,shiftHomotopyClass,Functor.map_add,
    Preadditive.comp_add,regrade_precomp,Preadditive.add_comp]

/-- The actual positive image of an intermediate error label is permanent.
The proof uses its complete image minus the specified complete correction,
so it applies to the full original restricted domain, including torsion. -/
private theorem positive_affine_error_label_image_permanent
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q))
    (D : BiHom (t-p) ((t-j)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (z : Ambient background T.X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
      (finiteTargetLabel background T.X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+2)
      (positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) c -
        D ≫ XModLambdaN.incl _ q)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p t z ∈
      permanentCycles background T.Y (p+1,t+1) := by
  have hmap := selective_positive_image_detects T hf q j hj hjq p t
    (levelQuotientShiftIso T.X 1 q) (level_quotient_shift_incl T.X 1 q) z
    (a ≫ XModLambdaN.incl _ q-c) hz
  let b := verticalTranslate _ 1 (t-p) (t-j) a ≫ lastLayerNormalizedMap T hf-D
  let hm : t-p=(t+1)-(p+1) := by omega
  let hw : (t-j)+1=(t+1)-j := by omega
  let b' := homotopyRegrade hm hw b
  have heq : b ≫ XModLambdaN.incl _ q-
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j)
        (a ≫ XModLambdaN.incl _ q-c) =
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) c-
        D ≫ XModLambdaN.incl _ q := by
    dsimp only [b]
    rw [Preadditive.sub_comp,positiveFiniteImage_sub,positive_finite_image_full_projection]
    abel
  have hdiff : FiltrationAtLeast background.syntheticTower ((p+1)+1)
      (b' ≫ XModLambdaN.incl _ q - homotopyRegrade hm hw
        (positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j)
          (a ≫ XModLambdaN.incl _ q-c))) := by
    change FiltrationAtLeast background.syntheticTower ((p+1)+1)
      (homotopyRegrade hm hw b ≫ XModLambdaN.incl _ q-_)
    rw [←regrade_comp,←homotopy_regrade_sub,heq]
    apply (regrade_filtration_iff hm hw _ _).mpr
    convert hhigh using 1; omega
  have hfinite := detects_of_next_filtration_difference (.quotient q (.nu T.Y))
    (p+1,t+1,(t+1)-j) _ _ _ hmap hdiff
  rw [←middle_finite_label_as_weight T.Y q j (p+1) (t+1)] at hfinite
  exact KIP126.ProofTools.finite_target_from_full_lift_is_permanent T.Y q (by omega)
    (p+1) (t+1) ((t+1)-j) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p t z) b' hfinite

/-- A full torsion correction and an actual zero-image finite correction
remove the specified final-boundary and H parts. The arbitrary K0 residual
is retained literally, ready for the next recursive comparison. -/
private theorem positive_affine_correction_with_residual
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c h : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q))
    (z u r : Ambient background T.X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
      (finiteTargetLabel background T.X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hu : Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
      (finiteTargetLabel background T.X q p t j u) h)
    (hzero : positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) h=0)
    (hzu : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u-r)) :
    ∃ (k : ℕ) (D : BiHom (t-p) t (background.nu.functor.obj (T.X.obj background.auxiliary))),
      D ≫ XModLambdaN.incl _ 1=nativeFirstLabel T.X p t (z-u-r) ∧
      lambdaMultiply k D=0 ∧
      (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      (c+h) ≫ (background.quotients.tower _).rho 1 q (by omega)=
        c ≫ (background.quotients.tower _).rho 1 q (by omega) ∧
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) (c+h)=
        positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) c ∧
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map (a-lambdaMultiply j D)=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X q p t j r)
        ((a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h)) := by
  letI := R.additive
  obtain ⟨k,D,hD,hDt,hDr⟩ := final_boundary_native_torsion_lift R T.X p t (z-u-r) hzu
  have hDdet := full_first_label_lambda_projection_detects T.X q j hj hjq p t (z-u-r) D hD
  have hhfil := KIP126.ProofTools.Internal.Leibniz.detects_filtration
    (.quotient q (.nu T.X)) (p,t,t-j) _ h hu
  have hhfirst := finite_filtered_first_quotient_zero T.X q j (by omega) hj p t h hhfil
  have hDfirst := lambda_power_first_quotient_zero T.X j hj (t-p) t D
  refine ⟨k,D,hD,hDt,?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hDfirst,sub_zero]
  · rw [Preadditive.add_comp,hhfirst,add_zero]
  · rw [positive_finite_image_add,hzero,add_zero]
  · have hr := realization_lambda_multiply R (t-p) t j D
    rw [hDr] at hr
    rw [Functor.map_sub,Preadditive.comp_sub,hr,sub_zero]
  · have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient q (.nu T.X)) (p,t,t-j) hz hDdet
    have hh := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient q (.nu T.X)) (p,t,t-j) hsub hu
    rw [←finiteTargetLabel_sub,←finiteTargetLabel_sub,
      show z-(z-u-r)-u=r by abel] at hh
    have heq : (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h) =
        a ≫ XModLambdaN.incl _ q-c-lambdaMultiply j D ≫ XModLambdaN.incl _ q-h := by
      rw [Preadditive.sub_comp]
      abel
    rw [heq]
    exact hh


private theorem positive_affine_correction_step
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c h : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q))
    (z u : Ambient background T.X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
      (finiteTargetLabel background T.X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hu : Detects (background.convergence (.quotient q (.nu T.X))) (p,t,t-j)
      (finiteTargetLabel background T.X q p t j u) h)
    (hzero : positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) h=0)
    (hzu : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u)) :
    ∃ (a' : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 q (by omega)=
        c ≫ (background.quotients.tower _).rho 1 q (by omega) ∧
      positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) c'=
        positiveFiniteImage T hf q (levelQuotientShiftIso T.X 1 q) (t-p) (t-j) c ∧
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a'=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ q-c') := by
  obtain ⟨k,D,_,_,hfirst,hcfirst,himage,hreal,hnext⟩ := positive_affine_correction_with_residual
    R T hf q j hj hjq p t a c h z u 0 hz hu hzero (by simpa only [sub_zero] using hzu)
  refine ⟨a-lambdaMultiply j D,c+h,hfirst,hcfirst,himage,hreal,?_⟩
  have hzlabel : finiteTargetLabel background T.X q p t j 0=0 := by
    simpa only [sub_self] using finiteTargetLabel_sub T.X q p t j 0 0
  rw [hzlabel] at hnext
  exact detects_zero_filtration (background.convergence (.quotient q (.nu T.X))) (p,t,t-j) hnext

private theorem positive_f_native_cycle_image_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N j L : ℕ) (hL : 0<L) (hN : N=j+L) (p t : ℤ)
    (z : Ambient background T.Z (p,t+1)) (hz : z ∈ cycles background T.Z L (p,t+1)) :
    ∃ b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      Detects (background.convergence (.quotient N (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X N p t j
          (KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t z)) b ∧
      positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-p) (t-j) b=0 := by
  subst N
  exact selective_positive_f_native_cycle_image T he hf hg hh hT j L hL p t
    (levelQuotientShiftIso T.X 1 (j+L)) (level_quotient_shift_incl T.X 1 (j+L)) z hz
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t z)
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T p t z)

/-- The original restricted final-boundary plus H-cycle condition supplies
both corrections at every positive-first-arrow stage. Membership of the
actual error in the restricted domain follows from its complete image. -/
private theorem positive_f_affine_correction_step
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (p+1,t+1)))
    (hP : permanentCycles background T.Y (p+1,t+1) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p t z ∈ P →
      ∃ w : Ambient background T.Z (p,t+1), w ∈ cycles background T.Z (N-j:ℕ) (p,t+1) ∧
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t)
          (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w))
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom (t-p) ((t-j)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+2)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-p) (t-j) c-
        W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom (t-p) (t-j) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-p) (t-j) c'=
        positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-p) (t-j) c ∧
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a'=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := positive_affine_error_label_image_permanent T hf N j hj hjN p t a c W z hzd hhigh
  obtain ⟨w,hw,hzw⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_f_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) p t w hw
  exact positive_affine_correction_step R T hf N j hj hjN p t a c b z
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w) hzd hb hbz hzw


private theorem positive_f_affine_correction_step_at
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (m w : ℤ) (hm : m=t-p) (hw : w=t-j)
    (P : Submodule ℤ (Ambient background T.Y (p+1,t+1)))
    (hP : permanentCycles background T.Y (p+1,t+1) ≤ P)
    (hmid : ∀ z : Ambient background T.X (p,t), z ∈ cycles background T.X (N-j:ℕ) (p,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p t z ∈ P →
      ∃ w : Ambient background T.Z (p,t+1), w ∈ cycles background T.Z (N-j:ℕ) (p,t+1) ∧
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t)
          (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m (w+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+2)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c-
        W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N (by omega)=
        c ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c'=
        positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c ∧
      (R.sphere m w).hom ≫ background.recovery.realization.map a'=
        (R.sphere m w).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_f_affine_correction_step R T hf hg hh hT N j hj hjN p t P hP hmid
    a c W herror hhigh


/-- Iterate the actual positive correction under precisely the restricted
cycle hypothesis. The complete source, finite first label, full finite
image and specified realization are retained throughout the iteration. -/
private theorem positive_f_affine_correction_to_last
    (R : RealizationCoordinates background)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (N : ℕ) (hN : 0<N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u-w) (hv : v≤(N:ℤ)+w-m)
    (P : ∀ p : ℤ, Submodule ℤ (Ambient background T.Y (p+1,m+p+1)))
    (hP : ∀ p : ℤ, u≤p → p<v → permanentCycles background T.Y (p+1,m+p+1) ≤ P p)
    (hmid : ∀ p : ℤ, u≤p → p<v →
      ∀ z : Ambient background T.X (p,m+p),
        z ∈ cycles background T.X (N-(m+p-w).toNat:ℕ) (p,m+p) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf p (m+p) z ∈ P p →
        ∃ zH : Ambient background T.Z (p,m+p+1),
          zH ∈ cycles background T.Z (N-(m+p-w).toNat:ℕ) (p,m+p+1) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p (m+p) zH))
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (W : BiHom m (w+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (herror : FiltrationAtLeast background.syntheticTower u (a ≫ XModLambdaN.incl _ N-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (v+1)
      (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c-
        W ≫ XModLambdaN.incl _ N)) :
    ∃ (a' : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (c' : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      c' ≫ (background.quotients.tower _).rho 1 N hN=c ≫ (background.quotients.tower _).rho 1 N hN ∧
      positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c'=
        positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c ∧
      (R.sphere m w).hom ≫ background.recovery.realization.map a'=
        (R.sphere m w).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower v (a' ≫ XModLambdaN.incl _ N-c') := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u a c with
  | h n ih =>
    by_cases heq : v≤u
    · have huv' : u=v := le_antisymm huv heq
      exact ⟨a,c,rfl,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u-w).toNat
      have hj : (j:ℤ)=m+u-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hjN : j<N := by omega
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+2)
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c-
            W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w+1) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hreal,hnext⟩ := positive_f_affine_correction_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower (v+1)
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c₁-
            W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hreal₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hreal₂.trans hreal,hfinal⟩


/-- The last positive affine comparison in native source coordinates.
Its finite error is an actual top class, and the complete torsion correction
vanishes under the same realization. Zero candidate labels are retained. -/
private theorem positive_affine_native_last_filtration_permanence
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (a : BiHom (t-s) (t-d) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (D : BiHom (t-s) ((t-d)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (hD : lambdaMultiply N D=0)
    (v : Ambient background T.Y (s+1,t+1)) (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : permanentCycles background T.Y (s+1,t+1) ≤ P) (hv : v∈P)
    (hterminal : (positiveFirstOperationLinear T hf s t).range ⊓ P ≤ finalBoundaries T.Y (s+1,t+1))
    (hfil : FiltrationAtLeast background.syntheticTower s (a ≫ XModLambdaN.incl _ (d+1)-c))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show (t-d)+1=(t+1)-d by omega)
        (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) (t-d) c) =
      homotopyRegrade (by omega) (by omega) (D ≫ XModLambdaN.incl _ (d+1))+
        finiteTopLabel T.Y d hd (s+1) (t+1) v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) v
        ((R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫ background.recovery.realization.map
          (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
            (show (t-d)+1=(t+1)-d by omega)
            (verticalTranslate _ 1 (t-s) (t-d) a ≫ lastLayerNormalizedMap T hf)) ≫
          (hcomp.nu T.Y).target.hom) := by
  letI := R.additive
  let B := background.nu.functor.obj (T.Y.obj background.auxiliary)
  let hm : t-s=(t+1)-(s+1) := by omega
  let hw : (t-d)+1=(t+1)-d := by omega
  let F : BiHom ((t+1)-(s+1)) ((t+1)-d) B := homotopyRegrade hm hw
    (verticalTranslate _ 1 (t-s) (t-d) a ≫ lastLayerNormalizedMap T hf)
  let D' : BiHom ((t+1)-(s+1)) ((t+1)-d) B := homotopyRegrade hm hw D
  obtain ⟨e,he⟩ := finiteTopLabel_exists T.X d hd s t (a ≫ XModLambdaN.incl _ (d+1)-c) hfil
  have himage : homotopyRegrade hm hw
      (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) (t-d)
        (a ≫ XModLambdaN.incl _ (d+1)-c)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [he]
    exact selective_positive_top_image T hf d hd s t
      (levelQuotientShiftIso T.X 1 (d+1)) (level_quotient_shift_incl T.X 1 (d+1)) e
  rw [positiveFiniteImage_sub,positive_finite_image_full_projection,homotopy_regrade_sub,hc] at himage
  have hcorrected : (F-D') ≫ XModLambdaN.incl B (d+1) =
      finiteTopLabel T.Y d hd (s+1) (t+1) v +
        finiteTopLabel T.Y d hd (s+1) (t+1)
          (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    have h' : F ≫ XModLambdaN.incl B (d+1)-
        (D' ≫ XModLambdaN.incl B (d+1)+finiteTopLabel T.Y d hd (s+1) (t+1) v) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
      simpa only [F,D',regrade_comp] using himage
    rw [Preadditive.sub_comp]
    apply sub_eq_iff_eq_add.mpr
    exact (sub_eq_iff_eq_add.mp h').trans (by abel)
  have hzero : ((F-D') ≫ 𝟙 B) ≫ XModLambdaN.incl B d=0 := by
    rw [Category.comp_id]
    have h := congrArg (fun z => z ≫ (background.quotients.tower B).rho d (d+1) (by omega)) hcorrected
    dsimp only [B] at h
    simpa only [Category.assoc,(background.quotients.tower _).rho_quotient,
      Preadditive.add_comp,finite_top_restriction_zero,zero_add] using h
  obtain ⟨b,hb,w,hwlabel,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp B T.Y
    (𝟙 B) d (s+1) (t+1) (F-D') hzero
  rw [Category.comp_id] at hb hdet
  have ht := lambda_power_first_label_projection_eq_top T.Y d hd (s+1) (t+1) b w hwlabel
  rw [hb] at ht
  have hwt := ht.symm.trans hcorrected
  have herr : w-v-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈
      boundaries background T.Y (d+1) (s+1,t+1) := by
    apply (finite_top_difference_zero_iff_boundary T.Y d hd (s+1) (t+1) w v _).mp
    rw [hwt]
    abel
  have hDt : lambdaMultiply N D'=0 := by
    dsimp only [D']
    rw [lambda_regrade,hD,regrade_zero]
  have hDzero := lambda_torsion_realization_zero R ((t+1)-(s+1)) ((t+1)-d) N D' hDt
  have hreal : (R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫
      background.recovery.realization.map (F-D') ≫ (hcomp.nu T.Y).target.hom =
      (R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫
        background.recovery.realization.map F ≫ (hcomp.nu T.Y).target.hom := by
    dsimp only [B] at F D' hDzero ⊢
    rw [Functor.map_sub,Preadditive.sub_comp,Preadditive.comp_sub]
    have hzero' := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) hDzero
    simp only [Category.assoc,zero_comp] at hzero'
    rw [hzero',sub_zero]
  have hdet' := hreal ▸ hdet
  exact classical_detects_of_terminal_image T.X T.Y (s,t) (s+1,t+1)
    (positiveFirstOperationLinear T hf s t) P hP hterminal w v hwp hv e (d+1) herr _ hdet'


private theorem positive_full_image_realization
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (m w : ℤ) (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary))) :
    (R.sphere m (w+1)).hom ≫ background.recovery.realization.map
      (verticalTranslate _ 1 m w a ≫ lastLayerNormalizedMap T hf) ≫ (hcomp.nu T.Y).target.hom =
      (R.sphere m w).hom ≫ background.recovery.realization.map a ≫ (hcomp.nu T.X).target.hom ≫ T.f := by
  have hn : background.recovery.realization.map (lastLayerNormalizedMap T hf) ≫ (hcomp.nu T.Y).target.hom =
      (hcomp.shiftedNu T.X 1).target.hom ≫ T.f := normalized_positive_realization_square R hcomp T hf
  rw [Functor.map_comp,Category.assoc,hn]
  have h := congrArg (fun z => z ≫ T.f) (positive_source_realization_eq R hcomp T.X 1 m w a)
  simp only [Category.assoc] at h
  convert h using 1; rfl

private theorem positive_realized_image_regrade
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (m w m' w' : ℤ) (hm : m=m') (hw : w+1=w')
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary))) :
    (R.sphere m' w').hom ≫ background.recovery.realization.map
      (homotopyRegrade hm hw (verticalTranslate _ 1 m w a ≫ lastLayerNormalizedMap T hf)) ≫
        (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) hm.symm) ≫
        (R.sphere m w).hom ≫ background.recovery.realization.map a ≫ (hcomp.nu T.X).target.hom ≫ T.f := by
  have h := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom)
    (realization_homotopy_regrade_full R hm hw (verticalTranslate _ 1 m w a ≫ lastLayerNormalizedMap T hf))
  simp only [Category.assoc] at h
  exact h.trans (congrArg (fun z => eqToHom (congrArg (Sphere (C:=Spectrum)) hm.symm) ≫ z)
    (positive_full_image_realization R hcomp T hf m w a))

/-- The complete positive-first-arrow affine comparison. Every correction
uses the original restricted cycle domain and preserves the same full
realization; the final candidate detects its specified classical image. -/
private theorem positive_f_affine_full_source_permanence
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r+1,t-s+r+1)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r+1,t-s+r+1) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d+1,t+d+1)) (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v∈P)
    (hterminal : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,t+d+1))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d+1)-(s+d+1)=t-s by omega) (show (t+d+1)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+d+1)-(s+d+1)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a ≫
            (hcomp.nu T.X).target.hom ≫ T.f) := by
  have herror : FiltrationAtLeast background.syntheticTower (s+1)
      (a ≫ XModLambdaN.incl _ (d+1)-c) := by
    apply finite_first_kernel_filtration T.X (d+1) (by omega) s t
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,hfirst,sub_self]
  have hhigh : FiltrationAtLeast background.syntheticTower (s+d+1)
      (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c-
        W ≫ XModLambdaN.incl _ (d+1)) := by
    rw [hc,add_sub_cancel_left]
    have htop := KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (d+1) (.nu T.Y))
      (s+d+1,t+d+1,(t+d+1)-d) (finiteTargetLabel background T.Y (d+1) (s+d+1) (t+d+1) d v)
      (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v) (finiteTopLabel_detects T.Y d hd (s+d+1) (t+d+1) v)
    exact (regrade_filtration_iff _ _ _ _).mpr htop
  obtain ⟨a₁,c₁,_,_,himage,hreal,hfinal⟩ := positive_f_affine_correction_to_last R T hf hg hh hT
    (d+1) (by omega) (t-s) t (s+1) (s+d) (by omega) (by omega) (by omega)
    Pmid hPmid (by
      intro r hr hrs
      have hi : (t-s+r-t).toNat=(r-s).toNat := by congr 1; omega
      simpa only [hi] using hmid r hr hrs) a c W herror hhigh
  let hm : t-s=(t+d)-(s+d) := by omega
  let hw : t=(t+d)-d := by omega
  let a₂ := homotopyRegrade hm hw a₁
  let c₂ := homotopyRegrade hm hw c₁
  let W₂ := homotopyRegrade hm (show t+1=((t+d)-d)+1 by omega) W
  have hW₂ : lambdaMultiply k W₂=0 := by
    dsimp only [W₂]
    rw [lambda_regrade,hW,regrade_zero]
  have herror₂ : FiltrationAtLeast background.syntheticTower (s+d)
      (a₂ ≫ XModLambdaN.incl _ (d+1)-c₂) := by
    dsimp only [a₂,c₂]
    rw [←regrade_comp,←homotopy_regrade_sub]
    exact (regrade_filtration_iff _ _ _ _).mpr hfinal
  have hc₂ : homotopyRegrade (show (t+d)-(s+d)=(t+d+1)-(s+d+1) by omega)
      (show ((t+d)-d)+1=(t+d+1)-d by omega)
      (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1))
        ((t+d)-(s+d)) ((t+d)-d) c₂) =
      homotopyRegrade (by omega) (by omega) (W₂ ≫ XModLambdaN.incl _ (d+1))+
        finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v := by
    dsimp only [c₂,W₂]
    rw [←positiveFiniteImage_regrade,himage,hc,regrade_add,regrade_add,
      ←regrade_comp,normalized_homotopy_regrade_trans,
      normalized_homotopy_regrade_trans,normalized_homotopy_regrade_trans]
    rfl
  obtain ⟨hp,hdet⟩ := positive_affine_native_last_filtration_permanence R hcomp T hf d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  refine ⟨hp,?_⟩
  have hr := positive_realized_image_regrade R hcomp T hf
    ((t+d)-(s+d)) ((t+d)-d) ((t+d+1)-(s+d+1)) ((t+d+1)-d) (by omega) (by omega) a₂
  have hr₂ := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom ≫ T.f)
    (realization_homotopy_regrade_full R hm hw a₁)
  have hr₃ := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom ≫ T.f) hreal
  simp only [Category.assoc] at hr₂ hr₃
  have hfinalreal : (R.sphere ((t+d+1)-(s+d+1)) ((t+d+1)-d)).hom ≫
      background.recovery.realization.map (homotopyRegrade
        (show (t+d)-(s+d)=(t+d+1)-(s+d+1) by omega)
        (show ((t+d)-d)+1=(t+d+1)-d by omega)
        (verticalTranslate _ 1 ((t+d)-(s+d)) ((t+d)-d) a₂ ≫ lastLayerNormalizedMap T hf)) ≫
        (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) (show (t+d+1)-(s+d+1)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a ≫
          (hcomp.nu T.X).target.hom ≫ T.f := by
    rw [hr]
    change _ ≫ ((R.sphere _ _).hom ≫ background.recovery.realization.map (homotopyRegrade hm hw a₁) ≫ _) = _
    rw [hr₂,hr₃]
    simp only [←Category.assoc,eqToHom_trans]
  exact hfinalreal ▸ hdet

/-- Affine permanence in the positive-first-arrow normalization.
Permanence requires only permanence of x, and each specified strict
classical detector is carried to its own f-image. The complete prescribed
torsion term and the original restricted middle domains are retained. -/
public theorem torsion_affine_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r+1,t-s+r+1)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r+1,t-s+r+1) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d+1,t+d+1)) (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v∈P)
    (hterminal : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,t+d+1))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d+1)-(s+d+1)=t-s by omega) (show (t+d+1)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨hp,_⟩ := positive_f_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  refine ⟨hp,?_⟩
  intro ξ hxs hdet
  obtain ⟨a₀,ha₀,hreal₀⟩ := prescribed_native_source hcomp T.X s t x ξ hxs hdet
  obtain ⟨a₁,ha₁,hreal₁⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨_,hvdet⟩ := positive_f_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₁ ≫
      (hcomp.nu T.X).target.hom=ξ := by
    have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₁
    simp only [Category.assoc] at h
    exact h.trans hreal₀
  have hresult := congrArg (fun z => eqToHom (congrArg (Sphere (C:=Spectrum))
    (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ z ≫ T.f) hsource
  simp only [Category.assoc] at hresult
  exact hresult ▸ hvdet

/-- The original classical differential gives a common finite source in
native coordinates, with the same first class and prescribed positive image. -/
private theorem finite_common_native_lift_positive_f_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d : ℕ) (hd : 0<d) (s t p u : ℤ) (hp : p=s+d+1) (hu : u=(t+1)+d)
    (z : Ambient background T.Z (s,t+1)) (x : Ambient background T.X (s,t))
    (v : Ambient background T.Y (p,u))
    (hH : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (d+1) (s,t+1) (p,u) z ((background.classical.map T.g).pageMap 2 (p,u) v)) :
    ∃ c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)),
      c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x ∧
      positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c=
        homotopyRegrade (show u-p=t-s by omega) (show u-d=t+1 by omega)
          (finiteTopLabel T.Y d hd p u v) := by
  subst p
  subst u
  obtain ⟨c,hc,hi⟩ := finite_common_lift_positive_f T he hT hf hg hh d hd s t z x v hH hdiff
  let E := verticalTranslate (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1))
    1 (t-s) t
  let c₀ := E.symm (c ≫ (levelQuotientShiftIso T.X 1 (d+1)).hom)
  have hc₀ : verticalTranslate _ 1 (t-s) t c₀=c ≫ (levelQuotientShiftIso T.X 1 (d+1)).hom :=
    E.apply_symm_apply _
  refine ⟨c₀,?_,?_⟩
  · apply (verticalTranslate _ 1 (t-s) t).injective
    rw [←vertical_translate_comp,hc₀]
    have h := quotient_shift_restriction_on_spheres T.X (0,1) 1 (d+1) (by decide) (by omega)
      (levelQuotientShiftIso T.X 1 1) (levelQuotientShiftIso T.X 1 (d+1))
      (level_quotient_shift_incl T.X 1 1) (level_quotient_shift_incl T.X 1 (d+1))
      (t-s) (t+1) c
    rw [Category.assoc,←h,←Category.assoc,hc]
    have hl := congrArg (fun q => q ≫ (levelQuotientShiftIso T.X 1 1).hom)
      (positive_first_label_shift T.X s t x)
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hl.symm
  · have heq : positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c₀=
        (verticalTranslate _ 1 (t-s) t c₀ ≫ (levelQuotientShiftIso T.X 1 (d+1)).inv) ≫
          XModLambdaN.map (normalizedFirstMap T hf) (d+1) := by
      simp [positiveFiniteImage,verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,
        susp_invariance,shiftHomotopyClass,Iso.homCongr,regrade_comp,Category.assoc,
        lastLayerNormalizedMap,normalizedFirstMap]
    rw [heq,hc₀]
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hi

/-- Selective permanence in positive-first-arrow normalization,
constructing the finite representative from H and the higher differential. -/
public theorem selective_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d : ℕ) (hd : 0<d) (s t : ℤ) (_hs : 0≤s)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r+1,t-s+r+1)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r+1,t-s+r+1) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH))
    (x : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (z : Ambient background T.Z (s,t+1))
    (v : Ambient background T.Y (s+d+1,t+d+1))
    (hH : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (d+1) (s,t+1) (s+d+1,t+d+1) z
        ((background.classical.map T.g).pageMap 2 (s+d+1,t+d+1) v))
    (_hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x=0)
    (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v∈P)
    (hterminal : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,t+d+1)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_native_lift_positive_f_at T (by simp [hf,hg,hh])
    hT hf hg hh d hd s t (s+d+1) (t+d+1) rfl (by omega) z x v hH hdiff
  have hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x-x) := by
    change x-x ∈ finalBoundaries T.X (s,t)
    rw [sub_self]
    exact Submodule.zero_mem _
  exact torsion_affine_permanence_positive_f T hf hg hh d hd s t
    Pmid hPmid hmid x x hx hxx c 0 1 (by decide)
    (by simp only [lambdaMultiply,comp_zero]) v P hP hv hterminal hfirst
    (by simpa only [zero_comp,zero_add] using himage)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
