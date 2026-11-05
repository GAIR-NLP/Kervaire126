module

import all KIP126.ProofTools.SyntheticCoverage.PositiveAffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence

/-! Positive first-arrow comparison with permanent higher-source corrections. -/

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

private theorem positive_source_adjusted_step
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
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w-r))
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
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := positive_affine_error_label_image_permanent T hf N j hj hjN p t a c W z hzd hhigh
  obtain ⟨w,hw,r,hr,hzwr⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_f_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) p t w hw
  obtain ⟨k,D,_,_,hfirst,hcfirst,himage,_,hres⟩ := positive_affine_correction_with_residual
    R T hf N j hj hjN p t a c b z
    (KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w) r hzd hb hbz hzwr
  obtain ⟨V,hV⟩ := permanent_native_source T.X p t r hr
  have hVdet := full_first_label_lambda_projection_detects T.X N j hj hjN p t r V hV
  have hnext := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (p,t,t-j) hres hVdet
  refine ⟨a-lambdaMultiply j D-lambdaMultiply j V,c+b,?_,hcfirst,himage,?_⟩
  · rw [Preadditive.sub_comp,lambda_power_first_quotient_zero T.X j hj (t-p) t V,sub_zero,hfirst]
  · have heq : (a-lambdaMultiply j D-lambdaMultiply j V) ≫ XModLambdaN.incl _ N-(c+b) =
        (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ N-(c+b)-lambdaMultiply j V ≫ XModLambdaN.incl _ N := by
      rw [Preadditive.sub_comp]
      abel
    rw [heq]
    exact hnext

private theorem positive_source_adjusted_step_at
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
        ∃ r : Ambient background T.X (p,t), r ∈ permanentCycles background T.X (p,t) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p t w-r))
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
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_source_adjusted_step R T hf hg hh hT N j hj hjN p t P hP hmid a c W herror hhigh

private theorem positive_source_adjusted_to_last
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
          ∃ r : Ambient background T.X (p,m+p), r ∈ permanentCycles background T.X (p,m+p) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p)
              (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T p (m+p) zH-r))
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
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+2)
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c-
            W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w+1) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hnext⟩ := positive_source_adjusted_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower (v+1)
          (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w c₁-
            W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hfinal⟩


private theorem positive_source_adjusted_terminal_comparison
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (a : BiHom (t-s) (t-d) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (D : BiHom (t-s) ((t-d)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (hD : lambdaMultiply N D=0)
    (v : Ambient background T.Y (s+1,t+1))
    (e : Ambient background T.X (s,t))
    (he : a ≫ XModLambdaN.incl _ (d+1)-c = finiteTopLabel T.X d hd s t e)
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show (t-d)+1=(t+1)-d by omega)
        (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) (t-d) c) =
      homotopyRegrade (by omega) (by omega) (D ≫ XModLambdaN.incl _ (d+1))+
        finiteTopLabel T.Y d hd (s+1) (t+1) v) :
    ∃ w : Ambient background T.Y (s+1,t+1),
      w ∈ permanentCycles background T.Y (s+1,t+1) ∧
      w-v-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈
        boundaries background T.Y (d+1) (s+1,t+1) ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) w
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
  exact ⟨w,hwp,herr,hdet'⟩




private theorem positive_source_adjusted_terminal
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
    (hterminal : ∀ e : Ambient background T.X (s,t),
      positiveFirstOperationLinear T hf s t e ∈ P →
      ∃ r : Ambient background T.X (s,t), r ∈ permanentCycles background T.X (s,t) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1)
          (positiveFirstOperationLinear T hf s t e-positiveFirstOperationLinear T hf s t r))
    (hfil : FiltrationAtLeast background.syntheticTower s (a ≫ XModLambdaN.incl _ (d+1)-c))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show (t-d)+1=(t+1)-d by omega)
        (positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) (t-d) c) =
      homotopyRegrade (by omega) (by omega) (D ≫ XModLambdaN.incl _ (d+1))+
        finiteTopLabel T.Y d hd (s+1) (t+1) v) :
    ∃ a' : BiHom (t-s) (t-d) (background.nu.functor.obj (T.X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) v
        ((R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫ background.recovery.realization.map
          (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
            (show (t-d)+1=(t+1)-d by omega)
            (verticalTranslate _ 1 (t-s) (t-d) a' ≫ lastLayerNormalizedMap T hf)) ≫
          (hcomp.nu T.Y).target.hom) := by
  obtain ⟨e,he⟩ := finiteTopLabel_exists T.X d hd s t (a ≫ XModLambdaN.incl _ (d+1)-c) hfil
  obtain ⟨w,hwp,herr,_⟩ := positive_source_adjusted_terminal_comparison R hcomp T hf d hd s t
    a c D N hD v e he hc
  have herrFinal := boundaries_le_finalBoundaries T.Y (s+1,t+1) (d+1) herr
  have herrP := hP (finalBoundaries_le_permanentCycles T.Y (s+1,t+1) herrFinal)
  have heP : positiveFirstOperationLinear T hf s t e ∈ P := by
    have h := P.sub_mem (P.sub_mem (hP hwp) hv) herrP
    change KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈ P
    simpa only [sub_sub_cancel] using h
  obtain ⟨r,hr,her⟩ := hterminal e heP
  obtain ⟨V,hV⟩ := permanent_native_source T.X s t r hr
  have hVtop := lambda_power_first_label_projection_eq_top T.X d hd s t V r hV
  let a' := a-lambdaMultiply d V
  have he' : a' ≫ XModLambdaN.incl _ (d+1)-c = finiteTopLabel T.X d hd s t (e-r) := by
    dsimp only [a']
    rw [Preadditive.sub_comp,finite_top_label_sub,←he,←hVtop]
    abel
  obtain ⟨w',_,herr',hdet'⟩ := positive_source_adjusted_terminal_comparison R hcomp T hf d hd s t
    a' c D N hD v (e-r) he' hc
  have hdiff : IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary))
      (s+1,t+1) (w'-v) := by
    have h := (finalBoundaries T.Y (s+1,t+1)).add_mem
      (boundaries_le_finalBoundaries T.Y (s+1,t+1) (d+1) herr') her
    change w'-v ∈ finalBoundaries T.Y (s+1,t+1)
    convert h using 1
    change w'-v = w'-v-positiveFirstOperationLinear T hf s t (e-r)+
      (positiveFirstOperationLinear T hf s t e-positiveFirstOperationLinear T hf s t r)
    rw [map_sub]
    abel
  obtain ⟨hp,hdet⟩ := classical_detects_of_final_boundary_difference T.Y (s+1,t+1) w' v _ hdet' hdiff
  refine ⟨a',?_,hp,hdet⟩
  dsimp only [a']
  rw [Preadditive.sub_comp,lambda_power_first_quotient_zero T.X d hd (t-s) t V,sub_zero]


private theorem positive_f_source_adjusted_full_permanence
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
          ∃ u : Ambient background T.X (r,t-s+r), u ∈ permanentCycles background T.X (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
              (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH-u))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d+1,t+d+1)) (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v∈P)
    (hterminal : ∀ e : Ambient background T.X (s+d,t+d),
      positiveFirstOperationLinear T hf (s+d) (t+d) e ∈ P →
      ∃ u : Ambient background T.X (s+d,t+d), u ∈ permanentCycles background T.X (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1)
          (positiveFirstOperationLinear T hf (s+d) (t+d) e-positiveFirstOperationLinear T hf (s+d) (t+d) u))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d+1)-(s+d+1)=t-s by omega) (show (t+d+1)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v)) :
    ∃ a' : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+d+1)-(s+d+1)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a' ≫
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
  obtain ⟨a₁,c₁,ha₁,_,himage,hfinal⟩ := positive_source_adjusted_to_last R T hf hg hh hT
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
  obtain ⟨a₃,ha₃,hp,hdet⟩ := positive_source_adjusted_terminal R hcomp T hf d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  let a₄ := homotopyRegrade hm.symm hw.symm a₃
  have hfirst₄ : a₄ ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 := by
    have h := congrArg (homotopyRegrade hm.symm hw.symm) ha₃
    have h' : a₄ ≫ XModLambdaN.incl _ 1=a₁ ≫ XModLambdaN.incl _ 1 := by
      simpa only [a₄,a₂,regrade_comp,normalized_homotopy_regrade_trans,positive_regrade_self] using h
    exact h'.trans ha₁
  refine ⟨a₄,hfirst₄,hp,?_⟩
  have hr := positive_realized_image_regrade R hcomp T hf
    ((t+d)-(s+d)) ((t+d)-d) ((t+d+1)-(s+d+1)) ((t+d+1)-d) (by omega) (by omega) a₃
  have hr₂ := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom ≫ T.f)
    (realization_homotopy_regrade_full R hm.symm hw.symm a₃)
  simp only [Category.assoc] at hr₂
  have hfinalreal : (R.sphere ((t+d+1)-(s+d+1)) ((t+d+1)-d)).hom ≫
      background.recovery.realization.map (homotopyRegrade
        (show (t+d)-(s+d)=(t+d+1)-(s+d+1) by omega)
        (show ((t+d)-d)+1=(t+d+1)-d by omega)
        (verticalTranslate _ 1 ((t+d)-(s+d)) ((t+d)-d) a₃ ≫ lastLayerNormalizedMap T hf)) ≫
        (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) (show (t+d+1)-(s+d+1)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₄ ≫
          (hcomp.nu T.X).target.hom ≫ T.f := by
    rw [hr]
    change _ = _ ≫ ((R.sphere _ _).hom ≫ background.recovery.realization.map (homotopyRegrade hm.symm hw.symm a₃) ≫ _)
    rw [hr₂]
    simp only [←Category.assoc,eqToHom_trans]
  exact hfinalreal ▸ hdet


end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
