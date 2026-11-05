module

public import KIP126.ProofTools.SyntheticCoverage.PositiveAffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.RecursivePermanence
import all KIP126.ProofTools.SyntheticCoverage.TorsionResidualCommon
import all KIP126.ProofTools.SyntheticCoverage.NonStrictSource

/-! Four-layer residual comparison for a normalized first map of exponent one.
All finite representatives stay on the chosen quotients. Residual first labels
are only required to have the indicated finite lifts, not to be permanent. -/

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

private def torsionResidualPositiveTopLabel
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s+2+1,t+2+1)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4) :=
  homotopyRegrade (show (t+2+1)-(s+2+1)=t-s by omega)
    (show (t+2+1)-(3:ℕ)=t by omega)
    (finiteTopLabel X 3 (by decide) (s+2+1) (t+2+1) x)

private def torsionResidualPositiveImage
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (a : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 4) :=
  homotopyRegrade rfl (show (t-1)+1=t by omega)
    (positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) a)

private theorem torsion_residual_positive_top_add
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x y : Ambient background X (s+2+1,t+2+1)) :
    torsionResidualPositiveTopLabel X s t (x+y)=
      torsionResidualPositiveTopLabel X s t x+torsionResidualPositiveTopLabel X s t y := by
  simp only [torsionResidualPositiveTopLabel,finite_top_label_add,regrade_add]

private theorem torsion_residual_positive_image_sub
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (a b : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4)) :
    torsionResidualPositiveImage T hf s t (a-b)=
      torsionResidualPositiveImage T hf s t a-torsionResidualPositiveImage T hf s t b := by
  simp only [torsionResidualPositiveImage,positiveFiniteImage_sub,homotopy_regrade_sub]

private theorem torsion_residual_positive_image_insert
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (c : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3)) :
    torsionResidualPositiveImage T hf s t
      (finiteCoefficientInsert _ 1 3 (by decide) (t-s) t c) =
      homotopyRegrade rfl (show (t+1)-1=t by omega)
        (finiteCoefficientInsert _ 1 3 (by decide) (t-s) (t+1)
          (positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) t c)) := by
  have h := positive_finite_image_coefficient_shift_level T hf 4 1 (by decide) (t-s) t c
  have h' := congrArg (homotopyRegrade (rfl : t-s=t-s) (show (t-1)+1=t by omega)) h
  simpa only [torsionResidualPositiveImage,finiteCoefficientInsert,normalized_homotopy_regrade_trans, Nat.reduceAdd, Nat.reduceSub, Int.natCast_one, eq_mpr_eq_cast, cast_eq] using h'


/-- The complete restricted first intermediate space decomposes into true
boundaries, finite connecting images and the specified finite residual space. -/
public def TorsionResidualPositiveFMiddle
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ y : Ambient background T.X (s,t), y∈cycles background T.X 3 (s,t) →
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t y∈P₁ →
    ∃ (z : Ambient background T.Z (s,t+1)) (k : Ambient background T.X (s,t)),
      z∈cycles background T.Z 3 (s,t+1) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t)
        (y-KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z-k)

/-- Every residual label has a three-layer representative with
boundary-congruent first label, prescribed image, and full-image
correction annihilated by lambda. -/
public def TorsionResidualPositiveFFamily
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (V : Submodule ℤ (Ambient background T.Y (s+2+1,t+2+1))) : Prop :=
  ∀ k∈K₀, ∃ (k' : Ambient background T.X (s,t))
    (z : Ambient background T.Y (s+2+1,t+2+1))
    (c : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary))),
    z∈V ∧ IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (k'-k) ∧
    c≫(background.quotients.tower _).rho 1 3 (by decide)=nativeFirstLabel T.X s t k' ∧
    lambdaMultiply 1 W=0 ∧
    positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) t c=
      W≫XModLambdaN.incl _ 3+homotopyRegrade
        (show (t+2+1)-(s+2+1)=t-s by omega) (show (t+2+1)-(2:ℕ)=t+1 by omega)
        (finiteTopLabel T.Y 2 (by decide) (s+2+1) (t+2+1) z)


private theorem torsion_residual_positive_image_of_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (e : Ambient background T.X (s+2,t+2)) :
    torsionResidualPositiveImage T hf s t (torsionResidualTopLabel T.X s t e)=
      torsionResidualPositiveTopLabel T.Y s t
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+2) (t+2) e) := by
  have h := selective_positive_top_image T hf 3 (by decide) (s+2) (t+2)
    (levelQuotientShiftIso T.X 1 4) (level_quotient_shift_incl T.X 1 4) e
  have h' := congrArg (homotopyRegrade
    (show ((t+2)+1)-((s+2)+1)=t-s by omega)
    (show ((t+2)+1)-(3:ℕ)=t by omega)) h
  simp only [torsionResidualPositiveImage,torsionResidualTopLabel,
    ←positiveFiniteImage_regrade,normalized_homotopy_regrade_trans]
  simp only [normalized_homotopy_regrade_trans] at h'
  exact h'

private theorem torsion_residual_positive_insert_middle_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (z : Ambient background T.Y (s+2+1,t+2+1))
    (c : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : lambdaMultiply 1 W=0)
    (hc : positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) t c=
      W≫XModLambdaN.incl _ 3+homotopyRegrade
        (show (t+2+1)-(s+2+1)=t-s by omega) (show (t+2+1)-(2:ℕ)=t+1 by omega)
        (finiteTopLabel T.Y 2 (by decide) (s+2+1) (t+2+1) z)) :
    torsionResidualPositiveImage T hf s t
      (finiteCoefficientInsert _ 1 3 (by decide) (t-s) t c)=
      torsionResidualPositiveTopLabel T.Y s t z := by
  rw [torsion_residual_positive_image_insert,hc,torsion_residual_insert_add,
    torsion_residual_insert_torsion_zero _ _ _ W hW,zero_add]
  rw [finite_coefficient_insert_regrade,normalized_homotopy_regrade_trans]
  have h := torsion_residual_insert_three_layer_top T.Y (s+2+1) (t+2+1) z
  have h' := congrArg (homotopyRegrade
    (show (t+2+1)-(s+2+1)=t-s by omega)
    (show (t+2+1)-(3:ℕ)=t by omega)) h
  simp only [normalized_homotopy_regrade_trans] at h'
  exact h'

private theorem torsion_residual_positive_image_from_residual
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (a c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4))
    (k : Ambient background T.X (s,t))
    (v z : Ambient background T.Y (s+2+1,t+2+1))
    (W₀ : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hres : Detects (background.convergence (.quotient 4 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 4 s t 1 k) (a-c))
    (hc : torsionResidualPositiveImage T hf s t c=
      W₀≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v)
    (d : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (hd : d≫(background.quotients.tower _).rho 1 3 (by decide)=nativeFirstLabel T.X s t k)
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : lambdaMultiply 1 W=0)
    (hdimage : positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) t d=
      W≫XModLambdaN.incl _ 3+homotopyRegrade
        (show (t+2+1)-(s+2+1)=t-s by omega) (show (t+2+1)-(2:ℕ)=t+1 by omega)
        (finiteTopLabel T.Y 2 (by decide) (s+2+1) (t+2+1) z))
    (hzero : Subsingleton (Ambient background T.X (s+1,t+1))) :
    ∃ e : Ambient background T.X (s+2,t+2),
      torsionResidualPositiveImage T hf s t a=
        W₀≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t
          (v+z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+2) (t+2) e) := by
  let b := finiteCoefficientInsert _ 1 3 (by decide) (t-s) t d
  have hdd := first_label_detects_unshifted T.X 3 (by decide) s t k d hd
  have hbd := finite_coefficient_insert_detects T.X 1 3 (by decide) s t k d hdd
  have hdiff := detects_sub_filtration (background.convergence (.quotient 4 (.nu T.X)))
    (s,t,t-1) hres hbd
  obtain ⟨e,he⟩ := torsion_residual_top_label_exists T.X s t (a-c-b) hdiff hzero
  have hb := torsion_residual_positive_insert_middle_top T hf s t z d W hW hdimage
  have h := congrArg (torsionResidualPositiveImage T hf s t) he
  rw [torsion_residual_positive_image_sub,torsion_residual_positive_image_sub,
    torsion_residual_positive_image_of_top,hc,hb] at h
  refine ⟨e,?_⟩
  rw [torsion_residual_positive_top_add,torsion_residual_positive_top_add]
  calc
    _ = (torsionResidualPositiveImage T hf s t a-
      (W₀≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v)-
      torsionResidualPositiveTopLabel T.Y s t z)+
      (W₀≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v)+
      torsionResidualPositiveTopLabel T.Y s t z := by abel
    _ = _ := by rw [h]; abel


private theorem torsion_residual_positive_full_image_of_top
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1) (s t : ℤ)
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (hW : lambdaMultiply N W=0)
    (v : Ambient background T.Y (s+2+1,t+2+1))
    (hi : torsionResidualPositiveImage T hf s t (a≫XModLambdaN.incl _ 4)=
      W≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v) :
    ∃ w : Ambient background T.Y (s+2+1,t+2+1),
      w∈permanentCycles background T.Y (s+2+1,t+2+1) ∧
      w-v∈boundaries background T.Y 4 (s+2+1,t+2+1) ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) w
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a ≫
            (hcomp.nu T.X).target.hom ≫ T.f) := by
  letI := R.additive
  let B := background.nu.functor.obj (T.Y.obj background.auxiliary)
  let hm : t-s=(t+2+1)-(s+2+1) := by omega
  let hw : (t-1)+1=(t+2+1)-(3:ℕ) := by omega
  let F := homotopyRegrade hm hw
    (verticalTranslate _ 1 (t-s) (t-1) a ≫ lastLayerNormalizedMap T hf)
  let W' := homotopyRegrade hm (show t=(t+2+1)-(3:ℕ) by omega) W
  have hi' : (F-W')≫XModLambdaN.incl _ 4=
      finiteTopLabel T.Y 3 (by decide) (s+2+1) (t+2+1) v := by
    have h := congrArg (homotopyRegrade hm (show t=(t+2+1)-(3:ℕ) by omega)) hi
    simp only [torsionResidualPositiveImage,positive_finite_image_full_projection,
      torsionResidualPositiveTopLabel,regrade_add,normalized_homotopy_regrade_trans] at h
    dsimp only [F,W']
    rw [Preadditive.sub_comp,←regrade_comp,←regrade_comp,h,add_sub_cancel_left]
    rfl
  have hz : ((F-W')≫𝟙 B)≫XModLambdaN.incl B 3=0 := by
    rw [Category.comp_id]
    have h := congrArg (fun z => z≫(background.quotients.tower B).rho 3 4 (by decide)) hi'
    dsimp only [B] at h
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero] at h
    exact h
  obtain ⟨b,hb,w,hwlabel,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp
    B T.Y (𝟙 B) 3 (s+2+1) (t+2+1) (F-W') hz
  rw [Category.comp_id] at hb hdet
  have ht := lambda_power_first_label_projection_eq_top T.Y 3 (by decide)
    (s+2+1) (t+2+1) b w hwlabel
  rw [hb,hi'] at ht
  have hbound : w-v∈boundaries background T.Y 4 (s+2+1,t+2+1) := by
    apply (finiteTopLabel_zero_iff_boundary T.Y 3 (by decide) (s+2+1) (t+2+1) _).mp
    rw [finite_top_label_sub,ht,sub_self]
  refine ⟨w,hwp,hbound,?_⟩
  have hW' : lambdaMultiply N W'=0 := by
    dsimp only [W']
    rw [lambda_regrade,hW,regrade_zero]
  have hWr := lambda_torsion_realization_zero R ((t+2+1)-(s+2+1)) ((t+2+1)-(3:ℕ)) N W' hW'
  have hreal : (R.sphere ((t+2+1)-(s+2+1)) ((t+2+1)-(3:ℕ))).hom ≫
      background.recovery.realization.map (F-W') ≫ (hcomp.nu T.Y).target.hom =
      (R.sphere ((t+2+1)-(s+2+1)) ((t+2+1)-(3:ℕ))).hom ≫
      background.recovery.realization.map F ≫ (hcomp.nu T.Y).target.hom := by
    have h := congrArg (fun z => z≫(hcomp.nu T.Y).target.hom) hWr
    simp only [Category.assoc,zero_comp] at h
    rw [Functor.map_sub,Preadditive.sub_comp,Preadditive.comp_sub]
    rw [h,sub_zero]
  rw [hreal] at hdet
  have hr := positive_realized_image_regrade R hcomp T hf (t-s) (t-1)
    ((t+2+1)-(s+2+1)) ((t+2+1)-(3:ℕ)) hm hw a
  exact hr ▸ hdet

private theorem torsion_residual_positive_classical_terminal
    (X Y : AdamsObject (coefficients := background.coefficients)) (p q : Bidegree)
    (F : Ambient background X p →ₗ[ℤ] Ambient background Y q)
    (P : Submodule ℤ (Ambient background Y q)) (hP : permanentCycles background Y q ≤ P)
    (w v z : Ambient background Y q) (e : Ambient background X p)
    (hw : w∈permanentCycles background Y q) (hv : v∈P)
    (herr : w-(v+z+F e)∈boundaries background Y 4 q)
    (hterminal : z+F e∈P → z+F e∈finalBoundaries Y q)
    (a : HomotopyGroup (q.2-q.1) (Y.obj background.auxiliary))
    (hdet : ClassicalDetects (background.classicalConvergence Y) q w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) q v ∧
      ClassicalDetects (background.classicalConvergence Y) q v a := by
  have hb := boundaries_le_finalBoundaries Y q 4 herr
  have hbP := hP (finalBoundaries_le_permanentCycles Y q hb)
  have hsumP : z+F e∈P := by
    have h := P.sub_mem (P.sub_mem (hP hw) hv) hbP
    convert h using 1
    abel
  have hsum := hterminal hsumP
  have hfinal : w-v∈finalBoundaries Y q := by
    have h := (finalBoundaries Y q).add_mem hb hsum
    convert h using 1
    abel
  exact classical_detects_of_final_boundary_difference Y q w v a hdet hfinal


private theorem torsion_residual_positive_f_full_source
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP₁ : permanentCycles background T.Y (s+1,t+1) ≤ P₁)
    (V P : Submodule ℤ (Ambient background T.Y (s+2+1,t+2+1)))
    (hP : permanentCycles background T.Y (s+2+1,t+2+1) ≤ P)
    (hmid : TorsionResidualPositiveFMiddle T hf s t P₁ K₀)
    (hfamily : TorsionResidualPositiveFFamily T hf s t K₀ V)
    (hzero : Subsingleton (Ambient background T.X (s+1,t+1)))
    (hterminal : (V ⊔ (positiveFirstOperationLinear T hf (s+2) (t+2)).range) ⊓ P ≤
      finalBoundaries T.Y (s+2+1,t+2+1))
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (hW : lambdaMultiply N W=0)
    (v : Ambient background T.Y (s+2+1,t+2+1)) (hv : v∈P)
    (hsame : a≫XModLambdaN.incl _ 1=c≫(background.quotients.tower _).rho 1 4 (by decide))
    (hc : torsionResidualPositiveImage T hf s t c=
      W≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+2+1,t+2+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a ≫
            (hcomp.nu T.X).target.hom ≫ T.f) := by
  obtain ⟨y,hy,hyd⟩ := torsion_residual_initial_middle_label T.X s t a c hsame
  let Wraw := homotopyRegrade (rfl : t-s=t-s) (show t=(t-1)+1 by omega) W
  have hhigh : FiltrationAtLeast background.syntheticTower (s+2)
      (positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) c-
        Wraw≫XModLambdaN.incl _ 4) := by
    apply (regrade_filtration_iff (rfl : t-s=t-s) (show (t-1)+1=t by omega) _ _).mp
    rw [homotopy_regrade_sub]
    change FiltrationAtLeast background.syntheticTower (s+2)
      (torsionResidualPositiveImage T hf s t c-homotopyRegrade rfl _ (Wraw≫XModLambdaN.incl _ 4))
    dsimp only [Wraw]
    rw [←regrade_comp,normalized_homotopy_regrade_trans]
    change FiltrationAtLeast background.syntheticTower (s+2)
      (torsionResidualPositiveImage T hf s t c-W≫XModLambdaN.incl _ 4)
    rw [hc,add_sub_cancel_left]
    have htop : FiltrationAtLeast background.syntheticTower (s+2+1)
        (torsionResidualPositiveTopLabel T.Y s t v) := by
      apply (regrade_filtration_iff _ _ _ _).mpr
      exact KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 4 (.nu T.Y))
        (s+2+1,t+2+1,(t+2+1)-3) _ _
        (finiteTopLabel_detects T.Y 3 (by decide) (s+2+1) (t+2+1) v)
    exact background.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) (by omega) htop
  have hFy := positive_affine_error_label_image_permanent T hf 4 1 (by decide) (by decide)
    s t a c Wraw y hyd hhigh
  obtain ⟨z₀,k,hz₀,hk,hboundary⟩ := hmid y hy (hP₁ hFy)
  obtain ⟨h,hhdet,hhzero⟩ := positive_f_native_cycle_image_at T _ hf hg hh hT
    4 1 3 (by decide) (by decide) s t z₀ hz₀
  obtain ⟨l,D,_,_,_,_,hcimage,hreal,hres⟩ := positive_affine_correction_with_residual
    R T hf 4 1 (by decide) (by decide) s t a c h y
      (KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z₀) k hyd hhdet hhzero hboundary
  obtain ⟨k',z,d,Wk,hz,hkk,hdfirst,hWk,hdimage⟩ := hfamily k hk
  have hzdet := KIP126.ProofTools.Internal.Mahowald.detects_sub
    (.quotient 4 (.nu T.X)) (s,t,t-1) hres hres
  rw [←finiteTargetLabel_sub,sub_self,sub_self] at hzdet
  have hzimage : positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) 0=0 := by
    simpa only [sub_self] using positiveFiniteImage_sub T hf 4
      (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) c c
  have hreverse : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t)
      (k-0-k') := by
    have hmem : k'-k ∈ finalBoundaries T.X (s,t) := hkk
    have hneg := (finalBoundaries T.X (s,t)).neg_mem hmem
    change k-0-k' ∈ finalBoundaries T.X (s,t)
    convert hneg using 1
    abel
  obtain ⟨l',D',_,_,_,_,_,hreal',hres'⟩ := positive_affine_correction_with_residual
    R T hf 4 1 (by decide) (by decide) s t (a-lambdaMultiply 1 D) (c+h) 0 k 0 k'
      hres hzdet hzimage hreverse
  simp only [add_zero] at hres'
  have hc' : torsionResidualPositiveImage T hf s t (c+h)=
      W≫XModLambdaN.incl _ 4+torsionResidualPositiveTopLabel T.Y s t v := by
    have hcimage' : positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) (c+h)=
        positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) c := by
      convert hcimage using 1 <;> rfl
    unfold torsionResidualPositiveImage
    rw [hcimage']
    exact hc
  obtain ⟨e,hi⟩ := torsion_residual_positive_image_from_residual T hf s t
    ((a-lambdaMultiply 1 D-lambdaMultiply 1 D')≫XModLambdaN.incl _ 4) (c+h)
    k' v z W hres' hc' d hdfirst Wk hWk hdimage hzero
  obtain ⟨w,hwp,hbound,hdet⟩ := torsion_residual_positive_full_image_of_top R hcomp T hf s t
    (a-lambdaMultiply 1 D-lambdaMultiply 1 D') W N hW _ hi
  have hclass := congrArg (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
    (show (t+2+1)-(s+2+1)=t-s by omega))≫q≫(hcomp.nu T.X).target.hom≫T.f)
    (hreal'.trans hreal)
  simp only [Category.assoc] at hclass
  have hclass' :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+2+1)-(s+2+1)=t-s by omega))≫
        (R.sphere (t-s) (t-1)).hom≫
          background.recovery.realization.map (a-lambdaMultiply 1 D-lambdaMultiply 1 D')≫
            (hcomp.nu T.X).target.hom≫T.f)=
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+2+1)-(s+2+1)=t-s by omega))≫
        (R.sphere (t-s) (t-1)).hom≫background.recovery.realization.map a≫
          (hcomp.nu T.X).target.hom≫T.f) := by
    convert hclass using 1 <;> rfl
  rw [hclass'] at hdet
  apply torsion_residual_positive_classical_terminal T.X T.Y (s+2,t+2) (s+2+1,t+2+1)
    (positiveFirstOperationLinear T hf (s+2) (t+2)) P hP w v z e hwp hv hbound _ _ hdet
  intro hsum
  apply hterminal
  refine ⟨?_,hsum⟩
  exact Submodule.add_mem_sup hz ⟨e,rfl⟩


/-- Four-layer finite residual comparison when the normalized first arrow
has exponent one. The source bidegree is `(s-1,t-1)`. Every prescribed
classical source is retained, including zero infinity classes, and an
extension representative exists. The residual labels need not be permanent. -/
public theorem torsion_residual_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 3 (s,t))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP₁ : permanentCycles background T.Y (s+1,t+1) ≤ P₁)
    (V P : Submodule ℤ (Ambient background T.Y (s+2+1,t+2+1)))
    (hP : permanentCycles background T.Y (s+2+1,t+2+1) ≤ P)
    (hmid : TorsionResidualPositiveFMiddle T hf s t P₁ K₀)
    (hfamily : TorsionResidualPositiveFFamily T hf s t K₀ V)
    (hzero : Subsingleton (Ambient background T.X (s+1,t+1)))
    (hterminal : (V ⊔ (positiveFirstOperationLinear T hf (s+2) (t+2)).range) ⊓ P ≤
      finalBoundaries T.Y (s+2+1,t+2+1))
    (x x' : Ambient background T.X (s-1,t-1))
    (hx : x∈permanentCycles background T.X (s-1,t-1))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s-1,t-1) (x'-x))
    (c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (_hN : 0<N) (hW : lambdaMultiply N W=0)
    (v : Ambient background T.Y (s+2+1,t+2+1)) (hv : v∈P)
    (hfirst : c≫(background.quotients.tower _).rho 1 4 (by decide)=
      homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl
        (nativeFirstLabel T.X (s-1) (t-1) x'))
    (hc : homotopyRegrade rfl (show (t-1)+1=t by omega)
      (positiveFiniteImage T hf 4 (levelQuotientShiftIso T.X 1 4) (t-s) (t-1) c)=
      W≫XModLambdaN.incl _ 4+homotopyRegrade
        (show (t+2+1)-(s+2+1)=t-s by omega) (show (t+2+1)-(3:ℕ)=t by omega)
        (finiteTopLabel T.Y 3 (by decide) (s+2+1) (t+2+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+2+1,t+2+1) v ∧
      (∀ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫ξ≫T.f)) ∧
      ∃ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫ξ≫T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hsource (a : BiHom ((t-1)-(s-1)) (t-1)
      (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (ha : a≫XModLambdaN.incl _ 1=nativeFirstLabel T.X (s-1) (t-1) x) :
      IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+2+1,t+2+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫
          (R.sphere ((t-1)-(s-1)) (t-1)).hom≫background.recovery.realization.map a≫
            (hcomp.nu T.X).target.hom≫T.f) := by
    obtain ⟨a₁,ha₁,hr₁⟩ := full_source_with_boundary_changed_first_label
      R T.X (s-1) (t-1) x x' a ha hxx
    let a₂ := homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl a₁
    have hsame : a₂≫XModLambdaN.incl _ 1=c≫(background.quotients.tower _).rho 1 4 (by decide) := by
      dsimp only [a₂]
      rw [←regrade_comp,ha₁,hfirst]
    obtain ⟨hp,hdet⟩ := torsion_residual_positive_f_full_source R hcomp T hf hg hh hT
      s t K₀ P₁ hP₁ V P hP hmid hfamily hzero hterminal a₂ c W N hW v hv hsame hc
    refine ⟨hp,?_⟩
    have ht := congrArg (fun z => z≫(hcomp.nu T.X).target.hom≫T.f)
      (realization_homotopy_regrade_full R (show (t-1)-(s-1)=t-s by omega) rfl a₁)
    have hr := congrArg (fun z => z≫(hcomp.nu T.X).target.hom≫T.f) hr₁
    simp only [Category.assoc] at ht hr
    have heq :
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=t-s by omega))≫
          (R.sphere (t-s) (t-1)).hom≫background.recovery.realization.map a₂≫
            (hcomp.nu T.X).target.hom≫T.f)=
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫
          (R.sphere ((t-1)-(s-1)) (t-1)).hom≫background.recovery.realization.map a≫
            (hcomp.nu T.X).target.hom≫T.f) := by
      dsimp only [a₂]
      rw [ht]
      rw [hr]
      simp only [←Category.assoc,eqToHom_trans]
    exact heq ▸ hdet
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X (s-1) (t-1) x hx
  have hall : ∀ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
      ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ →
      ClassicalDetects (background.classicalConvergence T.Y) (s+2+1,t+2+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫ξ≫T.f) := by
    intro ξ hξ
    obtain ⟨a,ha,hr⟩ := prescribed_native_source_nonstrict hcomp T.X (s-1) (t-1) x ξ hξ
    have hd := (hsource a ha).2
    have hreplace := congrArg (fun z => eqToHom (congrArg (Sphere (C:=Spectrum))
      (show (t+2+1)-(s+2+1)=(t-1)-(s-1) by omega))≫z≫T.f) hr
    simp only [Category.assoc] at hreplace
    exact hreplace ▸ hd
  refine ⟨(hsource a₀ ha₀).1,hall,?_⟩
  have hd := full_source_detects_first_label R hcomp T.X (s-1) (t-1) x a₀ ha₀
  exact ⟨_,hd,hall _ hd⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
