module

public import KIP126.ProofTools.SyntheticCoverage.PositivePermanence

public import KIP126.ProofTools.SyntheticCoverage.Permanence

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.MahowaldLeibniz.LastLayerNative

public import KIP126.ProofTools.MahowaldLeibniz.LastLayer

public import KIP126.ProofTools.MahowaldLeibniz.Bockstein

public import KIP126.ProofTools.GeneralizedLeibniz.LevelSource

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.PositivePermanence
import all KIP126.ProofTools.SyntheticCoverage.SelectiveHead
import all KIP126.ProofTools.SyntheticCoverage.EarlyPositiveNaturality
import all KIP126.ProofTools.SyntheticCoverage.PositiveAffinePermanence

/-! Three-layer permanence controlled by the whole two-layer relation.
The relation is applied to the actual residual label. Every common finite
representative and every subsequent error remains on the selected quotient.
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

/-- At the final Q3 grade detection determines the entire actual element,
including when the detecting label is zero or a boundary. -/
private theorem recursive_top_detects_unique
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-2)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (ha : Detects (background.convergence (.quotient 3 (.nu X))) (s,t,t-2)
      (finiteTargetLabel background X 3 s t 2 x) a) :
    a=finiteTopLabel X 2 (by decide) s t x := by
  have hd := detects_sub_filtration (background.convergence (.quotient 3 (.nu X)))
    (s,t,t-2) ha (finiteTopLabel_detects X 2 (by decide) s t x)
  exact sub_eq_zero.mp (finite_high_filtration_zero X 3 (by decide)
    (t-s) (t-2) (s+1) (by omega) _ hd)

/-- Inserting the Q2 top into Q3 gives the selected Q3 top,
by coefficient detection and vanishing of the next filtration. -/
private theorem recursive_insert_two_layer_top
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t)) :
    homotopyRegrade rfl (show (t-1)-1=t-2 by omega)
      (finiteCoefficientInsert _ 1 2 (by decide) (t-s) (t-1)
        (finiteTopLabel X 1 (by decide) s t x)) =
      finiteTopLabel X 2 (by decide) s t x := by
  apply recursive_top_detects_unique
  have h := finite_coefficient_shift_layer_detects X 3 1 1 (by decide) (by decide)
    s t x (finiteTopLabel X 1 (by decide) s t x)
    (finiteTopLabel_detects X 1 (by decide) s t x)
  convert h using 1 <;> rfl

/-- A middle label and surjectivity of the full relation give
a relation member and a common Q₂ representative. -/
private theorem recursive_common_lift_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (hsurj : ∀ k ∈ K₀, ∃ (U : Ambient background T.Z (s,t))
      (z : Ambient background T.Y (s+1+1,t+1)),
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z))
    (k : Ambient background T.X (s+1,t)) (hk : k∈K₀) :
    ∃ (U : Ambient background T.Z (s,t)) (z : Ambient background T.Y (s+1+1,t+1)),
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z) ∧
      ∃ c : BiHom (t-(s+1)) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
        c ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.X (s+1) t k ∧
        c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2=
          homotopyRegrade (show (t+1)-(s+1+1)=t-(s+1) by omega)
            (show (t+1)-(1:ℕ)=t by omega)
            (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1) z) := by
  obtain ⟨U,z,hU,hd⟩ := hsurj k hk
  obtain ⟨c,hc,hi⟩ := two_layer_common_lift_positive_h T he hT hf hg hh
    s t U k z hU hd
  exact ⟨U,z,hU,hd,c,hc,hi⟩

public def recursiveTopLabel (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3) :=
  homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-(2:ℕ)=t-1 by omega)
    (finiteTopLabel X 2 (by decide) (s+1) (t+1) x)

private def recursiveMiddleTopLabel (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2) :=
  homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-(1:ℕ)=t by omega)
    (finiteTopLabel X 1 (by decide) (s+1) (t+1) x)

private theorem recursive_top_label_add (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x y : Ambient background X (s+1,t+1)) :
    recursiveTopLabel X s t (x+y)=recursiveTopLabel X s t x+recursiveTopLabel X s t y := by
  simp only [recursiveTopLabel,finite_top_label_add,regrade_add]

private theorem recursive_top_label_natural (X Y : (AdamsObject (coefficients := background.coefficients)))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    recursiveTopLabel X s t x ≫ XModLambdaN.map (background.nu.functor.map f) 3=
      recursiveTopLabel Y s t ((background.classical.map f).pageMap 2 (s+1,t+1) x) := by
  simp only [recursiveTopLabel,←regrade_comp,finite_top_label_ordinary_natural]

private theorem recursive_top_label_exists (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (a : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a) :
    ∃ x : Ambient background X (s+1,t+1), a=recursiveTopLabel X s t x := by
  let a' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t-1=(t+1)-(2:ℕ) by omega) a
  have ha' : FiltrationAtLeast background.syntheticTower (s+1) a' :=
    (regrade_filtration_iff _ _ _ _).mpr ha
  obtain ⟨x,hx⟩ := finiteTopLabel_exists X 2 (by decide) (s+1) (t+1) a' ha'
  refine ⟨x,?_⟩
  have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-(2:ℕ)=t-1 by omega)) hx
  simpa only [a',recursiveTopLabel,homotopy_regrade_inverse] using h

private theorem recursive_insert_middle_top (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    finiteCoefficientInsert _ 1 2 (by decide) (t-s) t
      (recursiveMiddleTopLabel X s t x)=recursiveTopLabel X s t x := by
  dsimp only [recursiveMiddleTopLabel,recursiveTopLabel]
  rw [finite_coefficient_insert_regrade]
  have h := recursive_insert_two_layer_top X (s+1) (t+1) x
  have h' := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-(2:ℕ)=t-1 by omega)) h
  simp only [normalized_homotopy_regrade_trans] at h'
  convert h' using 1 <;> rfl

/-- Insert the common Q2 representative belonging to the actual residual k.
Its difference from the actual Q3 error is a single final-layer element,
so the resulting image is exactly v+z+F2(e), on this same Q3. -/
private theorem recursive_ordinary_image_from_residual
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ)
    (a c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (k : Ambient background X (s,t)) (v z : Ambient background Y (s+1,t+1))
    (hres : Detects (background.convergence (.quotient 3 (.nu X))) (s,t,t-1)
      (finiteTargetLabel background X 3 s t 1 k) (a-c))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 3=recursiveTopLabel Y s t v)
    (ck : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (hk : ck ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel X s t k)
    (hck : ck ≫ XModLambdaN.map (background.nu.functor.map f) 2=recursiveMiddleTopLabel Y s t z) :
    ∃ e : Ambient background X (s+1,t+1),
      a ≫ XModLambdaN.map (background.nu.functor.map f) 3=
        recursiveTopLabel Y s t
          (v+z+(background.classical.map f).pageMap 2 (s+1,t+1) e) := by
  let b := finiteCoefficientInsert _ 1 2 (by decide) (t-s) t ck
  have hkd := first_label_detects_unshifted X 2 (by decide) s t k ck hk
  have hbd := finite_coefficient_insert_detects X 1 2 (by decide) s t k ck hkd
  have hdiff := detects_sub_filtration (background.convergence (.quotient 3 (.nu X)))
    (s,t,t-1) hres hbd
  obtain ⟨e,he⟩ := recursive_top_label_exists X s t (a-c-b) hdiff
  have hb : b ≫ XModLambdaN.map (background.nu.functor.map f) 3=recursiveTopLabel Y s t z := by
    dsimp only [b]
    rw [finite_coefficient_insert_natural,hck,recursive_insert_middle_top]
  have h := congrArg (fun u => u ≫ XModLambdaN.map (background.nu.functor.map f) 3) he
  rw [Preadditive.sub_comp,Preadditive.sub_comp,recursive_top_label_natural,hc,hb] at h
  refine ⟨e,?_⟩
  rw [recursive_top_label_add,recursive_top_label_add]
  calc
    _ = (a ≫ XModLambdaN.map (background.nu.functor.map f) 3-
      recursiveTopLabel Y s t v-recursiveTopLabel Y s t z)+
        recursiveTopLabel Y s t v+recursiveTopLabel Y s t z := by abel
    _ = _ := by rw [h]; abel

/-- An actual complete image with a specified Q3 top has a permanent
label differing from that top only by the true B3 subgroup. -/
private theorem recursive_full_image_of_top
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticSpectrum) (Y : (AdamsObject (coefficients := background.coefficients)))
    (g : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) A) (v : Ambient background Y (s+1,t+1))
    (himage : (a≫g) ≫ XModLambdaN.incl _ 3=recursiveTopLabel Y s t v) :
    ∃ w : Ambient background Y (s+1,t+1),
      w ∈ permanentCycles background Y (s+1,t+1) ∧
      w-v ∈ boundaries background Y 3 (s+1,t+1) ∧
      ClassicalDetects (background.classicalConvergence Y) (s+1,t+1) w
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+1)-(s+1)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) ≫
            (hcomp.nu Y).target.hom) := by
  let a' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t-1=(t+1)-(2:ℕ) by omega) a
  have hi : (a'≫g) ≫ XModLambdaN.incl _ 3=finiteTopLabel Y 2 (by decide) (s+1) (t+1) v := by
    dsimp only [a']
    rw [←regrade_comp,←regrade_comp,himage]
    simp only [recursiveTopLabel,homotopy_regrade_inverse]
  have hz : (a'≫g) ≫ XModLambdaN.incl _ 2=0 := by
    have h := congrArg (fun u => u ≫ (background.quotients.tower
      (background.nu.functor.obj (Y.obj background.auxiliary))).rho 2 3 (by decide)) hi
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero] at h
    exact h
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects
    R hcomp A Y g 2 (s+1) (t+1) a' hz
  have hwtop := lambda_power_first_label_projection_eq_top Y 2 (by decide)
    (s+1) (t+1) b w hw
  rw [hb,hi] at hwtop
  have hbound : w-v ∈ boundaries background Y 3 (s+1,t+1) := by
    apply (finiteTopLabel_zero_iff_boundary Y 2 (by decide) (s+1) (t+1) _).mp
    rw [finite_top_label_sub,hwtop,sub_self]
  refine ⟨w,hwp,hbound,?_⟩
  have hr := realization_homotopy_regrade_full R
    (show t-s=(t+1)-(s+1) by omega) (show t-1=(t+1)-(2:ℕ) by omega) (a≫g)
  have hr' := congrArg (fun u => u ≫ (hcomp.nu Y).target.hom) hr
  have heq : (R.sphere ((t+1)-(s+1)) ((t+1)-(2:ℕ))).hom ≫
      background.recovery.realization.map (a'≫g) ≫ (hcomp.nu Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1)=t-s by omega)) ≫
        (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) ≫
          (hcomp.nu Y).target.hom := by
    simpa only [a',regrade_comp,Category.assoc] using hr'
  exact heq ▸ hdet

/-- The terminal condition is applied once to the sum of the actual
relation target z and the entire F2 error, including all possible choices. -/
private theorem recursive_classical_terminal
    (X Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree)
    (F : Ambient background X p →ₗ[ℤ] Ambient background Y p)
    (P : Submodule ℤ (Ambient background Y p))
    (hP : permanentCycles background Y p ≤ P)
    (w v z : Ambient background Y p) (e : Ambient background X p)
    (hw : w∈permanentCycles background Y p) (hv : v∈P)
    (herr : w-(v+z+F e) ∈ boundaries background Y 3 p)
    (hterminal : z+F e ∈ P → z+F e ∈ finalBoundaries Y p)
    (a : HomotopyGroup (p.2-p.1) (Y.obj background.auxiliary))
    (hdet : ClassicalDetects (background.classicalConvergence Y) p w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) p v ∧
      ClassicalDetects (background.classicalConvergence Y) p v a := by
  have hboundary := boundaries_le_finalBoundaries Y p 3 herr
  have hboundaryP := hP (finalBoundaries_le_permanentCycles Y p hboundary)
  have hsumP : z+F e∈P := by
    have h := P.sub_mem (P.sub_mem (hP hw) hv) hboundaryP
    convert h using 1
    abel
  have hsum := hterminal hsumP
  have hfinal : w-v ∈ finalBoundaries Y p := by
    have h := (finalBoundaries Y p).add_mem hboundary hsum
    convert h using 1
    abel
  exact classical_detects_of_final_boundary_difference Y p w v a hdet hfinal

private theorem recursive_initial_middle_label
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (hsame : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 3 (by decide)) :
    ∃ y : Ambient background X (s,t), y∈cycles background X 2 (s,t) ∧
      Detects (background.convergence (.quotient 3 (.nu X))) (s,t,t-1)
        (finiteTargetLabel background X 3 s t 1 y) (a ≫ XModLambdaN.incl _ 3-c) := by
  let d := a ≫ XModLambdaN.incl _ 3-c
  have hd : d ≫ (background.quotients.tower _).rho 1 3 (by decide)=0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,hsame,sub_self]
  let d' := homotopyRegrade (show t-s=(t-1)-(s-1) by omega) rfl d
  have hd' : d' ≫ (background.quotients.tower _).rho 1 3 (by decide)=0 := by
    dsimp only [d']
    rw [←regrade_comp,hd,regrade_zero]
  have hfil := finite_first_kernel_filtration X 3 (by decide) (s-1) (t-1) d' hd'
  rw [sub_add_cancel] at hfil
  have hfil' : FiltrationAtLeast background.syntheticTower s d :=
    (regrade_filtration_iff _ _ _ _).mp hfil
  exact middle_finite_filtration_label X 3 1 (by decide) s t d hfil'

private theorem recursive_top_label_filtration (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    FiltrationAtLeast background.syntheticTower (s+1) (recursiveTopLabel X s t x) := by
  apply (regrade_filtration_iff _ _ _ _).mpr
  exact KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu X))
    (s+1,t+1,(t+1)-2) _ _ (finiteTopLabel_detects X 2 (by decide) (s+1) (t+1) x)

public def RecursivePositiveHMiddle
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ y : Ambient background T.X (s+1,t), y∈cycles background T.X 2 (s+1,t) →
    (background.classical.map T.f).pageMap 2 (s+1,t) y∈P₁ →
    ∃ (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+1,t))
      (k : Ambient background T.X (s+1,t)),
      z∈cycles background T.Z 2 (s,t) ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
        (by simpa only [add_sub_cancel_right] using u) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) (y-u-k)

public def RecursivePositiveHSurjective
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ k∈K₀, ∃ (U : Ambient background T.Z (s,t)) (z : Ambient background T.Y (s+1+1,t+1)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
      (by simpa only [add_sub_cancel_right] using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z)

/-- Elementwise form of (pr_z R + image F2) ∩ P ≤ B∞ for the entire
actual relation R. Both U and z range over all relation members. -/
public def RecursivePositiveHTerminal
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1))) : Prop :=
  ∀ k∈K₀, ∀ (U : Ambient background T.Z (s,t)) (z : Ambient background T.Y (s+1+1,t+1)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
      (by simpa only [add_sub_cancel_right] using k) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z) →
    ∀ e : Ambient background T.X (s+1+1,t+1),
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈P →
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈finalBoundaries T.Y (s+1+1,t+1)

/-- Complete three-layer comparison for every full source in the positive-H
branch. The whole relation acts on the actual K0 residual, and torsion
correction preserves the realization of this same complete source. -/
private theorem recursive_positive_h_full_source
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP₁ : permanentCycles background T.Y (s+1,t) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P)
    (hmid : RecursivePositiveHMiddle T hh s t P₁ K₀)
    (hsurj : RecursivePositiveHSurjective T hh s t K₀)
    (hterminal : RecursivePositiveHTerminal T hh s t K₀ P)
    (a : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1)) (hv : v∈P)
    (hsame : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 3 (by decide))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
          (R.sphere (t-(s+1)) (t-1)).hom ≫
            background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
              (hcomp.nu T.Y).target.hom) := by
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X (s+1) t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3-
        (0 : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary))) ≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero,hc]
    exact recursive_top_label_filtration T.Y (s+1) t v
  have hFy := ordinary_affine_error_label_image_permanent T.X T.Y T.f 3 1 (by decide)
    (s+1) t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hboundary⟩ := hmid y hy (hP₁ hFy)
  obtain ⟨h,hhdet,hhzero⟩ := middle_positive_h_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t z₀ hz₀ u hu
  obtain ⟨l,D,_,_,_,_,hcimage,hreal,hres⟩ := ordinary_affine_correction_with_residual
    R T.X T.Y T.f 3 1 (by decide) (by decide) (s+1) t a c h y u k
      hyd hhdet hhzero hboundary
  obtain ⟨U,z,hU,hd,ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_h
    T he hT hf hg hh s t K₀ hsurj k hk
  obtain ⟨e,hi⟩ := recursive_ordinary_image_from_residual T.X T.Y T.f (s+1) t
    ((a-lambdaMultiply 1 D) ≫ XModLambdaN.incl _ 3) (c+h) k v z hres
    (hcimage.trans hc) ck hckfirst hckimage
  have hi' : ((a-lambdaMultiply 1 D)≫background.nu.functor.map T.f) ≫ XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y (s+1) t
        (v+z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e) := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  obtain ⟨w,hwp,hbound,hdet⟩ := recursive_full_image_of_top R hcomp
    (background.nu.functor.obj (T.X.obj background.auxiliary)) T.Y (background.nu.functor.map T.f)
    (s+1) t (a-lambdaMultiply 1 D) _ hi'
  have hclass :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map ((a-lambdaMultiply 1 D)≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) =
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) := by
    have h := congrArg
      (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫ q ≫
        background.recovery.realization.map (background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom) hreal
    simp only [Category.assoc] at h
    simp only [Functor.map_comp,Category.assoc]
    convert h using 1 <;> rfl
  rw [hclass] at hdet
  exact recursive_classical_terminal T.X T.Y (s+1+1,t+1)
    ((background.classical.map T.f).pageMap 2 (s+1+1,t+1)).hom P hP w v z e hwp hv
    hbound (hterminal k hk U z hU hd e) _ hdet

/-- Positive-H three-layer permanence. A permanent x gives a full source
before quantifying over strictly detected sources. Source bidegree
`(s,t−1)` places the target two steps higher. -/
public theorem recursive_positive_h_permanence
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 2 (s+1,t) ⊓
      LinearMap.ker ((background.classical.map T.f).pageMap 2 (s+1,t)).hom)
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP₁ : permanentCycles background T.Y (s+1,t) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P)
    (hmid : RecursivePositiveHMiddle T hh s t P₁ K₀)
    (hsurj : RecursivePositiveHSurjective T hh s t K₀)
    (hterminal : RecursivePositiveHTerminal T hh s t K₀ P)
    (x : Ambient background T.X (s,t-1)) (hx : x∈permanentCycles background T.X (s,t-1))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1)) (hv : v∈P)
    (hfirst : c ≫ (background.quotients.tower _).rho 1 3 (by decide)=
      homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl (nativeFirstLabel T.X s (t-1) x))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ∀ ξ : HomotopyGroup ((t-1)-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t-1) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+1)-(s+1+1)=(t-1)-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  have hsource (a : BiHom ((t-1)-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (ha : a ≫ XModLambdaN.incl _ 1=nativeFirstLabel T.X s (t-1) x) := by
    let a' := homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl a
    have hsame : a' ≫ XModLambdaN.incl _ 1=
        c ≫ (background.quotients.tower _).rho 1 3 (by decide) := by
      dsimp only [a']
      rw [←regrade_comp,ha,hfirst]
    exact recursive_positive_h_full_source R hcomp T he hT hf hg hh s t K₀ P₁ hP₁ P hP
      hmid hsurj hterminal a' c v hv hsame hc
  obtain ⟨a,ha⟩ := permanent_native_source T.X s (t-1) x hx
  refine ⟨(hsource a ha).1,?_⟩
  intro ξ hxstrict hξ
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp T.X s (t-1) x ξ hxstrict hξ
  have hdet := (hsource b hb).2
  have hreal' : (R.sphere ((t-1)-s) (t-1)).hom ≫
      background.recovery.realization.map (b≫background.nu.functor.map T.f) ≫
        (hcomp.nu T.Y).target.hom=ξ≫T.f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality T.f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target T.X]
    simpa only [Category.assoc] using congrArg (fun z => z≫T.f) hreal
  have ht := congrArg (fun z => z≫(hcomp.nu T.Y).target.hom)
    (realization_homotopy_regrade_full R
      (show (t-1)-s=t-(s+1) by omega) rfl (b≫background.nu.functor.map T.f))
  simp only [Category.assoc] at ht
  rw [hreal'] at ht
  have hactual :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map
            (homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl b≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom)=
      eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=(t-1)-s by omega)) ≫ ξ ≫ T.f := by
    rw [←regrade_comp,ht]
    simp only [←Category.assoc,eqToHom_trans]
  exact hactual ▸ hdet


private theorem recursive_common_lift_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (hsurj : ∀ k ∈ K₀, ∃ (U : Ambient background T.Z (s+1,t+1))
      (z : Ambient background T.Y (s+1+1,t+1)),
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z))
    (k : Ambient background T.X (s+1,t)) (hk : k∈K₀) :
    ∃ (U : Ambient background T.Z (s+1,t+1)) (z : Ambient background T.Y (s+1+1,t+1)),
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
        (by simpa only [add_sub_cancel_right] using k) ∧
      HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
        (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z) ∧
      ∃ c : BiHom (t-(s+1)) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
        c ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.X (s+1) t k ∧
        c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2=
          homotopyRegrade (show (t+1)-(s+1+1)=t-(s+1) by omega)
            (show (t+1)-(1:ℕ)=t by omega)
            (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1) z) := by
  obtain ⟨U,z,hU,hd⟩ := hsurj k hk
  obtain ⟨c,hc,hi⟩ := two_layer_common_lift_positive_g T he hT hf hg hh
    s t U k z hU hd
  exact ⟨U,z,hU,hd,c,hc,hi⟩

public def RecursivePositiveGMiddle
    (T : TriangleData background.auxiliary) (_hg : normalizedExponent background.classicalTower T.g=1)
    (s t : ℤ) (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ y : Ambient background T.X (s+1,t), y∈cycles background T.X 2 (s+1,t) →
    (background.classical.map T.f).pageMap 2 (s+1,t) y∈P₁ →
    ∃ (z : Ambient background T.Z (s+1,t+1)) (u : Ambient background T.X (s+1,t))
      (k : Ambient background T.X (s+1,t)),
      z∈cycles background T.Z 2 (s+1,t+1) ∧
      (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
        ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
        (by simpa only [add_sub_cancel_right] using u) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) (y-u-k)

public def RecursivePositiveGSurjective
    (T : TriangleData background.auxiliary) (hg : normalizedExponent background.classicalTower T.g=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t))) : Prop :=
  ∀ k∈K₀, ∃ (U : Ambient background T.Z (s+1,t+1)) (z : Ambient background T.Y (s+1+1,t+1)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
      (by simpa only [add_sub_cancel_right] using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z)

/-- Elementwise form of (pr_z R + image F2) ∩ P ≤ B∞ for the entire
actual relation R. Both U and z range over all relation members. -/
public def RecursivePositiveGTerminal
    (T : TriangleData background.auxiliary) (hg : normalizedExponent background.classicalTower T.g=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
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
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e∈finalBoundaries T.Y (s+1+1,t+1)

/-- Complete three-layer comparison for every full source in the positive-G
branch. The whole relation acts on the actual K0 residual, and torsion
correction preserves the realization of this same complete source. -/
private theorem recursive_positive_g_full_source
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP₁ : permanentCycles background T.Y (s+1,t) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P)
    (hmid : RecursivePositiveGMiddle T hg s t P₁ K₀)
    (hsurj : RecursivePositiveGSurjective T hg s t K₀)
    (hterminal : RecursivePositiveGTerminal T hg s t K₀ P)
    (a : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1)) (hv : v∈P)
    (hsame : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 3 (by decide))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
          (R.sphere (t-(s+1)) (t-1)).hom ≫
            background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
              (hcomp.nu T.Y).target.hom) := by
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X (s+1) t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3-
        (0 : BiHom (t-(s+1)) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary))) ≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero,hc]
    exact recursive_top_label_filtration T.Y (s+1) t v
  have hFy := ordinary_affine_error_label_image_permanent T.X T.Y T.f 3 1 (by decide)
    (s+1) t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hboundary⟩ := hmid y hy (hP₁ hFy)
  obtain ⟨h,hhdet,hhzero⟩ := selective_positive_g_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t z₀ hz₀ u hu
  obtain ⟨l,D,_,_,_,_,hcimage,hreal,hres⟩ := ordinary_affine_correction_with_residual
    R T.X T.Y T.f 3 1 (by decide) (by decide) (s+1) t a c h y u k
      hyd hhdet hhzero hboundary
  obtain ⟨U,z,hU,hd,ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_g
    T he hT hf hg hh s t K₀ hsurj k hk
  obtain ⟨e,hi⟩ := recursive_ordinary_image_from_residual T.X T.Y T.f (s+1) t
    ((a-lambdaMultiply 1 D) ≫ XModLambdaN.incl _ 3) (c+h) k v z hres
    (hcimage.trans hc) ck hckfirst hckimage
  have hi' : ((a-lambdaMultiply 1 D)≫background.nu.functor.map T.f) ≫ XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y (s+1) t
        (v+z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) e) := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  obtain ⟨w,hwp,hbound,hdet⟩ := recursive_full_image_of_top R hcomp
    (background.nu.functor.obj (T.X.obj background.auxiliary)) T.Y (background.nu.functor.map T.f)
    (s+1) t (a-lambdaMultiply 1 D) _ hi'
  have hclass :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map ((a-lambdaMultiply 1 D)≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) =
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) := by
    have h := congrArg
      (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫ q ≫
        background.recovery.realization.map (background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom) hreal
    simp only [Category.assoc] at h
    simp only [Functor.map_comp,Category.assoc]
    convert h using 1 <;> rfl
  rw [hclass] at hdet
  exact recursive_classical_terminal T.X T.Y (s+1+1,t+1)
    ((background.classical.map T.f).pageMap 2 (s+1+1,t+1)).hom P hP w v z e hwp hv
    hbound (hterminal k hk U z hU hd e) _ hdet

/-- Positive-G three-layer permanence. A permanent x gives a full source
before quantifying over strictly detected sources. Source bidegree
`(s,t−1)` places the target two steps higher. -/
public theorem recursive_positive_g_permanence
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 2 (s+1,t) ⊓
      LinearMap.ker ((background.classical.map T.f).pageMap 2 (s+1,t)).hom)
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP₁ : permanentCycles background T.Y (s+1,t) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P)
    (hmid : RecursivePositiveGMiddle T hg s t P₁ K₀)
    (hsurj : RecursivePositiveGSurjective T hg s t K₀)
    (hterminal : RecursivePositiveGTerminal T hg s t K₀ P)
    (x : Ambient background T.X (s,t-1)) (hx : x∈permanentCycles background T.X (s,t-1))
    (c : BiHom (t-(s+1)) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,t+1)) (hv : v∈P)
    (hfirst : c ≫ (background.quotients.tower _).rho 1 3 (by decide)=
      homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl (nativeFirstLabel T.X s (t-1) x))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 3=recursiveTopLabel T.Y (s+1) t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ∀ ξ : HomotopyGroup ((t-1)-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t-1) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+1)-(s+1+1)=(t-1)-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  have hsource (a : BiHom ((t-1)-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (ha : a ≫ XModLambdaN.incl _ 1=nativeFirstLabel T.X s (t-1) x) := by
    let a' := homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl a
    have hsame : a' ≫ XModLambdaN.incl _ 1=
        c ≫ (background.quotients.tower _).rho 1 3 (by decide) := by
      dsimp only [a']
      rw [←regrade_comp,ha,hfirst]
    exact recursive_positive_g_full_source R hcomp T he hT hf hg hh s t K₀ P₁ hP₁ P hP
      hmid hsurj hterminal a' c v hv hsame hc
  obtain ⟨a,ha⟩ := permanent_native_source T.X s (t-1) x hx
  refine ⟨(hsource a ha).1,?_⟩
  intro ξ hxstrict hξ
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp T.X s (t-1) x ξ hxstrict hξ
  have hdet := (hsource b hb).2
  have hreal' : (R.sphere ((t-1)-s) (t-1)).hom ≫
      background.recovery.realization.map (b≫background.nu.functor.map T.f) ≫
        (hcomp.nu T.Y).target.hom=ξ≫T.f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality T.f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target T.X]
    simpa only [Category.assoc] using congrArg (fun z => z≫T.f) hreal
  have ht := congrArg (fun z => z≫(hcomp.nu T.Y).target.hom)
    (realization_homotopy_regrade_full R
      (show (t-1)-s=t-(s+1) by omega) rfl (b≫background.nu.functor.map T.f))
  simp only [Category.assoc] at ht
  rw [hreal'] at ht
  have hactual :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫
        (R.sphere (t-(s+1)) (t-1)).hom ≫
          background.recovery.realization.map
            (homotopyRegrade (show (t-1)-s=t-(s+1) by omega) rfl b≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom)=
      eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+1)-(s+1+1)=(t-1)-s by omega)) ≫ ξ ≫ T.f := by
    rw [←regrade_comp,ht]
    simp only [←Category.assoc,eqToHom_trans]
  exact hactual ▸ hdet

private theorem recursive_positive_image_as_translate
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w a =
      (verticalTranslate _ 1 m w a ≫ (levelQuotientShiftIso T.X 1 N).inv) ≫
        XModLambdaN.map (normalizedFirstMap T hf) N := by
  simp [positiveFiniteImage,verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,
    susp_invariance,shiftHomotopyClass,Iso.homCongr,regrade_comp,Category.assoc,
    lastLayerNormalizedMap,normalizedFirstMap]

/-- The positive common representative is returned in native νX coordinates,
retaining the same U,k,z from the actual relation. -/
private theorem recursive_common_lift_positive_f
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (U : Ambient background T.Z (s,t+1)) (k : Ambient background T.X (s,t))
    (z : Ambient background T.Y (s+1+1,(t+1)+1))
    (hU : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) U) (by simpa using k))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t+1) (s+1+1,(t+1)+1) U
      ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) z)) :
    ∃ ck : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
      ck ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.X s t k ∧
      positiveFiniteImage T hf 2 (levelQuotientShiftIso T.X 1 2) (t-s) t ck=
        homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
          (show ((t+1)+1)-(1:ℕ)=t+1 by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) ((t+1)+1) z) := by
  obtain ⟨c,hc,hi⟩ := two_layer_common_lift_positive_f T he hT hf hg hh s t U k z hU hd
  let E := verticalTranslate (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2)
    1 (t-s) t
  let ck := E.symm (c≫(levelQuotientShiftIso T.X 1 2).hom)
  have hck : verticalTranslate _ 1 (t-s) t ck=c≫(levelQuotientShiftIso T.X 1 2).hom :=
    E.apply_symm_apply _
  refine ⟨ck,?_,?_⟩
  · apply (verticalTranslate _ 1 (t-s) t).injective
    rw [←vertical_translate_comp,hck]
    have h := quotient_shift_restriction_on_spheres T.X (0,1) 1 2 (by decide) (by decide)
      (levelQuotientShiftIso T.X 1 1) (levelQuotientShiftIso T.X 1 2)
      (level_quotient_shift_incl T.X 1 1) (level_quotient_shift_incl T.X 1 2)
      (t-s) (t+1) c
    rw [Category.assoc,←h,←Category.assoc,hc]
    have hl := congrArg (fun q => q≫(levelQuotientShiftIso T.X 1 1).hom)
      (positive_first_label_shift T.X s t k)
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hl.symm
  · rw [recursive_positive_image_as_translate,hck]
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hi

public def recursivePositiveTopLabel (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s+1+1,(t+1)+1)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3) :=
  homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
    (show ((t+1)+1)-(2:ℕ)=t by omega)
    (finiteTopLabel X 2 (by decide) (s+1+1) ((t+1)+1) x)

public def recursivePositiveImage
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ)
    (a : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 3) :=
  homotopyRegrade rfl (show (t-1)+1=t by omega)
    (positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) a)

private theorem recursive_positive_top_label_add (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x y : Ambient background X (s+1+1,(t+1)+1)) :
    recursivePositiveTopLabel X s t (x+y)=
      recursivePositiveTopLabel X s t x+recursivePositiveTopLabel X s t y := by
  simp only [recursivePositiveTopLabel,finite_top_label_add,regrade_add]

private theorem recursive_positive_image_sub
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ)
    (a b : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3)) :
    recursivePositiveImage T hf s t (a-b)=
      recursivePositiveImage T hf s t a-recursivePositiveImage T hf s t b := by
  simp only [recursivePositiveImage,positiveFiniteImage_sub,homotopy_regrade_sub]

private theorem recursive_positive_image_of_top
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (e : Ambient background T.X (s+1,t+1)) :
    recursivePositiveImage T hf s t (recursiveTopLabel T.X s t e)=
      recursivePositiveTopLabel T.Y s t
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) e) := by
  have h := selective_positive_top_image T hf 2 (by decide) (s+1) (t+1)
    (levelQuotientShiftIso T.X 1 3) (level_quotient_shift_incl T.X 1 3) e
  have h' := congrArg (homotopyRegrade
    (show ((t+1)+1)-((s+1)+1)=t-s by omega)
    (show ((t+1)+1)-(2:ℕ)=t by omega)) h
  simp only [recursivePositiveImage,recursiveTopLabel,←positiveFiniteImage_regrade,
    normalized_homotopy_regrade_trans]
  simp only [normalized_homotopy_regrade_trans] at h'
  exact h'

/-- Positive finite images commute with this same insertion into Q3. -/
private theorem recursive_positive_insert_middle_top
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (z : Ambient background T.Y (s+1+1,(t+1)+1))
    (ck : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hck : positiveFiniteImage T hf 2 (levelQuotientShiftIso T.X 1 2) (t-s) t ck=
      homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
        (show ((t+1)+1)-(1:ℕ)=t+1 by omega)
        (finiteTopLabel T.Y 1 (by decide) (s+1+1) ((t+1)+1) z)) :
    recursivePositiveImage T hf s t (finiteCoefficientInsert _ 1 2 (by decide) (t-s) t ck)=
      recursivePositiveTopLabel T.Y s t z := by
  have h := positive_finite_image_coefficient_shift_level T hf 3 1 (by decide) (t-s) t ck
  have hh := congrArg (homotopyRegrade (rfl : t-s=t-s) (show (t-(1:ℕ))+1=t by omega)) h
  rw [hck] at hh
  have hi := recursive_insert_two_layer_top T.Y (s+1+1) ((t+1)+1) z
  have hi' := congrArg (homotopyRegrade
    (show ((t+1)+1)-(s+1+1)=t-s by omega)
    (show ((t+1)+1)-(2:ℕ)=t by omega)) hi
  simp only [normalized_homotopy_regrade_trans] at hi'
  change recursivePositiveImage T hf s t _=_ at hh
  change recursivePositiveImage T hf s t (finiteCoefficientShiftClass _ 3 1 (by decide) (t-s) t ck)=_
  rw [hh]
  change homotopyRegrade rfl (show (t-1)+1=t by omega)
    (homotopyRegrade rfl (show (t+1)-1=(t-1)+1 by omega)
      (finiteCoefficientInsert _ 1 2 (by decide) (t-s) (t+1)
        (homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
          (show ((t+1)+1)-(1:ℕ)=t+1 by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) ((t+1)+1) z))))=_
  rw [finite_coefficient_insert_regrade]
  simp only [normalized_homotopy_regrade_trans]
  convert hi' using 1 <;> rfl


private theorem recursive_positive_image_from_residual
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ)
    (a c : BiHom (t-s) (t-1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (k : Ambient background T.X (s,t)) (v z : Ambient background T.Y (s+1+1,(t+1)+1))
    (hres : Detects (background.convergence (.quotient 3 (.nu T.X))) (s,t,t-1)
      (finiteTargetLabel background T.X 3 s t 1 k) (a-c))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v)
    (ck : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hk : ck ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.X s t k)
    (hck : positiveFiniteImage T hf 2 (levelQuotientShiftIso T.X 1 2) (t-s) t ck=
      homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
        (show ((t+1)+1)-(1:ℕ)=t+1 by omega)
        (finiteTopLabel T.Y 1 (by decide) (s+1+1) ((t+1)+1) z)) :
    ∃ e : Ambient background T.X (s+1,t+1),
      recursivePositiveImage T hf s t a=recursivePositiveTopLabel T.Y s t
        (v+z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) e) := by
  let b := finiteCoefficientInsert _ 1 2 (by decide) (t-s) t ck
  have hkd := first_label_detects_unshifted T.X 2 (by decide) s t k ck hk
  have hbd := finite_coefficient_insert_detects T.X 1 2 (by decide) s t k ck hkd
  have hdiff := detects_sub_filtration (background.convergence (.quotient 3 (.nu T.X)))
    (s,t,t-1) hres hbd
  obtain ⟨e,he⟩ := recursive_top_label_exists T.X s t (a-c-b) hdiff
  have hb := recursive_positive_insert_middle_top T hf s t z ck hck
  have h := congrArg (recursivePositiveImage T hf s t) he
  rw [recursive_positive_image_sub,recursive_positive_image_sub,recursive_positive_image_of_top,
    hc,hb] at h
  refine ⟨e,?_⟩
  rw [recursive_positive_top_label_add,recursive_positive_top_label_add]
  calc
    _ = (recursivePositiveImage T hf s t a-recursivePositiveTopLabel T.Y s t v-
      recursivePositiveTopLabel T.Y s t z)+recursivePositiveTopLabel T.Y s t v+
        recursivePositiveTopLabel T.Y s t z := by abel
    _ = _ := by rw [h]; abel

private theorem recursive_positive_realization_image
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (m w : ℤ) (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary))) :
    (R.sphere m (w+1)).hom ≫ background.recovery.realization.map
        (verticalTranslate _ 1 m w a≫normalizedFirstMap T hf) ≫ (hcomp.nu T.Y).target.hom =
      (R.sphere m w).hom ≫ background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
        (hcomp.nu T.Y).target.hom := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [normalized_positive_realization_square R hcomp T hf]
  have h := congrArg (fun q => q≫T.f) (positive_source_realization_eq R hcomp T.X 1 m w a)
  simp only [Category.assoc] at h
  have hn := background.recovery.nuRealizationIso.hom.naturality T.f
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  rw [Functor.map_comp,hcomp.nu_target]
  simp only [Category.assoc]
  rw [hn,←hcomp.nu_target T.X]
  convert h using 1 ; rfl

private theorem recursive_positive_full_image_of_top
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (a : BiHom (t-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hi : recursivePositiveImage T hf s t (a≫XModLambdaN.incl _ 3)=
      recursivePositiveTopLabel T.Y s t v) :
    ∃ w : Ambient background T.Y (s+1+1,(t+1)+1),
      w∈permanentCycles background T.Y (s+1+1,(t+1)+1) ∧
      w-v∈boundaries background T.Y 3 (s+1+1,(t+1)+1) ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,(t+1)+1) w
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show ((t+1)+1)-(s+1+1)=t-s by omega)) ≫
            (R.sphere (t-s) (t-1)).hom ≫
              background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
                (hcomp.nu T.Y).target.hom) := by
  let b := verticalTranslate _ 1 (t-s) (t-1) a
  let b' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show (t-1)+1=(t+1)-1 by omega) b
  have hi' : (b'≫normalizedFirstMap T hf)≫XModLambdaN.incl _ 3=
      recursiveTopLabel T.Y (s+1) (t+1) v := by
    have h := congrArg (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
      (show t=(t+1)-1 by omega)) hi
    simp only [recursivePositiveImage,positive_finite_image_full_projection,
      recursivePositiveTopLabel,normalized_homotopy_regrade_trans] at h
    dsimp only [b',b,recursiveTopLabel]
    rw [←regrade_comp,←regrade_comp]
    convert h using 1 ; rfl
  obtain ⟨w,hwp,hbound,hdet⟩ := recursive_full_image_of_top R hcomp _ T.Y
    (normalizedFirstMap T hf) (s+1) (t+1) b' v hi'
  refine ⟨w,hwp,hbound,?_⟩
  have hr := congrArg (fun q => q≫(hcomp.nu T.Y).target.hom)
    (realization_homotopy_regrade_full R
      (show t-s=(t+1)-(s+1) by omega)
      (show (t-1)+1=(t+1)-1 by omega) (b≫normalizedFirstMap T hf))
  simp only [Category.assoc] at hr
  rw [recursive_positive_realization_image R hcomp T hf] at hr
  have hr' := congrArg (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
    (show ((t+1)+1)-((s+1)+1)=(t+1)-(s+1) by omega))≫q) hr
  simp only [b,regrade_comp] at hr'
  rw [←Category.assoc (eqToHom _) (eqToHom _),eqToHom_trans] at hr'
  exact hr' ▸ hdet

private theorem recursive_positive_classical_terminal
    (X Y : (AdamsObject (coefficients := background.coefficients))) (p q : Bidegree)
    (F : Ambient background X p →ₗ[ℤ] Ambient background Y q)
    (P : Submodule ℤ (Ambient background Y q)) (hP : permanentCycles background Y q ≤ P)
    (w v z : Ambient background Y q) (e : Ambient background X p)
    (hw : w∈permanentCycles background Y q) (hv : v∈P)
    (herr : w-(v+z+F e)∈boundaries background Y 3 q)
    (hterminal : z+F e∈P → z+F e∈finalBoundaries Y q)
    (a : HomotopyGroup (q.2-q.1) (Y.obj background.auxiliary))
    (hdet : ClassicalDetects (background.classicalConvergence Y) q w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) q v ∧
      ClassicalDetects (background.classicalConvergence Y) q v a := by
  have hb := boundaries_le_finalBoundaries Y q 3 herr
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

public def RecursivePositiveFMiddle
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ y : Ambient background T.X (s,t), y∈cycles background T.X 2 (s,t) →
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t y∈P₁ →
    ∃ (z : Ambient background T.Z (s,t+1)) (u k : Ambient background T.X (s,t)),
      z∈cycles background T.Z 2 (s,t+1) ∧
      (background.classicalSuspension T.X).DesuspendsClass s (t+1)
        ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using u) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (y-u-k)

public def RecursivePositiveFSurjective (T : TriangleData background.auxiliary)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ k∈K₀, ∃ (U : Ambient background T.Z (s,t+1)) (z : Ambient background T.Y (s+1+1,(t+1)+1)),
    (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) U) (by simpa using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t+1) (s+1+1,(t+1)+1) U
      ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) z)

public def RecursivePositiveFTerminal
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
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
        finalBoundaries T.Y (s+1+1,(t+1)+1)

/-- All three layers in the positive-first-map branch retain the same full
source, the same residual k, and one member of the whole relation. -/
private theorem recursive_positive_f_full_source
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP₁ : permanentCycles background T.Y (s+1,t+1) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,(t+1)+1)))
    (hP : permanentCycles background T.Y (s+1+1,(t+1)+1) ≤ P)
    (hmid : RecursivePositiveFMiddle T hf s t P₁ K₀)
    (hsurj : RecursivePositiveFSurjective T s t K₀)
    (hterminal : RecursivePositiveFTerminal T hf s t K₀ P)
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1)) (hv : v∈P)
    (hsame : a≫XModLambdaN.incl _ 1=c≫(background.quotients.tower _).rho 1 3 (by decide))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,(t+1)+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,(t+1)+1) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show ((t+1)+1)-(s+1+1)=t-s by omega)) ≫
            (R.sphere (t-s) (t-1)).hom ≫
              background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
                (hcomp.nu T.Y).target.hom) := by
  obtain ⟨y,hy,hyd⟩ := recursive_initial_middle_label T.X s t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower (s+2)
      (positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) c-
        (0 : BiHom (t-s) ((t-1)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))≫
          XModLambdaN.incl _ 3) := by
    rw [zero_comp,sub_zero]
    apply (regrade_filtration_iff (rfl : t-s=t-s) (show (t-1)+1=t by omega) _ _).mp
    change FiltrationAtLeast background.syntheticTower (s+2) (recursivePositiveImage T hf s t c)
    rw [hc]
    apply (regrade_filtration_iff _ _ _ _).mpr
    have h : FiltrationAtLeast background.syntheticTower (s+1+1)
        (finiteTopLabel T.Y 2 (by decide) (s+1+1) ((t+1)+1) v) :=
      KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 3 (.nu T.Y))
        (s+1+1,(t+1)+1,((t+1)+1)-2) _ _
        (finiteTopLabel_detects T.Y 2 (by decide) (s+1+1) ((t+1)+1) v)
    convert h using 1 ; omega
  have hFy := positive_affine_error_label_image_permanent T hf 3 1 (by decide) (by decide)
    s t a c 0 y hyd hhigh
  obtain ⟨z₀,u,k,hz₀,hu,hk,hboundary⟩ := hmid y hy (hP₁ hFy)
  obtain ⟨h,hhdet,hhzero⟩ := selective_positive_f_native_cycle_image T he hf hg hh hT
    1 2 (by decide) s t (levelQuotientShiftIso T.X 1 3)
      (level_quotient_shift_incl T.X 1 3) z₀ hz₀ u hu
  obtain ⟨l,D,_,_,_,_,hcimage,hreal,hres⟩ := positive_affine_correction_with_residual
    R T hf 3 1 (by decide) (by decide) s t a c h y u k hyd hhdet hhzero hboundary
  obtain ⟨U,z,hU,hd⟩ := hsurj k hk
  obtain ⟨ck,hckfirst,hckimage⟩ := recursive_common_lift_positive_f
    T he hT hf hg hh s t U k z hU hd
  have hc' : recursivePositiveImage T hf s t (c+h)=recursivePositiveTopLabel T.Y s t v := by
    have hcimage' : positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) (c+h)=
        positiveFiniteImage T hf 3 (levelQuotientShiftIso T.X 1 3) (t-s) (t-1) c := by
      convert hcimage using 1 <;> rfl
    unfold recursivePositiveImage
    rw [hcimage']
    exact hc
  obtain ⟨e,hi⟩ := recursive_positive_image_from_residual T hf s t
    ((a-lambdaMultiply 1 D)≫XModLambdaN.incl _ 3) (c+h) k v z hres hc'
      ck hckfirst hckimage
  obtain ⟨w,hwp,hbound,hdet⟩ := recursive_positive_full_image_of_top R hcomp T hf s t
    (a-lambdaMultiply 1 D) _ hi
  have hclass :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show ((t+1)+1)-(s+1+1)=t-s by omega)) ≫
        (R.sphere (t-s) (t-1)).hom ≫
          background.recovery.realization.map ((a-lambdaMultiply 1 D)≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) =
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show ((t+1)+1)-(s+1+1)=t-s by omega)) ≫
        (R.sphere (t-s) (t-1)).hom ≫
          background.recovery.realization.map (a≫background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom) := by
    have h := congrArg (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
      (show ((t+1)+1)-(s+1+1)=t-s by omega))≫q≫
        background.recovery.realization.map (background.nu.functor.map T.f)≫(hcomp.nu T.Y).target.hom) hreal
    simp only [Category.assoc] at h
    simp only [Functor.map_comp,Category.assoc]
    convert h using 1 <;> rfl
  rw [hclass] at hdet
  exact recursive_positive_classical_terminal T.X T.Y (s+1,t+1) (s+1+1,(t+1)+1)
    (positiveFirstOperationLinear T hf (s+1) (t+1)) P hP w v z e hwp hv hbound
      (hterminal k hk U z hU hd e) _ hdet

/-- The original α=1 assertion, including permanent sources whose strict
class set might be empty and every individually prescribed strict class. -/
public theorem recursive_positive_f_permanence
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 2 (s,t) ⊓ LinearMap.ker (positiveFirstOperationLinear T hf s t))
    (P₁ : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP₁ : permanentCycles background T.Y (s+1,t+1) ≤ P₁)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,(t+1)+1)))
    (hP : permanentCycles background T.Y (s+1+1,(t+1)+1) ≤ P)
    (hmid : RecursivePositiveFMiddle T hf s t P₁ K₀)
    (hsurj : RecursivePositiveFSurjective T s t K₀)
    (hterminal : RecursivePositiveFTerminal T hf s t K₀ P)
    (x : Ambient background T.X (s-1,t-1)) (hx : x∈permanentCycles background T.X (s-1,t-1))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 3))
    (v : Ambient background T.Y (s+1+1,(t+1)+1)) (hv : v∈P)
    (hfirst : c≫(background.quotients.tower _).rho 1 3 (by decide)=
      homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl (nativeFirstLabel T.X (s-1) (t-1) x))
    (hc : recursivePositiveImage T hf s t c=recursivePositiveTopLabel T.Y s t v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,(t+1)+1) v ∧
      ∀ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s-1,t-1) x →
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,(t+1)+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show ((t+1)+1)-(s+1+1)=(t-1)-(s-1) by omega))≫ξ≫T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  have hsource (a : BiHom ((t-1)-(s-1)) (t-1) (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (ha : a≫XModLambdaN.incl _ 1=nativeFirstLabel T.X (s-1) (t-1) x) := by
    let a' := homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl a
    have hsame : a'≫XModLambdaN.incl _ 1=c≫(background.quotients.tower _).rho 1 3 (by decide) := by
      dsimp only [a']
      rw [←regrade_comp,ha,hfirst]
    exact recursive_positive_f_full_source R hcomp T he hT hf hg hh s t K₀ P₁ hP₁ P hP
      hmid hsurj hterminal a' c v hv hsame hc
  obtain ⟨a,ha⟩ := permanent_native_source T.X (s-1) (t-1) x hx
  refine ⟨(hsource a ha).1,?_⟩
  intro ξ hxstrict hξ
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp T.X (s-1) (t-1) x ξ hxstrict hξ
  have hdet := (hsource b hb).2
  have hreal' : (R.sphere ((t-1)-(s-1)) (t-1)).hom ≫
      background.recovery.realization.map (b≫background.nu.functor.map T.f)≫(hcomp.nu T.Y).target.hom=ξ≫T.f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality T.f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target T.X]
    simpa only [Category.assoc] using congrArg (fun z => z≫T.f) hreal
  have ht := congrArg (fun z => z≫(hcomp.nu T.Y).target.hom)
    (realization_homotopy_regrade_full R
      (show (t-1)-(s-1)=t-s by omega) rfl (b≫background.nu.functor.map T.f))
  simp only [Category.assoc] at ht
  rw [hreal'] at ht
  have hactual :
      (eqToHom (congrArg (Sphere (C:=Spectrum))
        (show ((t+1)+1)-(s+1+1)=t-s by omega))≫
        (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map
          (homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl b≫background.nu.functor.map T.f)≫
            (hcomp.nu T.Y).target.hom)=
      eqToHom (congrArg (Sphere (C:=Spectrum))
        (show ((t+1)+1)-(s+1+1)=(t-1)-(s-1) by omega))≫ξ≫T.f := by
    rw [←regrade_comp,ht]
    simp only [←Category.assoc,eqToHom_trans]
  exact hactual ▸ hdet

end
end KIP126.ProofTools.Internal.SyntheticCoverage
