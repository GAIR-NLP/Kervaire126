module

import all KIP126.ProofTools.SyntheticCoverage.RecursivePermanence

/-! Actual four-layer coefficient calculations for a finite residual whose
complete torsion vanishes after one coefficient insertion. -/

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
set_option maxHeartbeats 1500000

private def torsionResidualTopLabel (X : AdamsObject (coefficients := background.coefficients))
    (s t : ℤ) (x : Ambient background X (s+2,t+2)) :
    BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4) :=
  homotopyRegrade (show (t+2)-(s+2)=t-s by omega)
    (show (t+2)-(3:ℕ)=t-1 by omega)
    (finiteTopLabel X 3 (by decide) (s+2) (t+2) x)

private def torsionResidualMiddleTopLabel (X : AdamsObject (coefficients := background.coefficients))
    (s t : ℤ) (x : Ambient background X (s+2,t+2)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3) :=
  homotopyRegrade (show (t+2)-(s+2)=t-s by omega)
    (show (t+2)-(2:ℕ)=t by omega)
    (finiteTopLabel X 2 (by decide) (s+2) (t+2) x)

private theorem torsion_residual_top_label_add (X : AdamsObject (coefficients := background.coefficients))
    (s t : ℤ) (x y : Ambient background X (s+2,t+2)) :
    torsionResidualTopLabel X s t (x+y)=torsionResidualTopLabel X s t x+torsionResidualTopLabel X s t y := by
  simp only [torsionResidualTopLabel,finite_top_label_add,regrade_add]

private theorem torsion_residual_top_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s+2,t+2)) :
    torsionResidualTopLabel X s t x ≫ XModLambdaN.map (background.nu.functor.map f) 4=
      torsionResidualTopLabel Y s t ((background.classical.map f).pageMap 2 (s+2,t+2) x) := by
  simp only [torsionResidualTopLabel,←regrade_comp,finite_top_label_ordinary_natural]

private theorem torsion_residual_top_label_filtration (X : AdamsObject (coefficients := background.coefficients))
    (s t : ℤ) (x : Ambient background X (s+2,t+2)) :
    FiltrationAtLeast background.syntheticTower (s+2) (torsionResidualTopLabel X s t x) := by
  apply (regrade_filtration_iff _ _ _ _).mpr
  exact KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient 4 (.nu X))
    (s+2,t+2,(t+2)-3) _ _ (finiteTopLabel_detects X 3 (by decide) (s+2) (t+2) x)

private theorem torsion_residual_top_detects_unique
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-3) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (ha : Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-3)
      (finiteTargetLabel background X 4 s t 3 x) a) :
    a=finiteTopLabel X 3 (by decide) s t x := by
  have hd := detects_sub_filtration (background.convergence (.quotient 4 (.nu X)))
    (s,t,t-3) ha (finiteTopLabel_detects X 3 (by decide) s t x)
  exact sub_eq_zero.mp (finite_high_filtration_zero X 4 (by decide)
    (t-s) (t-3) (s+1) (by omega) _ hd)

private theorem torsion_residual_insert_three_layer_top
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    homotopyRegrade rfl (show (t-2)-1=t-3 by omega)
      (finiteCoefficientInsert _ 1 3 (by decide) (t-s) (t-2)
        (finiteTopLabel X 2 (by decide) s t x)) =
      finiteTopLabel X 3 (by decide) s t x := by
  apply torsion_residual_top_detects_unique
  have h := finite_coefficient_shift_layer_detects X 4 1 2 (by decide) (by decide)
    s t x (finiteTopLabel X 2 (by decide) s t x)
    (finiteTopLabel_detects X 2 (by decide) s t x)
  convert h using 1 <;> rfl

private theorem torsion_residual_insert_middle_top
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s+2,t+2)) :
    finiteCoefficientInsert _ 1 3 (by decide) (t-s) t
      (torsionResidualMiddleTopLabel X s t x)=torsionResidualTopLabel X s t x := by
  dsimp only [torsionResidualMiddleTopLabel,torsionResidualTopLabel]
  rw [finite_coefficient_insert_regrade]
  have h := torsion_residual_insert_three_layer_top X (s+2) (t+2) x
  have h' := congrArg (homotopyRegrade (show (t+2)-(s+2)=t-s by omega)
    (show (t+2)-(3:ℕ)=t-1 by omega)) h
  simp only [normalized_homotopy_regrade_trans] at h'
  convert h' using 1 <;> rfl

private theorem torsion_residual_insert_add (A : SyntheticSpectrum) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN A 3)) :
    finiteCoefficientInsert A 1 3 (by decide) m w (a+b)=
      finiteCoefficientInsert A 1 3 (by decide) m w a+
        finiteCoefficientInsert A 1 3 (by decide) m w b := by
  change finiteCoefficientShiftClass A 4 1 (by decide) m w (a+b)=
    finiteCoefficientShiftClass A 4 1 (by decide) m w a+
      finiteCoefficientShiftClass A 4 1 (by decide) m w b
  simp only [finiteCoefficientShiftClass,show ¬(1:ℕ)=0 by decide,
    ↓reduceDIte,shiftHomotopyClass,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,regrade_precomp]

private theorem torsion_residual_insert_torsion_zero
    (A : SyntheticSpectrum) (m w : ℤ) (T : BiHom m w A)
    (hT : lambdaMultiply 1 T=0) :
    finiteCoefficientInsert A 1 3 (by decide) m w (T ≫ XModLambdaN.incl _ 3)=0 := by
  have heq : finiteCoefficientInsert A 1 3 (by decide) m w (T ≫ XModLambdaN.incl _ 3)=
      lambdaMultiply 1 T ≫ XModLambdaN.incl _ 4 := by
    change finiteCoefficientShiftClass A 4 1 (by decide) m w (T ≫ XModLambdaN.incl _ 3)=
      lambdaMultiply 1 T ≫ XModLambdaN.incl _ 4
    simp only [finiteCoefficientShiftClass,show ¬(1:ℕ)=0 by decide,
      ↓reduceDIte,regrade_precomp,shiftHomotopyClass,Functor.map_comp,
      lambdaMultiply,Category.assoc]
    rw [((background.quotients.tower _).triangle (show 0<(1:ℕ) by decide)
      (show (1:ℕ)<4 by decide)).lambda_quotient]
    erw [←Category.assoc ((SyntheticCategory.biShift (0,-(1:ℤ))).map T),lambdaPow_naturality]
    simp only [←Category.assoc]
  rw [heq,hT,zero_comp]

private theorem torsion_residual_initial_middle_label
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (hsame : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 4 (by decide)) :
    ∃ y : Ambient background X (s,t), y∈cycles background X 3 (s,t) ∧
      Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-1)
        (finiteTargetLabel background X 4 s t 1 y) (a ≫ XModLambdaN.incl _ 4-c) := by
  let d := a ≫ XModLambdaN.incl _ 4-c
  have hd : d ≫ (background.quotients.tower _).rho 1 4 (by decide)=0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_quotient,hsame,sub_self]
  let d' := homotopyRegrade (show t-s=(t-1)-(s-1) by omega) rfl d
  have hd' : d' ≫ (background.quotients.tower _).rho 1 4 (by decide)=0 := by
    dsimp only [d']
    rw [←regrade_comp,hd,regrade_zero]
  have hfil := finite_first_kernel_filtration X 4 (by decide) (s-1) (t-1) d' hd'
  rw [sub_add_cancel] at hfil
  have hfil' : FiltrationAtLeast background.syntheticTower s d :=
    (regrade_filtration_iff _ _ _ _).mp hfil
  exact middle_finite_filtration_label X 4 1 (by decide) s t d hfil'

/-- Vanishing of the next first-label group controls every finite representative. -/
private theorem torsion_residual_top_label_exists
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a)
    (hzero : Subsingleton (Ambient background X (s+1,t+1))) :
    ∃ x : Ambient background X (s+2,t+2), a=torsionResidualTopLabel X s t x := by
  let a₁ := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t-1=(t+1)-(2:ℕ) by omega) a
  have ha₁ : FiltrationAtLeast background.syntheticTower (s+1) a₁ :=
    (regrade_filtration_iff _ _ _ _).mpr ha
  obtain ⟨y,_,hy⟩ := middle_finite_filtration_label X 4 2 (by decide) (s+1) (t+1) a₁ ha₁
  have hy0 : y=0 := hzero.elim _ _
  have hzlabel : finiteTargetLabel background X 4 (s+1) (t+1) 2 0=0 := by
    simpa only [sub_self] using finiteTargetLabel_sub X 4 (s+1) (t+1) 2 0 0
  rw [hy0,hzlabel] at hy
  have htop₁ := detects_zero_filtration (background.convergence (.quotient 4 (.nu X)))
    (s+1,t+1,(t+1)-2) hy
  have htop : FiltrationAtLeast background.syntheticTower (s+2) a := by
    have h := (regrade_filtration_iff (show t-s=(t+1)-(s+1) by omega)
      (show t-1=(t+1)-(2:ℕ) by omega) (s+1+1) a).mp htop₁
    convert h using 1 <;> omega
  let a₂ := homotopyRegrade (show t-s=(t+2)-(s+2) by omega)
    (show t-1=(t+2)-(3:ℕ) by omega) a
  have ha₂ : FiltrationAtLeast background.syntheticTower (s+2) a₂ :=
    (regrade_filtration_iff _ _ _ _).mpr htop
  obtain ⟨x,hx⟩ := finiteTopLabel_exists X 3 (by decide) (s+2) (t+2) a₂ ha₂
  refine ⟨x,?_⟩
  have h := congrArg (homotopyRegrade (show (t+2)-(s+2)=t-s by omega)
    (show (t+2)-(3:ℕ)=t-1 by omega)) hx
  simpa only [a₂,torsionResidualTopLabel,homotopy_regrade_inverse] using h

private theorem torsion_residual_full_image_of_top_core
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticSpectrum) (Y : (AdamsObject (coefficients := background.coefficients)))
    (g : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) A) (v : Ambient background Y (s+2,t+2))
    (himage : (a≫g) ≫ XModLambdaN.incl _ 4=torsionResidualTopLabel Y s t v) :
    ∃ w : Ambient background Y (s+2,t+2),
      w ∈ permanentCycles background Y (s+2,t+2) ∧
      w-v ∈ boundaries background Y 4 (s+2,t+2) ∧
      ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) w
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2)-(s+2)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) ≫
            (hcomp.nu Y).target.hom) := by
  let a' := homotopyRegrade (show t-s=(t+2)-(s+2) by omega)
    (show t-1=(t+2)-(3:ℕ) by omega) a
  have hi : (a'≫g) ≫ XModLambdaN.incl _ 4=finiteTopLabel Y 3 (by decide) (s+2) (t+2) v := by
    dsimp only [a']
    rw [←regrade_comp,←regrade_comp,himage]
    simp only [torsionResidualTopLabel,homotopy_regrade_inverse]
  have hz : (a'≫g) ≫ XModLambdaN.incl _ 3=0 := by
    have h := congrArg (fun u => u ≫ (background.quotients.tower
      (background.nu.functor.obj (Y.obj background.auxiliary))).rho 3 4 (by decide)) hi
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero] at h
    exact h
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects
    R hcomp A Y g 3 (s+2) (t+2) a' hz
  have hwtop := lambda_power_first_label_projection_eq_top Y 3 (by decide)
    (s+2) (t+2) b w hw
  rw [hb,hi] at hwtop
  have hbound : w-v ∈ boundaries background Y 4 (s+2,t+2) := by
    apply (finiteTopLabel_zero_iff_boundary Y 3 (by decide) (s+2) (t+2) _).mp
    rw [finite_top_label_sub,hwtop,sub_self]
  refine ⟨w,hwp,hbound,?_⟩
  have hr := realization_homotopy_regrade_full R
    (show t-s=(t+2)-(s+2) by omega) (show t-1=(t+2)-(3:ℕ) by omega) (a≫g)
  have hr' := congrArg (fun u => u ≫ (hcomp.nu Y).target.hom) hr
  have heq : (R.sphere ((t+2)-(s+2)) ((t+2)-(3:ℕ))).hom ≫
      background.recovery.realization.map (a'≫g) ≫ (hcomp.nu Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum))
        (show (t+2)-(s+2)=t-s by omega)) ≫
        (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) ≫
          (hcomp.nu Y).target.hom := by
    simpa only [a',regrade_comp,Category.assoc] using hr'
  exact heq ▸ hdet


private theorem torsion_residual_full_image_of_top
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticSpectrum) (Y : AdamsObject (coefficients := background.coefficients))
    (g : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) (s t : ℤ)
    (a : BiHom (t-s) (t-1) A)
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (l : ℕ) (hW : lambdaMultiply l W=0)
    (v : Ambient background Y (s+2,t+2))
    (himage : (a≫g) ≫ XModLambdaN.incl _ 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v) :
    ∃ w : Ambient background Y (s+2,t+2),
      w ∈ permanentCycles background Y (s+2,t+2) ∧
      w-v ∈ boundaries background Y 4 (s+2,t+2) ∧
      ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) w
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2)-(s+2)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) ≫
            (hcomp.nu Y).target.hom) := by
  letI := R.additive
  have hi : ((a≫g-W)≫𝟙 _) ≫ XModLambdaN.incl _ 4=torsionResidualTopLabel Y s t v := by
    rw [Category.comp_id,Preadditive.sub_comp,himage,add_sub_cancel_left]
  obtain ⟨w,hwp,hbound,hdet⟩ := torsion_residual_full_image_of_top_core R hcomp
    (background.nu.functor.obj (Y.obj background.auxiliary)) Y (𝟙 _) s t (a≫g-W) v hi
  refine ⟨w,hwp,hbound,?_⟩
  have hWr := lambda_torsion_realization_zero R (t-s) (t-1) l W hW
  have hr : (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map ((a≫g-W)≫𝟙 _)=
      (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map (a≫g) := by
    rw [Category.comp_id,Functor.map_sub,Preadditive.comp_sub,hWr,sub_zero]
  have heq := congrArg (fun z => eqToHom (congrArg (Sphere (C:=Spectrum))
    (show (t+2)-(s+2)=t-s by omega)) ≫ z ≫ (hcomp.nu Y).target.hom) hr
  simp only [Category.assoc] at heq
  exact heq ▸ hdet

private theorem torsion_residual_classical_terminal
    (X Y : AdamsObject (coefficients := background.coefficients)) (p : Bidegree)
    (F : Ambient background X p →ₗ[ℤ] Ambient background Y p)
    (P : Submodule ℤ (Ambient background Y p))
    (hP : permanentCycles background Y p ≤ P)
    (w v z : Ambient background Y p) (e : Ambient background X p)
    (hw : w∈permanentCycles background Y p) (hv : v∈P)
    (herr : w-(v+z+F e) ∈ boundaries background Y 4 p)
    (hterminal : z+F e ∈ P → z+F e ∈ finalBoundaries Y p)
    (a : HomotopyGroup (p.2-p.1) (Y.obj background.auxiliary))
    (hdet : ClassicalDetects (background.classicalConvergence Y) p w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) p v ∧
      ClassicalDetects (background.classicalConvergence Y) p v a := by
  have hboundary := boundaries_le_finalBoundaries Y p 4 herr
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

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
