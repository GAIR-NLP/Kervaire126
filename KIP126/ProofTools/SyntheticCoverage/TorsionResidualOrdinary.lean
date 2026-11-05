module

public import KIP126.ProofTools.SyntheticCoverage.RecursivePermanence
public import KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.TorsionResidualCommon
import all KIP126.ProofTools.SyntheticCoverage.NonStrictSource

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


/-- Actual three-layer representatives of every finite residual, with exact
torsion order and boundary-congruent first labels. -/
public def TorsionResidualOrdinaryFamily
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background X (s,t)))
    (R : Submodule ℤ (Ambient background Y (s+2,t+2))) : Prop :=
  ∀ k∈K₀, ∃ (k' : Ambient background X (s,t))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (W : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary)))
    (z : Ambient background Y (s+2,t+2)),
    IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (k'-k) ∧
    c ≫ (background.quotients.tower _).rho 1 3 (by decide)=nativeFirstLabel X s t k' ∧
    lambdaMultiply 1 W=0 ∧ z∈R ∧
    c ≫ XModLambdaN.map (background.nu.functor.map f) 3=
      W ≫ XModLambdaN.incl _ 3+homotopyRegrade
        (show (t+2)-(s+2)=t-s by omega) (show (t+2)-(2:ℕ)=t by omega)
        (finiteTopLabel Y 2 (by decide) (s+2) (t+2) z)

public def TorsionResidualPositiveHMiddle
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (P₁ : Submodule ℤ (Ambient background T.Y (s,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ y : Ambient background T.X (s,t), y∈cycles background T.X 3 (s,t) →
    (background.classical.map T.f).pageMap 2 (s,t) y∈P₁ →
    ∃ (z : Ambient background T.Z (s-1,t)) (u k : Ambient background T.X (s,t)),
      z∈cycles background T.Z 3 (s-1,t) ∧
      (background.classicalSuspension T.X).DesuspendsClass s (t+1)
        (middleLabelRegrade (X := .shift 1 T.X) (show (s-1+1,t+1)=(s,t+1) by congr 1; omega)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) (s-1) t z))
        (by simpa using u) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (y-u-k)

public def TorsionResidualPositiveGMiddle
    (T : TriangleData background.auxiliary)
    (s t : ℤ) (P₁ : Submodule ℤ (Ambient background T.Y (s,t)))
    (K₀ : Submodule ℤ (Ambient background T.X (s,t))) : Prop :=
  ∀ y : Ambient background T.X (s,t), y∈cycles background T.X 3 (s,t) →
    (background.classical.map T.f).pageMap 2 (s,t) y∈P₁ →
    ∃ (z : Ambient background T.Z (s,t+1)) (u k : Ambient background T.X (s,t)),
      z∈cycles background T.Z 3 (s,t+1) ∧
      (background.classicalSuspension T.X).DesuspendsClass s (t+1)
        ((background.classical.map T.h).pageMap 2 (s,t+1) z)
        (by simpa using u) ∧ k∈K₀ ∧
      IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (y-u-k)

/-- After matching its first label, every finite residual differs from the
chosen three-layer representative by a last-layer label. -/
private theorem torsion_residual_ordinary_image
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (a c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (k : Ambient background X (s,t)) (v z : Ambient background Y (s+2,t+2))
    (hres : Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-1)
      (finiteTargetLabel background X 4 s t 1 k) (a-c))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v)
    (ck : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 3))
    (Wk : BiHom (t-s) t (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hWk : lambdaMultiply 1 Wk=0)
    (hk : ck ≫ (background.quotients.tower _).rho 1 3 (by decide)=nativeFirstLabel X s t k)
    (hck : ck ≫ XModLambdaN.map (background.nu.functor.map f) 3=
      Wk ≫ XModLambdaN.incl _ 3+torsionResidualMiddleTopLabel Y s t z)
    (hzero : Subsingleton (Ambient background X (s+1,t+1))) :
    ∃ e : Ambient background X (s+2,t+2),
      a ≫ XModLambdaN.map (background.nu.functor.map f) 4=
        W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t
          (v+z+(background.classical.map f).pageMap 2 (s+2,t+2) e) := by
  let b := finiteCoefficientInsert _ 1 3 (by decide) (t-s) t ck
  have hkd := first_label_detects_unshifted X 3 (by decide) s t k ck hk
  have hbd := finite_coefficient_insert_detects X 1 3 (by decide) s t k ck hkd
  have hdiff := detects_sub_filtration (background.convergence (.quotient 4 (.nu X)))
    (s,t,t-1) hres hbd
  obtain ⟨e,he⟩ := torsion_residual_top_label_exists X s t (a-c-b) hdiff hzero
  have hb : b ≫ XModLambdaN.map (background.nu.functor.map f) 4=torsionResidualTopLabel Y s t z := by
    dsimp only [b]
    rw [finite_coefficient_insert_natural,hck,torsion_residual_insert_add,
      torsion_residual_insert_torsion_zero _ _ _ _ hWk,zero_add,torsion_residual_insert_middle_top]
  have h := congrArg (fun u => u ≫ XModLambdaN.map (background.nu.functor.map f) 4) he
  rw [Preadditive.sub_comp,Preadditive.sub_comp,torsion_residual_top_label_natural,hc,hb] at h
  refine ⟨e,?_⟩
  rw [torsion_residual_top_label_add,torsion_residual_top_label_add]
  calc
    _ = (a ≫ XModLambdaN.map (background.nu.functor.map f) 4-
      (W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v)-torsionResidualTopLabel Y s t z)+
        (W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v)+torsionResidualTopLabel Y s t z := by abel
    _ = _ := by rw [h]; abel

private theorem torsion_residual_ordinary_full_source
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background X (s,t)))
    (P₁ : Submodule ℤ (Ambient background Y (s,t)))
    (hP₁ : permanentCycles background Y (s,t) ≤ P₁)
    (Residual P : Submodule ℤ (Ambient background Y (s+2,t+2)))
    (hP : permanentCycles background Y (s+2,t+2) ≤ P)
    (hmid : ∀ y : Ambient background X (s,t), y∈cycles background X 3 (s,t) →
      (background.classical.map f).pageMap 2 (s,t) y∈P₁ →
      ∃ (u k : Ambient background X (s,t))
        (h : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4)),
        k∈K₀ ∧
        Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-1)
          (finiteTargetLabel background X 4 s t 1 u) h ∧
        h ≫ XModLambdaN.map (background.nu.functor.map f) 4=0 ∧
        IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (y-u-k))
    (hfamily : TorsionResidualOrdinaryFamily X Y f s t K₀ Residual)
    (hzero : Subsingleton (Ambient background X (s+1,t+1)))
    (hterminal : (Residual ⊔ ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range) ⊓ P ≤
      finalBoundaries Y (s+2,t+2))
    (a : BiHom (t-s) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (l : ℕ) (hW : lambdaMultiply l W=0)
    (v : Ambient background Y (s+2,t+2)) (hv : v∈P)
    (hsame : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 4 (by decide))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+2,t+2) v ∧
      ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2)-(s+2)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫
            background.recovery.realization.map (a≫background.nu.functor.map f) ≫
              (hcomp.nu Y).target.hom) := by
  obtain ⟨y,hy,hyd⟩ := torsion_residual_initial_middle_label X s t a c hsame
  have hhigh : FiltrationAtLeast background.syntheticTower (s+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map f) 4-W ≫ XModLambdaN.incl _ 4) := by
    rw [hc,add_sub_cancel_left]
    exact background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega)
      (torsion_residual_top_label_filtration Y s t v)
  have hFy := ordinary_affine_error_label_image_permanent X Y f 4 1 (by decide)
    s t a c W y hyd hhigh
  obtain ⟨u,k,h,hk,hhdet,hhzero,hboundary⟩ := hmid y hy (hP₁ hFy)
  obtain ⟨l₀,D,_,_,_,_,hcimage,hreal,hres⟩ := ordinary_affine_correction_with_residual
    R X Y f 4 1 (by decide) (by decide) s t a c h y u k hyd hhdet hhzero hboundary
  obtain ⟨k',ck,Wk,z,hkk,hckfirst,hWk,hz,hckimage⟩ := hfamily k hk
  have hzeroDet : Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-1)
      (finiteTargetLabel background X 4 s t 1 0) 0 := by
    have hd := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient 4 (.nu X)) (s,t,t-1) hres hres
    rwa [←finiteTargetLabel_sub,sub_self,sub_self] at hd
  have hneg : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (k-0-k') := by
    apply (mem_finalBoundaries_iff X (s,t) _).mp
    have hn := (finalBoundaries X (s,t)).neg_mem ((mem_finalBoundaries_iff X (s,t) _).mpr hkk)
    simpa only [neg_sub,sub_zero] using hn
  obtain ⟨l₁,D₁,_,_,_,_,hcimage₁,hreal₁,hres₁⟩ := ordinary_affine_correction_with_residual
    R X Y f 4 1 (by decide) (by decide) s t (a-lambdaMultiply 1 D) (c+h) 0 k 0 k'
      hres hzeroDet (by simp only [zero_comp]) hneg
  let a' := a-lambdaMultiply 1 D-lambdaMultiply 1 D₁
  have hc' : ((c+h)+0) ≫ XModLambdaN.map (background.nu.functor.map f) 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v :=
    hcimage₁.trans (hcimage.trans hc)
  obtain ⟨e,hi⟩ := torsion_residual_ordinary_image X Y f s t
    (a' ≫ XModLambdaN.incl _ 4) ((c+h)+0) W k' v z hres₁ hc' ck Wk hWk hckfirst hckimage hzero
  have hi' : (a'≫background.nu.functor.map f) ≫ XModLambdaN.incl _ 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t
        (v+z+(background.classical.map f).pageMap 2 (s+2,t+2) e) := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hi
  obtain ⟨w,hwp,hbound,hdet⟩ := torsion_residual_full_image_of_top R hcomp
    (background.nu.functor.obj (X.obj background.auxiliary)) Y (background.nu.functor.map f)
    s t a' W l hW _ hi'
  have hreal' : (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a'=
      (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map a := hreal₁.trans hreal
  have hclass := congrArg
    (fun q => eqToHom (congrArg (Sphere (C:=Spectrum))
      (show (t+2)-(s+2)=t-s by omega)) ≫ q ≫
        background.recovery.realization.map (background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom) hreal'
  simp only [Functor.map_comp,Category.assoc] at hdet ⊢
  simp only [Category.assoc] at hclass
  rw [hclass] at hdet
  apply torsion_residual_classical_terminal X Y (s+2,t+2)
    ((background.classical.map f).pageMap 2 (s+2,t+2)).hom P hP w v z e hwp hv hbound _ _ hdet
  intro hsum
  apply hterminal
  refine ⟨?_,hsum⟩
  exact (Residual ⊔ ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range).add_mem
    ((show Residual ≤ Residual ⊔ ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range from le_sup_left) hz)
    ((show ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range ≤
      Residual ⊔ ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range from le_sup_right) ⟨e,rfl⟩)

private theorem torsion_residual_ordinary_permanence
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background X (s,t)))
    (P₁ : Submodule ℤ (Ambient background Y (s,t)))
    (hP₁ : permanentCycles background Y (s,t) ≤ P₁)
    (Residual P : Submodule ℤ (Ambient background Y (s+2,t+2)))
    (hP : permanentCycles background Y (s+2,t+2) ≤ P)
    (hmid : ∀ y : Ambient background X (s,t), y∈cycles background X 3 (s,t) →
      (background.classical.map f).pageMap 2 (s,t) y∈P₁ →
      ∃ (u k : Ambient background X (s,t))
        (h : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4)),
        k∈K₀ ∧
        Detects (background.convergence (.quotient 4 (.nu X))) (s,t,t-1)
          (finiteTargetLabel background X 4 s t 1 u) h ∧
        h ≫ XModLambdaN.map (background.nu.functor.map f) 4=0 ∧
        IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (y-u-k))
    (hfamily : TorsionResidualOrdinaryFamily X Y f s t K₀ Residual)
    (hzero : Subsingleton (Ambient background X (s+1,t+1)))
    (hterminal : (Residual ⊔ ((background.classical.map f).pageMap 2 (s+2,t+2)).hom.range) ⊓ P ≤
      finalBoundaries Y (s+2,t+2))
    (x x' : Ambient background X (s-1,t-1))
    (hx : x∈permanentCycles background X (s-1,t-1))
    (hxx : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s-1,t-1) (x'-x))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (l : ℕ) (hW : lambdaMultiply l W=0)
    (v : Ambient background Y (s+2,t+2)) (hv : v∈P)
    (hfirst : c ≫ (background.quotients.tower _).rho 1 4 (by decide)=
      homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl (nativeFirstLabel X (s-1) (t-1) x'))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 4=
      W ≫ XModLambdaN.incl _ 4+torsionResidualTopLabel Y s t v) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+2,t+2) v ∧
      (∀ ξ : HomotopyGroup ((t-1)-(s-1)) (X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence X) (s-1,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ f)) ∧
      ∃ ξ : HomotopyGroup ((t-1)-(s-1)) (X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence X) (s-1,t-1) x ξ ∧
        ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  have hsource (a : BiHom ((t-1)-(s-1)) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
      (ha : a ≫ XModLambdaN.incl _ 1=nativeFirstLabel X (s-1) (t-1) x) :
      IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+2,t+2) v ∧
      ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫
          (R.sphere ((t-1)-(s-1)) (t-1)).hom ≫
            background.recovery.realization.map (a≫background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom) := by
    obtain ⟨a₁,ha₁,hr₁⟩ := full_source_with_boundary_changed_first_label R X (s-1) (t-1) x x' a ha hxx
    let a₂ := homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl a₁
    have hsame : a₂ ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 4 (by decide) := by
      dsimp only [a₂]
      rw [←regrade_comp,ha₁,hfirst]
    obtain ⟨hp,hdet⟩ := torsion_residual_ordinary_full_source R hcomp X Y f s t K₀ P₁ hP₁
      Residual P hP hmid hfamily hzero hterminal a₂ c W l hW v hv hsame hc
    refine ⟨hp,?_⟩
    have ht := congrArg (fun z => z≫(hcomp.nu Y).target.hom)
      (realization_homotopy_regrade_full R (show (t-1)-(s-1)=t-s by omega) rfl
        (a₁≫background.nu.functor.map f))
    have hr := congrArg (fun z => z≫background.recovery.realization.map (background.nu.functor.map f)≫
      (hcomp.nu Y).target.hom) hr₁
    simp only [Category.assoc] at ht hr
    have heq :
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (show (t+2)-(s+2)=t-s by omega)) ≫
          (R.sphere (t-s) (t-1)).hom ≫ background.recovery.realization.map
            (a₂≫background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom)=
        eqToHom (congrArg (Sphere (C:=Spectrum)) (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫
          (R.sphere ((t-1)-(s-1)) (t-1)).hom ≫ background.recovery.realization.map
            (a≫background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom := by
      dsimp only [a₂]
      rw [←regrade_comp,ht]
      simp only [Functor.map_comp,Category.assoc]
      rw [hr]
      simp only [←Category.assoc,eqToHom_trans]
    exact heq ▸ hdet
  obtain ⟨a₀,ha₀⟩ := permanent_native_source X (s-1) (t-1) x hx
  have hall : ∀ ξ : HomotopyGroup ((t-1)-(s-1)) (X.obj background.auxiliary),
      ClassicalDetects (background.classicalConvergence X) (s-1,t-1) x ξ →
      ClassicalDetects (background.classicalConvergence Y) (s+2,t+2) v
        (eqToHom (congrArg (Sphere (C:=Spectrum))
          (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ f) := by
    intro ξ hξ
    obtain ⟨a,ha,hr⟩ := prescribed_native_source_nonstrict hcomp X (s-1) (t-1) x ξ hξ
    have hd := (hsource a ha).2
    have himage : (R.sphere ((t-1)-(s-1)) (t-1)).hom ≫
        background.recovery.realization.map (a≫background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom=ξ≫f := by
      rw [Functor.map_comp,hcomp.nu_target]
      have hn := background.recovery.nuRealizationIso.hom.naturality f
      dsimp only [Functor.comp_map,Functor.id_map] at hn
      simp only [Category.assoc]
      rw [hn,←hcomp.nu_target X]
      simpa only [Category.assoc] using congrArg (fun z => z≫f) hr
    rw [himage] at hd
    exact hd
  refine ⟨(hsource a₀ ha₀).1,hall,?_⟩
  have hd := full_source_detects_first_label R hcomp X (s-1) (t-1) x a₀ ha₀
  exact ⟨_,hd,hall _ hd⟩

/-- The four-layer finite-residual criterion retains every specified classical source,
including zero infinity classes, and supplies an extension representative. -/
public theorem torsion_residual_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 3 (s,t))
    (P₁ : Submodule ℤ (Ambient background T.Y (s,t)))
    (hP₁ : permanentCycles background T.Y (s,t) ≤ P₁)
    (Residual P : Submodule ℤ (Ambient background T.Y (s+2,t+2)))
    (hP : permanentCycles background T.Y (s+2,t+2) ≤ P)
    (hmid : TorsionResidualPositiveHMiddle T hh s t P₁ K₀)
    (hfamily : TorsionResidualOrdinaryFamily T.X T.Y T.f s t K₀ Residual)
    (hzero : Subsingleton (Ambient background T.X (s+1,t+1)))
    (hterminal : (Residual ⊔ ((background.classical.map T.f).pageMap 2 (s+2,t+2)).hom.range) ⊓ P ≤
      finalBoundaries T.Y (s+2,t+2))
    (x x' : Ambient background T.X (s-1,t-1))
    (hx : x∈permanentCycles background T.X (s-1,t-1))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s-1,t-1) (x'-x))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (l : ℕ) (_hl : 0<l) (hW : lambdaMultiply l W=0)
    (v : Ambient background T.Y (s+2,t+2)) (hv : v∈P)
    (hfirst : c ≫ (background.quotients.tower _).rho 1 4 (by decide)=
      homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl (nativeFirstLabel T.X (s-1) (t-1) x'))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 4=
      W ≫ XModLambdaN.incl _ 4+homotopyRegrade
        (show (t+2)-(s+2)=t-s by omega) (show (t+2)-(3:ℕ)=t-1 by omega)
        (finiteTopLabel T.Y 3 (by decide) (s+2) (t+2) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+2,t+2) v ∧
      (∀ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ T.f)) ∧
      ∃ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ T.f) := by
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  apply torsion_residual_ordinary_permanence T.X T.Y T.f s t K₀ P₁ hP₁ Residual P hP
    ?_ hfamily hzero hterminal x x' hx hxx c W l hW v hv hfirst hc
  intro y hy hFy
  obtain ⟨z,u,k,hz,hu,hk,hboundary⟩ := hmid y hy hFy
  obtain ⟨h,hhdet,hhzero⟩ := positive_h_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    4 1 3 (by decide) (by decide) (s-1) s t (by omega) z hz u hu
  exact ⟨u,k,h,hk,hhdet,hhzero,hboundary⟩

/-- The four-layer finite-residual criterion retains every specified classical source,
including zero infinity classes, and supplies an extension representative. -/
public theorem torsion_residual_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (_hK₀ : K₀ ≤ cycles background T.X 3 (s,t))
    (P₁ : Submodule ℤ (Ambient background T.Y (s,t)))
    (hP₁ : permanentCycles background T.Y (s,t) ≤ P₁)
    (Residual P : Submodule ℤ (Ambient background T.Y (s+2,t+2)))
    (hP : permanentCycles background T.Y (s+2,t+2) ≤ P)
    (hmid : TorsionResidualPositiveGMiddle T s t P₁ K₀)
    (hfamily : TorsionResidualOrdinaryFamily T.X T.Y T.f s t K₀ Residual)
    (hzero : Subsingleton (Ambient background T.X (s+1,t+1)))
    (hterminal : (Residual ⊔ ((background.classical.map T.f).pageMap 2 (s+2,t+2)).hom.range) ⊓ P ≤
      finalBoundaries T.Y (s+2,t+2))
    (x x' : Ambient background T.X (s-1,t-1))
    (hx : x∈permanentCycles background T.X (s-1,t-1))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s-1,t-1) (x'-x))
    (c : BiHom (t-s) (t-1) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 4))
    (W : BiHom (t-s) (t-1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (l : ℕ) (_hl : 0<l) (hW : lambdaMultiply l W=0)
    (v : Ambient background T.Y (s+2,t+2)) (hv : v∈P)
    (hfirst : c ≫ (background.quotients.tower _).rho 1 4 (by decide)=
      homotopyRegrade (show (t-1)-(s-1)=t-s by omega) rfl (nativeFirstLabel T.X (s-1) (t-1) x'))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) 4=
      W ≫ XModLambdaN.incl _ 4+homotopyRegrade
        (show (t+2)-(s+2)=t-s by omega) (show (t+2)-(3:ℕ)=t-1 by omega)
        (finiteTopLabel T.Y 3 (by decide) (s+2) (t+2) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+2,t+2) v ∧
      (∀ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ T.f)) ∧
      ∃ ξ : HomotopyGroup ((t-1)-(s-1)) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s-1,t-1) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+2,t+2) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+2)-(s+2)=(t-1)-(s-1) by omega)) ≫ ξ ≫ T.f) := by
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  apply torsion_residual_ordinary_permanence T.X T.Y T.f s t K₀ P₁ hP₁ Residual P hP
    ?_ hfamily hzero hterminal x x' hx hxx c W l hW v hv hfirst hc
  intro y hy hFy
  obtain ⟨z,u,k,hz,hu,hk,hboundary⟩ := hmid y hy hFy
  obtain ⟨h,hhdet,hhzero⟩ := positive_g_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    4 1 3 (by decide) (by decide) (s-1) s t (by omega) z hz u hu
  exact ⟨u,k,h,hk,hhdet,hhzero,hboundary⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
