module

public import KIP126.ProofTools.SyntheticCoverage.Permanence

public import KIP126.ProofTools.SyntheticCoverage.MiddleElimination

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.MahowaldLeibniz.LastLayer

public import KIP126.ProofTools.MahowaldLeibniz.Bockstein

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.FinitePermanence
import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence
import all KIP126.ProofTools.SyntheticCoverage.SelectiveHead

/-! Corrections of complete and finite representatives for the permanence
comparison with true final-boundary terms. All corrections retain the fixed
classical realization; the torsion conclusion concerns the actual full class.
-/

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
set_option maxHeartbeats 300000

/-- Each element of the final boundary object belongs to a finite boundary stage. -/
private theorem final_boundary_element_has_finite_stage
    (D : SSData (ModuleCat.{0} ℤ))
    (b : (Subobject.underlying.obj (D.B ⊤) : ModuleCat.{0} ℤ)) :
    ∃ (n : ℕ) (c : (Subobject.underlying.obj (D.B (n:WithTop ℕ)) : ModuleCat.{0} ℤ)),
      Subobject.ofLE (D.B (n:WithTop ℕ)) (D.B ⊤) (D.B_mono le_top) c = b := by
  have htop : D.B ⊤ = ⨆ n : ℕ, D.B (n:WithTop ℕ) :=
    le_antisymm (D.B_top_least _ (fun n => le_iSup (fun n : ℕ => D.B (n:WithTop ℕ)) n))
      (iSup_le fun n => D.B_mono le_top)
  have hb : (D.B ⊤).arrow b ∈ (ModuleCat.subobjectModule D.V) (D.B ⊤) :=
    ⟨b,rfl⟩
  have hmod := congrArg (ModuleCat.subobjectModule D.V) htop
  rw [(ModuleCat.subobjectModule D.V).map_iSup] at hmod
  rw [hmod] at hb
  have hm : Monotone (fun n : ℕ => (ModuleCat.subobjectModule D.V) (D.B (n:WithTop ℕ))) := by
    intro i j hij
    exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono (by exact_mod_cast hij))
  obtain ⟨n,c,hc⟩ := (Submodule.mem_iSup_of_directed _ hm.directed_le).mp hb
  refine ⟨n,c,?_⟩
  apply ((ModuleCat.mono_iff_injective (D.B ⊤).arrow).mp inferInstance)
  change (Subobject.ofLE (D.B (n:WithTop ℕ)) (D.B ⊤) (D.B_mono le_top) ≫
    (D.B ⊤).arrow) c = (D.B ⊤).arrow b
  rw [Subobject.ofLE_arrow]
  exact hc

/-- A true final E2 boundary belongs to some inclusive finite boundary
submodule. This is the pointwise finite cutoff used to choose its torsion lift. -/
private theorem final_boundary_mem_finite_boundaries
    (X : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree) (x : Ambient background X p)
    (hx : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) p x) :
    ∃ n : ℕ, x ∈ boundaries background X (n+1) p := by
  let E := background.classical.obj (X.obj background.auxiliary)
  let D := E.ssData p
  let m : WithTop ℕ := ↑(2-E.r₀).toNat
  obtain ⟨b,hb⟩ := hx
  obtain ⟨n,c,hc⟩ := final_boundary_element_has_finite_stage D b
  refine ⟨n,?_⟩
  have hm : m=0 := by dsimp [m,E]; rw [background.classical.firstPage]; rfl
  change (Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
    Subobject.ofLE (D.Z ⊤) (D.Z m) (D.Z_anti le_top) ≫ D.pageπ m) b = x at hb
  rw [←hc] at hb
  change (Subobject.ofLE (D.B (n:WithTop ℕ)) (D.B ⊤) (D.B_mono le_top) ≫
    Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
    Subobject.ofLE (D.Z ⊤) (D.Z m) (D.Z_anti le_top) ≫ D.pageπ m) c = x at hb
  rw [normalizeInitialProjection D m ⊤ hm le_top] at hb
  try simp only [←Category.assoc,Subobject.ofLE_comp_ofLE] at hb
  change x ∈ LinearMap.range (boundaryLabel background X (↑(((n:ℤ)+1)-1).toNat) p).hom
  rw [show (((n:ℤ)+1)-1).toNat=n by omega]
  exact ⟨c,hb⟩

/-- Every true final boundary has an exact full first-label lift killed by
some lambda power and with zero realization in the selected coordinates. -/
private theorem final_boundary_native_torsion_lift
    (R : RealizationCoordinates background) (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : Ambient background X (s,t))
    (hx : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) x) :
    ∃ (k : ℕ) (b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))),
      b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x ∧
      lambdaMultiply k b=0 ∧
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map b=0 := by
  obtain ⟨k,hk⟩ := final_boundary_mem_finite_boundaries X (s,t) x hx
  obtain ⟨b,hb,ht⟩ := cumulative_boundary_torsion_lift_unshifted X k s t x hk
  exact ⟨k,b,hb,ht,lambda_torsion_realization_zero R (t-s) t k b ht⟩

private theorem lambda_power_first_quotient_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (j : ℕ) (hj : 0<j) (m t : ℤ)
    (b : BiHom m t (background.nu.functor.obj (X.obj background.auxiliary))) :
    lambdaMultiply j b ≫ XModLambdaN.incl _ 1=0 := by
  rw [←(background.quotients.tower _).rho_quotient (show 1≤j by omega),←Category.assoc]
  rw [KIP126.ProofTools.Internal.Leibniz.lambdaMultiply_quotient_zero,zero_comp]

private theorem finite_filtered_first_quotient_zero
    (X : (AdamsObject (coefficients := background.coefficients))) (q j : ℕ) (hq : 0<q) (hj : 0<j) (p t : ℤ)
    (b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : FiltrationAtLeast background.syntheticTower p b) :
    b ≫ (background.quotients.tower _).rho 1 q hq=0 := by
  have hmap := map_preserves_filtration (background.convergentMap
    (.quotient q (.nu X)) (.quotient 1 (.nu X)) ((background.quotients.tower _).rho 1 q hq))
      (t-p,t-j) p b hb
  exact finite_high_filtration_zero X 1 (by decide) (t-p) (t-j) p (by omega) _ hmap

private theorem full_first_label_lambda_projection_detects
    (X : (AdamsObject (coefficients := background.coefficients))) (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (x : Ambient background X (p,t))
    (b : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hb : b ≫ XModLambdaN.incl _ 1=nativeFirstLabel X p t x) :
    Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j x)
      (lambdaMultiply j b ≫ XModLambdaN.incl _ q) := by
  have hfirst : (b ≫ XModLambdaN.incl _ (q-j)) ≫
      (background.quotients.tower _).rho 1 (q-j) (by omega)=nativeFirstLabel X p t x := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hb]
  have h := KIP126.ProofTools.Internal.Leibniz.finite_quotient_lambda_detects X q j hj hjq
    p t x (b ≫ XModLambdaN.incl _ (q-j)) hfirst
  rwa [finite_lambda_inclusion] at h

/-- An affine correction step. Full torsion lifts the final-boundary part,
and a zero-image finite H part corrects c. Both first quotients and the full
source realization are preserved while the error moves one filtration higher.
The restricted subspace hypothesis supplies the H part. -/
private theorem ordinary_affine_correction_step
    (R : RealizationCoordinates background)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c h : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (z u : Ambient background X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hu : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j u) h)
    (hzero : h ≫ XModLambdaN.map (background.nu.functor.map f) q=0)
    (hzu : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (p,t) (z-u)) :
    ∃ (k : ℕ) (D : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary))),
      D ≫ XModLambdaN.incl _ 1=nativeFirstLabel X p t (z-u) ∧
      lambdaMultiply k D=0 ∧
      (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      (c+h) ≫ (background.quotients.tower _).rho 1 q (by omega)=
        c ≫ (background.quotients.tower _).rho 1 q (by omega) ∧
      (c+h) ≫ XModLambdaN.map (background.nu.functor.map f) q=
        c ≫ XModLambdaN.map (background.nu.functor.map f) q ∧
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map (a-lambdaMultiply j D)=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1)
        ((a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h)) := by
  letI := R.additive
  obtain ⟨k,D,hD,hDt,hDr⟩ := final_boundary_native_torsion_lift R X p t (z-u) hzu
  have hDdet := full_first_label_lambda_projection_detects X q j hj hjq p t (z-u) D hD
  have hhfil := KIP126.ProofTools.Internal.Leibniz.detects_filtration
    (.quotient q (.nu X)) (p,t,t-j) _ h hu
  have hhfirst := finite_filtered_first_quotient_zero X q j (by omega) hj p t h hhfil
  have hDfirst := lambda_power_first_quotient_zero X j hj (t-p) t D
  refine ⟨k,D,hD,hDt,?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hDfirst,sub_zero]
  · rw [Preadditive.add_comp,hhfirst,add_zero]
  · rw [Preadditive.add_comp,hzero,add_zero]
  · have hr := realization_lambda_multiply R (t-p) t j D
    rw [hDr] at hr
    rw [Functor.map_sub,Preadditive.comp_sub,hr,sub_zero]
  · have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient q (.nu X)) (p,t,t-j) hz hDdet
    rw [←finiteTargetLabel_sub,show z-(z-u)=u by abel] at hsub
    have hh := detects_sub_filtration (background.convergence (.quotient q (.nu X)))
      (p,t,t-j) hsub hu
    have heq : (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h) =
        a ≫ XModLambdaN.incl _ q-c-lambdaMultiply j D ≫ XModLambdaN.incl _ q-h := by
      rw [Preadditive.sub_comp]
      abel
    rw [heq]
    exact hh

/-- The same actual correction retains an arbitrary specified residual label.
This is used when a full relation space controls the remaining K0 direction. -/
private theorem ordinary_affine_correction_with_residual
    (R : RealizationCoordinates background)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q j : ℕ) (hj : 0<j) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c h : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (z u r : Ambient background X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hu : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j u) h)
    (hzero : h ≫ XModLambdaN.map (background.nu.functor.map f) q=0)
    (hzu : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (p,t) (z-u-r)) :
    ∃ (k : ℕ) (D : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary))),
      D ≫ XModLambdaN.incl _ 1=nativeFirstLabel X p t (z-u-r) ∧
      lambdaMultiply k D=0 ∧
      (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ 1=a ≫ XModLambdaN.incl _ 1 ∧
      (c+h) ≫ (background.quotients.tower _).rho 1 q (by omega)=
        c ≫ (background.quotients.tower _).rho 1 q (by omega) ∧
      (c+h) ≫ XModLambdaN.map (background.nu.functor.map f) q=
        c ≫ XModLambdaN.map (background.nu.functor.map f) q ∧
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map (a-lambdaMultiply j D)=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
        (finiteTargetLabel background X q p t j r)
        ((a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h)) := by
  letI := R.additive
  obtain ⟨k,D,hD,hDt,hDr⟩ := final_boundary_native_torsion_lift R X p t (z-u-r) hzu
  have hDdet := full_first_label_lambda_projection_detects X q j hj hjq p t (z-u-r) D hD
  have hhfil := KIP126.ProofTools.Internal.Leibniz.detects_filtration
    (.quotient q (.nu X)) (p,t,t-j) _ h hu
  have hhfirst := finite_filtered_first_quotient_zero X q j (by omega) hj p t h hhfil
  have hDfirst := lambda_power_first_quotient_zero X j hj (t-p) t D
  refine ⟨k,D,hD,hDt,?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,hDfirst,sub_zero]
  · rw [Preadditive.add_comp,hhfirst,add_zero]
  · rw [Preadditive.add_comp,hzero,add_zero]
  · have hr := realization_lambda_multiply R (t-p) t j D
    rw [hDr] at hr
    rw [Functor.map_sub,Preadditive.comp_sub,hr,sub_zero]
  · have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient q (.nu X)) (p,t,t-j) hz hDdet
    have hh := KIP126.ProofTools.Internal.Mahowald.detects_sub
      (.quotient q (.nu X)) (p,t,t-j) hsub hu
    rw [←finiteTargetLabel_sub,←finiteTargetLabel_sub,
      show z-(z-u-r)-u=r by abel] at hh
    have heq : (a-lambdaMultiply j D) ≫ XModLambdaN.incl _ q-(c+h) =
        a ≫ XModLambdaN.incl _ q-c-lambdaMultiply j D ≫ XModLambdaN.incl _ q-h := by
      rw [Preadditive.sub_comp]
      abel
    rw [heq]
    exact hh

/-- At an intermediate stage the actual source-error label has permanent
ordinary image: the candidate contribution is one filtration higher and the
remaining image is the projection of a complete class. This is why the
restricted condition applies to the actual error, including torsion terms. -/
private theorem ordinary_affine_error_label_image_permanent
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q j : ℕ) (hjq : j<q) (p t : ℤ)
    (a : BiHom (t-p) (t-j) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (T : BiHom (t-p) (t-j) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (z : Ambient background X (p,t))
    (hz : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j z) (a ≫ XModLambdaN.incl _ q-c))
    (hhigh : FiltrationAtLeast background.syntheticTower (p+1)
      (c ≫ XModLambdaN.map (background.nu.functor.map f) q-T ≫ XModLambdaN.incl _ q)) :
    (background.classical.map f).pageMap 2 (p,t) z ∈ permanentCycles background Y (p,t) := by
  have hmap := KIP126.ProofTools.Internal.detects_map (.quotient q (.nu X)) (.quotient q (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) q) (p,t,t-j) _ _ hz
  rw [←middle_finite_label_as_weight X q j p t z] at hmap
  erw [finite_weight_label_natural X Y f q p t (t-j) (by omega) z] at hmap
  have hdiff : FiltrationAtLeast background.syntheticTower (p+1)
      ((a ≫ background.nu.functor.map f-T) ≫ XModLambdaN.incl _ q-
        (a ≫ XModLambdaN.incl _ q-c) ≫ XModLambdaN.map (background.nu.functor.map f) q) := by
    have heq : (a ≫ background.nu.functor.map f-T) ≫ XModLambdaN.incl _ q-
        (a ≫ XModLambdaN.incl _ q-c) ≫ XModLambdaN.map (background.nu.functor.map f) q =
        c ≫ XModLambdaN.map (background.nu.functor.map f) q-T ≫ XModLambdaN.incl _ q := by
      simp only [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality]
      abel
    rw [heq]
    exact hhigh
  have hfinite := detects_of_next_filtration_difference (.quotient q (.nu Y))
    (p,t,t-j) _ _ _ hmap hdiff
  exact KIP126.ProofTools.finite_target_from_full_lift_is_permanent Y q (by omega)
    p t (t-j) (by omega) ((background.classical.map f).pageMap 2 (p,t) z)
      (a ≫ background.nu.functor.map f-T) hfinite

/-- A permanent source has a complete representative even when its final
class is zero. This is used before any strict-source quantification. -/
private theorem permanent_native_source
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t))
    (hx : x ∈ permanentCycles background X (s,t)) :
    ∃ a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      a ≫ XModLambdaN.incl _ 1=nativeFirstLabel X s t x := by
  have hp := KIP126.ProofTools.Paper.NuNumericalExtensions.permanent_cycle_of_member X (s,t) x hx
  obtain ⟨b,hb⟩ := (KIP126.Literature.Standard.permanent_lift X s t x).mp hp
  refine ⟨b ≫ SyntheticCategory.biShift_zero.hom.app _,?_⟩
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
  exact congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hb

/-- The allowed initial true-boundary change of source label is effected
by a full torsion class and preserves the entire specified realization. -/
private theorem full_source_with_boundary_changed_first_label
    (R : RealizationCoordinates background) (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x x' : Ambient background X (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1=nativeFirstLabel X s t x)
    (hxx : IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (x'-x)) :
    ∃ a' : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      a' ≫ XModLambdaN.incl _ 1=nativeFirstLabel X s t x' ∧
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a'=
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a := by
  letI := R.additive
  obtain ⟨k,D,hD,_,hDr⟩ := final_boundary_native_torsion_lift R X s t (x'-x) hxx
  refine ⟨a+D,?_,?_⟩
  · rw [Preadditive.add_comp,ha,hD,←native_first_label_add]
    congr 1
    abel
  · rw [Functor.map_add,Preadditive.comp_add,hDr,add_zero]

private theorem positive_h_native_cycle_image_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (N j L : ℕ) (hL : 0<L) (hN : N=j+L) (s p t : ℤ) (hp : p=s+1)
    (z : Ambient background T.Z (s,t)) (hz : z ∈ cycles background T.Z L (s,t))
    (u : Ambient background T.X (p,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass p (t+1)
      (middleLabelRegrade (X := .shift 1 T.X) (show (s+1,t+1)=(p,t+1) by rw [hp])
        (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z))
      (by simpa using u)) :
    ∃ b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      Detects (background.convergence (.quotient N (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X N p t j u) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=0 := by
  subst p
  subst N
  exact middle_positive_h_native_cycle_image T he hf hg hh hT j L hL s t z hz u hu

/-- One step from the original restricted B-infinity plus H-cycle condition
in the positive-h normalization. Membership in P is derived from the actual
complete image, and both correcting representatives are constructed here. -/
private theorem positive_h_affine_correction_step
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
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u))
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
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a'=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := ordinary_affine_error_label_image_permanent T.X T.Y T.f N j hjN p t
    a c W z hzd hhigh
  obtain ⟨w,hw,u,hu,hzu⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_h_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) (p-1) p t (by omega) w hw u hu
  obtain ⟨k,D,_,_,hfirst,hcfirst,himage,hreal,hnext⟩ := ordinary_affine_correction_step R
    T.X T.Y T.f N j hj hjN p t a c b z u hzd hb hbz hzu
  exact ⟨a-lambdaMultiply j D,c+b,hfirst,hcfirst,himage,hreal,hnext⟩

private theorem positive_h_affine_correction_step_at
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
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u))
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
      (R.sphere m w).hom ≫ background.recovery.realization.map a'=
        (R.sphere m w).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_h_affine_correction_step R T hf hg hh hT N j hj hjN p t P hP hmid a c W herror hhigh

/-- Finite iteration of the actual positive-h correction. The complete
source may change by full torsion, the finite candidate may change by H
images, and their first quotients, the entire candidate image, and the same
complete realization are all retained. The middle condition is imposed on
all actual cycle vectors whose ordinary F2 image lies in the selected P. -/
private theorem positive_h_affine_correction_to_last
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p) (z-z'))
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
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+1)
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hreal,hnext⟩ := positive_h_affine_correction_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower v
          (c₁ ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hreal₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hreal₂.trans hreal,hfinal⟩

/-- The actual ordinary-arrow terminal comparison, allowing the original
complete torsion term in the finite candidate image. The image of the
specified full source is retained after realization. -/
private theorem ordinary_affine_last_filtration_permanence
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (d : ℕ) (hd : 0<d) (p t : ℤ)
    (a : BiHom (t-p) (t-d) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-p) (t-d) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background Y (p,t)) (P : Submodule ℤ (Ambient background Y (p,t)))
    (hP : permanentCycles background Y (p,t) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (p,t)).hom.range ⊓ P ≤ finalBoundaries Y (p,t))
    (herror : FiltrationAtLeast background.syntheticTower p (a ≫ XModLambdaN.incl _ (d+1)-c))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) (d+1) =
      W ≫ XModLambdaN.incl _ (d+1)+finiteTopLabel Y d hd p t v) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (p,t) v ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) v
        ((R.sphere (t-p) (t-d)).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
          (hcomp.nu Y).target.hom) := by
  letI := R.additive
  obtain ⟨e,he⟩ := finiteTopLabel_exists X d hd p t (a ≫ XModLambdaN.incl _ (d+1)-c) herror
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
  exact classical_detects_of_terminal_image X Y (p,t) (p,t)
    ((background.classical.map f).pageMap 2 (p,t)).hom P hP hterminal w v hwp hv e (d+1) herr _ hdet

/-- Complete positive-h affine comparison for an arbitrary specified full
source. The restricted hypothesis uses the actual full cycle spaces, with
j=r-s; its endpoint and the prescribed full torsion term are retained. -/
private theorem positive_h_affine_full_source_permanence
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) ≫
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
  obtain ⟨a₁,c₁,_,_,himage,hreal,hfinal⟩ := positive_h_affine_correction_to_last R T hf hg hh hT
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
  obtain ⟨hp,hdet⟩ := ordinary_affine_last_filtration_permanence R hcomp T.X T.Y T.f d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  refine ⟨hp,?_⟩
  have hrealimage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f)=
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) := by
    simpa only [Functor.map_comp,Category.assoc] using
      congrArg (fun z => z ≫ background.recovery.realization.map (background.nu.functor.map T.f)) hreal
  have ht := realization_homotopy_regrade_full R (show t-s=(t+d)-(s+d) by omega)
    (show t=(t+d)-d by omega) (a₁ ≫ background.nu.functor.map T.f)
  have htransport := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) ht
  simp only [Category.assoc] at htransport
  have hreplace := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
    (show (t+d)-(s+d)=t-s by omega)) ≫ z ≫ (hcomp.nu T.Y).target.hom) hrealimage
  have hresult := htransport.trans (by simpa only [Category.assoc] using hreplace)
  have hresult' : (R.sphere ((t+d)-(s+d)) ((t+d)-d)).hom ≫
      background.recovery.realization.map (a₂ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom := by
    simpa only [a₂,regrade_comp] using hresult
  exact hresult' ▸ hdet

/-- Affine permanence in the positive-h normalization. Permanence
is obtained from x being permanent alone, even if no strict detector exists.
For every specified strict detector the same classical image is retained.
Here d+1 is the quotient length; r=s+j reindexes the original middle layers. -/
public theorem torsion_affine_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨hp,_⟩ := positive_h_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  refine ⟨hp,?_⟩
  intro ξ hxs hdet
  obtain ⟨a₀,ha₀,hreal₀⟩ := prescribed_native_source hcomp T.X s t x ξ hxs hdet
  obtain ⟨a₁,ha₁,hreal₁⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨_,hvdet⟩ := positive_h_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₁ ≫
      (hcomp.nu T.X).target.hom=ξ := by
    have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₁
    simp only [Category.assoc] at h
    exact h.trans hreal₀
  have himage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
      (a₁ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom=ξ ≫ T.f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality T.f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target T.X]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hsource
  have himage' := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
    (show (t+d)-(s+d)=t-s by omega)) ≫ z) himage
  have heq : eqToHom (congrArg (Sphere (C := Spectrum))
      (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f := by
    simpa only [Category.assoc] using himage'
  exact heq ▸ hvdet

/-- The corresponding ordinary-H cycle construction in the positive-g normalization. -/
private theorem positive_g_native_cycle_image_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N j L : ℕ) (hL : 0<L) (hN : N=j+L) (s p t : ℤ) (hp : p=s+1)
    (z : Ambient background T.Z (p,t+1)) (hz : z ∈ cycles background T.Z L (p,t+1))
    (u : Ambient background T.X (p,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass p (t+1)
      ((background.classical.map T.h).pageMap 2 (p,t+1) z)
      (by simpa using u)) :
    ∃ b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      Detects (background.convergence (.quotient N (.nu T.X))) (p,t,t-j)
        (finiteTargetLabel background T.X N p t j u) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=0 := by
  subst p
  subst N
  exact selective_positive_g_native_cycle_image T he hf hg hh hT j L hL s t z hz u hu

/-- One step from the original restricted B-infinity plus H-cycle condition
in the positive-g normalization. Membership in P is derived from the actual
complete image, and both correcting representatives are constructed here. -/
private theorem positive_g_affine_correction_step
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
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u))
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
      (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a'=
        (R.sphere (t-p) (t-j)).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label T.X N j hjN p t
    (a ≫ XModLambdaN.incl _ N-c) herror
  have hzp := ordinary_affine_error_label_image_permanent T.X T.Y T.f N j hjN p t
    a c W z hzd hhigh
  obtain ⟨w,hw,u,hu,hzu⟩ := hmid z hzc (hP hzp)
  obtain ⟨b,hb,hbz⟩ := positive_g_native_cycle_image_at T (by simp [hf,hg,hh]) hf hg hh hT
    N j (N-j) (by omega) (by omega) (p-1) p t (by omega) w hw u hu
  obtain ⟨k,D,_,_,hfirst,hcfirst,himage,hreal,hnext⟩ := ordinary_affine_correction_step R
    T.X T.Y T.f N j hj hjN p t a c b z u hzd hb hbz hzu
  exact ⟨a-lambdaMultiply j D,c+b,hfirst,hcfirst,himage,hreal,hnext⟩

private theorem positive_g_affine_correction_step_at
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
        IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,t) (z-u))
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
      (R.sphere m w).hom ≫ background.recovery.realization.map a'=
        (R.sphere m w).hom ≫ background.recovery.realization.map a ∧
      FiltrationAtLeast background.syntheticTower (p+1) (a' ≫ XModLambdaN.incl _ N-c') := by
  subst m
  subst w
  exact positive_g_affine_correction_step R T hf hg hh hT N j hj hjN p t P hP hmid a c W herror hhigh

/-- Finite iteration of the actual positive-g correction. The complete
source may change by full torsion, the finite candidate may change by H
images, and their first quotients, the entire candidate image, and the same
complete realization are all retained. The middle condition is imposed on
all actual cycle vectors whose ordinary F2 image lies in the selected P. -/
private theorem positive_g_affine_correction_to_last
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (p,m+p) (z-z'))
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
      have hhigh' : FiltrationAtLeast background.syntheticTower (u+1)
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) :=
        background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hhigh
      obtain ⟨a₁,c₁,ha₁,hc₁,hcimage,hreal,hnext⟩ := positive_g_affine_correction_step_at
        R T hf hg hh hT N j hjpos hjN u (m+u) m w (by omega) (by omega)
        (P u) (hP u le_rfl (by omega)) (hmid u le_rfl (by omega)) a c W herror hhigh'
      have hhigh₁ : FiltrationAtLeast background.syntheticTower v
          (c₁ ≫ XModLambdaN.map (background.nu.functor.map T.f) N-W ≫ XModLambdaN.incl _ N) := by
        rw [hcimage]
        exact hhigh
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨a₂,c₂,ha₂,hc₂,hcimage₂,hreal₂,hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1)
        (by omega) (by omega)
        (fun p hp hpv => hP p (by omega) hpv)
        (fun p hp hpv => hmid p (by omega) hpv)
        a₁ c₁ hnext hhigh₁ rfl
      exact ⟨a₂,c₂,ha₂.trans ha₁,hc₂.trans hc₁,hcimage₂.trans hcimage,hreal₂.trans hreal,hfinal⟩

private theorem positive_g_affine_full_source_permanence
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u))
    (a : BiHom (t-s) t (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d))
    (hfirst : a ≫ XModLambdaN.incl _ 1=c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) ≫
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
  obtain ⟨a₁,c₁,_,_,himage,hreal,hfinal⟩ := positive_g_affine_correction_to_last R T hf hg hh hT
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
  obtain ⟨hp,hdet⟩ := ordinary_affine_last_filtration_permanence R hcomp T.X T.Y T.f d hd
    (s+d) (t+d) a₂ c₂ W₂ k hW₂ v P hP hv hterminal herror₂ hc₂
  refine ⟨hp,?_⟩
  have hrealimage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f)=
      (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) := by
    simpa only [Functor.map_comp,Category.assoc] using
      congrArg (fun z => z ≫ background.recovery.realization.map (background.nu.functor.map T.f)) hreal
  have ht := realization_homotopy_regrade_full R (show t-s=(t+d)-(s+d) by omega)
    (show t=(t+d)-d by omega) (a₁ ≫ background.nu.functor.map T.f)
  have htransport := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) ht
  simp only [Category.assoc] at htransport
  have hreplace := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
    (show (t+d)-(s+d)=t-s by omega)) ≫ z ≫ (hcomp.nu T.Y).target.hom) hrealimage
  have hresult := htransport.trans (by simpa only [Category.assoc] using hreplace)
  have hresult' : (R.sphere ((t+d)-(s+d)) ((t+d)-d)).hom ≫
      background.recovery.realization.map (a₂ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom := by
    simpa only [a₂,regrade_comp] using hresult
  exact hresult' ▸ hdet

/-- Affine permanence in the positive-g normalization. Permanence
is obtained from x being permanent alone, even if no strict detector exists.
For every specified strict detector the same classical image is retained.
Here d+1 is the quotient length; r=s+j reindexes the original middle layers. -/
public theorem torsion_affine_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
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
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x →
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨hp,_⟩ := positive_g_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  refine ⟨hp,?_⟩
  intro ξ hxs hdet
  obtain ⟨a₀,ha₀,hreal₀⟩ := prescribed_native_source hcomp T.X s t x ξ hxs hdet
  obtain ⟨a₁,ha₁,hreal₁⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨_,hvdet⟩ := positive_g_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid a₁ c W k hW v P hP hv hterminal (ha₁.trans hfirst.symm) hc
  have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₁ ≫
      (hcomp.nu T.X).target.hom=ξ := by
    have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₁
    simp only [Category.assoc] at h
    exact h.trans hreal₀
  have himage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
      (a₁ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom=ξ ≫ T.f := by
    rw [Functor.map_comp,hcomp.nu_target]
    have hn := background.recovery.nuRealizationIso.hom.naturality T.f
    dsimp only [Functor.comp_map,Functor.id_map] at hn
    simp only [Category.assoc]
    rw [hn,←hcomp.nu_target T.X]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hsource
  have himage' := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
    (show (t+d)-(s+d)=t-s by omega)) ≫ z) himage
  have heq : eqToHom (congrArg (Sphere (C := Spectrum))
      (show (t+d)-(s+d)=t-s by omega)) ≫
        (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f) ≫
          (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f := by
    simpa only [Category.assoc] using himage'
  exact heq ▸ hvdet

private theorem finite_common_lift_positive_h_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t p u : ℤ) (hp : p=s+q+1) (hu : u=t+q)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (p,u))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (p,u) z ((background.classical.map T.g).pageMap 2 (p,u) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1) =
        homotopyRegrade (show (u)-(p)=t-(s+1) by omega)
          (show (u)-q=t by omega)
          (finiteTopLabel T.Y q hq (p) (u) v) := by
  subst p
  subst u
  exact finite_common_lift_positive_h T he hT hf hg hh q hq s t z x v hx hd

/-- Selective permanence: the original classical fold constructs the same finite
candidate, and every specified strict classical source is retained. -/
public theorem selective_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (_hs : 0≤s)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-(s+1)+r)))
    (hPmid : ∀ r : ℤ, (s+1)+1≤r → r<(s+1)+q → permanentCycles background T.Y (r,t-(s+1)+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, (s+1)+1≤r → r<(s+1)+q →
      ∀ z : Ambient background T.X (r,t-(s+1)+r), z ∈ cycles background T.X (q+1-(r-(s+1)).toNat:ℕ) (r,t-(s+1)+r) →
        (background.classical.map T.f).pageMap 2 (r,t-(s+1)+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r-1,t-(s+1)+r),
          zH ∈ cycles background T.Z (q+1-(r-(s+1)).toNat:ℕ) (r-1,t-(s+1)+r) ∧
          ∃ u : Ambient background T.X (r,t-(s+1)+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-(s+1)+r+1)
              (middleLabelRegrade (X := .shift 1 T.X)
                (show (r-1+1,t-(s+1)+r+1)=(r,t-(s+1)+r+1) by congr 1; omega)
                (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
                  (r-1) (t-(s+1)+r) zH)) (by simpa using u) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-(s+1)+r) (z-u))
    (x : Ambient background T.X (s+1,t))
    (hx : x ∈ permanentCycles background T.X (s+1,t))
    (z : Ambient background T.Z (s,t))
    (v : Ambient background T.Y ((s+1)+q,t+q))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) ((s+1)+q,t+q) z
      ((background.classical.map T.g).pageMap 2 ((s+1)+q,t+q) v))
    (_hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (P : Submodule ℤ (Ambient background T.Y ((s+1)+q,t+q)))
    (hP : permanentCycles background T.Y ((s+1)+q,t+q) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 ((s+1)+q,t+q)).hom.range ⊓ P ≤
      finalBoundaries T.Y ((s+1)+q,t+q)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) ((s+1)+q,t+q) v ∧
      ∀ ξ : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) ((s+1),t) x →
        ClassicalDetects (background.classicalConvergence T.X) ((s+1),t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) ((s+1)+q,t+q) v
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+q)-((s+1)+q)=t-(s+1) by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_lift_positive_h_at T (by simp [hf,hg,hh])
    hT hf hg hh q hq s t ((s+1)+q) (t+q) (by omega) rfl z x v hH hdiff
  have hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) (x-x) := by
    change x-x ∈ finalBoundaries T.X (s+1,t)
    rw [sub_self]
    exact Submodule.zero_mem _
  exact torsion_affine_permanence_positive_h T hf hg hh q hq (s+1) t
    Pmid hPmid hmid x x hx hxx c 0 1 (by decide)
    (by simp only [lambdaMultiply,comp_zero]) v P hP hv hterminal hfirst
    (by simpa only [zero_comp,zero_add] using himage)

private theorem finite_common_lift_positive_g_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (s t p u : ℤ) (hp : p=s+q+1) (hu : u=t+q)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (p,u))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((p)+1,(u)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (p) (u) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1) =
        homotopyRegrade (show (u)-(p)=t-(s+1) by omega)
          (show (u)-q=t by omega)
          (finiteTopLabel T.Y q hq (p) (u) v) := by
  subst p
  subst u
  exact finite_common_lift_positive_g T he hT hf hg hh q hq s t z x v hx hd

/-- Selective permanence: the original classical fold constructs the same finite
candidate, and every specified strict classical source is retained. -/
public theorem selective_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (_hs : 0≤s+1)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-(s+1)+r)))
    (hPmid : ∀ r : ℤ, (s+1)+1≤r → r<(s+1)+q → permanentCycles background T.Y (r,t-(s+1)+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, (s+1)+1≤r → r<(s+1)+q →
      ∀ z : Ambient background T.X (r,t-(s+1)+r), z ∈ cycles background T.X (q+1-(r-(s+1)).toNat:ℕ) (r,t-(s+1)+r) →
        (background.classical.map T.f).pageMap 2 (r,t-(s+1)+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-(s+1)+r+1),
          zH ∈ cycles background T.Z (q+1-(r-(s+1)).toNat:ℕ) (r,t-(s+1)+r+1) ∧
          ∃ u : Ambient background T.X (r,t-(s+1)+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-(s+1)+r+1)
              ((background.classical.map T.h).pageMap 2 (r,t-(s+1)+r+1) zH) (by simpa using u) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-(s+1)+r) (z-u))
    (x : Ambient background T.X (s+1,t))
    (hx : x ∈ permanentCycles background T.X (s+1,t))
    (z : Ambient background T.Z (s+1,t+1))
    (v : Ambient background T.Y ((s+1)+q,t+q))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) (((s+1)+q)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+1)+q) (t+q) v))
    (_hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (P : Submodule ℤ (Ambient background T.Y ((s+1)+q,t+q)))
    (hP : permanentCycles background T.Y ((s+1)+q,t+q) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map T.f).pageMap 2 ((s+1)+q,t+q)).hom.range ⊓ P ≤
      finalBoundaries T.Y ((s+1)+q,t+q)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) ((s+1)+q,t+q) v ∧
      ∀ ξ : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary),
        NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) ((s+1),t) x →
        ClassicalDetects (background.classicalConvergence T.X) ((s+1),t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) ((s+1)+q,t+q) v
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+q)-((s+1)+q)=t-(s+1) by omega)) ≫ ξ ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_lift_positive_g_at T (by simp [hf,hg,hh])
    hT hf hg hh q hq s t ((s+1)+q) (t+q) (by omega) rfl z x v hH hdiff
  have hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) (x-x) := by
    change x-x ∈ finalBoundaries T.X (s+1,t)
    rw [sub_self]
    exact Submodule.zero_mem _
  exact torsion_affine_permanence_positive_g T hf hg hh q hq (s+1) t
    Pmid hPmid hmid x x hx hxx c 0 1 (by decide)
    (by simp only [lambdaMultiply,comp_zero]) v P hP hv hterminal hfirst
    (by simpa only [zero_comp,zero_add] using himage)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
