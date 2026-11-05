module

import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.StrictSource
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.FiniteFiltration

/-! Prescribed classical representatives without a nonzero-grade hypothesis.
The first-label comparison retains the actual classical representative,
including when its associated grade is zero. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem classical_detects_difference
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a b : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (hb : ClassicalDetects (background.classicalConvergence X) (s,t) x b) :
    a-b ∈ (background.classicalTower.tower (X.obj background.auxiliary)).filtrationSubmodule
      (s+1) (t-s) := by
  obtain ⟨za,hza,ar,har,hga⟩ := ha
  obtain ⟨zb,hzb,br,hbr,hgb⟩ := hb
  have hinf := SSData.infinity_projection_eq_of_page_projection_eq
    ((background.classical.obj (X.obj background.auxiliary)).ssData (s,t))
    _ za zb (hza.trans hzb.symm)
  have hgrade := hga.symm.trans ((congrArg
    (fun z => ((background.classicalConvergence X).identification (s,t)).hom z) hinf).trans hgb)
  have h := (element_grade_equal_iff
    (background.classicalTower.tower (X.obj background.auxiliary)).filtration s (t-s) ar br).mp hgrade
  rw [har,hbr] at h
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using h

private theorem full_source_detects_first_label
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x) :
    ClassicalDetects (background.classicalConvergence X) (s,t) x
      ((R.sphere (t-s) t).hom ≫ background.recovery.realization.map a ≫
        (hcomp.nu X).target.hom) := by
  obtain ⟨y,hy,_,hdet⟩ := full_representative_first_label_detects R hcomp X s t a
  have hxy := native_first_label_injective X s t (hy.symm.trans ha)
  simpa only [hxy] using hdet

/-- Two labels of the same specified classical representative have the
same infinity class, so their difference is a true final boundary. -/
private theorem classical_detects_label_difference
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x y : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (hy : ClassicalDetects (background.classicalConvergence X) (s,t) y a) :
    IsFinalBoundary (background.classical.obj (X.obj background.auxiliary)) (s,t) (x-y) := by
  obtain ⟨zx,hzx,ar,har,hgx⟩ := hx
  obtain ⟨zy,hzy,br,hbr,hgy⟩ := hy
  have hab : ar = br := (ModuleCat.mono_iff_injective _).mp inferInstance (har.trans hbr.symm)
  have hinf := (ModuleCat.mono_iff_injective
    ((background.classicalConvergence X).identification (s,t)).hom).mp inferInstance
    (hgx.trans (by simpa only [hab] using hgy.symm))
  let D := (background.classical.obj (X.obj background.auxiliary)).ssData (s,t)
  have hz : D.pageπ ⊤ (zx-zy)=0 := by rw [map_sub,hinf,sub_self]
  obtain ⟨b,hb⟩ := (D.pageπ_eq_zero_iff ⊤ (zx-zy)).mp hz
  refine ⟨b,?_⟩
  change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ _)
    (Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) b) = x-y
  rw [hb,map_sub,hzx,hzy]

private theorem classical_filtration_regrade
    (X : AdamsObject (coefficients := background.coefficients)) (s m m' : ℤ)
    (h : m'=m) (a : HomotopyGroup m (X.obj background.auxiliary)) :
    eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫ a ∈
      (background.classicalTower.tower (X.obj background.auxiliary)).filtrationSubmodule s m' ↔
    a ∈ (background.classicalTower.tower (X.obj background.auxiliary)).filtrationSubmodule s m := by
  subst m'
  simp only [eqToHom_refl,Category.id_comp]

/-- A filtered classical class has a complete native lift. A nonzero class
is first lifted at its exact filtration, then lowered by a lambda power. -/
private theorem native_lift_of_classical_filtration
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (ha : a ∈ (background.classicalTower.tower (X.obj background.auxiliary)).filtrationSubmodule s (t-s)) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      (KIP126.Literature.Standard.realizationData.sphere (t-s) t).hom ≫
        background.recovery.realization.map b ≫ (hcomp.nu X).target.hom = a := by
  classical
  let R := KIP126.Literature.Standard.realizationData
  letI := R.additive
  by_cases ha0 : a=0
  · refine ⟨0,?_⟩
    simp only [Functor.map_zero,comp_zero,zero_comp,ha0]
  let T := background.classicalTower.tower (X.obj background.auxiliary)
  have hex : ∃ n : ℕ, a ∉ T.filtrationSubmodule n (t-s) := by
    by_contra h
    apply ha0
    apply classical_filtration_separated X (t-s) a
    intro n
    change a ∈ T.filtrationSubmodule n (t-s)
    exact not_not.mp (fun hn => h ⟨n,hn⟩)
  obtain ⟨n,hn⟩ := hex
  have hsn : s ≤ (n:ℤ) := by
    by_contra h
    exact hn (T.filtrationSubmodule_antitone (t-s) (by omega) ha)
  have hN : s+((n-s).toNat:ℤ)=(n:ℤ) := by omega
  obtain ⟨u,hsu,_,hu,hu'⟩ := KIP126.ProofTools.first_nonzero_filtration_grade
    (fun j => (T.filtrationSubmodule j (t-s)).toAddSubgroup) s (n-s).toNat a ha
    (by change a ∉ T.filtrationSubmodule (s+((n-s).toNat:ℤ)) (t-s); rw [hN]; exact hn)
  change a ∈ T.filtrationSubmodule u (t-s) at hu
  change a ∉ T.filtrationSubmodule (u+1) (t-s) at hu'
  let au : HomotopyGroup ((t-s+u)-u) (X.obj background.auxiliary) :=
    eqToHom (congrArg (Sphere (C := Spectrum)) (show (t-s+u)-u=t-s by omega)) ≫ a
  have hu0 : au ∈ T.filtrationSubmodule u ((t-s+u)-u) := by
    exact (classical_filtration_regrade X u (t-s) ((t-s+u)-u) (by omega) a).mpr hu
  have hu1 : au ∉ T.filtrationSubmodule (u+1) ((t-s+u)-u) := by
    exact fun h => hu' ((classical_filtration_regrade X (u+1) (t-s) ((t-s+u)-u) (by omega) a).mp h)
  obtain ⟨det⟩ := nonzeroClassicalDetection_of_exact
    (background.classicalConvergence X) (u,t-s+u) au hu0 hu1
  have hsurv : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary))
      (u,t-s+u) det.pageElement := ⟨det.representative,rfl,det.nonzero⟩
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp X u (t-s+u) det.pageElement
    au hsurv det.detects
  let k := (u-s).toNat
  have hk : (k:ℤ)=u-s := by dsimp only [k]; omega
  let b' : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) (lambdaMultiply k b)
  refine ⟨b',?_⟩
  dsimp only [b']
  rw [←Category.assoc,realization_homotopy_regrade_full]
  have hr := realization_lambda_multiply R ((t-s+u)-u) (t-s+u) k b
  rw [Category.assoc,Category.assoc,←Category.assoc (R.sphere _ _).hom,hr,Category.assoc,hreal]
  simp only [au,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]

private theorem prescribed_native_source_nonstrict
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      b ≫ XModLambdaN.incl _ 1=nativeFirstLabel X s t x ∧
      (KIP126.Literature.Standard.realizationData.sphere (t-s) t).hom ≫
        background.recovery.realization.map b ≫ (hcomp.nu X).target.hom = a := by
  have hmem : a ∈ (background.classicalTower.tower (X.obj background.auxiliary)).filtrationSubmodule s (t-s) := by
    obtain ⟨_,_,ar,har,_⟩ := ha
    have h : a ∈ ModuleCat.subobjectModule _
        ((background.classicalTower.tower (X.obj background.auxiliary)).filtration.F s (t-s)) := ⟨ar,har⟩
    simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using h
  obtain ⟨b,hreal⟩ := native_lift_of_classical_filtration hcomp X s t a hmem
  obtain ⟨y,hy,_,hdet⟩ := full_representative_first_label_detects
    KIP126.Literature.Standard.realizationData hcomp X s t b
  rw [hreal] at hdet
  have hxy := classical_detects_label_difference X s t x y a ha hdet
  obtain ⟨b',hb',hreal'⟩ := full_source_with_boundary_changed_first_label
    KIP126.Literature.Standard.realizationData X s t y x b hy hxy
  refine ⟨b',hb',?_⟩
  rw [←Category.assoc,hreal',Category.assoc]
  exact hreal

end
end KIP126.ProofTools.Internal.SyntheticCoverage
