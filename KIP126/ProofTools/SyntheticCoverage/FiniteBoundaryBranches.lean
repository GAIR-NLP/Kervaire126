module

public import KIP126.ProofTools.SyntheticCoverage.Subspaces

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.Subspaces
import all KIP126.ProofTools.Representatives
import all KIP126.ProofTools.SyntheticCoverage.TerminalComparison
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZMod

/-! Finite branches for the third and fourth differentials on the full
source cycle space. Each branch test covers every solution on its kernel;
soundness requires the genuine differential representatives to satisfy
the imposed constraints. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem branch_le_three : (2:ℤ)≤3 := by decide
private theorem branch_le_four : (2:ℤ)≤4 := by decide
private theorem branch_le_five : (2:ℤ)≤5 := by decide

/-- An integer submodule of an F₂ vector space has the induced
F₂ scalar action on the same elements and additive group. -/
private abbrev branchScalar {A : Type v} [AddCommGroup A] [Module ℤ A]
    [Module (ZMod 2) A] (S : Submodule ℤ A) : Module (ZMod 2) S :=
  inferInstanceAs (Module (ZMod 2) ((AddSubgroup.toZModSubmodule 2) S.toAddSubgroup))

private def branchIntLinearMap {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (g : A →+ B) : A →ₗ[ℤ] B where
  toFun := g
  map_add' := g.map_add
  map_smul' c a := map_intCast_smul g ℤ ℤ c a

/-- A total linear relation between F₂ vector spaces admits
a linear selection for constructing representatives. -/
private theorem branch_relation_selection {A B : Type v}
    [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    [Module (ZMod 2) A] [Module (ZMod 2) B]
    (R : Submodule ℤ (A × B)) (htotal : ∀ a, ∃ b, (a,b) ∈ R) :
    ∃ f : A →ₗ[ℤ] B, ∀ a, (a,f a) ∈ R := by
  letI := branchScalar R
  let π : R →ₗ[ZMod 2] A :=
    ((AddMonoidHom.fst A B).comp R.subtype.toAddMonoidHom).toZModLinearMap 2
  have hπ : Function.Surjective π := by
    intro a
    obtain ⟨b,hb⟩ := htotal a
    exact ⟨⟨(a,b),hb⟩,rfl⟩
  obtain ⟨σ,hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  let g : A →+ B := (AddMonoidHom.snd A B).comp (R.subtype.toAddMonoidHom.comp σ.toAddMonoidHom)
  let f : A →ₗ[ℤ] B := {
    toFun := g
    map_add' := g.map_add
    map_smul' := by
      intro c a
      exact map_intCast_smul g ℤ ℤ c a }

  refine ⟨f,fun a => ?_⟩
  have hfst : (σ a).val.1=a := LinearMap.congr_fun hσ a
  have hmem := (σ a).property
  change ((σ a).val.1,(σ a).val.2) ∈ R at hmem
  rw [hfst] at hmem
  exact hmem

variable (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))

@[no_expose] public def branchCycles (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (E.Page 2 p) where
  carrier := {x | ReachesPage E r p x}
  zero_mem' := ⟨0,RepresentsOnPage.zero hr⟩
  add_mem' := reaches_add E
  smul_mem' := by
    intro c x hx
    obtain ⟨xr,hxr⟩ := hx
    refine ⟨c • xr,?_⟩
    convert represents_smul E hxr c using 1
    exact int_smul_eq_zsmul _ c x

private theorem branch_differential_add (r : ℤ) (p : ℤ × ℤ)
    {x x' : E.Page 2 p} {y y' : E.Page 2 (p+E.diffDeg r)}
    (h : HasDifferential E r p (p+E.diffDeg r) x y)
    (h' : HasDifferential E r p (p+E.diffDeg r) x' y') :
    HasDifferential E r p (p+E.diffDeg r) (x+x') (y+y') := by
  obtain ⟨_,xr,yr,hx,hy,hd⟩ := h
  obtain ⟨_,xr',yr',hx',hy',hd'⟩ := h'
  refine ⟨rfl,xr+xr',yr+yr',middle_add hx hx',middle_add hy hy',?_⟩
  simpa only [eqToHom_refl,Category.comp_id,map_add,hd,hd'] using congrArg₂ (·+·) hd hd'

private theorem branch_differential_smul (r : ℤ) (p : ℤ × ℤ)
    {x : E.Page 2 p} {y : E.Page 2 (p+E.diffDeg r)}
    (h : HasDifferential E r p (p+E.diffDeg r) x y) (c : ℤ) :
    HasDifferential E r p (p+E.diffDeg r) (c • x) (c • y) := by
  obtain ⟨_,xr,yr,hx,hy,hd⟩ := h
  refine ⟨rfl,c • xr,c • yr,represents_smul E hx c,represents_smul E hy c,?_⟩
  simpa only [eqToHom_refl,Category.comp_id,map_zsmul] using congrArg (c • ·) hd

private theorem branch_differential_exists (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    {x : E.Page 2 p} (hx : ReachesPage E r p x) :
    ∃ y, HasDifferential E r p (p+E.diffDeg r) x y := by
  obtain ⟨xr,hxr⟩ := hx
  obtain ⟨y,hy⟩ := page_has_initial_representative hr (E.d r p xr)
  exact ⟨y,rfl,xr,E.d r p xr,hxr,hy,by simp⟩

/-- Select a linear representative on any genuine linear cycle domain. -/
private theorem branch_linear_representative (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    {A : Type v} [AddCommGroup A] [Module ℤ A] [Module (ZMod 2) A]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))]
    (ι : A →ₗ[ℤ] E.Page 2 p) (hι : ∀ a, ReachesPage E r p (ι a)) :
    ∃ f : A →ₗ[ℤ] E.Page 2 (p+E.diffDeg r),
      ∀ a, HasDifferential E r p (p+E.diffDeg r) (ι a) (f a) := by
  let R : Submodule ℤ (A × E.Page 2 (p+E.diffDeg r)) := {
    carrier := {z | HasDifferential E r p (p+E.diffDeg r) (ι z.1) z.2}
    zero_mem' := by simpa using hasDifferential_zero (E:=E) hr (rfl : p+E.diffDeg r=p+E.diffDeg r)
    add_mem' := by
      intro a b ha hb
      simpa only [Set.mem_setOf_eq,Prod.fst_add,Prod.snd_add,map_add] using branch_differential_add E r p ha hb
    smul_mem' := by
      intro c a ha
      simpa only [Set.mem_setOf_eq,Prod.smul_fst,Prod.smul_snd,int_smul_eq_zsmul,map_zsmul] using branch_differential_smul E r p ha c }
  exact branch_relation_selection R (fun a => branch_differential_exists E r hr p (hι a))

private theorem branch_zero_reaches (r t : ℤ) (ht : 2≤t) (p : ℤ × ℤ)
    {x : E.Page 2 p} (hx : RepresentsOnPage E r p x 0) : ReachesPage E t p x := by
  obtain ⟨_,z,hz,hzero⟩ := hx
  let D := E.ssData p
  let m : WithTop ℕ := ↑(r-E.r₀).toNat
  obtain ⟨b,hb⟩ := (D.pageπ_eq_zero_iff m z).mp hzero
  apply permanent_reaches E (r:=t) (hr:=ht)
  refine ⟨Subobject.ofLE (D.B m) (D.Z ⊤) ((D.B_mono le_top).trans (D.B_le_Z ⊤)) b,?_⟩
  rw [←hb] at hz
  dsimp only [D,m] at hz ⊢
  simpa only [←ModuleCat.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE] using hz

/-- The true next cycle domain is detected by vanishing of the current
page differential, including the old-boundary ambiguity of E₂ labels. -/
private theorem branch_reaches_next_iff (r : ℤ) (hr : 2 ≤ r) (hr0 : E.r₀ ≤ r)
    (p : ℤ × ℤ) {x : E.Page 2 p} {xr : E.Page r p}
    (hx : RepresentsOnPage E r p x xr) :
    ReachesPage E (r+1) p x ↔ E.d r p xr=0 := by
  constructor
  · exact fun h => represents_d_zero_of_later hr0 (by omega : r<r+1) hx h
  · intro hd
    let D := E.ssData p
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    have hmem : xr ∈ LinearMap.ker (E.d r p).hom := hd
    rw [←subobjectModule_kernel,E.Z_succ r p hr0,subobjectModule_image] at hmem
    obtain ⟨z,hz⟩ := hmem
    let x' := (Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑(2-E.r₀).toNat)
      (D.Z_anti (by dsimp only [n]; exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat+1 by omega)))
      ≫D.pageπ _) z
    have hx' : RepresentsOnPage E r p x' xr := by
      refine ⟨hr,Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm) z,?_,hz⟩
      dsimp only [x']
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    have hx'next : ReachesPage E (r+1) p x' := by
      have hn : (r+1-E.r₀).toNat=n+1 := by dsimp only [n]; omega
      let znext : (Subobject.underlying.obj (D.Z ↑(r+1-E.r₀).toNat) : ModuleCat ℤ) :=
        Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑(r+1-E.r₀).toNat) (by rw [hn]) z
      refine ⟨D.pageπ ↑(r+1-E.r₀).toNat znext,by omega,znext,?_,rfl⟩
      dsimp only [znext,x']
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    have hdiff : RepresentsOnPage E r p (x-x') 0 := by
      simpa only [sub_self] using represents_sub hx hx'
    have hlater := branch_zero_reaches E r (r+1) (by omega) p hdiff
    have hh := reaches_add E hlater hx'next
    simpa only [sub_add_cancel] using hh


private def branchRepresentative (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ)
    [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))] :
    branchCycles E r hr p →ₗ[ℤ] E.Page 2 (p+E.diffDeg r) := by
  letI := branchScalar (branchCycles E r hr p)
  exact (branch_linear_representative E r hr p (branchIntLinearMap (branchCycles E r hr p).subtype.toAddMonoidHom)
    (fun x => x.property)).choose

private theorem branch_representative_spec (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ)
    [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))]
    (x : branchCycles E r hr p) :
    HasDifferential E r p (p+E.diffDeg r) x.val (branchRepresentative E r hr p x) := by
  letI := branchScalar (branchCycles E r hr p)
  exact (branch_linear_representative E r hr p (branchIntLinearMap (branchCycles E r hr p).subtype.toAddMonoidHom)
    (fun x => x.property)).choose_spec x

/-- The differential on E₂ cycle labels, valued in the quotient by earlier
boundaries. Its kernel is the next cycle domain. -/
@[no_expose] public def branchQuotientDifferential (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ)
    [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))] :
    branchCycles E r hr p →ₗ[ℤ]
      ((E.Page 2 (p+E.diffDeg r)) ⧸ pageBoundaries E r hr (p+E.diffDeg r)) :=
  (pageBoundaries E r hr (p+E.diffDeg r)).mkQ.comp (branchRepresentative E r hr p)

private theorem branch_differential_quotient_eq (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ)
    [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))]
    (x : branchCycles E r hr p) (y : E.Page 2 (p+E.diffDeg r))
    (h : HasDifferential E r p (p+E.diffDeg r) x.val y) :
    branchQuotientDifferential E r hr p x=(pageBoundaries E r hr (p+E.diffDeg r)).mkQ y := by
  obtain ⟨_,xr,yr,hxr,hyr,hd⟩ := branch_representative_spec E r hr p x
  obtain ⟨_,xr',yr',hxr',hyr',hd'⟩ := h
  have he : yr=yr' := by
    simp only [eqToHom_refl,Category.comp_id] at hd hd'
    rw [←hd,←hd',hxr.unique hxr']
  have hb : branchRepresentative E r hr p x-y ∈ pageBoundaries E r hr (p+E.diffDeg r) := by
    change RepresentsOnPage E r _ _ 0
    simpa only [he,sub_self] using represents_sub hyr hyr'
  exact (Submodule.Quotient.eq _).mpr hb

/-- Equality of the entire cycle domains. -/
private theorem branch_quotient_kernel_iff (r : ℤ) (hr : 2≤r) (hr0 : E.r₀≤r)
    (p : ℤ × ℤ) [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg r))]
    (x : branchCycles E r hr p) :
    x ∈ LinearMap.ker (branchQuotientDifferential E r hr p) ↔ ReachesPage E (r+1) p x.val := by
  obtain ⟨_,xr,yr,hxr,hyr,hd⟩ := branch_representative_spec E r hr p x
  simp only [eqToHom_refl,Category.comp_id] at hd
  change (pageBoundaries E r hr (p+E.diffDeg r)).mkQ
    (branchRepresentative E r hr p x)=0 ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    have hzero : yr=0 := hyr.unique hy
    apply (branch_reaches_next_iff E r hr hr0 p hxr).mpr
    exact hd.trans hzero
  · intro hx
    have hzero := (branch_reaches_next_iff E r hr hr0 p hxr).mp hx
    change RepresentsOnPage E r _ _ 0
    simpa only [←hd,hzero] using hyr

/-- Every complete candidate d₃ matrix includes its full kernel. On the
actual branch we construct a linear d₄ representative on that entire
kernel; sound necessary constraints include it, so a range test for all
solutions proves there are no new fourth-page boundaries. -/
private theorem finite_boundary_branches
    (hstart : E.r₀≤2) (p : ℤ × ℤ)
    [Module (ZMod 2) (E.Page 2 p)]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg 3))]
    [Module (ZMod 2) (E.Page 2 (p+E.diffDeg 4))]
    (candidates : Finset (branchCycles E 3 branch_le_three p →ₗ[ℤ]
      ((E.Page 2 (p+E.diffDeg 3)) ⧸ pageBoundaries E 3 branch_le_three (p+E.diffDeg 3))))
    (hactual : branchQuotientDifferential E 3 branch_le_three p ∈ candidates)
    (constraints : ∀ T : branchCycles E 3 branch_le_three p →ₗ[ℤ]
      ((E.Page 2 (p+E.diffDeg 3)) ⧸ pageBoundaries E 3 branch_le_three (p+E.diffDeg 3)),
      (LinearMap.ker T →ₗ[ℤ] E.Page 2 (p+E.diffDeg 4)) → Prop)
    (hsound : ∀ T ∈ candidates, T=branchQuotientDifferential E 3 branch_le_three p →
      ∀ f : LinearMap.ker T →ₗ[ℤ] E.Page 2 (p+E.diffDeg 4),
        (∀ x, HasDifferential E 4 p (p+E.diffDeg 4) x.val.val (f x)) → constraints T f)
    (L : Submodule ℤ (E.Page 2 (p+E.diffDeg 4)))
    (hL : pageBoundaries E 4 branch_le_four (p+E.diffDeg 4)=L)
    (htest : ∀ T ∈ candidates, ∀ f, constraints T f → LinearMap.range f ≤ L) :
    pageBoundaries E 5 branch_le_five (p+E.diffDeg 4)=L := by
  let T := branchQuotientDifferential E 3 branch_le_three p
  letI := branchScalar (branchCycles E 3 branch_le_three p)
  letI := branchScalar (LinearMap.ker T)
  let ι : LinearMap.ker T →ₗ[ℤ] E.Page 2 p :=
    branchIntLinearMap ((branchCycles E 3 branch_le_three p).subtype.toAddMonoidHom.comp
      (LinearMap.ker T).subtype.toAddMonoidHom)
  have hι : ∀ x, ReachesPage E 4 p (ι x) := by
    intro x
    exact (branch_quotient_kernel_iff E 3 branch_le_three (by omega) p x.val).mp x.property
  obtain ⟨f,hf⟩ := branch_linear_representative E 4 branch_le_four p ι hι
  have hconstraint : constraints T f := hsound T hactual rfl f hf
  have hrange := htest T hactual f hconstraint
  apply boundary_complete_of_targets E hstart 4 (by all_goals decide) p L
  · exact le_of_eq hL
  · rw [←hL]
    intro y hy
    have hreaches := branch_zero_reaches E 4 5 (by all_goals decide) (p+E.diffDeg 4) hy
    obtain ⟨yr,hyr⟩ := hreaches
    change RepresentsOnPage E 5 _ y 0
    simpa only [represents_later_zero (by decide : (4:ℤ)≤5) hy hyr] using hyr
  · intro x hx
    have hx3 : x ∈ branchCycles E 3 branch_le_three p := reaches_earlier (by all_goals decide) (by decide : (3:ℤ)≤4) hx
    let x3 : branchCycles E 3 branch_le_three p := ⟨x,hx3⟩
    have hxK : x3 ∈ LinearMap.ker T :=
      (branch_quotient_kernel_iff E 3 branch_le_three (by omega) p x3).mpr hx
    let xK : LinearMap.ker T := ⟨x3,hxK⟩
    exact ⟨f xK,hrange ⟨xK,rfl⟩,hf xK⟩

/-- Replacing an unknown early-boundary space by a reliable upper bound
preserves every true solution of a family of linear naturality constraints.
The residuals may couple arbitrary vectors or entire matrix columns. -/
private theorem branch_constraints_upper_bound
    {ι A : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℤ (V i)]
    (residual : ∀ i, A → V i) (B U : ∀ i, Submodule ℤ (V i))
    (hupper : ∀ i, B i ≤ U i) (a : A) (ha : ∀ i, residual i a ∈ B i) :
    ∀ i, residual i a ∈ U i := fun i => hupper i (ha i)


/-- Complete d₂ determines the whole initial branch domain. -/
private theorem branch_cycles_three_eq_d2_kernel (hstart : E.r₀≤2) (p : ℤ × ℤ) :
    branchCycles E 3 branch_le_three p = LinearMap.ker (E.d 2 p).hom := by
  ext x
  exact PageThree.reachesPage_iff_d2_eq_zero hstart p x

open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route

public abbrev branchStandardSequence (X : (AdamsObject (coefficients := background.coefficients))) :=
  background.classical.obj (X.obj background.auxiliary)

/-- The actual E₂ groups are killed by two. Apply
first-quotient sphere-automorphism invariance to -id, then reflect the
result through the injective native first label. This concerns actual
first-quotient classes, never unquotiented homotopy groups. -/
private theorem standard_branch_e2_add_self_zero (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x : (branchStandardSequence X).Page 2 (s,t)) : x+x=0 := by
  let u : KIP126.Synthetic.Context.Smn (Syn:=SyntheticSpectrum) (t-s) t ≅
      KIP126.Synthetic.Context.Smn (t-s) t := {
    hom := -𝟙 _
    inv := -𝟙 _
    hom_inv_id := by simp
    inv_hom_id := by simp }
  have h := KIP126.ProofTools.Internal.Mahowald.sphere_automorphism_first_finite
    X (t-s) t u (KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel X s t x)
  have hneg : -KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel X s t x=
      KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel X s t x := by
    simpa only [u,Preadditive.neg_comp,Category.id_comp] using h
  apply KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_injective X s t
  rw [native_first_label_add]
  have hz : KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel X s t 0=0 := by
    simp only [KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel_eq_regrade,
      map_zero,KIP126.ProofTools.Internal.MahowaldLeibniz.last_layer_regrade_zero,zero_comp]
  rw [hz]
  exact (congrArg (fun y => y+KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel X s t x)
    hneg.symm).trans (neg_add_cancel _)

@[no_expose] public instance standardBranchScalar (X : (AdamsObject (coefficients := background.coefficients))) (p : ℤ × ℤ) :
    Module (ZMod 2) ((branchStandardSequence X).Page 2 p) :=
  AddCommGroup.zmodModule (n:=2) (fun x => by
    simpa only [two_nsmul] using standard_branch_e2_add_self_zero X p.1 p.2 x)

/-- The generic cycle space is the classical Z-space, with parameter r
denoting the paper’s `Z_{<r}`. -/
private theorem standard_branch_cycles_eq (X : (AdamsObject (coefficients := background.coefficients))) (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ) :
    branchCycles (branchStandardSequence X) r hr p = KIP126.Literature.cycles background X (r-1) p := by
  ext x
  constructor
  · intro hx
    exact ((KIP126.ProofTools.isCycle_iff_reaches background X r hr p x).mpr hx).2
  · intro hx
    exact (KIP126.ProofTools.isCycle_iff_reaches background X r hr p x).mp ⟨by omega,hx⟩

/-- The zero-class definition is exactly the actual cumulative boundary
subspace, with the indexing used in the original statement. -/
private theorem standard_branch_boundaries_eq (X : (AdamsObject (coefficients := background.coefficients))) (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ) :
    pageBoundaries (branchStandardSequence X) r hr p = KIP126.Literature.boundaries background X (r-1) p := by
  ext x
  constructor
  · intro hx
    obtain ⟨_,z,hz,hzero⟩ := hx
    let E := branchStandardSequence X
    let D := E.ssData p
    let m : WithTop ℕ := ↑(r-E.r₀).toNat
    obtain ⟨b,hb⟩ := (D.pageπ_eq_zero_iff m z).mp hzero
    have hn : (↑(r-1-1).toNat : WithTop ℕ)=m := by
      dsimp only [m,E,branchStandardSequence]
      rw [background.classical.firstPage]
      congr 2
      omega
    change ∃ b, KIP126.Literature.boundaryLabel background X (↑(r-1-1).toNat) p b=x
    rw [hn]
    refine ⟨b,?_⟩
    rw [KIP126.ProofTools.initialProjection_eq_cycleLabel background X r hr p] at hz
    rw [←hb] at hz
    change (Subobject.ofLE (D.B m) (D.Z m) _≫KIP126.Literature.cycleLabel background X m p) b=x at hz
    dsimp only [D,E,branchStandardSequence] at hz
    simpa only [KIP126.Literature.cycleLabel,KIP126.Literature.boundaryLabel,
      ←Category.assoc,Subobject.ofLE_comp_ofLE] using hz
  · intro hx
    exact KIP126.ProofTools.representsOnPage_of_congruent background X hr
      (RepresentsOnPage.zero hr) ⟨by omega,by simpa only [sub_zero] using hx⟩

/-- The finite-branch criterion on the Standard Adams sequence. Its F₂
structures come from first-quotient sphere invariance. The hypotheses
specify the boundary equality, inclusion of the true d₃ quotient matrix,
and soundness of the candidate-matrix and ordinary-map constraints. -/
public theorem standard_finite_boundary_branches
    (X : (AdamsObject (coefficients := background.coefficients))) (p : ℤ × ℤ)
    (candidates : Finset (branchCycles (branchStandardSequence X) 3 (by decide) p →ₗ[ℤ]
      (((branchStandardSequence X).Page 2 (p+(branchStandardSequence X).diffDeg 3)) ⧸
        pageBoundaries (branchStandardSequence X) 3 (by decide) (p+(branchStandardSequence X).diffDeg 3))))
    (hactual : branchQuotientDifferential (branchStandardSequence X) 3 (by decide) p ∈ candidates)
    (constraints : ∀ T : branchCycles (branchStandardSequence X) 3 (by decide) p →ₗ[ℤ]
      (((branchStandardSequence X).Page 2 (p+(branchStandardSequence X).diffDeg 3)) ⧸
        pageBoundaries (branchStandardSequence X) 3 (by decide) (p+(branchStandardSequence X).diffDeg 3)),
      (LinearMap.ker T →ₗ[ℤ] (branchStandardSequence X).Page 2 (p+(branchStandardSequence X).diffDeg 4)) → Prop)
    (hsound : ∀ T ∈ candidates, T=branchQuotientDifferential (branchStandardSequence X) 3 (by decide) p →
      ∀ f : LinearMap.ker T →ₗ[ℤ] (branchStandardSequence X).Page 2 (p+(branchStandardSequence X).diffDeg 4),
        (∀ x, HasDifferential (branchStandardSequence X) 4 p (p+(branchStandardSequence X).diffDeg 4)
          x.val.val (f x)) → constraints T f)
    (L : Submodule ℤ ((branchStandardSequence X).Page 2 (p+(branchStandardSequence X).diffDeg 4)))
    (hL : KIP126.Literature.boundaries background X 3 (p+(branchStandardSequence X).diffDeg 4)=L)
    (htest : ∀ T ∈ candidates, ∀ f, constraints T f → LinearMap.range f ≤ L) :
    KIP126.Literature.boundaries background X 4 (p+(branchStandardSequence X).diffDeg 4)=
      KIP126.Literature.boundaries background X 3 (p+(branchStandardSequence X).diffDeg 4) ∧
    KIP126.Literature.boundaries background X 3 (p+(branchStandardSequence X).diffDeg 4)=L := by
  have hstart : (branchStandardSequence X).r₀≤2 := by rw [background.classical.firstPage]
  have hL' : pageBoundaries (branchStandardSequence X) 4 branch_le_four
      (p+(branchStandardSequence X).diffDeg 4)=L := by
    rw [standard_branch_boundaries_eq]
    exact hL
  have h := finite_boundary_branches (branchStandardSequence X) hstart p candidates hactual
    constraints hsound L hL' htest
  rw [standard_branch_boundaries_eq] at h
  exact ⟨h.trans hL.symm,hL⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
